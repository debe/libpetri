/**
 * @module clock
 *
 * The executor's time seam, per **TIME-015** (`spec/03-timing.md`).
 *
 * An executor reads time from two unrelated sources and waits on a third thing —
 * the next timing boundary. {@link Clock} bundles all three so a host can drive a
 * net on virtual time. The seam is **per executor**, never per net: a `PetriNet` is
 * immutable and shared across `compose()` ([MOD-010]), so a net-attached clock
 * would have to be merged at every composition, and a host running two executors in
 * one process — a differential harness, or one net under virtual time while another
 * runs live — needs them on independent clocks. That is precisely what a
 * process-global test-framework clock (`vi.useFakeTimers`) cannot express.
 *
 * Supplying no clock leaves the executor on `performance.now()`, `Date.now()` and
 * `setTimeout` exactly as before ([TIME-015] AC#1).
 *
 * ## Scope limit: action timeouts are not virtualized
 *
 * One kind of net-declared timing stays on real time. The `timeout(after, recovery)`
 * branch of an output spec ([IO-013]) is enforced by a **per-action** wait, while this
 * seam owns the executor's single orchestrator wait — so under an injected clock the
 * recovery tokens are stamped from {@link Clock.epochNow} ([TIME-015] AC#13), but the
 * `after` interval itself still elapses in real time. A net declaring `timeout(…)` is
 * therefore **not fully virtualizable**: a host replaying one waits the real interval,
 * even though its `delayed`, `window`, `deadline` and `exact` timings do not.
 *
 * Stated explicitly because the rest of this seam would otherwise imply the opposite, and
 * the mix is easy to hit — a host that compiles its own sleeps to `delayed(…)` and its step
 * timeouts to `Out.Timeout` gets one virtualized and one not.
 *
 * It is a boundary, not an oversight: bringing action timeouts under the seam means the
 * clock mediating every in-flight action's wait rather than one orchestrator wait, which is
 * a larger change than adding a seam. And the tempting half-fix is **forbidden** — routing
 * the timeout interval through the clock while the action's own wait stays on real time
 * would fire the recovery branch at a virtual instant the action never reached, producing a
 * recovery for work that is still running.
 */

import type { Token } from '../core/token.js';
import { tokenAt } from '../core/token.js';

/**
 * A host-supplied time source for one executor ([TIME-015]).
 *
 * ## Two time bases, not one
 *
 * {@link now} and {@link epochNow} have **unrelated origins** and MUST NOT be
 * conflated — in this runtime they correspond to `performance.now()` and
 * `Date.now()`, whose zero points differ. A host MAY derive both from one logical
 * source, and should when it needs them to agree across a replay.
 *
 * ## Contract
 *
 * All five hold. None is an error condition the runtime can detect, and each is
 * silent when violated — hence spelled out rather than validated:
 *
 * 1. **{@link now} is monotonic.** It MUST NOT go backwards. Every timing decision
 *    is `now() - enabledAtMs`, so a backwards step makes elapsed time negative,
 *    re-opens the earliest bound of an already-due transition, and can stall the
 *    net indefinitely with no error raised.
 * 2. **{@link sleep} suspends or advances — and where there is no boundary, it
 *    suspends.** Given a *finite* `delayMs` it MUST either suspend until that
 *    boundary or advance {@link now} to it; a host clock that advances only on
 *    demand, paired with a `sleep` that does neither, spins forever with elapsed
 *    time never reaching the bound.
 *
 *    **`Infinity` is not a boundary, and neither of those applies to it.** The
 *    executor passes `Infinity` whenever nothing timed is pending — which is most
 *    of the time: parked on an in-flight action, or waiting for an external event.
 *    There is no instant to advance to, so the wait MUST **suspend until woken**.
 *    Returning immediately is non-conforming: the executor re-enters the wait at
 *    once and the loop becomes a spin of resolved promises. JavaScript makes that
 *    worse than a busy core — a loop of already-resolved promises never yields to
 *    the macrotask queue, so timers and I/O never run, the external event the
 *    executor is waiting for can never arrive, and not even the `run(timeoutMs)`
 *    budget fires. Measured on this runtime: a host that returned on `Infinity`
 *    produced no output in 30 seconds and starved a 200ms `setTimeout`. Test your
 *    clock against `Infinity` explicitly; it is the case a first reading misses.
 * 3. **{@link sleep} MAY complete early, for no reason.** The executor re-checks
 *    its boundary conditions and never treats "the wait completed" as "the
 *    boundary is reached", so a host may resolve whenever it likes.
 * 4. **{@link sleep} resolves on abort — it does not reject.** The signal fires
 *    during `close()`, which is exactly the path where a rejection escapes
 *    unobserved as an unhandled rejection.
 * 5. **The `ready` predicate is time-free.** It is cheap, repeatable and
 *    side-effect free, and a host MUST NOT wrap it in anything that consults a
 *    clock — a time-based predicate reintroduces the real clock behind the seam.
 *
 * @example A virtual clock that advances on demand
 * ```ts
 * class VirtualClock implements Clock {
 *   private t = 0;
 *   now(): number { return this.t; }
 *   epochNow(): number { return 1_700_000_000_000 + this.t; }
 *
 *   sleep(delayMs: number, ready: () => boolean, signal: AbortSignal): Promise<void> {
 *     if (ready()) return Promise.resolve();       // work already queued: don't move time
 *     if (delayMs === Infinity) {
 *       // No boundary to advance to, so suspend until something wakes us (contract 2).
 *       // Returning here instead would spin the executor and starve the event loop —
 *       // including the very event it is waiting for.
 *       return new Promise(resolve => {
 *         signal.addEventListener('abort', () => resolve(), { once: true });
 *       });
 *     }
 *     this.t += delayMs;                           // contract 2: advance to the boundary
 *     return Promise.resolve();
 *   }
 * }
 * ```
 */
export interface Clock {
  /**
   * The **firing clock**: a monotonic source, in milliseconds, with an arbitrary
   * origin. Drives enablement stamps ([TIME-010]), every elapsed-time decision
   * ([TIME-004], [TIME-005], [TIME-006]), deadline enforcement ([TIME-013]) and the
   * wake-up interval. Must never go backwards (contract 1).
   *
   * Defaults to `performance.now()`.
   */
  now(): number;

  /**
   * The **epoch clock**: wall-clock milliseconds since the Unix epoch. Stamps the
   * `createdAt` of every token the *executor* produces ([CORE-011]) and the
   * `timestamp` of every emitted event. Never feeds a firing decision.
   *
   * Defaults to `Date.now()`.
   *
   * **The line is who chooses the timestamp, not who supplies the value.** An action
   * calling `ctx.output(place, value)` supplies a value; libpetri constructs the token
   * and picks its `createdAt`, so that token is executor-produced and follows this
   * clock — as do raw-value injections and the recovery outputs synthesised when an
   * action timeout fires. Only a token the **host itself** constructs, whose timestamp
   * it has therefore already chosen, falls outside: those are never re-stamped, which
   * is what keeps a [CORE-073] restore faithful. {@link seedToken} covers the initial
   * marking, the one place a host must mint before any executor exists.
   */
  epochNow(): number;

  /**
   * Waits for the next timing boundary. **The seam owns the wait**: a clock
   * supplying only {@link now} would leave the executor sleeping on the real timer,
   * so stamps go virtual while waiting stays real and a `delayed(1000)` still costs
   * a real second.
   *
   * The returned promise resolves when the host decides the wait is over. The
   * executor races it against its own wake sources (an in-flight action completing,
   * an external event arriving), re-checks every boundary afterwards, and abandons a
   * `sleep` promise that loses the race — so resolving *late*, or not at all while
   * another wake source can still fire, is safe.
   *
   * Resolving **early is not**, when `delayMs` is `Infinity`: see contract 2. The
   * race does protect a single early resolution, which is why contract 3 permits a
   * spurious one — but a host that returns on `Infinity` *every* time turns the
   * executor's loop into a spin that starves the event loop it is waiting on.
   *
   * **Injecting from in here: inject and return, never await admission.** This is the
   * only admission path a clock-only host has, and it is legal — but the promise
   * {@link import('./bitmap-net-executor.js').BitmapNetExecutor.inject} returns settles
   * when the *orchestrator* admits the token, and inside this call the orchestrator is
   * the caller. Awaiting it suspends the only thing that could resolve it. Use
   * `injectNoAwait(place, value)`, which has no result to await; the tokens arrive in
   * the executor's external-events phase on a following cycle either way.
   *
   * @param delayMs milliseconds until the next boundary — an earliest firing time or
   *        a deadline needing enforcement — or `Infinity` when no timed transition is
   *        pending and the executor is waiting purely for external work. Never `0`:
   *        a boundary already due is not waited on at all (the executor returns and
   *        lets the next cycle act on it).
   * @param ready a time-free predicate that is `true` when work is already queued and
   *        the executor would return immediately. A host consults it to avoid
   *        advancing its clock past work that is already waiting (contract 5).
   * @param signal aborted when the executor is closing ([ENV-013]). On abort the
   *        returned promise MUST **resolve**, never reject (contract 4).
   */
  sleep(delayMs: number, ready: () => boolean, signal: AbortSignal): Promise<void>;
}

/**
 * Mints a **fresh seed token** stamped from `clock`'s epoch reading, for an initial marking
 * ([TIME-015] AC#12).
 *
 * An initial marking is built *before* any executor exists, so no seam reaches it: a marking
 * seeded with `tokenOf(value)` carries a wall-clock `createdAt` that differs on every attempt,
 * *inside the marking*, and a replay diverges before the run has begun. This is the one token
 * path a host cannot route through its clock by choosing a different executor option, which is
 * why it gets an affordance rather than a note.
 *
 * It mints; it never re-stamps. Tokens the host already holds — restored from a snapshot
 * ([CORE-073]), or carried over from an earlier run — keep their own `createdAt`, and silently
 * re-stamping them would defeat exactly the preservation a restore exists for. Pass those
 * through unchanged, or build them with `tokenAt(value, createdAt)` directly.
 *
 * @example
 * ```ts
 * const clock = new VirtualClock();
 * const initial = new Map([[REQ, [seedToken(clock, 'x')]]]);
 * const executor = new BitmapNetExecutor(net, initial, { clock, deadlineToleranceMs: 0 });
 * ```
 */
export function seedToken<T>(clock: Clock, value: T): Token<T> {
  return tokenAt(value, clock.epochNow());
}

/**
 * The {@link Clock} the executor behaves as if it had when none is supplied:
 * `performance.now()`, `Date.now()` and `setTimeout`.
 *
 * Supplying this explicitly is **semantically** identical to supplying nothing, and
 * exists so a host can delegate to the default rather than reimplement it — a clock
 * that virtualizes only `now()`, say, or one that logs each wait. It is not quite
 * *operationally* identical: with no clock the executor skips the seam entirely and
 * allocates nothing extra, so the zero-clock path stays the one existing timing
 * conformance runs on ([TIME-015] AC#1).
 *
 * Its `sleep` honours the abort signal by resolving (contract 4) and clears its
 * timer when it does, so a `close()` mid-wait leaves nothing pending.
 */
export function systemClock(): Clock {
  return SYSTEM_CLOCK;
}

const SYSTEM_CLOCK: Clock = {
  now(): number {
    return performance.now();
  },
  epochNow(): number {
    return Date.now();
  },
  sleep(delayMs: number, _ready: () => boolean, signal: AbortSignal): Promise<void> {
    if (signal.aborted) return Promise.resolve();
    // `Infinity` means nothing timed is pending: suspend until the executor's own
    // wake sources fire, or until close aborts us. The executor races this promise,
    // so never resolving is correct here rather than a stall.
    if (!(delayMs < Infinity)) {
      return new Promise<void>(resolve => {
        signal.addEventListener('abort', () => resolve(), { once: true });
      });
    }
    return new Promise<void>(resolve => {
      const onAbort = (): void => {
        clearTimeout(timer);
        resolve();
      };
      const timer = setTimeout(() => {
        signal.removeEventListener('abort', onAbort);
        resolve();
      }, delayMs);
      signal.addEventListener('abort', onAbort, { once: true });
    });
  },
};
