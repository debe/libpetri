/**
 * @module marking
 *
 * Mutable token state (marking) of a running Petri net.
 *
 * Tokens per place are stored in FIFO arrays (push to end, shift from front).
 * Not thread-safe — all mutation occurs from the single-threaded orchestrator.
 *
 * For typical nets (≤10 tokens per place), Array.shift() is faster than a deque
 * due to cache locality. Only optimize if profiling shows a bottleneck.
 */
import type { Place } from '../core/place.js';
import type { Token } from '../core/token.js';
import { compareCodePoints } from '../core/internal/code-point-order.js';

const EMPTY_TOKENS: readonly Token<any>[] = Object.freeze([]);

/**
 * A place reference plus an optional per-token predicate.
 *
 * Used by the ν-net join path (NU-020/NU-021) to select the tokens whose
 * projected correlation name equals the chosen binding. This is *not* an input
 * guard (IO-006, removed) — input specifications are purely structural; the
 * predicate here is always derived from name correlation.
 */
export interface PredicateSpec<T = any> {
  readonly place: Place<T>;
  readonly predicate?: (value: T) => boolean;
}

/**
 * A marking captured in the normative snapshot form of **CORE-073**: place **name** to that
 * place's FIFO token sequence.
 *
 * The entry type is the ordinary {@link Token} — it already *is* `(value, createdAt)`, and a
 * parallel `SnapshotEntry` would be a second name for one shape, which is the duplication
 * CORE-073 exists to prevent.
 *
 * A `Map` rather than a plain object, for insertion order and because a place named
 * `__proto__` or `constructor` would otherwise collide with a prototype key. That is reachable
 * input rather than a hypothetical: a host compiling place names from user-supplied step or
 * node identifiers can be handed either. Java (`Map<String, List<Token<?>>>`) and Rust
 * (`BTreeMap<Arc<str>, Vec<ErasedToken>>`) carry the structurally identical form.
 *
 * Named `…Form` rather than `MarkingSnapshot` because that name is already taken by the
 * `marking-snapshot` **event** payload — the third instance of this collision across the three
 * languages: Java's is with the same event record, Rust's is with `ExecutorSignal::Snapshot`.
 * The name is TypeScript-local: Java carries the identical structure as a raw map type with no
 * alias, and Rust names it `MarkingSnapshot` (`pub type`, re-exported from the crate root). An
 * alias is a name for the structure, not a second structure, so none of this forks the agreed
 * form.
 *
 * @see Marking.snapshot
 * @see Marking.fromSnapshot
 */
export type MarkingSnapshotForm = ReadonlyMap<string, readonly Token<unknown>[]>;

/**
 * Mutable marking (token state) of a Petri Net during execution.
 *
 * Tokens in each place are maintained in FIFO order (array: push to end, shift from front).
 * Not thread-safe — all access must be from the orchestrator.
 */
export class Marking {
  /** Place name -> FIFO queue of tokens. */
  private readonly tokens = new Map<string, Token<any>[]>();
  /** Place name -> Place reference (for inspection). */
  private readonly placeRefs = new Map<string, Place<any>>();

  static empty(): Marking {
    return new Marking();
  }

  /**
   * Captures this marking in the normative snapshot form (**CORE-073**): place **name** to
   * that place's FIFO token sequence.
   *
   * Keyed by name rather than by {@link Place} because a snapshot MUST survive a round-trip
   * through a net that has since gained or lost a place (CORE-073 AC#7, [CORE-072]) — there
   * is no `Place` to construct for a name the receiving net never declared.
   *
   * **Structural, not serialized.** Token values are carried through untouched; the engine
   * imposes no codec and does not require them to be serializable, because only the host
   * knows what its values are. A closure, a class instance or a native handle round-trips
   * within the process unchanged (AC#8). Persisting a snapshot across processes is therefore
   * the host's encoding to choose.
   *
   * Each sequence is an owned copy in FIFO order ([CORE-013]); token order decides which
   * token a firing consumes, so a snapshot that lost it would not be a restore (AC#6).
   * Places are emitted in code-point order of their names. The form is a mapping, so only the
   * per-place sequence is *required* to be ordered — but a deterministic key order makes a
   * snapshot content-addressable, makes two captures diffable without normalising first, and
   * matches the order Rust's `BTreeMap<Arc<str>, _>` and Java's `TreeMap` produce, so two
   * implementations snapshotting one marking agree key for key (AC#12). Do not relax it.
   *
   * **Empty places are omitted.** A place that was drained, or restored empty, does not appear.
   * One emission rule is what makes "agree key for key" achievable at all: Java, Rust and the
   * precompiled executor never had such keys to emit, and a `Marking` cannot tell "declared and
   * drained" from "never there" anyway — it only knows places that once held a token.
   * {@link fromSnapshot} still accepts both forms and restores them identically (AC#7).
   *
   * **Persisting one.** The values are yours. If they are not JSON-safe that is a host concern
   * this engine cannot answer — a codec hook would not help, since "what does this closure mean
   * in another process" is a question only the host can answer. The walk is a line each way, as
   * an **array of entries**: `JSON.stringify([...marking.snapshot()])` on the way to storage,
   * and `new Map(JSON.parse(stored))` on the way back into {@link fromSnapshot}.
   *
   * Not `Object.fromEntries(...)`. A JSON *object* is an unordered medium, and a JavaScript
   * object is worse than unordered: integer-like keys are hoisted ahead of every other key in
   * numeric order, so places named `'9'`, `'10'`, `'-1'`, `'a'` — canonical order
   * `-1, 10, 9, a` — come back as `9, 10, -1, a`. A host naming places after node ids hits
   * that at once. It still *restores* correctly, because a restore ignores the order it is
   * handed; what is lost is the canonical order of the stored artefact, and with it the
   * byte-comparability that order exists for. An array of entries keeps it, and needs no
   * reasoning about a place named `__proto__` either.
   */
  snapshot(): MarkingSnapshotForm {
    const names: string[] = [];
    for (const [name, queue] of this.tokens) {
      if (queue.length > 0) names.push(name);
    }
    names.sort(compareCodePoints);
    const out = new Map<string, readonly Token<unknown>[]>();
    for (const name of names) {
      out.set(name, [...this.tokens.get(name)!] as readonly Token<unknown>[]);
    }
    return out;
  }

  /**
   * Restores a marking from the snapshot form (**CORE-073**).
   *
   * Accepts a place that is **absent** and one **present but empty** as the same thing, per
   * AC#7 — an emitted snapshot omits empties, a hand-built or foreign one may carry them, and
   * this side carries the obligation to treat the two alike.
   *
   * Token `createdAt` values are carried through verbatim: the engine MUST NOT re-stamp a
   * restored token, including under an injected epoch clock ([TIME-015] AC#9 / CORE-073
   * AC#9). Restoring is the one path where the engine hands back a timestamp it did not
   * choose, and re-stamping would make a resume indistinguishable from a fresh start.
   *
   * The restored marking carries no {@link Place} references — a snapshot holds names only.
   * That is what lets a name the receiving net does not declare survive the round-trip
   * ([CORE-072]); such tokens are retained and inert.
   *
   * **The clocks do not come back.** A restored token's `createdAt` is metadata, not a firing
   * clock: every transition this marking enables starts its timing interval fresh at the
   * resuming executor's enablement ([TIME-010], [TIME-011]). A `Delayed` lower bound is still
   * satisfied — measured again from zero it is still at least that bound — but a `Deadline` or
   * `Window` **upper** bound receives a fresh full budget, so a deadline the net promised can
   * be silently missed across a restore. A hard bound that must survive one belongs in the
   * token payload or in an action timeout ([IO-013]), not in net timing.
   *
   * **Restore must stay occasional.** Every restore restarts every clock, so a transition
   * whose `Delayed(d)` clock is restarted more often than every `d` never accumulates `d` and
   * never fires — starvation, not slowdown. Sound for a suspend boundary or a checkpoint;
   * unsound for a scheduler that parks and resumes as a matter of course.
   */
  static fromSnapshot(snapshot: MarkingSnapshotForm): Marking {
    const m = new Marking();
    for (const [name, tokens] of snapshot) {
      if (tokens.length === 0) continue; // absent and empty are one thing (AC#7)
      m.tokens.set(name, [...tokens]);
    }
    return m;
  }

  static from(initial: Map<Place<any>, Token<any>[]>): Marking {
    const m = new Marking();
    for (const [place, tokens] of initial) {
      m.placeRefs.set(place.name, place);
      m.tokens.set(place.name, [...tokens]);
    }
    return m;
  }

  // ======================== Token Addition ========================

  addToken<T>(place: Place<T>, token: Token<T>): void {
    this.placeRefs.set(place.name, place);
    const queue = this.tokens.get(place.name);
    if (queue) {
      queue.push(token);
    } else {
      this.tokens.set(place.name, [token]);
    }
  }

  // ======================== Token Removal ========================

  /** Removes and returns the oldest token. Returns null if empty. */
  removeFirst<T>(place: Place<T>): Token<T> | null {
    const queue = this.tokens.get(place.name);
    if (!queue || queue.length === 0) return null;
    return queue.shift() as Token<T>;
  }

  /** Removes and returns all tokens from a place. */
  removeAll<T>(place: Place<T>): Token<T>[] {
    const queue = this.tokens.get(place.name);
    if (!queue || queue.length === 0) return [];
    const result = [...queue] as Token<T>[];
    queue.length = 0;
    return result;
  }

  /**
   * Removes and returns the first token whose value satisfies the predicate.
   *
   * Performs a linear scan of the place's FIFO queue. If no predicate is
   * provided, behaves like `removeFirst()`. Otherwise skips non-matching
   * tokens and splices the first match out of the queue (O(n) worst case).
   */
  removeFirstMatching(spec: PredicateSpec): Token<any> | null {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return null;
    if (!spec.predicate) {
      return queue.shift()!;
    }
    for (let i = 0; i < queue.length; i++) {
      const token = queue[i]!;
      if (spec.predicate(token.value)) {
        // Head removal (the common ν-net case — the matched token is the oldest,
        // hence at the front with distinct timestamps) uses the V8-optimized
        // shift() rather than an O(n) splice, keeping a draining join linear.
        if (i === 0) queue.shift();
        else queue.splice(i, 1);
        return token;
      }
    }
    return null;
  }

  // ======================== Token Inspection ========================

  /** Check if any token satisfies the predicate. */
  hasMatchingToken(spec: PredicateSpec): boolean {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return false;
    if (!spec.predicate) return true;
    return queue.some(t => spec.predicate!(t.value));
  }

  /**
   * Counts tokens in a place whose values satisfy the predicate.
   *
   * If no predicate is provided, returns the total token count (O(1)).
   * With a predicate, performs a linear scan over all tokens (O(n)).
   * Used by the executor to size a ν-net correlated `all`/`at-least` consume.
   */
  countMatching(spec: PredicateSpec): number {
    const queue = this.tokens.get(spec.place.name);
    if (!queue || queue.length === 0) return 0;
    if (!spec.predicate) return queue.length;
    let count = 0;
    for (const t of queue) {
      if (spec.predicate(t.value)) count++;
    }
    return count;
  }

  /**
   * Returns tokens in a place. **Returns a live reference** to the internal
   * array — callers must not mutate it. Copy with `[...peekTokens(p)]` if
   * mutation or snapshot semantics are needed.
   */
  peekTokens<T>(place: Place<T>): readonly Token<T>[] {
    return (this.tokens.get(place.name) ?? EMPTY_TOKENS) as readonly Token<T>[];
  }

  /** Returns the oldest token without removing it. */
  peekFirst<T>(place: Place<T>): Token<T> | null {
    const queue = this.tokens.get(place.name);
    return queue && queue.length > 0 ? queue[0] as Token<T> : null;
  }

  /** Checks if a place has any tokens. */
  hasTokens(place: Place<any>): boolean {
    const queue = this.tokens.get(place.name);
    return queue !== undefined && queue.length > 0;
  }

  /** Returns the number of tokens in a place. */
  tokenCount(place: Place<any>): number {
    const queue = this.tokens.get(place.name);
    return queue ? queue.length : 0;
  }

  // ======================== Debugging ========================

  toString(): string {
    const parts: string[] = [];
    for (const [name, queue] of this.tokens) {
      if (queue.length > 0) {
        parts.push(`${name}: ${queue.length}`);
      }
    }
    return `Marking{${parts.join(', ')}}`;
  }
}
