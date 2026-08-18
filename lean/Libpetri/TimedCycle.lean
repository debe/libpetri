/-
# Deadline reaping: the dirty-marking asymmetry between backends

A witness module for the one place where the two shipped backends' timed
control paths *disagree*: what `enforce_deadlines` does to the dirty set when
it reaps a hard deadline (TIME-013). On `elapsed > latest_ms +
deadline_tolerance_ms` both backends clear the enabled bit and reset
`enabled_at_ms` to `NEG_INFINITY` — but

* `PrecompiledBackend::enforce_deadlines`
  (`rust/libpetri-runtime/src/precompiled_backend.rs:813`, reap block
  `:841-847`) **also calls `mark_transition_dirty(tid)`** (`:845`), while
* `BitmapBackend::enforce_deadlines` (`bitmap_backend.rs:479`, reap block
  `:492-497`) does **not** touch the dirty set.

Both `update_enablement`s are dirty-gated with otherwise *identical* branch
logic (`precompiled_backend.rs:755`, newly-enabled path `:790-794`;
`bitmap_backend.rs:432`, `:456-461`): a dirty, disabled transition whose
tokens still satisfy `can_enable` is re-enabled with a **fresh** clock
(`enabled_at_ms[tid] = now_ms` — the TIME-011 restart-from-zero, the same
newly-enabled path initialization takes). The reaped transition's tokens were
never consumed, so on the very next update phase the precompiled backend
re-enables it and — once its window reopens (`collect_ready_general`,
`precompiled_backend.rs:896-897` / `bitmap_backend.rs:524-527`) — fires it;
the bitmap backend never re-examines it, because in a *quiet* net (no token
mutation: no other firing, no injection, no reset) nothing else dirties it.
This is not compensated elsewhere: `post_fire` marks dirty in **both**
backends (`precompiled_backend.rs:1104-1111`, `bitmap_backend.rs:684-691`)
and `disable` in **neither** (`:1113-1119`, `:693-699`, the EXEC-003 loser
path of `Enablement.lean`'s `disable_frame`) — the reap is the unique
asymmetric dirty site. The executor consumes the reaped list only to emit
`TransitionTimedOut` (EVT-009; `executor_core/executor.rs:194` sync,
`:624` async) — no token change, no re-dirty route.

**This module rules that the two shipped behaviors differ; it deliberately
does not rule which one is spec-correct.** TIME-013 mandates "disables it and
emits `TransitionTimedOut`" and is *silent* on whether the transition may
re-enable afterwards while its tokens remain; TIME-011 governs the clock
*when* a re-enablement happens but does not say whether this one should. That
semantics decision is pending (phase 4); the theorems below are the neutral
evidence it will be made against.

The model is the per-transition control cell at cycle granularity — token
presence abstracted to one `Bool` (enough for `can_enable`, which the quiet
net keeps constant), `Nat` clocks per `Sched.lean`'s convention with `none`
for `NEG_INFINITY`. A cycle is the executor loop's phase order (`run_sync`,
`executor_core/executor.rs:171`; async loop Phase 3/4/5): update enablement,
enforce deadlines, then the ready/fire decision — the observable. Firing
*effects* are outside the fragment: the divergence is observable at the fire
decision itself, before any consumption happens. `exact()` timing is excluded
(never reaped, TIME-006 / TIME-013 AC3), and `deadline_tolerance_ms` is
folded into `latest` (it only translates the reap threshold, TIME-013 AC2).

* `deadline_reap_dirty_diverges` — the concrete witness: one `window(3,5)`
  transition, cycle timestamps `[0, 10, 12, 15]` (the executor blocked past
  the deadline between the first two cycles, exactly TIME-013's test
  derivation); the precompiled run fires it after the reap, the bitmap run
  never does, so the observable firing sequences differ.
* `bb_reaped_stays_disabled` / `bb_never_fires_after_reap` — the "never"
  half, by induction: a disabled, clean cell is a fixed point of the bitmap
  cycle, so no schedule extension ever re-enables it.
* `pb_update_reenables` — the mechanism half: one dirty-gated update step
  re-enables the reaped cell with the fresh clock.
* `reap_dirty_is_the_asymmetry` / `no_reap_frame` — the two enforce paths
  agree everywhere except the dirty bit on a reap.
-/
import Libpetri.Sched

namespace Libpetri

/-! ## The per-transition control cell -/

/-- One transition's timed control state, at the granularity the deadline
path reads and writes: `tokens` abstracts the marking to "would
`can_enable` pass" (`precompiled_backend.rs:566` / `bitmap_backend.rs:284` —
constant in a quiet net), `enabled` is the enabled bit, `clock` is
`enabled_at_ms` (`none` = `NEG_INFINITY`), `dirty` is the transition's bit in
`dirty_bitmap` / `dirty_set`. -/
structure Cell where
  tokens  : Bool
  enabled : Bool
  clock   : Option Nat
  dirty   : Bool
  deriving DecidableEq, Repr

/-- The one-transition timing constraint: a hard `window(earliest, latest)`
(`deadline(d)` is `earliest = 0`). `latest` stands for
`latest_ms + deadline_tolerance_ms` — the tolerance only translates the reap
threshold (TIME-013 AC2). -/
structure Timing where
  earliest : Nat
  latest   : Nat

/-- `elapsed > latest`: the reap test of both backends
(`precompiled_backend.rs:838-841`, `bitmap_backend.rs:490-492`), with `Nat`
truncated subtraction as in `Sched.lean`'s `isReady`. `none` is
`NEG_INFINITY`, whose elapsed time exceeds everything — unreachable for an
enabled transition (every disable path writes both fields together), modeled
as-shipped anyway. -/
def deadlineExpired (latest now : Nat) : Option Nat → Bool
  | some c => decide (latest < now - c)
  | none   => true

/-- `earliest_ms <= elapsed`: the TIME-010 window gate of
`collect_ready_general` (`precompiled_backend.rs:896-897`,
`bitmap_backend.rs:524-527`). Same `none` convention. -/
def windowOpen (earliest now : Nat) : Option Nat → Bool
  | some c => decide (earliest ≤ now - c)
  | none   => true

/-! ## The three steps -/

/-- The dirty-gated enablement update — one body for **both** backends,
because their branch logic is line-for-line identical
(`precompiled_backend.rs:755` `update_enablement`, dirty-word scan then
`:790-801`; `bitmap_backend.rs:432`, dirty snapshot then `:456-468`): a
clean cell is skipped outright; a dirty one has its bit cleared and is
re-evaluated — newly enabled gets the fresh clock (`enabled_at_ms = now_ms`,
TIME-011 restart-from-zero, `:793` / `:460`), newly disabled gets
`NEG_INFINITY` (`:798` / `:465`). The third branch (`clock_restarted`,
TIME-012) needs `has_input_from_reset_place`, which is `false` with no
pending resets (`precompiled_backend.rs:647-649`, `bitmap_backend.rs:352`) —
a quiet net has none, so it is elided. -/
def updateCell (now : Nat) (s : Cell) : Cell :=
  if s.dirty then
    if s.tokens && !s.enabled then
      { s with dirty := false, enabled := true, clock := some now }
    else if !s.tokens && s.enabled then
      { s with dirty := false, enabled := false, clock := none }
    else
      { s with dirty := false }
  else s

/-- The shared reap test: enabled and past the hard deadline. Exact-timed
transitions never reach it (`is_exact` continue, TIME-006). -/
def reaps (latest now : Nat) (s : Cell) : Bool :=
  s.enabled && deadlineExpired latest now s.clock

/-- `BitmapBackend::enforce_deadlines` (`bitmap_backend.rs:479`, reap block
`:492-497`): clear the enabled flag, `enabled_at_ms = NEG_INFINITY` — and
**nothing else**; the dirty set is untouched. -/
def enforceBB (latest now : Nat) (s : Cell) : Cell :=
  if reaps latest now s then { s with enabled := false, clock := none } else s

/-- `PrecompiledBackend::enforce_deadlines` (`precompiled_backend.rs:813`,
reap block `:841-847`): the same clear — plus `mark_transition_dirty(tid)`
(`:845`, the bit-set of `:486-490`). The one-field diff from `enforceBB` is
the entire subject of this module. -/
def enforcePB (latest now : Nat) (s : Cell) : Cell :=
  if reaps latest now s then
    { s with enabled := false, clock := none, dirty := true }
  else s

/-- The observable of one cycle: does the ready phase fire the transition?
Enabled-and-window-open is `collect_ready_general`'s gate; `tokens` is
`recheck_can_fire` re-running `can_enable` (`bitmap_backend.rs:544-547`),
redundant while enabled bits are in sync but kept for faithfulness. -/
def fires (earliest now : Nat) (s : Cell) : Bool :=
  s.tokens && s.enabled && windowOpen earliest now s.clock

/-! ## One executor cycle, and runs over a schedule

Phase order per the loop (`run_sync`, `executor_core/executor.rs:171`; the
async loop's Phase 3/4/5, `:619-657`): update enablement, enforce deadlines,
collect ready + fire. Advancing time between cycles is the schedule itself:
a run is driven by the list of cycle timestamps `now`, monotone in every
scenario proved below. -/

/-- One cycle under the given enforcement step. Returns the post-cycle cell
and the fire observable. Firing effects (consumption, `post_fire`) are
outside the fragment — the divergence below is decided at the observable. -/
def cycle (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (now : Nat)
    (s : Cell) : Cell × Bool :=
  let s' := enforce tm.latest now (updateCell now s)
  (s', fires tm.earliest now s')

/-- The observable firing sequence of a run over the cycle timestamps. -/
def run (enforce : Nat → Nat → Cell → Cell) (tm : Timing) (s : Cell) :
    List Nat → List Bool
  | [] => []
  | now :: rest =>
    (cycle enforce tm now s).2 :: run enforce tm (cycle enforce tm now s).1 rest

/-- The precompiled model's observable run. -/
def obsPB (tm : Timing) (s : Cell) (nows : List Nat) : List Bool :=
  run enforcePB tm s nows

/-- The bitmap model's observable run. -/
def obsBB (tm : Timing) (s : Cell) (nows : List Nat) : List Bool :=
  run enforceBB tm s nows

/-! ## The mechanism, made explicit -/

/-- On a reap, the two enforcement paths agree on every field **except** the
dirty bit — `enforcePB` is `enforceBB` plus `mark_transition_dirty`. -/
theorem reap_dirty_is_the_asymmetry {latest now : Nat} {s : Cell}
    (h : reaps latest now s = true) :
    enforcePB latest now s = { enforceBB latest now s with dirty := true }
      ∧ (enforceBB latest now s).dirty = s.dirty := by
  simp [enforcePB, enforceBB, h]

/-- Off the reap path both enforcement steps are the identity — the reap is
the *only* behavioral difference between the two `enforce_deadlines`. -/
theorem no_reap_frame {latest now : Nat} {s : Cell}
    (h : reaps latest now s = false) :
    enforcePB latest now s = s ∧ enforceBB latest now s = s := by
  simp [enforcePB, enforceBB, h]

/-- **PB half of the mechanism**: one dirty-gated update step re-enables a
reaped cell whose tokens are still present, with the fresh TIME-011 clock —
the newly-enabled path of `update_enablement`
(`precompiled_backend.rs:790-794`), the same path initialization takes. -/
theorem pb_update_reenables (now : Nat) {s : Cell} (ht : s.tokens = true)
    (he : s.enabled = false) (hd : s.dirty = true) :
    updateCell now s
      = { s with dirty := false, enabled := true, clock := some now } := by
  simp [updateCell, ht, he, hd]

/-- **BB half of the mechanism**, step case: a disabled, clean cell is a
fixed point of the bitmap cycle — `update_enablement` skips it (not dirty),
`enforce_deadlines` skips it (not enabled), the ready phase rejects it (not
enabled). -/
theorem bb_cycle_disabled_frame (tm : Timing) (now : Nat) {s : Cell}
    (he : s.enabled = false) (hd : s.dirty = false) :
    cycle enforceBB tm now s = (s, false) := by
  simp [cycle, updateCell, enforceBB, reaps, fires, he, hd]

/-- **BB half of the mechanism**: after a reap with no subsequent token
mutation (the quiet net — dirty stays clear because `mark_place_dirty` needs
a token change and `post_fire` needs a firing), `enabled` stays false
*forever*: every future cycle observes no fire, over any schedule. -/
theorem bb_reaped_stays_disabled (tm : Timing) {s : Cell}
    (he : s.enabled = false) (hd : s.dirty = false) :
    ∀ nows : List Nat, run enforceBB tm s nows
      = List.replicate nows.length false := by
  intro nows
  induction nows with
  | nil => rfl
  | cons now rest ih =>
    simp only [run, bb_cycle_disabled_frame tm now he hd, List.length_cons,
      List.replicate_succ]
    rw [ih]

/-! ## The divergence witness -/

/-- The witness timing: `window(3, 5)` — a lower bound keeps the transition
from firing at its enablement instant, the hard `latest` makes it reapable
(TIME-013 applies to `Deadline`/`Window` only). -/
def wTiming : Timing := { earliest := 3, latest := 5 }

/-- The cell as `initialize` leaves it (`precompiled_backend.rs:725`,
`bitmap_backend.rs:399`): tokens present from the initial marking, everything
dirty (`mark_all_dirty`), nothing enabled yet. -/
def wInit : Cell := { tokens := true, enabled := false, clock := none, dirty := true }

/-- The cycle timestamps: enable at 0; the executor is blocked past the
deadline (TIME-013's own test derivation) and next wakes at 10 — the reap;
a cycle at 12 — where the backends part ways; a cycle at 15 — where the
re-opened window would fire. -/
def wSched : List Nat := [0, 10, 12, 15]

/-- **The divergence witness (TIME-013's dirty-marking asymmetry).** On one
quiet `window(3,5)` transition with schedule `[0, 10, 12, 15]`: cycle 0
enables it (clock 0); cycle 10 reaps it in both backends; at cycle 12 the
precompiled backend — and only it — finds the transition dirty, re-enables it
with the fresh clock 12 (TIME-011 path); at cycle 15 its window has reopened
(`3 ≤ 15 - 12`) and it **fires**. The bitmap backend never re-examines it.
The observable firing sequences differ — the two shipped `enforce_deadlines`
are not behaviorally equivalent. Which of the two is TIME-013-correct is a
pending semantics decision this theorem does not take a side on. -/
theorem deadline_reap_dirty_diverges :
    obsPB wTiming wInit wSched = [false, false, false, true]
      ∧ obsBB wTiming wInit wSched = [false, false, false, false]
      ∧ obsPB wTiming wInit wSched ≠ obsBB wTiming wInit wSched := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The bitmap side of the witness, strengthened from the given schedule to
*every* schedule: after the enable-then-reap prefix `[0, 10]`, no quiet
continuation ever fires the transition again — `bb_reaped_stays_disabled`
applied to the concrete post-reap cell. -/
theorem bb_never_fires_after_reap (rest : List Nat) :
    obsBB wTiming wInit (0 :: 10 :: rest)
      = false :: false :: List.replicate rest.length false := by
  have h1 : (cycle enforceBB wTiming 0 wInit).2 = false := rfl
  have h2 : (cycle enforceBB wTiming 10 (cycle enforceBB wTiming 0 wInit).1).2
      = false := rfl
  have hs : (cycle enforceBB wTiming 10 (cycle enforceBB wTiming 0 wInit).1).1
      = { tokens := true, enabled := false, clock := none, dirty := false } := rfl
  simp only [obsBB, run, h1, h2, hs]
  rw [bb_reaped_stays_disabled wTiming
    (s := { tokens := true, enabled := false, clock := none, dirty := false })
    rfl rfl rest]

end Libpetri
