/-
# Deadline reaping: a reaped transition stays disabled (TIME-013)

What `enforce_deadlines` does when it reaps a hard deadline (TIME-013). On
`elapsed > latest_ms + deadline_tolerance_ms` both backends clear the enabled
bit and reset `enabled_at_ms` to `NEG_INFINITY`, and neither touches the dirty
set: `BitmapBackend::enforce_deadlines` (`bitmap_backend.rs:646`, reap block
`:659-664`) and `PrecompiledBackend::enforce_deadlines`
(`rust/libpetri-runtime/src/precompiled_backend.rs:1017`, reap block
`:1049-1054`). `enforceBB` is that one body.

**The ruling (2026-09-30).** A reaped transition stays disabled until a token
on one of its input places changes. The token change marks it dirty
(`mark_place_dirty`), the next `update_enablement` re-evaluates it, and it is
re-enabled on a fresh clock (TIME-011) if its inputs still enable it
(`reaped_rearms_on_touch`). With no such change it never fires again
(`bb_reaped_stays_disabled`, `bb_never_fires_after_reap`), over any schedule.

**Before the ruling** the precompiled backend also called
`mark_transition_dirty(tid)` on a reap. `enforcePB` keeps that path as the
retrodiction of the divergence the ruling removed: the next dirty-gated update
re-enabled the reaped transition on a fresh clock (`pb_update_reenables`), so
once its window reopened it fired, while the bitmap backend never re-examined
it in a quiet net (no other firing, no injection, no reset). The mark was the
only asymmetric dirty site: `post_fire` marks dirty in both backends
(`precompiled_backend.rs:1336-1343`, `bitmap_backend.rs:883-890`) and
`disable` in neither (`precompiled_backend.rs:1345-1351`,
`bitmap_backend.rs:892-898`, the EXEC-003 loser path of `Enablement.lean`'s
`disable_frame`). The executor consumes the reaped list only to emit
`TransitionTimedOut` (EVT-009; `executor_core/executor.rs:403` sync, `:1075`
async), with no token change and no re-dirty route. The Rust tests
`time013_reap_is_not_rearmed_on_either_backend`,
`time013_reap_witness_backends_agree` and
`time013_reaped_transition_rearms_when_an_input_changes` (the runtime's
differential property tests) run `deadline_reap_dirty_diverges`'s witness on
both backends and assert the ruling.

The model is the per-transition control cell at cycle granularity — token
presence abstracted to one `Bool` (enough for `can_enable`, which the quiet
net keeps constant), `Nat` clocks per `Sched.lean`'s convention with `none`
for `NEG_INFINITY`. A cycle is the executor loop's phase order (`run_sync`,
`executor_core/executor.rs:364`; async loop Phase 3/4/5): update enablement,
enforce deadlines, then the ready/fire decision — the observable. Firing
*effects* are outside the fragment: the divergence is observable at the fire
decision itself, before any consumption happens. `exact()` timing is excluded
(never reaped, TIME-006 / TIME-013 AC3), and `deadline_tolerance_ms` is
folded into `latest` (it only translates the reap threshold, TIME-013 AC2).

* `bb_reaped_stays_disabled` / `bb_never_fires_after_reap`: the ruling's
  "stays disabled", by induction: a disabled, clean cell is a fixed point of
  the shipped cycle, so no quiet schedule extension ever re-enables it.
* `reaped_rearms_on_touch`: the ruling's "until an input changes": a token
  change marks the reaped cell dirty, and the next cycle re-enables it on the
  fresh clock, which the same cycle does not reap again.
* `deadline_reap_dirty_diverges`, the retrodiction: one `window(3,5)`
  transition, cycle timestamps `[0, 10, 12, 15]` (the executor blocked past
  the deadline between the first two cycles, exactly TIME-013's test
  derivation); the pre-ruling precompiled run fires it after the reap, the
  shipped run never does.
* `pb_update_reenables`, the pre-ruling mechanism: one dirty-gated update
  step re-enables the reaped cell with the fresh clock.
* `reap_dirty_is_the_asymmetry` / `no_reap_frame`: the pre-ruling path
  differed from the shipped one only in the dirty bit on a reap.
-/
import Libpetri.Sched

namespace Libpetri

/-! ## The per-transition control cell -/

/-- One transition's timed control state, at the granularity the deadline
path reads and writes: `tokens` abstracts the marking to "would
`can_enable` pass" (`precompiled_backend.rs:710` / `bitmap_backend.rs:329` —
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
(`precompiled_backend.rs:1042-1049`, `bitmap_backend.rs:657-659`), with `Nat`
truncated subtraction as in `Sched.lean`'s `isReady`. `none` is
`NEG_INFINITY`, whose elapsed time exceeds everything — unreachable for an
enabled transition (every disable path writes both fields together), modeled
as-shipped anyway. -/
def deadlineExpired (latest now : Nat) : Option Nat → Bool
  | some c => decide (latest < now - c)
  | none   => true

/-- `earliest_ms <= elapsed`: the TIME-010 window gate of
`collect_ready_general` (`precompiled_backend.rs:1104-1105`,
`bitmap_backend.rs:689-691`). Same `none` convention. -/
def windowOpen (earliest now : Nat) : Option Nat → Bool
  | some c => decide (earliest ≤ now - c)
  | none   => true

/-! ## The three steps -/

/-- The dirty-gated enablement update — one body for **both** backends,
because their branch logic is line-for-line identical
(`precompiled_backend.rs:948` `update_enablement`, dirty-word scan then
`:965-1000`; `bitmap_backend.rs:590`, dirty snapshot then `:612-632`): a
clean cell is skipped outright; a dirty one has its bit cleared and is
re-evaluated — newly enabled gets the fresh clock (`enabled_at_ms = now_ms`,
TIME-011 restart-from-zero, `:986` / `:618`), newly disabled gets
`NEG_INFINITY` (`:991` / `:623`). The third branch (`clock_restarted`,
TIME-012) needs the transition's pending-restart bit
(`precompiled_backend.rs:993-999`, `bitmap_backend.rs:625-631`), which
only a firing sets: `update_bitmap_after_consumption` calls
`flag_clock_restarts` (`precompiled_backend.rs:822`, `bitmap_backend.rs:425`)
for each consumed place left below its `restart_threshold`, which flags each
other enabled transition failing `can_enable` on the live marking. A quiet
net fires nothing, so the bit is never set and the branch is elided. -/
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

/-- `BitmapBackend::enforce_deadlines` (`bitmap_backend.rs:646`, reap block
`:659-664`) and, since the TIME-013 ruling, `PrecompiledBackend::enforce_deadlines`
(`precompiled_backend.rs:1017`, reap block `:1049-1054`): clear the enabled
flag, `enabled_at_ms = NEG_INFINITY`, and **nothing else**; the dirty set is
untouched. -/
def enforceBB (latest now : Nat) (s : Cell) : Cell :=
  if reaps latest now s then { s with enabled := false, clock := none } else s

/-- `PrecompiledBackend::enforce_deadlines` **before the TIME-013 ruling**: the
same clear, plus `mark_transition_dirty(tid)` (the bit-set of
`precompiled_backend.rs:566-570`). The shipped path no longer calls it and is
`enforceBB`. Kept as the retrodiction the ruling was made against. -/
def enforcePB (latest now : Nat) (s : Cell) : Cell :=
  if reaps latest now s then
    { s with enabled := false, clock := none, dirty := true }
  else s

/-- The observable of one cycle: does the ready phase fire the transition?
Enabled-and-window-open is `collect_ready_general`'s gate; `tokens` is
`recheck_can_fire` re-running `can_enable` (`bitmap_backend.rs:708-713`),
redundant while enabled bits are in sync but kept for faithfulness.

Since the EXEC-003 AC3/AC4 work that recheck reads the fire-pass presence
snapshot and passes `pre_deposit = true`, so `can_enable` additionally
discounts the pass's `deposit_delta` from every cardinality gate and defers
any ν-join whose correlated input took a same-pass deposit. A quiet net
fires nothing, so no deposit is ever recorded: `has_deposits` stays false,
the discount is inert, and the snapshot equals the live marking. `tokens`
is therefore the whole content of the recheck in this fragment. -/
def fires (earliest now : Nat) (s : Cell) : Bool :=
  s.tokens && s.enabled && windowOpen earliest now s.clock

/-! ## One executor cycle, and runs over a schedule

Phase order per the loop (`run_sync`, `executor_core/executor.rs:385`; the
async loop's Phase 3/4/5, `:921-977`): update enablement, enforce deadlines,
collect ready + fire. Advancing time between cycles is the schedule itself:
a run is driven by the list of cycle timestamps `now`.

The concrete witnesses below use monotone schedules, but nothing in the
model requires one: `run` quantifies over an arbitrary `List Nat`, and
`bb_reaped_stays_disabled` / `bb_never_fires_after_reap` are proved for
*every* such list. That is what makes the model survive TIME-015's injectable
clock, whose contract point 1 requires the firing clock to be non-decreasing
but explicitly does **not** promise it advances between two reads: a host
clock derived from millisecond wall time or a replay log yields a schedule
with repeated timestamps, which is already inside this quantification. The
executor still reads the clock exactly once per cycle (`let cycle_now =
self.elapsed_ms()`, `:393` sync / `:1064` async), which is the `now` here. -/

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

/-- The observable run of the precompiled path before the TIME-013 ruling. -/
def obsPB (tm : Timing) (s : Cell) (nows : List Nat) : List Bool :=
  run enforcePB tm s nows

/-- The observable run of both shipped backends. -/
def obsBB (tm : Timing) (s : Cell) (nows : List Nat) : List Bool :=
  run enforceBB tm s nows

/-! ## The mechanism, made explicit -/

/-- On a reap, the pre-ruling path agreed with the shipped one on every field
**except** the dirty bit: `enforcePB` is `enforceBB` plus
`mark_transition_dirty`. -/
theorem reap_dirty_is_the_asymmetry {latest now : Nat} {s : Cell}
    (h : reaps latest now s = true) :
    enforcePB latest now s = { enforceBB latest now s with dirty := true }
      ∧ (enforceBB latest now s).dirty = s.dirty := by
  simp [enforcePB, enforceBB, h]

/-- Off the reap path both enforcement steps are the identity: the reap was the
*only* behavioral difference between the pre-ruling and the shipped
`enforce_deadlines`. -/
theorem no_reap_frame {latest now : Nat} {s : Cell}
    (h : reaps latest now s = false) :
    enforcePB latest now s = s ∧ enforceBB latest now s = s := by
  simp [enforcePB, enforceBB, h]

/-- **The re-enabling step**: one dirty-gated update step re-enables a
disabled, dirty cell whose tokens are still present, with the fresh TIME-011
clock: the newly-enabled path of `update_enablement`
(`precompiled_backend.rs:983-987`), the same path initialization takes. Before
the ruling the reap itself set the dirty bit, so this step followed every reap;
now only a token change sets it (`reaped_rearms_on_touch`). -/
theorem pb_update_reenables (now : Nat) {s : Cell} (ht : s.tokens = true)
    (he : s.enabled = false) (hd : s.dirty = true) :
    updateCell now s
      = { s with dirty := false, enabled := true, clock := some now } := by
  simp [updateCell, ht, he, hd]

/-- **The ruling**, step case: a disabled, clean cell is a fixed point of the
shipped cycle: `update_enablement` skips it (not dirty),
`enforce_deadlines` skips it (not enabled), the ready phase rejects it (not
enabled). -/
theorem bb_cycle_disabled_frame (tm : Timing) (now : Nat) {s : Cell}
    (he : s.enabled = false) (hd : s.dirty = false) :
    cycle enforceBB tm now s = (s, false) := by
  simp [cycle, updateCell, enforceBB, reaps, fires, he, hd]

/-- **The ruling, "stays disabled"**: after a reap with no subsequent token
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

/-- A token change on one of the transition's input places: `mark_place_dirty`
sets the dirty bit of every transition reading the place, and
`update_bitmap_after_consumption` / the deposit path refresh presence, which
`tokens` stands for. -/
def touch (tokens : Bool) (s : Cell) : Cell := { s with tokens := tokens, dirty := true }

/-- **The ruling, "until an input changes"**: a reaped (disabled) cell whose
input place then changes and still enables it is re-enabled by the next cycle
on the fresh clock `now` (TIME-011), and that cycle does not reap it again,
since no time has passed on the fresh clock. Both shipped backends run this
path (`time013_reaped_transition_rearms_when_an_input_changes`). -/
theorem reaped_rearms_on_touch (tm : Timing) (now : Nat) {s : Cell}
    (he : s.enabled = false) :
    (cycle enforceBB tm now (touch true s)).1
      = { s with tokens := true, enabled := true, clock := some now, dirty := false } := by
  simp [cycle, touch, updateCell, enforceBB, reaps, deadlineExpired, he]

/-! ## The divergence witness (before the ruling) -/

/-- The witness timing: `window(3, 5)` — a lower bound keeps the transition
from firing at its enablement instant, the hard `latest` makes it reapable
(TIME-013 applies to `Deadline`/`Window` only). -/
def wTiming : Timing := { earliest := 3, latest := 5 }

/-- The cell as `initialize` leaves it (`precompiled_backend.rs:911`,
`bitmap_backend.rs:550`): tokens present from the initial marking, everything
dirty (`mark_all_dirty`), nothing enabled yet. -/
def wInit : Cell := { tokens := true, enabled := false, clock := none, dirty := true }

/-- The cycle timestamps: enable at 0; the executor is blocked past the
deadline (TIME-013's own test derivation) and next wakes at 10 — the reap;
a cycle at 12, where the pre-ruling precompiled path re-enabled it; a cycle
at 15, where the re-opened window would fire. -/
def wSched : List Nat := [0, 10, 12, 15]

/-- **The divergence witness (TIME-013's dirty-marking asymmetry, before the
ruling).** On one quiet `window(3,5)` transition with schedule
`[0, 10, 12, 15]`: cycle 0 enables it (clock 0); cycle 10 reaps it in both
backends; at cycle 12 the pre-ruling precompiled path, and only it, found the
transition dirty and re-enabled it with the fresh clock 12 (TIME-011 path); at
cycle 15 its window has reopened (`3 ≤ 15 - 12`) and it **fires**. The bitmap
backend never re-examines it. The observable firing sequences differ. The
TIME-013 ruling (2026-09-30) took the bitmap side: `obsBB` is now the run of
both shipped backends, and the Rust test
`time013_reap_is_not_rearmed_on_either_backend` runs this witness on both. -/
theorem deadline_reap_dirty_diverges :
    obsPB wTiming wInit wSched = [false, false, false, true]
      ∧ obsBB wTiming wInit wSched = [false, false, false, false]
      ∧ obsPB wTiming wInit wSched ≠ obsBB wTiming wInit wSched := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- The shipped side of the witness, strengthened from the given schedule to
*every* schedule: after the enable-then-reap prefix `[0, 10]`, no quiet
continuation ever fires the transition again — `bb_reaped_stays_disabled`
applied to the concrete post-reap cell. Both backends, since the ruling. -/
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
