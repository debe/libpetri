import Libpetri.Novel.ForwardDeposit
import Libpetri.Strengthening.Hypotheses

/-!
# In-flight actions: when an atomic firing is enough, and the split net ([VER-004], [EXEC-001], [EXEC-003], [EXEC-042])

Every route reads a firing as one atomic step: consume and deposit together. The executor does
not fire that way. It consumes a firing's inputs when the action starts and deposits its outputs
when the action completes, and other transitions fire in between (an asynchronous action for as
long as it runs, a synchronous one until the end of its firing pass, [EXEC-003] AC5). This module
mechanises the reordering argument `rust/libpetri-verification/src/in_flight.rs` states in its
module docs, which cite the results below.

## The model

A net is a list of flat rows `(t, d)`: a transition and one way its firing can end
(`branch_outcomes::outcomes`, a `ForwardDeposit.Deposit` each).

* `XStep`, **the executor**: any enabled row may start (`startA`: inputs taken, resets and
  drains emptied, nothing deposited, which is `consume_for_firing`), which puts its transition in
  flight; an in-flight transition completes with any of its rows (the action decides the branch
  when it finishes), depositing that row (`addD`). An atomic firing is a start directly followed
  by its completion (`fireAD_eq_addD_startA`).
* `live`, **the strict stop** ([EXEC-042]): no step, start or completion, is taken from a marking
  `live` rejects. On a net with terminal places `live a` says no terminal is marked: `run_sync`
  and `run_async` start nothing once `terminal_reached()`, and `run_async` re-reads it before each
  completion it admits, so an action still in flight then is abandoned (its inputs consumed, its
  outputs never deposited). `fun _ => True` is the net without terminals.
* `SStep sp`, **the split net** `split_in_flight` builds, for the set `sp` of split transitions
  (`in_flight_transitions_for`): a transition outside `sp` fires atomically (`fireAD`); a
  transition `t` in `sp` starts (the Rust `t` with its outputs replaced by `inflight:t`) and
  later completes with any of its rows (the Rust `complete:t`, immediate, consuming
  `inflight:t` and depositing `t`'s output spec, every branch, which `halves` builds with
  `completion_output`: a forward leaf deposits its one token as a plain output). The pending
  list stands for the `inflight:*` places: its multiplicity of `t` is the count of `inflight:t`.
  A completion is a constructor of its own, never a row, so it is never split again, which is
  what `is_completion` keeps true when the Rust splits an already-split net. `live` gates every
  step: `TerminalRewrite.lean`'s rewrite runs after the split and makes every terminal inhibit
  every transition of the split net, each `complete:t` included.
* A place `p` is **tested non-monotonically** by a transition when the transition has an
  inhibitor on `p`, a reset on `p`, or a draining input (`all`, `at_least`) on `p`
  (`non_monotone_places`). `Untested rows d`: no row tests a place the deposit `d` writes. A
  terminal place is in `non_monotone_places` too: here that is the premise that a row outside
  the split keeps `live` when it deposits (`hlive`).

## Results

Every result is stated for an arbitrary split set `sp` that meets the criterion, so a split
larger than the Rust's plain one is covered too: the demands of `quiescent_count_demand` and
`conflict_demand` add transitions to split and never remove one.

* `commute_add` (**the reordering lemma**, one step): a step `u` that tests no place of `d`
  non-monotonically commutes with depositing `d`: `u` stays enabled with `d` added first, and
  ends in the same marking plus `d`. So a completion moves left past every such step.
* **`split_covers_executor`**: if every transition outside `sp` has only untested outputs (the
  Rust criterion: `in_flight_transitions` is exactly the transitions with a tested output) and
  never deposits into a terminal place, then for every executor state and every choice of branch
  for each non-split action in flight, the split net reaches the marking with those actions
  completed, with the split actions in flight exactly as in the executor. The split net
  over-approximates the executor.
* **`atomic_covers_executor`** (the commutation lemma, `sp` empty): when no transition tests any
  output non-monotonically, every interleaving of starts and completions is matched by an
  atomic run, whose marking is the executor's plus the pending deposits.
* **`split_stop_sound`**: a `Proven` on the split net of a property that reads the places `Q`
  exactly and every other place upward-closed holds at every executor state, provided no
  transition outside `sp` deposits into `Q`. The executor state may have actions in flight that
  never complete: this is the terminal stop, which abandons them. `split_safety_sound` is the
  case `Q = ∅`: a `Proven` of an upward-closed marking property (every safety property
  `SmtProperty` has: a place bound, an unreachable marked set, a mutual exclusion) on the split
  net holds at every executor state, in-flight states included.
* **`quiescent_count_stop_sound`** ([VER-002] AC8, [EXEC-042]): the `QuiescentCount` lower bound
  read at a terminal stop (`stopCountBad`) is such a property with `Q` its counted places and its
  waiver places, which is `quiescent_count_demand`'s `tested` set. `stop_min_zero` and
  `stop_waived` are the two cases the Rust leaves the demand empty: a zero lower bound, and every
  terminal a waiver.
* `split_rest_sound`: where nothing is in flight (where the executor rests when no terminal
  stops it: `run_async` waits for in-flight actions), the executor's marking is a split-net
  marking with nothing pending, exactly. A quiescence `Proven` of the split net therefore covers
  the executor's rests.
* `inflight_witness` (the criterion is needed): `t : p → q` and `u : r, inhibitor p,
  inhibitor q → bad`. The atomic net never marks `bad`; the executor does, with `t` in flight;
  the split net with `t` split does too (the Rust splits `t`, since `u` inhibits its output).
* `terminal_stop_witness` (the demand is needed): `t : a → ok`, `f : s → done`, `done`
  terminal, `QuiescentCount([a, ok], 1)`. The plain split splits only `f` (it marks the
  terminal); on it the count never falls short. The executor starts `t`, lets `f` mark `done`
  and stops with `t` abandoned, so `a = ok = 0`; the split with `t` added reaches that stop too.

## Where the Rust uses it

`SmtVerifier::with_in_flight` (`smt_verifier.rs`) runs every route on `split_in_flight_for`'s
net unless the caller sets `assume_atomic_firing`, before the terminal rewrite
(`TerminalRewrite.lean`) so that a terminal counts as a test and also inhibits each completion
step. The split set is `in_flight_transitions_for` under a `SplitDemand`: the plain criterion
(outputs in `non_monotone_places`), plus the depositors into `quiescent_count_demand`'s places
(`split_stop_sound`), plus, where Route B reads conflict priority, `conflict_demand`'s pruners
and the depositors into their input and read places. `verify_net` answers `Unknown` before any
route when the split is refused. `open_net/verify_open_net.rs::verify_open_net` splits the
closed net with the plain criterion and the carrier places its `configure_smt` hook declares,
and excuses the `inflight:*` places in the contract; its contracts have no `QuiescentCount`
demand, since every net terminal becomes a designed terminal that waives each clause's lower
bound (`stop_waived`). That includes a graph the [VER-017] state-space cache returns:
`verify_terminals_split` takes the cache key from the net after the split, so a graph built from
the atomic net under `assume_atomic_firing` never answers a query on the split one (the Rust test
`the_in_flight_split_is_part_of_the_key`). Before that fix the key was taken before the split,
and an atomic query's cached graph gave the split query a wrong `Proven`.

## Not modelled

* Timing: the split is untimed; `complete:t` is immediate and not reapable, so a marked
  `inflight:t` never rests unless a terminal stops the net.
* Priorities. Conflict priority ([NU-052]) is a non-monotone test of the pruner's input and read
  places, and the Rust answers it with `conflict_demand` (split every pruner and every depositor
  into those places) and with the guard in `priority_dominated` (a pruner pre-empts nothing while
  `inflight:<pruner>` is marked, `RouteB/Graph.lean` `BaseLayer.idle`). The theorems here cover
  that larger split for the priority-free step relation. That the executor's priority rule then
  keeps Route B's premise 5 on the split net (`RouteB.lean`) is argued in `in_flight.rs` and
  has no proof here: `XStep` has no priorities. When a pruner or a feeder cannot be split,
  `with_in_flight` turns the pruning off (`PrioritySemantics::None`), which only adds runs.
* Environment places, and the refusals (`first_unsplittable`, `refusal_cause`: a ν-join or a
  coloured-place writer, a `Timeout` forward of more than one token, a name clash).
* `ctx.flush()`: an action that publishes some outputs before it completes. The split deposits
  every output of a completion together (`FLUSH_NOTE` says so on every split verdict).

The model fixes nothing about which branch a completion takes, as the executor does not.
[CONC-002]'s re-start rule (Rust may start a transition again while an earlier firing of it is
in flight, Java and TypeScript do not) is covered either way: `XStep` allows the re-start, and a
run without it is still an `XStep` run. A counterexample of the split net may re-start, so the
Rust labels one that does (`restart_note`): on Java and TypeScript it may be a false alarm.
-/

namespace Libpetri.Novel.InFlight

open Libpetri Libpetri.Novel.ForwardDeposit

/-- A flat row: a transition and one of its outcomes. -/
abbrev Row := Transition × Deposit

/-- Deposit `d` on top of `a`. -/
def addD (a : AMarking) (d : Deposit) : AMarking := fun p => a p + d.count p

/-- Deposit every row of `ds` on top of `a`. -/
def addAll (a : AMarking) (ds : List Row) : AMarking :=
  fun p => a p + (ds.map fun r => r.2.count p).sum

/-- The start of a firing: inputs taken, resets and drained inputs emptied, nothing deposited
(`consume_for_firing`). -/
def startA (a : AMarking) (t : Transition) : AMarking := fireAD a t []

theorem fireAD_eq_addD_startA (a : AMarking) (t : Transition) (d : Deposit) :
    fireAD a t d = addD (startA a t) d := by
  funext p
  simp only [fireAD, addD, startA, List.count_nil]
  split_ifs <;> omega

theorem addAll_nil (a : AMarking) : addAll a [] = a := by
  funext p; simp [addAll]

theorem addAll_cons (a : AMarking) (r : Row) (ds : List Row) :
    addAll a (r :: ds) = addAll (addD a r.2) ds := by
  funext p; simp only [addAll, addD, List.map_cons, List.sum_cons]; omega

theorem addD_addAll (a : AMarking) (d : Deposit) (ds : List Row) :
    addD (addAll a ds) d = addAll (addD a d) ds := by
  funext p; simp only [addAll, addD]; omega

theorem addAll_perm {a : AMarking} {ds ds' : List Row} (h : ds.Perm ds') :
    addAll a ds = addAll a ds' := by
  funext p
  simp only [addAll]
  rw [(h.map _).sum_eq]

theorem le_addAll (a : AMarking) (ds : List Row) (p : PlaceId) : a p ≤ addAll a ds p := by
  simp [addAll]

/-- A place no row of `ds` deposits into keeps its count. -/
theorem addAll_of_zero {a : AMarking} {ds : List Row} {p : PlaceId}
    (h : ∀ r ∈ ds, r.2.count p = 0) : addAll a ds p = a p := by
  have : (ds.map fun r => r.2.count p).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact h r hr
  simp [addAll, this]

/-! ## Non-monotone tests and the one-step commutation -/

/-- Transition `t` tests `p` only monotonically: no inhibitor, no reset, no draining input on
`p` (the complement of `non_monotone_places`). -/
def MonoAt (t : Transition) (p : PlaceId) : Prop :=
  p ∉ t.inhibitors ∧ t.resets.contains p = false ∧ consumeAllAt t p = false

/-- No row of `rows` tests a place the deposit `d` writes non-monotonically. -/
def Untested (rows : List Row) (d : Deposit) : Prop :=
  ∀ u ∈ rows, ∀ p, 0 < d.count p → MonoAt u.1 p

/-- More tokens on places `t` tests monotonically keep `t` enabled. -/
theorem enabledA_addD {a : AMarking} {t : Transition} {d : Deposit}
    (hm : ∀ p, 0 < d.count p → MonoAt t p) (h : enabledA a t = true) :
    enabledA (addD a d) t = true := by
  unfold enabledA at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  obtain ⟨⟨hin, hinh⟩, hrd⟩ := h
  refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
  · have := hin s hs
    simp only [addD]
    omega
  · have h0 := hinh p hp
    simp only [addD, h0, Nat.zero_add]
    by_contra hne
    exact (hm p (Nat.pos_of_ne_zero hne)).1 hp
  · have := hrd p hp
    simp only [addD]
    omega

/-- **Starting commutes with a deposit it does not drain or reset.** -/
theorem startA_addD {a : AMarking} {t : Transition} {d : Deposit}
    (hm : ∀ p, 0 < d.count p → MonoAt t p) (hen : enabledA a t = true) :
    startA (addD a d) t = addD (startA a t) d := by
  funext p
  simp only [startA, fireAD, addD, List.count_nil]
  by_cases hd : d.count p = 0
  · rw [hd]
    split_ifs <;> omega
  · obtain ⟨-, hr, hc⟩ := hm p (Nat.pos_of_ne_zero hd)
    have hle := pre_le_of_enabledA hen p
    simp only [hr, hc, Bool.false_eq_true, if_false]
    omega

/-- **The reordering lemma.** A step `u` that tests no place of `d` non-monotonically commutes
with depositing `d`: with `d` deposited first, `u` is still enabled and ends in the same marking
plus `d`. A completion therefore moves left past it. -/
theorem commute_add {a : AMarking} {u : Row} {d : Deposit}
    (hm : ∀ p, 0 < d.count p → MonoAt u.1 p) (hen : enabledA a u.1 = true) :
    enabledA (addD a d) u.1 = true ∧
      fireAD (addD a d) u.1 u.2 = addD (fireAD a u.1 u.2) d := by
  refine ⟨enabledA_addD hm hen, ?_⟩
  rw [fireAD_eq_addD_startA, fireAD_eq_addD_startA, startA_addD hm hen]
  funext p
  simp only [addD]
  omega

theorem enabledA_addAll {rows : List Row} {a : AMarking} {t : Transition} {ds : List Row}
    (hu : ∀ r ∈ ds, Untested rows r.2) (ht : ∃ d, (t, d) ∈ rows)
    (h : enabledA a t = true) : enabledA (addAll a ds) t = true := by
  obtain ⟨d0, hd0⟩ := ht
  induction ds generalizing a with
  | nil => rw [addAll_nil]; exact h
  | cons r ds ih =>
    rw [addAll_cons]
    exact ih (fun r' hr' => hu r' (List.mem_cons_of_mem r hr'))
      (enabledA_addD (fun p hp => hu r List.mem_cons_self (t, d0) hd0 p hp) h)

theorem startA_addAll {rows : List Row} {a : AMarking} {t : Transition} {ds : List Row}
    (hu : ∀ r ∈ ds, Untested rows r.2) (ht : ∃ d, (t, d) ∈ rows)
    (h : enabledA a t = true) : startA (addAll a ds) t = addAll (startA a t) ds := by
  obtain ⟨d0, hd0⟩ := ht
  induction ds generalizing a with
  | nil => simp [addAll_nil]
  | cons r ds ih =>
    have hm : ∀ p, 0 < r.2.count p → MonoAt t p :=
      fun p hp => hu r List.mem_cons_self (t, d0) hd0 p hp
    rw [addAll_cons, addAll_cons, ← startA_addD hm h]
    exact ih (fun r' hr' => hu r' (List.mem_cons_of_mem r hr')) (enabledA_addD hm h)


/-! ## The executor and the split net -/

/-- A state: the marking and the names of the transitions in flight (with multiplicity; a name
stands for its transition, premise 1 of `TimedScg/Succ.lean`). -/
structure XState where
  a : AMarking
  pend : List String

/-- **The executor.** A row starts when enabled; an in-flight transition completes with any of
its rows. Neither happens from a marking `live` rejects (the strict stop, [EXEC-042]). -/
inductive XStep (rows : List Row) (live : AMarking → Prop) : XState → XState → Prop
  | start (s : XState) (r : Row) (hr : r ∈ rows) (hl : live s.a)
      (hen : enabledA s.a r.1 = true) :
      XStep rows live s ⟨startA s.a r.1, r.1.name :: s.pend⟩
  | complete (s : XState) (r : Row) (hr : r ∈ rows) (hl : live s.a) (hp : r.1.name ∈ s.pend) :
      XStep rows live s ⟨addD s.a r.2, s.pend.erase r.1.name⟩

/-- **The split net** for the split set `sp` (by transition name): a transition outside `sp`
fires atomically, one in `sp` starts and completes as the executor does. Every step is gated by
`live`, as the terminal rewrite gates every transition of the split net. -/
inductive SStep (rows : List Row) (sp : String → Bool) (live : AMarking → Prop) :
    XState → XState → Prop
  | atomic (s : XState) (r : Row) (hr : r ∈ rows) (hsp : sp r.1.name = false) (hl : live s.a)
      (hen : enabledA s.a r.1 = true) : SStep rows sp live s ⟨fireAD s.a r.1 r.2, s.pend⟩
  | start (s : XState) (r : Row) (hr : r ∈ rows) (hsp : sp r.1.name = true) (hl : live s.a)
      (hen : enabledA s.a r.1 = true) :
      SStep rows sp live s ⟨startA s.a r.1, r.1.name :: s.pend⟩
  | complete (s : XState) (r : Row) (hr : r ∈ rows) (hl : live s.a) (hp : r.1.name ∈ s.pend) :
      SStep rows sp live s ⟨addD s.a r.2, s.pend.erase r.1.name⟩

def XReach (rows : List Row) (live : AMarking → Prop) (a0 : AMarking) : XState → Prop :=
  Relation.ReflTransGen (XStep rows live) ⟨a0, []⟩

def SReach (rows : List Row) (sp : String → Bool) (live : AMarking → Prop) (a0 : AMarking) :
    XState → Prop :=
  Relation.ReflTransGen (SStep rows sp live) ⟨a0, []⟩

/-- Transition names are unique among the rows (premise 1 of `TimedScg/Succ.lean`). -/
def NamesUnique (rows : List Row) : Prop :=
  ∀ r ∈ rows, ∀ r' ∈ rows, r.1.name = r'.1.name → r.1 = r'.1

/-- `ds` completes the in-flight list `L`: one row of each in-flight transition, in any order. -/
def Completes (rows : List Row) (L : List String) (ds : List Row) : Prop :=
  (ds.map fun r => r.1.name).Perm L ∧ ∀ r ∈ ds, r ∈ rows

theorem filter_erase_of_false {L : List String} {t : String} {f : String → Bool}
    (h : f t = false) : (L.erase t).filter f = L.filter f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hx : x = t
    · subst hx
      simp [List.erase_cons_head, h]
    · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hx)]
      by_cases hfx : f x = true <;> simp [hfx, ih]

theorem filter_erase_of_true {L : List String} {t : String} {f : String → Bool}
    (h : f t = true) : (L.erase t).filter f = (L.filter f).erase t := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hx : x = t
    · subst hx
      simp [List.erase_cons_head, h]
    · rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hx)]
      by_cases hfx : f x = true
      · simp only [List.filter_cons, hfx, if_true]
        rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hx), ih]
      · simp [hfx, ih]

/-- Every in-flight transition has a row: it started as one. -/
theorem pend_has_row {rows : List Row} {live : AMarking → Prop} {a0 : AMarking} {s : XState}
    (h : XReach rows live a0 s) : ∀ t ∈ s.pend, ∃ r ∈ rows, r.1.name = t := by
  induction h with
  | refl => intro t ht; exact absurd ht List.not_mem_nil
  | tail _ hstep ih =>
    cases hstep with
    | start r hr _ hen =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨r, hr, rfl⟩
      · exact ih t ht
    | complete r hr _ hp =>
      intro t ht
      exact ih t (List.mem_of_mem_erase ht)

/-- A completion of the actions in flight exists. -/
theorem completes_exists {rows : List Row} :
    ∀ {L : List String}, (∀ t ∈ L, ∃ r ∈ rows, r.1.name = t) → ∃ ds, Completes rows L ds
  | [], _ => ⟨[], List.Perm.refl _, fun _ h => absurd h List.not_mem_nil⟩
  | t :: L, h => by
    obtain ⟨r, hr, hrt⟩ := h t List.mem_cons_self
    obtain ⟨ds, hperm, hmem⟩ := completes_exists (fun t' ht' => h t' (List.mem_cons_of_mem t ht'))
    refine ⟨r :: ds, ?_, fun x hx => ?_⟩
    · rw [List.map_cons, hrt]
      exact hperm.cons t
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hmem x hx

/-- A completion of the non-split actions in flight holds only rows outside the split. -/
theorem completes_nonsplit {rows : List Row} {sp : String → Bool} {L : List String}
    {ds : List Row} (hc : Completes rows (L.filter fun t => !sp t) ds) :
    ∀ r ∈ ds, r ∈ rows ∧ sp r.1.name = false := by
  intro r hr
  have hmem : r.1.name ∈ L.filter (fun t => !sp t) :=
    hc.1.subset (List.mem_map.mpr ⟨r, hr, rfl⟩)
  exact ⟨hc.2 r hr, by simpa using (List.mem_filter.mp hmem).2⟩

/-- Deposits of rows outside the split keep `live`. -/
theorem live_addAll {rows : List Row} {sp : String → Bool} {live : AMarking → Prop}
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2))
    {ds : List Row} (hds : ∀ r ∈ ds, r ∈ rows ∧ sp r.1.name = false) :
    ∀ {a : AMarking}, live a → live (addAll a ds) := by
  induction ds with
  | nil => intro a h; rw [addAll_nil]; exact h
  | cons r ds ih =>
    intro a h
    rw [addAll_cons]
    obtain ⟨hr, hsp⟩ := hds r List.mem_cons_self
    exact ih (fun r' hr' => hds r' (List.mem_cons_of_mem r hr')) (hlive r hr hsp a h)

/-- **The split net covers the executor.** Given that every transition outside `sp` has only
untested outputs and keeps `live` when it deposits, for every executor state and every
completion `ds` of its non-split actions in flight, the split net reaches the executor's marking
with `ds` deposited and the split actions in flight as in the executor. -/
theorem split_covers_executor {rows : List Row} {sp : String → Bool} {live : AMarking → Prop}
    {a0 : AMarking} (hnames : NamesUnique rows)
    (hcrit : ∀ r ∈ rows, sp r.1.name = false → Untested rows r.2)
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2)) {s : XState}
    (h : XReach rows live a0 s) :
    ∀ ds, Completes rows (s.pend.filter fun t => !sp t) ds →
      SReach rows sp live a0 ⟨addAll s.a ds, s.pend.filter sp⟩ := by
  have hunt : ∀ {L : List String} {ds : List Row},
      Completes rows (L.filter fun t => !sp t) ds → ∀ r ∈ ds, Untested rows r.2 :=
    fun hc r hr => hcrit r (completes_nonsplit hc r hr).1 (completes_nonsplit hc r hr).2
  have hl' : ∀ {L : List String} {ds : List Row} {a : AMarking},
      Completes rows (L.filter fun t => !sp t) ds → live a → live (addAll a ds) :=
    fun hc h => live_addAll hlive (completes_nonsplit hc) h
  induction h with
  | refl =>
    intro ds hds
    have hnil : ds = [] := by
      have h0 : (ds.map fun r => r.1.name) = [] := List.perm_nil.mp (by simpa using hds.1)
      exact List.map_eq_nil_iff.mp h0
    subst hnil
    show SReach rows sp live a0 ⟨addAll a0 [], []⟩
    rw [addAll_nil]
    exact Relation.ReflTransGen.refl
  | @tail s1 s2 hr1 hstep ih =>
    cases hstep with
    | start r hr hl hen =>
      intro ds hds
      have hrow : ∃ d, (r.1, d) ∈ rows := ⟨r.2, hr⟩
      cases hsp : sp r.1.name with
      | true =>
        have hf : (r.1.name :: s1.pend).filter (fun t => !sp t) =
            s1.pend.filter (fun t => !sp t) := by
          simp [hsp]
        rw [hf] at hds
        have hprev := ih ds hds
        have hstep' := SStep.start (sp := sp) (live := live)
          ⟨addAll s1.a ds, s1.pend.filter sp⟩ r hr hsp (hl' hds hl)
          (enabledA_addAll (hunt hds) hrow hen)
        simp only at hstep'
        rw [startA_addAll (hunt hds) hrow hen] at hstep'
        have hq : (r.1.name :: s1.pend).filter sp = r.1.name :: s1.pend.filter sp := by
          simp [hsp]
        rw [hq]
        exact Relation.ReflTransGen.tail hprev hstep'
      | false =>
        have hf : (r.1.name :: s1.pend).filter (fun t => !sp t) =
            r.1.name :: s1.pend.filter (fun t => !sp t) := by
          simp [hsp]
        rw [hf] at hds
        -- the row of `ds` completing this start
        have hmem : r.1.name ∈ ds.map fun r => r.1.name := hds.1.symm.subset List.mem_cons_self
        obtain ⟨r', hr', hr'1⟩ := List.mem_map.mp hmem
        obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hr'
        have hperm : ds.Perm (r' :: (l1 ++ l2)) := hsplit ▸ List.perm_middle
        have hsub : ∀ x ∈ l1 ++ l2, x ∈ ds := fun x hx => by
          rw [hsplit]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
        have hds' : Completes rows (s1.pend.filter fun t => !sp t) (l1 ++ l2) := by
          refine ⟨?_, fun x hx => hds.2 x (hsub x hx)⟩
          have h1 := (hperm.map fun r => r.1.name).symm.trans hds.1
          rw [List.map_cons, hr'1] at h1
          exact (List.perm_cons _).mp h1
        have hprev := ih (l1 ++ l2) hds'
        have hr'rows := hds.2 r' hr'
        have heq : r'.1 = r.1 := hnames r' hr'rows r hr hr'1
        have hr'sp : sp r'.1.name = false := by rw [heq]; exact hsp
        have hen' : enabledA s1.a r'.1 = true := by rw [heq]; exact hen
        have hrow' : ∃ d, (r'.1, d) ∈ rows := ⟨r'.2, hr'rows⟩
        have hstep' := SStep.atomic (sp := sp) (live := live)
          ⟨addAll s1.a (l1 ++ l2), s1.pend.filter sp⟩ r' hr'rows hr'sp (hl' hds' hl)
          (enabledA_addAll (hunt hds') hrow' hen')
        simp only at hstep'
        rw [fireAD_eq_addD_startA, startA_addAll (hunt hds') hrow' hen', addD_addAll] at hstep'
        have hq : (r.1.name :: s1.pend).filter sp = s1.pend.filter sp := by
          simp [hsp]
        rw [hq, addAll_perm hperm, addAll_cons, ← heq]
        exact Relation.ReflTransGen.tail hprev hstep'
    | complete r hr hl hp =>
      intro ds hds
      cases hsp : sp r.1.name with
      | true =>
        have hf : (s1.pend.erase r.1.name).filter (fun t => !sp t) =
            s1.pend.filter (fun t => !sp t) :=
          filter_erase_of_false (by simp [hsp])
        rw [hf] at hds
        have hprev := ih ds hds
        have hin : r.1.name ∈ s1.pend.filter sp := List.mem_filter.mpr ⟨hp, hsp⟩
        have hstep' := SStep.complete (sp := sp) (live := live)
          ⟨addAll s1.a ds, s1.pend.filter sp⟩ r hr (hl' hds hl) hin
        simp only at hstep'
        rw [addD_addAll, ← filter_erase_of_true hsp] at hstep'
        exact Relation.ReflTransGen.tail hprev hstep'
      | false =>
        have hin : r.1.name ∈ s1.pend.filter (fun t => !sp t) :=
          List.mem_filter.mpr ⟨hp, by simp [hsp]⟩
        have hds' : Completes rows (s1.pend.filter fun t => !sp t) (r :: ds) := by
          refine ⟨?_, fun x hx => ?_⟩
          · rw [List.map_cons]
            have h1 := List.Perm.cons r.1.name hds.1
            rw [filter_erase_of_true (f := fun t => !sp t) (by simp [hsp])] at h1
            exact h1.trans (List.perm_cons_erase hin).symm
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hr
            · exact hds.2 x hx
        have hprev := ih (r :: ds) hds'
        rw [addAll_cons] at hprev
        show SReach rows sp live a0
          ⟨addAll (addD s1.a r.2) ds, (s1.pend.erase r.1.name).filter sp⟩
        rw [filter_erase_of_false hsp]
        exact hprev

/-- **The commutation lemma.** With no output tested non-monotonically, every interleaving of
starts and completions is matched by an atomic run (`ReachAD`), which reaches the executor's
marking with the pending deposits added. -/
theorem atomic_covers_executor {rows : List Row} {live : AMarking → Prop} {a0 : AMarking}
    (hnames : NamesUnique rows) (hcrit : ∀ r ∈ rows, Untested rows r.2)
    (hlive : ∀ r ∈ rows, ∀ a, live a → live (addD a r.2)) {s : XState}
    (h : XReach rows live a0 s) :
    ∀ ds, Completes rows s.pend ds → ReachAD rows a0 (addAll s.a ds) := by
  intro ds hds
  have hS := split_covers_executor (sp := fun _ => false) hnames (fun r hr _ => hcrit r hr)
    (fun r hr _ => hlive r hr) h ds (by simpa using hds)
  -- with nothing split the pending list of the split net stays empty
  have key : ∀ x, SReach rows (fun _ => false) live a0 x → x.pend = [] ∧ ReachAD rows a0 x.a := by
    intro x hx
    induction hx with
    | refl => exact ⟨rfl, Relation.ReflTransGen.refl⟩
    | tail _ hst ih =>
      obtain ⟨hp, hreach⟩ := ih
      cases hst with
      | atomic r hr _ _ hen => exact ⟨hp, Relation.ReflTransGen.tail hreach ⟨r, hr, hen, rfl⟩⟩
      | start r hr hsp _ _ => exact absurd hsp (by simp)
      | complete r hr _ hpend => rw [hp] at hpend; exact absurd hpend List.not_mem_nil
  exact (key _ hS).2

/-- A marking property closed upward: more tokens never make it good again. Every safety
property of `SmtProperty` is one (a place bound, an unreachable marked set, a mutual exclusion,
a branch place bound). -/
def UpClosed (bad : AMarking → Prop) : Prop := ∀ a b, (∀ p, a p ≤ b p) → bad a → bad b

/-- A marking property that reads the places `Q` exactly and every other place upward-closed:
with `Q` unchanged, more tokens elsewhere never make it good again. -/
def UpClosedOff (Q : PlaceId → Prop) (bad : AMarking → Prop) : Prop :=
  ∀ a b, (∀ p, a p ≤ b p) → (∀ p, Q p → a p = b p) → bad a → bad b

theorem upClosedOff_of_upClosed {bad : AMarking → Prop} (h : UpClosed bad) :
    UpClosedOff (fun _ => False) bad :=
  fun a b hle _ hb => h a b hle hb

/-- **A `Proven` of the split net holds at every executor state, abandoned actions included.**
The property reads `Q` exactly and the rest upward-closed; no transition outside `sp` deposits
into `Q`. The executor state may hold actions in flight that never complete: the split net
reaches a marking that agrees with it on `Q` and holds at least as much elsewhere. -/
theorem split_stop_sound {rows : List Row} {sp : String → Bool} {live : AMarking → Prop}
    {a0 : AMarking} (hnames : NamesUnique rows)
    (hcrit : ∀ r ∈ rows, sp r.1.name = false → Untested rows r.2)
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2))
    {Q : PlaceId → Prop} (hQ : ∀ r ∈ rows, sp r.1.name = false → ∀ p, Q p → r.2.count p = 0)
    {bad : AMarking → Prop} (hbad : UpClosedOff Q bad)
    (hproven : ∀ x, SReach rows sp live a0 x → ¬ bad x.a) {s : XState}
    (h : XReach rows live a0 s) : ¬ bad s.a := by
  intro hb
  obtain ⟨ds, hds⟩ := completes_exists (rows := rows) (L := s.pend.filter fun t => !sp t)
    (fun t ht => pend_has_row h t (List.mem_filter.mp ht).1)
  have hns := completes_nonsplit hds
  refine hproven _ (split_covers_executor hnames hcrit hlive h ds hds)
    (hbad _ _ (le_addAll s.a ds) (fun p hp => ?_) hb)
  exact (addAll_of_zero fun r hr => hQ r (hns r hr).1 (hns r hr).2 p hp).symm

/-- **A safety `Proven` of the split net holds at every executor state**, an action in flight
or not. -/
theorem split_safety_sound {rows : List Row} {sp : String → Bool} {live : AMarking → Prop}
    {a0 : AMarking} (hnames : NamesUnique rows)
    (hcrit : ∀ r ∈ rows, sp r.1.name = false → Untested rows r.2)
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2))
    {bad : AMarking → Prop} (hup : UpClosed bad)
    (hproven : ∀ x, SReach rows sp live a0 x → ¬ bad x.a) {s : XState}
    (h : XReach rows live a0 s) : ¬ bad s.a :=
  split_stop_sound hnames hcrit hlive (fun _ _ _ _ hp => absurd hp id)
    (upClosedOff_of_upClosed hup) hproven h

/-- **Where nothing is in flight, the executor's state is a split-net state.** -/
theorem split_rest_sound {rows : List Row} {sp : String → Bool} {live : AMarking → Prop}
    {a0 : AMarking} (hnames : NamesUnique rows)
    (hcrit : ∀ r ∈ rows, sp r.1.name = false → Untested rows r.2)
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2)) {a : AMarking}
    (h : XReach rows live a0 ⟨a, []⟩) : SReach rows sp live a0 ⟨a, []⟩ := by
  have := split_covers_executor hnames hcrit hlive h []
    ⟨by simp, fun _ h => absurd h List.not_mem_nil⟩
  rw [addAll_nil] at this
  exact this

/-! ## The `QuiescentCount` lower bound at a terminal stop -/

/-- The `QuiescentCount` lower-bound violation at a terminal stop ([VER-002] AC8, [EXEC-042]):
a terminal of `terms` is marked, so the rewritten net enables nothing and the marking is
quiescent (`TerminalRewrite.lean`); the count over `P` is below `min`; every waiver place of `W`
is empty. -/
def stopCountBad (terms P W : List PlaceId) (min : Nat) (a : AMarking) : Prop :=
  (∃ τ ∈ terms, 0 < a τ) ∧ (P.map a).sum < min ∧ ∀ w ∈ W, a w = 0

/-- It reads the counted and waiver places exactly (`quiescent_count_demand`'s `tested` set)
and the terminals upward-closed. -/
theorem stopCountBad_upClosedOff (terms P W : List PlaceId) (min : Nat) :
    UpClosedOff (fun p => p ∈ P ∨ p ∈ W) (stopCountBad terms P W min) := by
  intro a b hle hQ ⟨⟨τ, hτ, hpos⟩, hsum, hw⟩
  refine ⟨⟨τ, hτ, lt_of_lt_of_le hpos (hle τ)⟩, ?_, fun w hw' => ?_⟩
  · have : P.map b = P.map a := List.map_congr_left fun p hp => (hQ p (Or.inl hp)).symm
    rw [this]
    exact hsum
  · rw [← hQ w (Or.inr hw')]
    exact hw w hw'

/-- A zero lower bound is never short: `quiescent_count_demand` is empty for `min = 0`. -/
theorem stop_min_zero (terms P W : List PlaceId) (a : AMarking) :
    ¬ stopCountBad terms P W 0 a :=
  fun ⟨_, h, _⟩ => Nat.not_lt_zero _ h

/-- A stop by a terminal that is also a waiver is waived: `quiescent_count_demand` is empty
when every terminal is a waiver place. -/
theorem stop_waived {terms P W : List PlaceId} {min : Nat} (h : ∀ τ ∈ terms, τ ∈ W)
    (a : AMarking) : ¬ stopCountBad terms P W min a := by
  rintro ⟨⟨τ, hτ, hpos⟩, _, hw⟩
  rw [hw τ (h τ hτ)] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- **The `QuiescentCount` lower bound holds at every terminal stop of the executor** when the
split net proves it and every transition depositing into a counted or waiver place is split
(`quiescent_count_demand`). An action the stop abandons is in flight in the split net too, or
deposits nowhere the count reads. -/
theorem quiescent_count_stop_sound {rows : List Row} {sp : String → Bool}
    {live : AMarking → Prop} {a0 : AMarking} {terms P W : List PlaceId} {min : Nat}
    (hnames : NamesUnique rows)
    (hcrit : ∀ r ∈ rows, sp r.1.name = false → Untested rows r.2)
    (hlive : ∀ r ∈ rows, sp r.1.name = false → ∀ a, live a → live (addD a r.2))
    (hQ : ∀ r ∈ rows, sp r.1.name = false → ∀ p, p ∈ P ∨ p ∈ W → r.2.count p = 0)
    (hproven : ∀ x, SReach rows sp live a0 x → ¬ stopCountBad terms P W min x.a) {s : XState}
    (h : XReach rows live a0 s) : ¬ stopCountBad terms P W min s.a :=
  split_stop_sound hnames hcrit hlive hQ (stopCountBad_upClosedOff terms P W min) hproven h

/-! ## The criterion is needed -/

section Witness

/-- Places: `p = 0`, `q = 1`, `r = 2`, `bad = 3`. `t : p → q`. -/
def tW : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- `u : r, inhibitor p, inhibitor q → bad`: it tests `t`'s output `q` by an inhibitor. -/
def uW : Transition :=
  { name := "u", inputs := [⟨2, .one, none⟩], inhibitors := [0, 1], reads := [], resets := [] }

def rowsW : List Row := [(tW, [1]), (uW, [3])]

def a0W : AMarking := fun x => if x = 0 ∨ x = 2 then 1 else 0

/-- No terminal place: every marking is live. -/
def liveW : AMarking → Prop := fun _ => True

/-- `u` tests `t`'s output: the criterion splits `t`. -/
theorem t_output_tested : ¬ Untested rowsW [1] := by
  intro h
  exact (h (uW, [3]) (by simp [rowsW]) 1 (by decide)).1 (by simp [uW])

/-- **The executor marks `bad`**, with `t` in flight. -/
theorem executor_marks_bad : ∃ s, XReach rowsW liveW a0W s ∧ s.a 3 = 1 := by
  have h1 := XStep.start (rows := rowsW) (live := liveW) ⟨a0W, []⟩ (tW, [1]) (by simp [rowsW])
    trivial (by decide)
  have h2 := XStep.start (rows := rowsW) (live := liveW) ⟨startA a0W tW, ["t"]⟩ (uW, [3])
    (by simp [rowsW]) trivial (by decide)
  have h3 := XStep.complete (rows := rowsW) (live := liveW)
    ⟨startA (startA a0W tW) uW, ["u", "t"]⟩ (uW, [3]) (by simp [rowsW]) trivial (by decide)
  exact ⟨_, ((Relation.ReflTransGen.single h1).tail h2).tail h3, by decide⟩

/-- **The atomic net never marks `bad`.** -/
theorem atomic_never_bad : ∀ a, ReachAD rowsW a0W a → a 3 = 0 := by
  suffices H : ∀ a, ReachAD rowsW a0W a → a 0 + a 1 = 1 ∧ a 3 = 0 from fun a h => (H a h).2
  intro a h
  induction h with
  | refl => decide
  | @tail x y _ hst ih =>
    obtain ⟨ih1, ih3⟩ := ih
    obtain ⟨tr, htr, hen, rfl⟩ := hst
    simp only [rowsW, List.mem_cons, List.not_mem_nil, or_false] at htr
    rcases htr with rfl | rfl
    · have hen0 : 1 ≤ x 0 := by
        simp only [enabledA, tW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hen
        simpa [Card.required] using hen.1.1
      refine ⟨?_, ?_⟩ <;>
        simp [fireAD, tW, consumeAllAt, pre, specAt, Card.consumesAll, Card.required] <;> omega
    · exfalso
      simp only [enabledA, uW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
        beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false] at hen
      have h0 : x 0 = 0 := hen.1.2 0 (Or.inl rfl)
      have h1 : x 1 = 0 := hen.1.2 1 (Or.inr rfl)
      omega

/-- **The split net with `t` split marks `bad` too**, as the executor does. -/
theorem split_marks_bad :
    ∃ x, SReach rowsW (fun t => t == "t") liveW a0W x ∧ x.a 3 = 1 := by
  have h1 := SStep.start (rows := rowsW) (sp := fun t => t == "t") (live := liveW) ⟨a0W, []⟩
    (tW, [1]) (by simp [rowsW]) (by decide) trivial (by decide)
  have h2 := SStep.atomic (rows := rowsW) (sp := fun t => t == "t") (live := liveW)
    ⟨startA a0W tW, ["t"]⟩ (uW, [3]) (by simp [rowsW]) (by decide) trivial (by decide)
  exact ⟨_, (Relation.ReflTransGen.single h1).tail h2, by decide⟩

/-- **The criterion is needed.** On a net where another transition inhibits `t`'s output, the
executor marks `bad`, the atomic net never does, and the split net does. -/
theorem inflight_witness :
    ¬ Untested rowsW [1] ∧ (∃ s, XReach rowsW liveW a0W s ∧ s.a 3 = 1) ∧
      (∀ a, ReachAD rowsW a0W a → a 3 = 0) ∧
      ∃ x, SReach rowsW (fun t => t == "t") liveW a0W x ∧ x.a 3 = 1 :=
  ⟨t_output_tested, executor_marks_bad, atomic_never_bad, split_marks_bad⟩

end Witness

/-! ## The terminal demand is needed -/

section TerminalWitness

/-- Places: `a = 0`, `ok = 1`, `s = 2`, `done = 3` (terminal). `t : a → ok`, with the terminal
inhibitor the rewrite adds. -/
def tF : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [3], reads := [], resets := [] }

/-- `f : s → done`, with the terminal inhibitor. -/
def fF : Transition :=
  { name := "f", inputs := [⟨2, .one, none⟩], inhibitors := [3], reads := [], resets := [] }

def rowsF : List Row := [(tF, [1]), (fF, [3])]

def a0F : AMarking := fun x => if x = 0 ∨ x = 2 then 1 else 0

/-- The strict stop: nothing happens once `done` is marked. -/
abbrev liveF : AMarking → Prop := fun a => a 3 = 0

/-- The plain split: `f` deposits into the terminal, `t` into an untested place. -/
def spPlain : String → Bool := fun n => n == "f"

/-- The split with `quiescent_count_demand([a, ok], 1)`: `t` deposits into `ok`. -/
def spDemand : String → Bool := fun n => n == "t" || n == "f"

/-- `QuiescentCount([a, ok], 1)`, no waiver, read at a stop by `done`. -/
def shortF : AMarking → Prop := stopCountBad [3] [0, 1] [] 1

/-- The plain split meets the criterion and the strict-stop premise. -/
theorem plain_premises :
    (∀ r ∈ rowsF, spPlain r.1.name = false → Untested rowsF r.2) ∧
      (∀ r ∈ rowsF, spPlain r.1.name = false → ∀ a, liveF a → liveF (addD a r.2)) := by
  refine ⟨fun r hr hsp u hu p hp => ?_, fun r hr hsp a ha => ?_⟩
  · simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr hu
    rcases hr with rfl | rfl
    · have hp1 : p = 1 := by simpa using List.count_pos_iff.mp hp
      subst hp1
      rcases hu with rfl | rfl <;> exact ⟨by simp [tF, fF], by decide, by decide⟩
    · exact absurd hsp (by decide)
  · simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [liveF, addD] at ha ⊢
      simp [ha]
    · exact absurd hsp (by decide)

/-- The plain split fails the demand's premise: `t` is not split and deposits into `ok`. -/
theorem plain_misses_demand :
    ¬ ∀ r ∈ rowsF, spPlain r.1.name = false → ∀ p, p ∈ [0, 1] ∨ p ∈ ([] : List PlaceId) →
      r.2.count p = 0 := by
  intro h
  exact absurd (h (tF, [1]) (by simp [rowsF]) (by decide) 1 (by simp)) (by decide)

/-- The demand's split meets every premise of `quiescent_count_stop_sound`: nothing is left
unsplit. -/
theorem demand_premises :
    (∀ r ∈ rowsF, spDemand r.1.name = false → Untested rowsF r.2) ∧
      (∀ r ∈ rowsF, spDemand r.1.name = false → ∀ a, liveF a → liveF (addD a r.2)) ∧
      (∀ r ∈ rowsF, spDemand r.1.name = false → ∀ p, p ∈ [0, 1] ∨ p ∈ ([] : List PlaceId) →
        r.2.count p = 0) := by
  have hall : ∀ r ∈ rowsF, spDemand r.1.name = true := by
    intro r hr
    simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨fun r hr hsp => ?_, fun r hr hsp => ?_, fun r hr hsp => ?_⟩ <;>
    exact absurd hsp (by rw [hall r hr]; decide)

/-- **On the plain split the count is never short**: `t` fires atomically, so `a + ok = 1`. -/
theorem plain_never_short : ∀ x, SReach rowsF spPlain liveF a0F x → ¬ shortF x.a := by
  suffices H : ∀ x, SReach rowsF spPlain liveF a0F x →
      x.a 0 + x.a 1 = 1 ∧ ∀ n ∈ x.pend, n = "f" by
    intro x hx ⟨_, hsum, _⟩
    have := (H x hx).1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    omega
  intro x hx
  induction hx with
  | refl => exact ⟨by decide, fun n hn => absurd hn List.not_mem_nil⟩
  | @tail x y _ hst ih =>
    obtain ⟨ih1, ihp⟩ := ih
    cases hst with
    | atomic r hr hsp _ hen =>
      simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hen0 : 1 ≤ x.a 0 := by
          simp only [enabledA, tF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
            List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hen
          simpa [Card.required] using hen.1.1
        refine ⟨?_, ihp⟩
        simp [fireAD, tF, consumeAllAt, pre, specAt, Card.consumesAll, Card.required]
        omega
      · exact absurd hsp (by decide)
    | start r hr hsp _ hen =>
      simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact absurd hsp (by decide)
      · refine ⟨?_, fun n hn => ?_⟩
        · simp only [startA, fireAD, fF, consumeAllAt, pre, specAt]
          simpa using ih1
        · rcases List.mem_cons.mp hn with rfl | hn
          · rfl
          · exact ihp n hn
    | complete r hr _ hp =>
      simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact absurd (ihp _ hp) (by decide)
      · refine ⟨?_, fun n hn => ihp n (List.mem_of_mem_erase hn)⟩
        simp [addD]
        omega

/-- **The executor stops short**: `t` starts, `f` marks `done`, and the stop abandons `t`. -/
theorem executor_stops_short : ∃ s, XReach rowsF liveF a0F s ∧ shortF s.a := by
  have h1 := XStep.start (rows := rowsF) (live := liveF) ⟨a0F, []⟩ (tF, [1]) (by simp [rowsF])
    (by decide) (by decide)
  have h2 := XStep.start (rows := rowsF) (live := liveF) ⟨startA a0F tF, ["t"]⟩ (fF, [3])
    (by simp [rowsF]) (by decide) (by decide)
  have h3 := XStep.complete (rows := rowsF) (live := liveF)
    ⟨startA (startA a0F tF) fF, ["f", "t"]⟩ (fF, [3]) (by simp [rowsF]) (by decide) (by decide)
  exact ⟨_, ((Relation.ReflTransGen.single h1).tail h2).tail h3,
    ⟨3, by simp, by decide⟩, by decide, by simp⟩

/-- **The demand's split stops short too**, as the executor does. -/
theorem demand_stops_short : ∃ x, SReach rowsF spDemand liveF a0F x ∧ shortF x.a := by
  have h1 := SStep.start (rows := rowsF) (sp := spDemand) (live := liveF) ⟨a0F, []⟩ (tF, [1])
    (by simp [rowsF]) (by decide) (by decide) (by decide)
  have h2 := SStep.start (rows := rowsF) (sp := spDemand) (live := liveF)
    ⟨startA a0F tF, ["t"]⟩ (fF, [3]) (by simp [rowsF]) (by decide) (by decide) (by decide)
  have h3 := SStep.complete (rows := rowsF) (sp := spDemand) (live := liveF)
    ⟨startA (startA a0F tF) fF, ["f", "t"]⟩ (fF, [3]) (by simp [rowsF]) (by decide) (by decide)
  exact ⟨_, ((Relation.ReflTransGen.single h1).tail h2).tail h3,
    ⟨3, by simp, by decide⟩, by decide, by simp⟩

/-- **The terminal demand is needed.** The plain split proves `QuiescentCount([a, ok], 1)` at
every stop and misses the demand's premise; the executor stops short; the split with the demand
reaches that stop. -/
theorem terminal_stop_witness :
    (∀ x, SReach rowsF spPlain liveF a0F x → ¬ shortF x.a) ∧
      (¬ ∀ r ∈ rowsF, spPlain r.1.name = false → ∀ p, p ∈ [0, 1] ∨ p ∈ ([] : List PlaceId) →
        r.2.count p = 0) ∧
      (∃ s, XReach rowsF liveF a0F s ∧ shortF s.a) ∧
      ∃ x, SReach rowsF spDemand liveF a0F x ∧ shortF x.a :=
  ⟨plain_never_short, plain_misses_demand, executor_stops_short, demand_stops_short⟩

end TerminalWitness

end Libpetri.Novel.InFlight
