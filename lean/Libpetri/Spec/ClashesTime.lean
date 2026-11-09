import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.EXEC_002

set_option linter.missingDocs true

/-!
# Open clashes of the TIME and EXEC slice, Phase 1

Three clashes of the plan's section 8 are still open after the rulings, and one Phase 2
obligation is recorded with them. Each gets the evidence
the registry allows until it is ruled; none of them encodes a ruling.

* **TIME-014 bullet 2 against EXEC-002 (ruling D9 open).** "Among equal priority, Immediate
  transitions fire before Delayed ones" has two readings. Read as an ordering rule
  (`TIME_014_bullet2_order`), it contradicts EXEC-002's stamp order once the `Delayed`
  transition is ready and was armed first (`TIME_014_bullet2_order_conflicts_EXEC_002`). Read
  through its parenthesis, "since Delayed transitions are not ready until their earliest bound"
  (`TIME_014_bullet2_ready`), it asks only that a transition that is not ready is not in the
  order, which the reference order meets (`TIME_014_bullet2_ambiguity`). Both readings are
  plain definitions over the ready-order interface of EXEC-002, not requirement blocks (ruling
  5): TIME-014 has no block until D9 is ruled, and a candidate reading is not evidence that
  TIME-014 holds. The registry's `conflict` and `ambiguity` roles name requirement blocks only,
  so the conflict is recorded as a citation of EXEC-002 (what it shows is a fact about
  EXEC-002's order on a reachable input), and the ambiguity and the negative examples of the
  two readings are documented theorems without an evidence tag. No theorem here cites TIME-014.
* **TIME-015 AC10, a coarse clock (ruling D12 open).** On the timed reference step a clock that
  repeats its reading changes nothing (`refTStepW_delay_zero`). What decides the outcome is the
  size of the increment: a `Window(3, 5)` transition with tolerance `0` fires under a clock that
  advances 1 ms per reading and is reaped, its token stranded, under one whose next reading after
  `0` is `10`, an increment wider than the window (`time015_ac10_coarse_jump`). Both clocks are
  strictly increasing, so AC10's outcome depends on which strictly increasing clock it is
  compared against. TIME-015's block is written in another module, so the evidence is a
  citation.
* **TIME-013, the reap before the firing pass (Phase 2 obligation).** The atomic step relation
  lets another transition fire while a `Deadline` transition is expired, and a firing that drains
  and refills its input place restarts its clock under [TIME-012], so it is never reaped
  (`clash013_refresh_rescue`). A real cycle cannot do this: its deadline step reaps at the
  cycle's reading before its firing pass ([EXEC-001] steps 4 and 5). Every TIME block holds of
  the reference step that takes this run, so the Phase 2 cycle relation must exclude it.
* **EXEC-040 condition 1 against a rest with a reaped transition enabled.** After the reap of
  the same example, nothing is armed, nothing can fire, and the reaped transition stays enabled
  in every reachable state (`exec040_rest_reaped_enabled`): an executor that waits for "no
  transition enabled" never stops there. The spec text of EXEC-040 already reads "No transition
  is armed", so this is evidence for the text as it stands, as a citation; EXEC-040's block is
  Phase 2.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## TIME-014 bullet 2: two readings -/

/-- **Candidate reading of TIME-014's second bullet as an ordering rule** (ruling D9 open; not
a requirement block, ruling 5). The bullet: "Among equal priority, Immediate transitions fire
before Delayed ones (since Delayed transitions are not ready until their earliest bound)."
Together with the first bullet, "Higher priority transitions are preferred.", read on the ready
order of EXEC-002: for every input of a pass that does not take the all-immediate fast path,
and every two ready transitions `a` and `b`, if `a` has the higher priority, `a` comes before
`b`; if they have equal priority, `a` is `Immediate` and `b` is `Delayed`, `a` comes before `b`.
'Fire before' is read as 'is offered before in the pass's order', and the parenthesis as a
reason, not a restriction, so the second line ranges over every ready pair of equal priority,
one `Immediate` and one `Delayed`, competing or not. Under this reading the bullet conflicts with
EXEC-002 (`TIME_014_bullet2_order_conflicts_EXEC_002`) on an input the timed reference step
reaches (`clash014_reached`). -/
def TIME_014_bullet2_order : ReadyOrder → Prop :=
  fun O => ∀ I : ReadyIn, ¬ I.FastPath → ∀ a ∈ I.readyList, ∀ b ∈ I.readyList,
    (I.prio b < I.prio a → [a, b].Sublist (O I)) ∧
    (I.prio a = I.prio b → I.timing a = .immediate → (∃ e, I.timing b = .delayed e) →
      [a, b].Sublist (O I))

/- The pinned readable form: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_014_bullet2_order : ReadyOrder → Prop :=
fun O =>
  ∀ (I : ReadyIn),
    ¬I.FastPath →
      ∀ a ∈ I.readyList,
        ∀ b ∈ I.readyList,
          (I.prio b < I.prio a → [a, b].Sublist (O I)) ∧
            (I.prio a = I.prio b →
              I.timing a = Timing.immediate → (∃ e, I.timing b = Timing.delayed e) → [a, b].Sublist (O I))
-/
#guard_msgs in #print TIME_014_bullet2_order

/-- **Candidate reading of TIME-014's second bullet through readiness** (ruling D9 open; not a
requirement block, ruling 5). The bullet is read through its parenthesis: a `Delayed`
transition before its earliest bound is not ready, so it is not in the pass's order, and a ready
`Immediate` transition of equal priority is in it and fires first; once both are ready the
bullet adds nothing to EXEC-002. On the ready order of EXEC-002, for every input of a pass that
does not take the all-immediate fast path: the order holds every ready transition exactly once
and nothing else, and of two ready transitions the one with the higher priority comes first.
The bullet's content comes from the bridge `ReadyIn.ofTSt`, which takes the ready bit from
glossary Ready (`time014_ready_bullet2`). The reference order of EXEC-002 meets this reading and
breaks the ordering reading (`TIME_014_bullet2_ambiguity`). -/
def TIME_014_bullet2_ready : ReadyOrder → Prop :=
  fun O => ∀ I : ReadyIn, ¬ I.FastPath →
    (O I).Perm I.readyList ∧
    (∀ a ∈ I.readyList, ∀ b ∈ I.readyList, I.prio b < I.prio a → [a, b].Sublist (O I))

/- The pinned readable form: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_014_bullet2_ready : ReadyOrder → Prop :=
fun O =>
  ∀ (I : ReadyIn),
    ¬I.FastPath →
      (O I).Perm I.readyList ∧ ∀ a ∈ I.readyList, ∀ b ∈ I.readyList, I.prio b < I.prio a → [a, b].Sublist (O I)
-/
#guard_msgs in #print TIME_014_bullet2_ready

/-- Every ordering function that satisfies EXEC-002 satisfies the readiness reading of TIME-014's
second bullet. -/
theorem time014_ready_of_EXEC_002 {O : ReadyOrder} (h : EXEC_002 O) : TIME_014_bullet2_ready O :=
  fun I hI => ⟨(h I).1, fun _ ha _ hb hlt =>
    sublist_pair_of_pairwise (fun _ _ h1 h2 => I.key.lt_asymm h1 h2) ((h I).2.2 hI)
      ((h I).1.mem_iff.2 ha) ((h I).1.mem_iff.2 hb) (Or.inl hlt)⟩

/-- The bullet's content under the readiness reading, on an input bridged from a timed state: a
transition of the list that has not reached its earliest bound is not offered, and a transition
of the list that is Ready is offered. With a `Delayed` transition before its bound and a ready
`Immediate` one, the pass offers the `Immediate` one and not the `Delayed` one. Not a citation
of TIME-014: it holds of a candidate reading, and ruling D9 is open. -/
theorem time014_ready_bullet2 {N : Type} [DecidableEq N] {O : ReadyOrder}
    (h : TIME_014_bullet2_ready O) (X : TimedNet N) (prio : Trans N → Int) (s : TSt N)
    (ts : List (Trans N)) (hI : ¬ (ReadyIn.ofTSt X prio s ts).FastPath) (i : Nat)
    (hi : i < ts.length) :
    (Elapsed s ts[i] < (TimingOf X ts[i]).earliest → i ∉ O (ReadyIn.ofTSt X prio s ts)) ∧
      (Ready X s ts[i] → i ∈ O (ReadyIn.ofTSt X prio s ts)) := by
  refine ⟨fun he hm => ReadyIn.ofTSt_not_ready_early X prio s ts i hi he
    ((h _ hI).1.mem_iff.1 hm), fun hr => (h _ hI).1.mem_iff.2 ?_⟩
  rw [ReadyIn.mem_readyList]
  exact ⟨hi, (ReadyIn.ofTSt_ready X prio s ts i hi).2 hr⟩

/-! ### The clash input, reached by the timed reference step -/

/-- The `Immediate` transition of the clash: input place `2`, output place `3`. -/
def clash014_a : Trans Nat :=
  { core := { name := "a", inputs := [⟨2, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 3) }

/-- The `Delayed(3)` transition of the clash: input place `0`, output place `4`. -/
def clash014_b : Trans Nat :=
  { core := { name := "b", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 4) }

/-- The `Delayed(5)` transition that enables `a` at reading `5`: input place `1`, output place
`2`. -/
def clash014_g : Trans Nat :=
  { core := { name := "g", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The timings of the clash net by name. -/
def clash014_timing (t : Trans Nat) : Timing :=
  if t.core.name = "b" then .delayed 3 else if t.core.name = "g" then .delayed 5 else .immediate

/-- The clash net: `a`, `b`, `g` in declaration order, tolerance `0`. -/
def clash014_X : TimedNet Nat :=
  { net := { places := [0, 1, 2, 3, 4], transitions := [clash014_a, clash014_b, clash014_g] },
    timing := clash014_timing, tol := 0 }

/-- The initial state at reading `0`: one token in place `0` and one in place `1`, so `b` and
`g` are armed at `0`. -/
def clash014_s0 : TSt Nat := TSt.init clash014_X (fun p => if p = 0 ∨ p = 1 then 1 else 0) 0

/-- The state at reading `5`. -/
def clash014_s5 : TSt Nat := { clash014_s0 with now := 5 }

/-- The marking after `g` fires at reading `5`. -/
def clash014_m' : Nat → Nat := fireNC clash014_s5.m clash014_g.core (depProd [2])

/-- The state after `g` fires at reading `5`: `a` newly armed at `5`, `b` still armed since
`0`. -/
def clash014_s : TSt Nat :=
  { m := clash014_m', now := 5, stamp := restampAll refPolicy clash014_X clash014_s5 clash014_g [2] clash014_m' }

/-- The clash input: the ready order's inputs at `clash014_s` for `a` (index `0`) and `b`
(index `1`), both of priority `0`. -/
def clash014_I : ReadyIn := ReadyIn.ofTSt clash014_X (fun _ => 0) clash014_s [clash014_a, clash014_b]

/-- The clash input is reached by the timed reference step, and it is what the clash needs: two
transitions of equal priority, both ready, `a` `Immediate` and newly armed at `5`, `b`
`Delayed(3)` armed at `0`, on the general path. -/
theorem clash014_reached :
    RefTStep clash014_X clash014_s0 (.delay 5) clash014_s5 ∧
      RefTStep clash014_X clash014_s5 (.fire clash014_g [2]) clash014_s ∧
      ¬ clash014_I.FastPath ∧ clash014_I.readyList = [0, 1] ∧
      clash014_I.prio 0 = clash014_I.prio 1 ∧
      clash014_I.timing 0 = .immediate ∧ clash014_I.timing 1 = .delayed 3 ∧
      clash014_I.clock 0 = 5 ∧ clash014_I.clock 1 = 0 := by
  refine ⟨RefTStepW.delay _ _ 5,
    RefTStepW.fire _ _ _ _ _ (by simp [clash014_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide, rfl, by decide, by decide,
    by decide, by decide⟩

theorem clash014_general : ¬ clash014_I.FastPath := clash014_reached.2.2.1

/-- The ordering reading of TIME-014's second bullet and EXEC-002 cannot both hold: on the
clash input EXEC-002 offers the `Delayed` transition `1`, armed first, before the `Immediate`
transition `0`, and the ordering reading asks for `0` before `1`. A citation of EXEC-002, not of
TIME-014: it shows that EXEC-002's stamp order does not yield to the timing kind on a reachable
input, which is why the ordering reading of the bullet cannot be ruled in without changing
EXEC-002. -/
@[evidence cites "EXEC-002" "stamp order is not overridden by timing kind: on an input reached by the timed reference step, with two ready transitions of equal priority, a Delayed one armed at 0 and an Immediate one armed at 5, every order that satisfies the block offers the Delayed one first, so no such order also satisfies TIME-014 bullet 2 read as an ordering rule (candidate reading, ruling D9 open)"]
theorem TIME_014_bullet2_order_conflicts_EXEC_002 :
    ¬ ∃ O : ReadyOrder, EXEC_002 O ∧ TIME_014_bullet2_order O := by
  rintro ⟨O, h, h'⟩
  have e : O clash014_I = [1, 0] :=
    EXEC_002_forced h clash014_general (by decide) (by decide)
  have := (h' clash014_I clash014_general 0 (by decide) 1 (by decide)).2 rfl (by decide)
    ⟨3, by decide⟩
  rw [e] at this
  exact absurd this (by decide)

/-- The two readings of TIME-014's second bullet disagree on the reference ready order of
EXEC-002: it meets the readiness reading and breaks the ordering reading. Not an evidence tag:
both readings are candidates, not blocks (ruling 5). -/
theorem TIME_014_bullet2_ambiguity :
    TIME_014_bullet2_ready refReadyOrder ∧ ¬ TIME_014_bullet2_order refReadyOrder :=
  ⟨time014_ready_of_EXEC_002 EXEC_002_reference,
    fun h => TIME_014_bullet2_order_conflicts_EXEC_002 ⟨_, EXEC_002_reference, h⟩⟩

/-- On the test derivation of EXEC-002 (priorities 5, 10, 5) the declaration-order scan offers
the priority-5 transition `0` before the priority-10 transition `1`. -/
theorem clash014_scan_breaks_priority :
    ¬ [1, 0].Sublist (exec002_scanOrder exec002_I3) := by decide

/-- The declaration-order scan, which ignores priority, breaks the ordering reading (first
line, AC1's priority preference). -/
theorem TIME_014_bullet2_order_forbids_scan : ¬ TIME_014_bullet2_order exec002_scanOrder :=
  fun h => clash014_scan_breaks_priority
    ((h exec002_I3 exec002_I3_general 1 (by decide) 0 (by decide)).1 (by decide))

/-- The declaration-order scan breaks the readiness reading (second line). -/
theorem TIME_014_bullet2_ready_forbids_scan : ¬ TIME_014_bullet2_ready exec002_scanOrder :=
  fun h => clash014_scan_breaks_priority
    ((h exec002_I3 exec002_I3_general).2 1 (by decide) 0 (by decide) (by decide))

/-- The order that offers every transition of the net, ready or not, by the canonical key. -/
def clash014_allOrder : ReadyOrder := fun I => sortBy I.key.lt (List.range I.n)

/-- An input of the bullet's own case: equal priority, `0` `Immediate` and ready, `1`
`Delayed(3)` and not ready (before its earliest bound). -/
def clash014_Ib : ReadyIn :=
  { n := 2, prio := fun _ => 0, timing := fun t => if t = 0 then .immediate else .delayed 3,
    clock := fun _ => 0, ready := fun t => t == 0 }

theorem clash014_Ib_general : ¬ clash014_Ib.FastPath := by decide

/-- An order that offers a transition that is not ready breaks the readiness reading (first
line): with the `Delayed` transition `1` not ready, it is still offered. -/
theorem TIME_014_bullet2_ready_forbids_notReady : ¬ TIME_014_bullet2_ready clash014_allOrder := by
  intro h
  have h1 : (1 : Nat) ∈ clash014_allOrder clash014_Ib :=
    (sortBy_perm _ _).mem_iff.2 (by decide)
  exact absurd ((h clash014_Ib clash014_Ib_general).1.mem_iff.1 h1) (by decide)

/-- Offers nothing when every ready transition has the same priority, else the reference. -/
def clash014_dropEq : ReadyOrder := fun I =>
  if ∀ a ∈ I.readyList, ∀ b ∈ I.readyList, I.prio a = I.prio b then [] else refReadyOrder I

/-- An order that drops the ready `Immediate` transition in the bullet's own case breaks the
readiness reading (first line): the bullet says it fires. -/
theorem TIME_014_bullet2_ready_forbids_dropEq : ¬ TIME_014_bullet2_ready clash014_dropEq := by
  intro h
  have := (h clash014_Ib clash014_Ib_general).1.mem_iff.2 (by decide : (0 : Nat) ∈ clash014_Ib.readyList)
  revert this
  simp only [clash014_dropEq]
  decide

/-- Every line of both readings has a case on the reference order: on the clash input, reached
by the timed reference step, both transitions are ready, of equal priority, one `Immediate` and
one `Delayed`, on the general path, and the reference offers the `Delayed` one first; on the
test derivation of EXEC-002 the priority-10 transition comes first; in the bullet's own case
the ready `Immediate` transition is offered and the `Delayed` one, not yet ready, is not. -/
theorem TIME_014_bullet2_nonvacuous :
    ¬ clash014_I.FastPath ∧ clash014_I.readyList = [0, 1] ∧ clash014_I.prio 0 = clash014_I.prio 1 ∧
      clash014_I.timing 0 = .immediate ∧ clash014_I.timing 1 = .delayed 3 ∧
      refReadyOrder clash014_I = [1, 0] ∧
      refReadyOrder exec002_I3 = [1, 0, 2] ∧
      refReadyOrder clash014_Ib = [0] :=
  ⟨clash014_general, by decide, rfl, by decide, by decide,
    EXEC_002_forced EXEC_002_reference clash014_general (by decide) (by decide),
    exec002_I3_forced EXEC_002_reference,
    EXEC_002_forced EXEC_002_reference clash014_Ib_general (by decide) (by decide)⟩

/-! ## TIME-013: a firing that rescues an expired transition from its reap -/

/-- The `Deadline(5)` transition of the rescue: one input arc on place `0`. -/
def clash013_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The refresh transition: it takes the token of place `0` and puts one back. -/
def clash013_r : Trans Nat :=
  { core := { name := "r", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The rescue net: `u` is `Deadline(5)`, `r` is `Immediate`, tolerance `0`. -/
def clash013_X : TimedNet Nat :=
  { net := { places := [0], transitions := [clash013_u, clash013_r] },
    timing := fun t => if t.core.name = "u" then .deadline 5 else .immediate, tol := 0 }

/-- The state at reading `6`: one token in place `0`, both transitions armed since `0`. -/
def clash013_s6 : TSt Nat :=
  { TSt.init clash013_X (fun p => if p = 0 then 1 else 0) 0 with now := 6 }

/-- The marking after `r` fires: still one token in place `0`. -/
def clash013_m' : Nat → Nat := fireNC clash013_s6.m clash013_r.core (depProd [0])

/-- The state after `r` fires at reading `6`. -/
def clash013_after : TSt Nat :=
  { m := clash013_m', now := 6,
    stamp := restampAll refPolicy clash013_X clash013_s6 clash013_r [0] clash013_m' }

/-- **Gap, Phase 2 obligation.** On the timed reference step, which meets every TIME block, the
`Deadline(5)` transition `u` is expired at reading `6`, yet the refresh transition `r` may fire
first: it drains `u`'s input place and refills it, so `u` is disabled in the intermediate marking
and enabled after, and its clock restarts at `6` ([TIME-012]). `u` is then armed and no longer
expired, and is never reaped for having passed its bound at `0 + 5`. A cycle reaps `u` in its
deadline step before the firing pass ([EXEC-001] steps 4 and 5), so the Phase 2 cycle relation
must exclude this run; the atomic relation of Phase 1 cannot. -/
theorem clash013_refresh_rescue :
    Expired clash013_X clash013_s6 clash013_u ∧
      RefTStep clash013_X clash013_s6 (.fire clash013_r [0]) clash013_after ∧
      Armed clash013_after clash013_u ∧ clash013_after.stamp "u" = some 6 ∧
      ¬ Expired clash013_X clash013_after clash013_u :=
  ⟨by decide,
    RefTStepW.fire _ _ _ _ _ (by simp [clash013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide),
    by decide, by decide, by decide⟩

/-! ## A reapable window: TIME-015 AC10 and EXEC-040 -/

/-- The transition of the timed examples: one input arc on place `0`, output `Place(1)`. -/
def clashT_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- The timed net of the examples: `u` alone, `Window(3, 5)`, tolerance `0` (strict
enforcement, as a host verifying deadlines under an injected clock sets it, [TIME-015]). -/
def clashT_X : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [clashT_u] },
    timing := fun _ => .window 3 5, tol := 0 }

/-- The initial marking: one token in place `0`. -/
def clashT_m0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The initial state at reading `0`: `u` is enabled and stamped `0` (TSt.init). -/
def clashT_s0 : TSt Nat := TSt.init clashT_X clashT_m0 0

/-- The initial state with the clock at reading `k`. -/
def clashT_at (k : Nat) : TSt Nat := { clashT_s0 with now := k }

/-- The state after `u` is reaped at reading `10`. -/
def clashT_reaped : TSt Nat :=
  { clashT_at 10 with stamp := fun n => if n = "u" then none else (clashT_at 10).stamp n }

/-- The reachable states of the timed reference step from `s`. -/
def TReach (X : TimedNet Nat) (s : TSt Nat) : TSt Nat → Prop :=
  Relation.ReflTransGen (fun a b => ∃ l, RefTStep X a l b) s

/-- Under any policy, a delay of `0` (the clock repeats its reading) leaves the state as it
is. -/
@[evidence cites "TIME-015" "AC10, repeated readings only: on the timed reference step, under any policy, a delay of 0 ms (a clock that returns the same reading on consecutive cycles) leaves the marking, the reading and every stamp unchanged, so repeated readings add only identity steps; clock jumps are not covered (ruling D12 open)"]
theorem refTStepW_delay_zero {N : Type} [DecidableEq N] {P : Policy N} {X : TimedNet N}
    {s s' : TSt N} (h : RefTStepW P X s (.delay 0) s') : s' = s := by
  cases h
  rfl

/-- The only transition of the example net is `u`. -/
theorem clashT_mem {t : Trans Nat} (ht : t ∈ clashT_X.net.transitions) : t = clashT_u := by
  simpa [clashT_X] using ht

/-- Once the clock is at `10` or later with `u` still stamped `0`, or once `u` holds no stamp,
the marking stays the initial one and `u` stays without a stamp or past its window. -/
def clashT_inv (s : TSt Nat) : Prop :=
  s.m = clashT_m0 ∧ (s.stamp "u" = none ∨ (s.stamp "u" = some 0 ∧ 10 ≤ s.now))

theorem clashT_inv_step {s s' : TSt Nat} {l : TLbl Nat} (hs : clashT_inv s)
    (h : RefTStep clashT_X s l s') : clashT_inv s' := by
  obtain ⟨hm, hst⟩ := hs
  match h with
  | .delay _ _ δ =>
    refine ⟨hm, ?_⟩
    rcases hst with e | ⟨e, hn⟩
    · exact .inl e
    · exact .inr ⟨e, by simp; omega⟩
  | .reap _ _ t _ _ =>
    refine ⟨hm, ?_⟩
    by_cases hn : "u" = t.core.name
    · exact .inl (by simp [hn])
    · simpa [hn] using hst
  | .fire _ _ t d m' ht _ ha _ hx =>
    exfalso
    obtain rfl := clashT_mem ht
    rcases hst with e | ⟨e, hn⟩
    · simp [TSt.armed, clashT_u, e] at ha
    · have : tExpired clashT_X s clashT_u = true := by
        simp only [tExpired, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨rfl, ha⟩, ?_⟩
        simp [TSt.elapsed, clashT_X, clashT_u, e, Timing.latest]
        omega
      simp [refPolicy, this] at hx

theorem clashT_inv_reach {s s' : TSt Nat} (hs : clashT_inv s) (h : TReach clashT_X s s') :
    clashT_inv s' := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => obtain ⟨l, hl⟩ := hst; exact clashT_inv_step ih hl

/-- A clock whose increment is wider than a window skips it, while a clock advancing 1 ms per
reading meets it; repeating a reading plays no part. From the initial state, three delays of
1 ms bring `u` into its window `[3, 5]` and it fires, leaving a token in place `1`. One delay of
`0` (a repeated reading) leaves the state as it is, and one delay of `10` (the strictly
increasing readings 0, then 10) brings `u` past `latest + tolerance = 5` without a reading in
the window, and from there no run of the reference step ever marks place `1`. -/
@[evidence cites "TIME-015" "AC10 depends on which strictly increasing clock it is compared against (ruling D12 open): on a Window(3, 5) transition with tolerance 0, the timed reference step fires it under a clock advancing 1 ms per reading, while under the strictly increasing readings 0 then 10, an increment wider than the window (latest - elapsed + tolerance), no reachable state marks the output place; a repeated reading is an identity step (refTStepW_delay_zero) and changes nothing"]
theorem time015_ac10_coarse_jump :
    RefTStep clashT_X clashT_s0 (.delay 1) (clashT_at 1) ∧
      RefTStep clashT_X (clashT_at 1) (.delay 1) (clashT_at 2) ∧
      RefTStep clashT_X (clashT_at 2) (.delay 1) (clashT_at 3) ∧
      (∃ s', RefTStep clashT_X (clashT_at 3) (.fire clashT_u [1]) s' ∧ s'.m 1 = 1) ∧
      RefTStep clashT_X clashT_s0 (.delay 0) clashT_s0 ∧
      RefTStep clashT_X clashT_s0 (.delay 10) (clashT_at 10) ∧
      ∀ s, TReach clashT_X (clashT_at 10) s → s.m 1 = 0 := by
  refine ⟨RefTStepW.delay _ _ 1, RefTStepW.delay _ _ 1, RefTStepW.delay _ _ 1,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [clashT_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide⟩,
    RefTStepW.delay _ _ 0, RefTStepW.delay _ _ 10, fun s hs => ?_⟩
  have := (clashT_inv_reach ⟨rfl, .inr ⟨by decide, le_refl _⟩⟩ hs).1
  rw [this]
  rfl

/-- After the reap, `u` stays without a stamp and the marking stays the initial one. -/
def clashT_invR (s : TSt Nat) : Prop := s.m = clashT_m0 ∧ s.stamp "u" = none

theorem clashT_invR_reach {s s' : TSt Nat} (hs : clashT_invR s) (h : TReach clashT_X s s') :
    clashT_invR s' := by
  induction h with
  | refl => exact hs
  | tail _ hst ih =>
    obtain ⟨l, hl⟩ := hst
    obtain ⟨hm, hn⟩ := clashT_inv_step ⟨ih.1, .inl ih.2⟩ hl
    rcases hn with e | ⟨e, -⟩
    · exact ⟨hm, e⟩
    · exfalso
      obtain ⟨-, h2⟩ := ih
      match hl with
      | .delay _ _ _ => simp [h2] at e
      | .reap _ _ t _ _ =>
        by_cases hu : "u" = t.core.name
        · simp [hu] at e
        · simp [hu, h2] at e
      | .fire _ _ t _ _ ht _ ha _ _ =>
        obtain rfl := clashT_mem ht
        simp [TSt.armed, clashT_u, h2] at ha

/-- A run that rests with a reaped transition enabled: at reading `10` the expired `u` is
reaped, and in every state reachable from there `u` is enabled but not armed, no transition of
the net is armed, and nothing can fire. A stop condition of "no transition enabled" never holds
on this run, so an executor that waits for it never stops; "no transition armed", as EXEC-040
now reads, holds from the reap on. -/
@[evidence cites "EXEC-040" "condition 1 reads 'no transition armed', not 'no transition enabled': on the timed reference step a Window(3, 5) transition reaped at reading 10 stays enabled but not armed in every reachable state, no transition is armed and none can fire, so the literal 'no transition enabled' never holds on a run that rests there, while 'no transition armed' does; atomic Phase 1 step, no in-flight actions or environment places"]
theorem exec040_rest_reaped_enabled :
    RefTStep clashT_X (clashT_at 10) (.reap clashT_u) clashT_reaped ∧
      ∀ s, TReach clashT_X clashT_reaped s →
        Reaped s clashT_u ∧ (∀ t ∈ clashT_X.net.transitions, ¬ Armed s t) ∧
          ∀ t d s', ¬ RefTStep clashT_X s (.fire t d) s' := by
  refine ⟨RefTStepW.reap _ _ _ (by simp [clashT_X]) (by decide), fun s hs => ?_⟩
  obtain ⟨hm, hn⟩ := clashT_invR_reach ⟨rfl, by decide⟩ hs
  have hna : ∀ t ∈ clashT_X.net.transitions, ¬ Armed s t := by
    intro t ht
    obtain rfl := clashT_mem ht
    intro ha
    have := ha.2
    simp [clashT_u, hn] at this
  refine ⟨⟨by rw [hm]; decide, hna clashT_u (by simp [clashT_X])⟩, hna, fun t d s' h => ?_⟩
  obtain ⟨ht, -, ha, -⟩ := refTStep_fire_inv h
  exact hna t ht ha.1

end Libpetri.Spec
