import Libpetri.Novel.RouteB.Exec

/-!
# Route B simulates the untimed, environment-free executor ([NU-050], [VER-012] AC1)

`NuStepC` is one executor firing seen through the analysis's eyes: the count effect of a
`ForwardDeposit.StepCR` step for the fired branch outcome, drained forwards resolved at the
count the firing drained (`Row.resolve`, [IO-014]), together with the name effect `ExecNames`
of `Exec.lean`, restricted to contract-abiding actions (`Contract`) and, under
`PrioritySemantics::Conflict`, to firings the [NU-052] prune does not call dominated (the eager,
priority-ordered executor never produces those; `Priority.lean` is the untimed argument). It has
no time and no environment injection.

* **`name_step_simulates_exec`**: from a class `S` with the key of the executor marking's view,
  every executor ν step is a labelled successor of `S`, landing on the key of the executor's next
  view. The class and the executor marking need only share a key: the successor is found in the
  view's own expansion (`exec_names_step`) and moved to `S` by `routeB_equivariant`.
* `exec_reach_simulated`: induction — every executor-reachable marking's view key is reached by
  the plain exploration (`Explorer.Reach`), so by `routeB_interned_keys_eq` by the interned one.
* `nu_reach_reachAN`, `routeB_base_reachAN`: on counts an executor ν run is a run of resolved
  branch outcomes (`StepAN`, the transfer rows of `TransferRows.lean`), and every Route B class
  projects to a count marking reachable that way: the name layer only removes behaviour from the
  plain untimed graph. `nu_reach_reachAD`, `routeB_base_reachAD`: on a net with no drained
  forward, the same over the fixed rows `Enumeration.succRows` explores ([VER-017]).
* `exec_quiescent_succ_nil`: a class with the key of a quiescent executor marking (no transition
  base-enabled with, for a join, a selectable name) has no successor. `exec_rests_succ_reap` is
  the [TIME-013] reading: a class with the key of a marking where the executor can fire only
  reapable transitions (`ExecRests`) has only reapable successors. It needs one premise more
  than the step: every join key consumes at least one token (`PosKeys`;
  `Classify.zeroKey_breaks_quiescence`; `TransitionBuilder::build` now enforces it,
  `Classify.builderOK_posKeys`), which also makes the order of `coloured_in` irrelevant
  (`Classify.joinEnab_perm_of_pos`). The converse is not claimed and fails in general: a
  consumer fires in the graph on any resident symbol, the executor on the FIFO head only, so the
  graph over-approximates.

Premises beyond `InFragment` and the contracts: `coloured_order` is duplicate-free (it is a
`BTreeSet`), every input arc is unguarded (guards were removed in [IO-006]), the one total name
projection (`ProjCoherent`, built into `NuStepC`), and, for the initial class, the coloured
places start empty (`verify_via_name_scg` returns `None` otherwise).
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.TransferRows (consumedA consumedAt_eq_consumedA)

section Sim

variable (co : List PlaceId) (nameOf : Colour → ℕ) (net : List NuTrans) (role : NuTrans → Role)
  (conflict : Bool)

/-- **One untimed, environment-free executor ν step**: some transition of the net fires on some
branch outcome `r`, depositing its resolved deposit (every drained forward at the count the
firing actually drained, `consumedAt`, [IO-014]); the count marking moves as `StepCR` says, the
names as `ExecNames` says under the role's contract, and the firing is not one the [NU-052]
prune removes (the executor's priority order). Names are read through the one total `nameOf`
(the `ProjCoherent` premise of `Exec.lean`). -/
def NuStepC (m m' : CMarking) : Prop :=
  ∃ T ∈ net, ∃ r ∈ T.rows,
    enabledC m T.base = true ∧
    alpha m' = alphaFireC m T.base (fun p => (r.resolve (consumedAt m T.base)).count p) ∧
    ExecNames co T (r.resolve (consumedAt m T.base)) (nameLayer co nameOf m)
      (nameLayer co nameOf m') (Contract co (role T) T (nameLayer co nameOf m)) ∧
    (conflict = true → dominated untimedBase net role (view co nameOf m) T = false)

/-- No input arc carries a guard ([IO-006] removed them). -/
def GuardFree (t : Transition) : Prop := ∀ s ∈ t.inputs, s.guard = none

/-- The initial class: the initial count marking, an empty name layer. -/
def initState (a0 : AMarking) : NState co AMarking :=
  ⟨a0, fun _ _ => 0, 0, fun _ _ _ => rfl⟩

variable {co nameOf net role conflict}

theorem guardFree_consumeAll {t : Transition} (h : GuardFree t) : GuardFreeConsumeAll t :=
  fun s hs _ => h s hs

theorem init_key {m0 : CMarking} (hempty : ∀ i : Fin co.length, m0 co[i.1] = []) :
    keyOf (initState co (alpha m0)) = keyOf (view co nameOf m0) := by
  have : nameLayer co nameOf m0 = fun _ _ => 0 := by
    funext n i
    simp [nameLayer, hempty i]
  simp only [keyOf, initState, view, this]

theorem succKeyed_perm {S S' : NState co AMarking} (h : keyOf S = keyOf S') :
    (succKeyed untimedBase net role conflict S.bound S).Perm
      (succKeyed untimedBase net role conflict S'.bound S') := by
  rw [← succ_keyed, ← succ_keyed]
  exact (routeB_equivariant (co := co) (base := untimedBase) (net := net) (role := role)
    (conflict := conflict)).key_succ S S' S.bound S'.bound h le_rfl le_rfl

/-- **Every executor ν step is an edge of the name graph.** -/
theorem name_step_simulates_exec (hco : co.Nodup) (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {S : NState co AMarking} {m m' : CMarking}
    (hS : keyOf S = keyOf (view co nameOf m)) (h : NuStepC co nameOf net role conflict m m') :
    ∃ l S', (l, S') ∈ succ untimedBase net role conflict S.bound S ∧
      keyOf S' = keyOf (view co nameOf m') := by
  obtain ⟨T, hT, d, hd, hen, heff, hnames, hprio⟩ := h
  have hk : consumedAt m T.base = consumedA (alpha m) T.base :=
    funext (consumedAt_eq_consumedA (guardFree_consumeAll (hG T hT)))
  rw [hk] at heff hnames
  obtain ⟨henA, hfire⟩ := prop1_step_deposit m T.base (d.resolve (consumedA (alpha m) T.base))
    (guardFree_consumeAll (hG T hT)) hen
  obtain ⟨M'', hM'', hkey⟩ :=
    exec_names_step hco (hfr T hT) hd hnames (view co nameOf m).supp (le_refl _)
  have hmem : (T.base.name, keyOf (view co nameOf m')) ∈
      succKeyed untimedBase net role conflict (view co nameOf m).bound (view co nameOf m) := by
    unfold succKeyed
    rw [List.mem_flatMap]
    refine ⟨T, List.mem_filter.mpr ⟨hT, henA⟩, ?_⟩
    have hnd : (conflict && dominated untimedBase net role (view co nameOf m) T) = false := by
      cases conflict
      · rfl
      · simp [hprio rfl]
    rw [if_neg (by simp [hnd])]
    rw [List.mem_flatMap]
    refine ⟨d, hd, ?_⟩
    show (T.base.name, keyOf (view co nameOf m')) ∈
      ((nameSuccs co (role T) (nameLayer co nameOf m) d.places (nameBound co nameOf m)
        (nameBound co nameOf m)).map canonicalKey).map
        fun k => (T.base.name, (fireAD (alpha m) T.base (d.resolve (consumedA (alpha m) T.base)), k))
    rw [List.mem_map]
    refine ⟨canonicalKey M'', List.mem_map_of_mem hM'', ?_⟩
    simp only [keyOf, view, hkey, heff, hfire]
  have hmem' := (succKeyed_perm hS.symm).mem_iff.mp hmem
  rw [← succ_keyed] at hmem'
  obtain ⟨⟨l, S'⟩, hin, hk⟩ := List.mem_map.mp hmem'
  refine ⟨l, S', hin, ?_⟩
  exact (Prod.mk.inj hk).2

/-- **Every executor-reachable marking is reached by Route B**, up to key. -/
theorem exec_reach_simulated (hco : co.Nodup) (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {S0 : NState co AMarking} {m0 m : CMarking}
    (h0 : keyOf S0 = keyOf (view co nameOf m0))
    (h : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    ∃ S, Explorer.Reach (routeB untimedBase net role conflict) S0 S ∧
      keyOf S = keyOf (view co nameOf m) := by
  induction h with
  | refl => exact ⟨S0, Explorer.Reach.init, h0⟩
  | tail _ hs ih =>
    obtain ⟨S, hR, hk⟩ := ih
    obtain ⟨l, S', hmem, hk'⟩ := name_step_simulates_exec hco hfr hG hk hs
    exact ⟨S', Explorer.Reach.step (E := routeB untimedBase net role conflict) hR le_rfl hmem, hk'⟩

/-! ## Quiescence -/

/-- The executor can fire `T`: base-enabled and, for a join, a name `select_match_name` takes. -/
def ExecEnabled (T : NuTrans) (m : CMarking) : Prop :=
  enabledC m T.base = true ∧
    ∀ ks, T.keys = some ks → ∃ n, Selectable co T (nameLayer co nameOf m) n

/-- The executor is quiescent: no transition can fire. -/
def ExecQuiescent (m : CMarking) : Prop := ∀ T ∈ net, ¬ ExecEnabled (co := co) (nameOf := nameOf) T m

/-- The executor rests ([TIME-013]): every transition it can fire is reapable (`reap`, by
transition name), so a late executor reaps them all and stops with the marking unchanged. With
nothing reapable this is `ExecQuiescent` (`execRests_noReap`). -/
def ExecRests (reap : String → Bool) (m : CMarking) : Prop :=
  ∀ T ∈ net, ExecEnabled (co := co) (nameOf := nameOf) T m → reap T.base.name = true

theorem execRests_noReap {m : CMarking} :
    ExecRests (co := co) (nameOf := nameOf) (net := net) (fun _ => false) m ↔
      ExecQuiescent (co := co) (nameOf := nameOf) (net := net) m := by
  constructor
  · intro h T hT hen
    exact absurd (h T hT hen) (by simp)
  · intro h T hT hen
    exact absurd hen (h T hT)

theorem matchCount_of_guard {m : CMarking} {s : InSpec} (h : s.guard = none) :
    matchCount m s = (m s.place).length := by
  unfold matchCount; rw [h]

theorem enabledC_of_enabledA {m : CMarking} {t : Transition} (hg : GuardFree t)
    (h : enabledA (alpha m) t = true) : enabledC m t = true := by
  unfold enabledA at h
  unfold enabledC
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hIn, hInh⟩, hRd⟩ := h
  exact ⟨⟨fun s hs => by rw [matchCount_of_guard (hg s hs)]; exact hIn s hs, hInh⟩, hRd⟩

theorem liveSet_finite_view (m : CMarking) : (liveSet (nameLayer co nameOf m)).Finite :=
  liveSet_finite (nameLayer_supp co nameOf m)

/-- **Every join key consumes at least one token.** `classify` admits a key whose first input
spec is `In::Exactly { count: 0 }` (the enum variant is public); `TransitionBuilder::build` now
panics on an input that requires zero tokens ([IO-002], [IO-004]), so every buildable join meets
it (`Classify.builderOK_posKeys`). `enabling_symbols` seeds its candidates from the head of
`coloured_in` (name-sorted in the Rust) and asks every other key place only for
`count ≥ required`, so a zero-count key that is not the head is asked for a count `≥ 0`, while
`select_match_name` still needs the name present there. The premise is needed only for
quiescence (`zeroKey_breaks_quiescence` in `Classify.lean`). It is stronger than needed (a
zero-count head key is still asked for presence), and under it the order of `coloured_in` does
not matter (`joinEnab_perm_of_pos`). -/
def PosKeys (r : Role) : Prop := ∀ cin rel, r = .join cin rel → ∀ pr ∈ cin, 1 ≤ pr.2

/-- **A successor of the graph is a transition the executor can fire.** -/
theorem exec_enabled_of_succ (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {S : NState co AMarking} {m : CMarking}
    (hS : keyOf S = keyOf (view co nameOf m)) {c : ℕ} {l : String} {S' : NState co AMarking}
    (h : (l, S') ∈ succ untimedBase net role conflict c S) :
    ∃ T ∈ net, T.base.name = l ∧ ExecEnabled (co := co) (nameOf := nameOf) T m := by
  have hk : (l, keyOf S') ∈ succKeyed untimedBase net role conflict c S := by
    rw [← succ_keyed]
    exact List.mem_map_of_mem (f := (routeB untimedBase net role conflict).keyed) h
  unfold succKeyed at hk
  obtain ⟨T, hTf, hTin⟩ := List.mem_flatMap.mp hk
  obtain ⟨hT, henA⟩ := List.mem_filter.mp hTf
  have hl : T.base.name = l := by
    split at hTin
    · exact absurd hTin List.not_mem_nil
    obtain ⟨d, -, hd⟩ := List.mem_flatMap.mp hTin
    split at hd
    · exact absurd hd List.not_mem_nil
    obtain ⟨k, -, he⟩ := List.mem_map.mp hd
    exact (Prod.mk.inj he).1
  simp only [keyOf, Prod.mk.injEq] at hS
  obtain ⟨hb, hm⟩ := hS
  refine ⟨T, hT, hl, ?_, ?_⟩
  · have h1 : enabledA S.b T.base = true := henA
    rw [hb] at h1
    exact enabledC_of_enabledA (hG T hT) h1
  · intro ks hks
    split at hTin
    · exact absurd hTin List.not_mem_nil
    obtain ⟨d, -, hd⟩ := List.mem_flatMap.mp hTin
    have hfrT := hfr T hT
    have hposT := hpos T hT
    generalize hr : role T = r at hd hfrT hposT
    cases r with
    | ordinary => rw [hfrT.2.1] at hks; cases hks
    | mint => rw [hfrT.2.1] at hks; cases hks
    | consume inp => rw [hfrT.2.1] at hks; cases hks
    | join cin rel =>
      obtain ⟨-, ks', hks', hmemks, -, hcin, -⟩ := hfrT
      rw [hks] at hks'
      cases hks'
      -- a name successor exists, so an enabling symbol does
      change (l, keyOf S') ∈ ((nameSuccs co (Role.join cin rel) S.m d.places S.bound c).map
        canonicalKey).map fun k => (T.base.name, (fireAD S.b T.base
          (d.resolve (consumedA S.b T.base)), k)) at hd
      obtain ⟨k, hk', -⟩ := List.mem_map.mp hd
      obtain ⟨M', hM', -⟩ := List.mem_map.mp hk'
      obtain ⟨s, hs, -⟩ := List.mem_map.mp hM'
      have hen := (mem_dsig_range hs).2
      obtain ⟨σ, hσ⟩ := canonicalKey_complete (liveSet_finite S.supp) (liveSet_finite_view m) hm
      cases cin with
      | nil => simp [joinEnab] at hen
      | cons pr0 rest =>
        refine ⟨σ.symm s, fun ks'' hks'' => ?_⟩
        rw [hks] at hks''
        cases hks''
        refine ⟨fun he => ?_, fun p hp => ?_⟩
        · have := (hmemks pr0.1).mpr (by simp)
          rw [he] at this
          exact absurd this List.not_mem_nil
        obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ((hmemks p).mp hp)
        obtain ⟨-, s0, hfs, hfc⟩ := hcin pr hpr
        rw [keyReq_of T hfs hfc, hσ, cnt_comp]
        simp only [Equiv.apply_symm_apply]
        simp only [joinEnab, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
        have h2 := hen.2 pr hpr
        exact ⟨Nat.le_trans (hposT _ _ rfl pr hpr) h2, h2⟩

/-- **Quiescence the executor reaches is quiescence the graph sees**: a class with the key of a
quiescent executor marking has no successor. Needs `PosKeys` on top of the fragment. -/
theorem exec_quiescent_succ_nil (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {S : NState co AMarking} {m : CMarking}
    (hS : keyOf S = keyOf (view co nameOf m))
    (hq : ExecQuiescent (co := co) (nameOf := nameOf) (net := net) m) (c : ℕ) :
    succ untimedBase net role conflict c S = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  rintro ⟨l, S'⟩ h
  obtain ⟨T, hT, -, hen⟩ := exec_enabled_of_succ hfr hpos hG hS h
  exact hq T hT hen

/-- **A resting executor marking is a resting class** ([TIME-013], [VER-002]): every successor of
a class with the key of a marking where the executor can fire only reapable transitions is a
firing of a reapable transition, the reading `is_quiescent` gives `fires_unreapable`. With
nothing reapable this is `exec_quiescent_succ_nil`. Needs `PosKeys` on top of the fragment. -/
theorem exec_rests_succ_reap (hfr : ∀ T ∈ net, InFragment co T (role T))
    (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {reap : String → Bool} {S : NState co AMarking}
    {m : CMarking} (hS : keyOf S = keyOf (view co nameOf m))
    (hr : ExecRests (co := co) (nameOf := nameOf) (net := net) reap m) (c : ℕ) :
    ∀ ly ∈ succ untimedBase net role conflict c S, reap ly.1 = true := by
  rintro ⟨l, S'⟩ h
  obtain ⟨T, hT, hl, hen⟩ := exec_enabled_of_succ hfr hpos hG hS h
  rw [← hl]
  exact hr T hT hen

/-! ## A successor's base comes from `fire` -/

theorem mem_succ_base {β : Type} {co : List PlaceId} {base : BaseLayer β} {net : List NuTrans}
    {role : NuTrans → Role} {conflict : Bool} {c : ℕ} {S : NState co β} {l : String}
    {s : NState co β} (h : (l, s) ∈ succ base net role conflict c S) :
    ∃ T ∈ net, base.enabled S.b T.base = true ∧ ∃ d ∈ T.rows, base.fire S.b T.base d = some s.b := by
  unfold succ at h
  obtain ⟨T, hTf, hT⟩ := List.mem_flatMap.mp h
  obtain ⟨hTn, hen⟩ := List.mem_filter.mp hTf
  refine ⟨T, hTn, hen, ?_⟩
  split at hT
  · exact absurd hT List.not_mem_nil
  obtain ⟨d, hd, hmem⟩ := List.mem_flatMap.mp hT
  refine ⟨d, hd, ?_⟩
  split at hmem
  · exact absurd hmem List.not_mem_nil
  · rename_i b' hf
    obtain ⟨M', -, he⟩ := List.mem_map.mp hmem
    rw [← (Prod.mk.inj he).2]
    exact hf

/-! ## The count layer: `ForwardDeposit`, `TransferRows` and the enumeration of [VER-017] -/

/-- One abstract step of a ν-net's branch outcomes, every drained forward resolved at the
marking fired in: the count successor `compute_successor` takes, the transfer rows of
`TransferRows.lean`. -/
def StepAN (net : List NuTrans) (a a' : AMarking) : Prop :=
  ∃ T ∈ net, ∃ r ∈ T.rows, enabledA a T.base = true ∧
    a' = fireAD a T.base (r.resolve (consumedA a T.base))

/-- The fixed deposit rows of a ν-net: one per transition and branch outcome, as
`ForwardDeposit.flatRows` / `Enumeration.succRows` read them. They are the whole outcome only
on a net with no drained forward (`stepAN_stepAD`). -/
def nuRows (net : List NuTrans) : List (Transition × Deposit) :=
  net.flatMap fun T => T.rows.map fun r => (T.base, r.fixed)

theorem mem_nuRows {net : List NuTrans} {T : NuTrans} (hT : T ∈ net) {r : Row}
    (hd : r ∈ T.rows) : (T.base, r.fixed) ∈ nuRows net :=
  List.mem_flatMap.mpr ⟨T, hT, List.mem_map.mpr ⟨r, hd, rfl⟩⟩

/-- On a net with no drained forward the resolved step is a step of the fixed rows. -/
theorem stepAN_stepAD {net : List NuTrans} (hfix : ∀ T ∈ net, ∀ r ∈ T.rows, r.drains = [])
    {a a' : AMarking} (h : StepAN net a a') : StepAD (nuRows net) a a' := by
  obtain ⟨T, hT, r, hr, hen, rfl⟩ := h
  refine ⟨(T.base, r.fixed), mem_nuRows hT hr, hen, ?_⟩
  simp [Row.resolve, hfix T hT r hr]

/-- An executor ν step is, on counts, a resolved step of the net's branch outcomes. -/
theorem nuStepC_stepAN (hG : ∀ T ∈ net, GuardFree T.base) {m m' : CMarking}
    (h : NuStepC co nameOf net role conflict m m') : StepAN net (alpha m) (alpha m') := by
  obtain ⟨T, hT, r, hr, hen, heff, -, -⟩ := h
  have hk : consumedAt m T.base = consumedA (alpha m) T.base :=
    funext (consumedAt_eq_consumedA (guardFree_consumeAll (hG T hT)))
  obtain ⟨henA, hfire⟩ := prop1_step_deposit m T.base (r.resolve (consumedA (alpha m) T.base))
    (guardFree_consumeAll (hG T hT)) hen
  exact ⟨T, hT, r, hr, henA, by rw [heff, hk, hfire]⟩

/-- **Proposition 1 for ν runs**, drained forwards included: the count marking of every
executor-reachable marking is reachable by resolved steps of the branch outcomes. -/
theorem nu_reach_reachAN (hG : ∀ T ∈ net, GuardFree T.base) {m0 m : CMarking}
    (h : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    Relation.ReflTransGen (StepAN net) (alpha m0) (alpha m) :=
  Relation.ReflTransGen.lift alpha (fun _ _ hs => nuStepC_stepAN hG hs) m0 m h

/-- On a net with no drained forward, the same over the fixed rows: `ReachAD`, the abstraction
the flat CHC route and the enumeration read. -/
theorem nu_reach_reachAD (hG : ∀ T ∈ net, GuardFree T.base)
    (hfix : ∀ T ∈ net, ∀ r ∈ T.rows, r.drains = []) {m0 m : CMarking}
    (h : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    ReachAD (nuRows net) (alpha m0) (alpha m) :=
  Relation.ReflTransGen.lift id (fun _ _ hs => stepAN_stepAD hfix hs) _ _ (nu_reach_reachAN hG h)

/-- **Route B's base layer refines the resolved rows**: the count marking of every successor is
a resolved step of an enabled branch outcome. -/
theorem routeB_base_stepAN {c : ℕ} {S : NState co AMarking} {l : String} {s : NState co AMarking}
    (h : (l, s) ∈ succ untimedBase net role conflict c S) : StepAN net S.b s.b := by
  obtain ⟨T, hT, hen, d, hd, hf⟩ := mem_succ_base h
  exact ⟨T, hT, d, hd, hen, (Option.some.inj hf).symm⟩

/-- Every Route B class projects to a count marking reachable by resolved steps: the name layer
only removes behaviour from the plain untimed graph, never adds it. -/
theorem routeB_base_reachAN {S0 S : NState co AMarking}
    (h : Explorer.Reach (routeB untimedBase net role conflict) S0 S) :
    Relation.ReflTransGen (StepAN net) S0.b S.b := by
  induction h with
  | init => exact Relation.ReflTransGen.refl
  | step _ _ hmem ih => exact Relation.ReflTransGen.tail ih (routeB_base_stepAN hmem)

/-- On a net with no drained forward: `ReachAD` over the fixed rows ([VER-017]'s `succRows`). -/
theorem routeB_base_reachAD (hfix : ∀ T ∈ net, ∀ r ∈ T.rows, r.drains = [])
    {S0 S : NState co AMarking}
    (h : Explorer.Reach (routeB untimedBase net role conflict) S0 S) :
    ReachAD (nuRows net) S0.b S.b :=
  Relation.ReflTransGen.lift id (fun _ _ hs => stepAN_stepAD hfix hs) _ _ (routeB_base_reachAN h)

end Sim

end Libpetri.Novel.RouteB
