import Libpetri.Novel.RouteB.Graph
import Libpetri.Novel.TransferRows

/-!
# Route B against the executor: every executor ν step is an edge of the name graph

The untimed instance of the Route B step (`untimedBase`: the class base is the count marking,
enabled by `enabledA`, fired by `ForwardDeposit.fireAD` over the branch outcome with every
drained forward resolved at the marking fired in, every transition ready at once) and a model
of what one executor firing does to the **names** in the coloured places, stated per input spec
from the runtime rules:

* a match key consumes `required` tokens of the **matched** name ([NU-020], `consume_for_firing`
  with the `key_for` predicate; `All` / `AtLeast` keys take every token of that name), the name
  being one that `select_match_name` accepts: at least one key, and the name present, at the
  required count and at least once, in every key place (`Selectable`, `find_match_binding`);
* any other input takes tokens **FIFO**, whatever their names ([EXEC-010]): the names are
  unconstrained beyond their number (`SpecTakes`);
* a reset empties its place;
* the action writes the resolved deposit of the branch outcome (`Row.resolve`: fixed counts plus
  one token per drained token, [IO-014]) and a relay target of a join receives only the matched
  name ([NU-054] AC, checked at run time by output validation). A firing that fails that check
  deposits nothing and is not a step here. The shipped `classify` keeps it from being forced by
  the net: a join's coloured timeout write must forward one of its match keys
  (`Classify.classifyS_join`), since a unit token or another input's name always fails it.

Premises the runtime does not check:
* **Mint** ([NU-010], `Contract`): a transition classified `Mint` writes one freshly minted name
  into every coloured output. The shipped `classify` reads a writer as a mint only when the net
  declares it (`mints`) and it writes no coloured place on timeout (`Classify.classifyS_mint`);
  what the declared action writes is still not checked, and `Classify.lean`
  (`copyingMint_breaks_simulation`) shows the premise is load-bearing.
* **Consume** ([NU-051] precondition, documented only; `Contract`): a consumer writes into its
  coloured outputs only a name it consumed from a coloured input. Its timeout writes are checked:
  each coloured one must forward the consumed input (`Classify.classifyS_consume`).
* **One total name projection** (`ProjCoherent`, UNCHECKED; [NU-050] now states it as a contract
  on the net). The executor's names are read
  through a single `nameOf : Colour → ℕ` (`nameLayer`, and so `Selectable`, `SpecTakes`, the
  relay clause of `ExecNames` and the contracts). The runtime has one partial `KeyFn` per match
  key and per relay target (`MatchKey::extract` returns `Option<NameId>`), and
  `find_match_binding` indexes each key place with its own projection, skipping `None`. So the
  model describes the executor only when every key and relay projection that reads a coloured
  place agrees with `nameOf` there (across joins, and between a relay and the downstream key
  that reads the same place) and none returns `None`. This premise is built into the types, not
  stated as a hypothesis; `keyIndex_eq_nameLayer` is what it buys.

`InFragment` is what `classify` (`name_fragment.rs`) establishes for the role it assigns:
`Classify.classifyT_inFragment` proves it from `classifyT = some r`, given two join conditions
`classify` does not check: a join's keys are distinct places, and each key place carries at most
one input spec (`classify` reads only the first, `.find`). Both hold of every built transition:
`TransitionBuilder::build` panics on a place keyed twice ([NU-020]) and on two input arcs on one
place ([CORE-030] AC3) (`Classify.BuilderOK`).

Results:
* `exec_names_step`: under `InFragment` and the contracts, the executor's name successor has the
  key of one of `name_successors`' outputs (the orbit dedup keeps every signature).
* **`name_step_simulates_exec`** (`Sim.lean`): an untimed, environment-free executor ν step
  (`NuStepC`) from a marking whose view has the key of a class `S` is matched by a labelled
  successor of `S` with the key of the executor's successor view.
* `exec_reach_simulated`, `exec_quiescent_succ_nil` (`Sim.lean`).

Out of scope here: time (the timed base is abstract in `Graph.lean`; this file is the untimed
instance), environment places (`Retrodict.lean` covers the two VER-006 fixes), and the token
order the executor picks among names beyond what the analysis reads.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.TransferRows (consumedA)

section Untimed

/-- `consumed_demand`: tokens `t` consumes from `p` on one firing, summed over its specs. -/
def demandOn (t : Transition) (p : PlaceId) : ℕ :=
  ((t.inputs.filter fun s => s.place == p).map fun s => s.card.required).sum

/-- `shares_consumed_input`: a shared consumed place that cannot satisfy both demands. -/
def sharesConsumed (a : AMarking) (H L : Transition) : Bool :=
  H.inputs.any fun sh =>
    L.inputs.any (fun sl => sl.place == sh.place)
      && decide (a sh.place < demandOn H sh.place + demandOn L sh.place)

/-- The untimed base layer: count markings, `enabledA`, `fireAD` over the branch outcome with
every drained forward resolved at the marking fired in (`produce_marking`: the count
`input_consume_count(spec, marking.count(from))`, `TransferRows.consumedA`), every transition
ready at once (all `ready_earliest` are `0`), and nothing in flight: the executor here fires
atomically, and the net has no `inflight:` place, so the in-flight guard never applies. -/
def untimedBase : BaseLayer AMarking where
  enabled := enabledA
  fire a t r := some (fireAD a t (r.resolve (consumedA a t)))
  readyLe _ _ _ := true
  compete := sharesConsumed
  idle _ _ := true

end Untimed

section Pointwise

variable {co : List PlaceId}

theorem get_inj (hco : co.Nodup) {i j : Fin co.length} : co[i.1] = co[j.1] ↔ i = j := by
  rw [Fin.ext_iff]; exact hco.getElem_inj_iff

theorem idx_get (hco : co.Nodup) (i : Fin co.length) : idx co co[i.1] = some i := by
  unfold idx
  cases h : (List.finRange co.length).find? (fun j => co[j.1] == co[i.1]) with
  | none => exact absurd (List.find?_eq_none.mp h i (List.mem_finRange i)) (by simp)
  | some j =>
    have := List.find?_some h
    simp only [beq_iff_eq] at this
    exact congrArg some ((get_inj hco).mp this)

theorem get_of_idx {p : PlaceId} {i : Fin co.length} (h : idx co p = some i) : co[i.1] = p := by
  unfold idx at h
  have := List.find?_some h
  simpa using this

theorem idx_none {p : PlaceId} (h : idx co p = none) (i : Fin co.length) : co[i.1] ≠ p := by
  intro e
  unfold idx at h
  exact (List.find?_eq_none.mp h i (List.mem_finRange i)) (by simpa using e)

theorem get_coloured (hco : co.Nodup) (i : Fin co.length) : (idx co co[i.1]).isSome = true := by
  rw [idx_get hco]; rfl

theorem cnt_get (hco : co.Nodup) (M : NM co) (s : ℕ) (i : Fin co.length) :
    cnt co M s co[i.1] = M s i := by
  unfold cnt; rw [idx_get hco]

theorem addAt_apply (hco : co.Nodup) (p : PlaceId) (s c : ℕ) (M : NM co) (u : ℕ)
    (i : Fin co.length) :
    addAt co p s c M u i = M u i + if u = s ∧ co[i.1] = p then c else 0 := by
  unfold addAt
  cases h : idx co p with
  | none =>
    have := idx_none h i
    simp [this]
  | some j =>
    have hj := get_of_idx h
    have hij : co[i.1] = p ↔ i = j := by rw [← hj]; exact get_inj hco
    by_cases hu : u = s <;> by_cases hi : i = j
    · subst hi; simp [hu, hj]
    · simp [hu, hi, hij.not.mpr hi]
    · simp [hu]
    · simp [hu]

theorem removeAt_apply (hco : co.Nodup) (p : PlaceId) (s c : ℕ) (M : NM co)
    (hc : c ≤ cnt co M s p) (u : ℕ) (i : Fin co.length) :
    removeAt co p s c M u i = M u i - if u = s ∧ co[i.1] = p then c else 0 := by
  unfold removeAt
  cases h : idx co p with
  | none =>
    have := idx_none h i
    simp [this]
  | some j =>
    have hj := get_of_idx h
    have hij : co[i.1] = p ↔ i = j := by rw [← hj]; exact get_inj hco
    have hc' : c ≤ M s j := by unfold cnt at hc; rw [h] at hc; exact hc
    simp only [if_pos hc']
    by_cases hu : u = s <;> by_cases hi : i = j
    · subst hi; simp [hu, hj]
    · simp [hu, hi, hij.not.mpr hi]
    · simp [hu]
    · simp [hu]

theorem foldl_add_apply (hco : co.Nodup) (s : ℕ) :
    ∀ (L : List PlaceId), L.Nodup → ∀ (M : NM co) (u : ℕ) (i : Fin co.length),
      (L.foldl (fun M p => addAt co p s 1 M) M) u i =
        M u i + if u = s ∧ co[i.1] ∈ L then 1 else 0
  | [], _, M, u, i => by simp
  | p :: L, hL, M, u, i => by
    rw [List.nodup_cons] at hL
    simp only [List.foldl_cons]
    rw [foldl_add_apply hco s L hL.2, addAt_apply hco]
    by_cases hu : u = s
    · by_cases hp : co[i.1] = p
      · simp [hu, hp, hL.1]
      · by_cases hL' : co[i.1] ∈ L <;> simp [hu, hp, hL']
    · simp [hu]

/-- The total a join's `coloured_in` removes at coloured place `i`. -/
def subAt (co : List PlaceId) (cin : List (PlaceId × ℕ)) (i : Fin co.length) : ℕ :=
  ((cin.filter fun pr => pr.1 == co[i.1]).map Prod.snd).sum

theorem cnt_removeAt_ne (hco : co.Nodup) {p q : PlaceId} (hpq : q ≠ p) {s c : ℕ} {M : NM co}
    (hc : c ≤ cnt co M s p) (u : ℕ) : cnt co (removeAt co p s c M) u q = cnt co M u q := by
  unfold cnt
  cases h : idx co q with
  | none => rfl
  | some j =>
    simp only
    rw [removeAt_apply hco p s c M hc u j, get_of_idx h]
    simp [hpq]

theorem foldl_remove_apply (hco : co.Nodup) (s : ℕ) :
    ∀ (cin : List (PlaceId × ℕ)), (cin.map Prod.fst).Nodup → ∀ (M : NM co),
      (∀ pr ∈ cin, pr.2 ≤ cnt co M s pr.1) → ∀ (u : ℕ) (i : Fin co.length),
      (cin.foldl (fun M pr => removeAt co pr.1 s pr.2 M) M) u i =
        M u i - if u = s then subAt co cin i else 0
  | [], _, M, _, u, i => by simp [subAt]
  | (p, r) :: rest, hn, M, hle, u, i => by
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.foldl_cons]
    have hr : r ≤ cnt co M s p := hle (p, r) List.mem_cons_self
    have hle' : ∀ pr ∈ rest, pr.2 ≤ cnt co (removeAt co p s r M) s pr.1 := by
      intro pr hpr
      have hne : pr.1 ≠ p := fun e => hn.1 (by simpa [e] using List.mem_map_of_mem (f := Prod.fst) hpr)
      rw [cnt_removeAt_ne hco hne hr]
      exact hle pr (List.mem_cons_of_mem _ hpr)
    rw [foldl_remove_apply hco s rest hn.2 _ hle', removeAt_apply hco p s r M hr]
    have hsub : subAt co ((p, r) :: rest) i = (if co[i.1] = p then r else 0) + subAt co rest i := by
      unfold subAt
      by_cases hp : co[i.1] = p
      · simp [hp]
      · have : ¬ p = co[i.1] := Ne.symm hp
        simp [hp, this]
    rw [hsub]
    by_cases hu : u = s
    · by_cases hp : co[i.1] = p <;> simp [hu, hp, Nat.sub_sub]
    · simp [hu]

end Pointwise

section Executor

variable (co : List PlaceId) (nameOf : Colour → ℕ)

/-- The executor's name layer of a concrete marking, **under one global total projection**
`nameOf`: tokens whose projected name is `n` at the `i`-th coloured place. The runtime has no
such global projection (see `ProjCoherent`); the model takes one, and describes the executor
only when every key and relay projection agrees with it. -/
def nameLayer (m : CMarking) : NM co :=
  fun n i => ((m co[i.1]).filter fun c => nameOf c == n).length

/-- One above every name in a coloured place. -/
def nameBound (m : CMarking) : ℕ := ((co.flatMap fun p => (m p).map nameOf).foldr max 0) + 1

theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | _ :: _, _, List.Mem.head _ => Nat.le_max_left _ _
  | _ :: _, _, List.Mem.tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem nameLayer_supp (m : CMarking) : Supp (nameLayer co nameOf m) (nameBound co nameOf m) := by
  intro s hs i
  unfold nameLayer
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc heq
  have hmem : nameOf c ∈ co.flatMap fun p => (m p).map nameOf :=
    List.mem_flatMap.mpr ⟨co[i.1], List.getElem_mem i.isLt, List.mem_map_of_mem hc⟩
  have := le_foldr_max hmem
  simp only [beq_iff_eq] at heq
  unfold nameBound at hs
  omega

/-- Whether `p` is one of `T`'s match keys. -/
def isKey (T : NuTrans) (p : PlaceId) : Bool :=
  match T.keys with
  | some ks => ks.contains p
  | none => false

/-- The per-key name index `find_match_binding` builds for one key place: the tokens whose
projection under that key's own `KeyFn` (`MatchKey::extract`) is `some n`. A token the
projection maps to `None` is skipped. -/
def keyIndex (f : Colour → Option ℕ) (m : CMarking) (p : PlaceId) (n : ℕ) : ℕ :=
  ((m p).filter fun c => f c == some n).length

/-- **The projection premise** (not a hypothesis of the end-to-end theorems: it is built into
`NuStepC` through the single `nameOf`). The runtime reads names through one `KeyFn` per match
key of each join and one per [NU-054] relay target, each partial (`Option<NameId>`). The model
reads every coloured token through one total `nameOf`. The model describes the executor when,
at every marking the executor reaches, every key or relay projection of every transition maps
every token in its place to `some (nameOf c)`: then all projections that read one place agree
(across joins, and between a relay and the key downstream that reads the same place), and none
returns `None`. `classify` checks neither. -/
def ProjCoherent (keyFn : NuTrans → PlaceId → Colour → Option ℕ) (net : List NuTrans)
    (m : CMarking) : Prop :=
  ∀ T ∈ net, ∀ p, (isKey T p = true ∨ p ∈ T.relays) → ∀ c ∈ m p, keyFn T p c = some (nameOf c)

/-- What the premise buys: on a key place, the runtime's per-key index is the model's name
layer. -/
theorem keyIndex_eq_nameLayer {f : Colour → Option ℕ} {m : CMarking} (i : Fin co.length)
    (h : ∀ c ∈ m co[i.1], f c = some (nameOf c)) (n : ℕ) :
    keyIndex f m co[i.1] n = nameLayer co nameOf m n i := by
  unfold keyIndex nameLayer
  congr 1
  refine List.filter_congr fun c hc => ?_
  rw [h c hc]
  simp

/-- The class an executor marking is seen as: its count marking and its name layer. -/
def view (m : CMarking) : NState co AMarking :=
  ⟨alpha m, nameLayer co nameOf m, nameBound co nameOf m, nameLayer_supp co nameOf m⟩

/-- `find_match_binding`'s required count on a key place: read off the first input spec on it. -/
def keyReq (T : NuTrans) (p : PlaceId) : ℕ :=
  match T.base.inputs.find? (fun s => s.place == p) with
  | some s => match s.card with
    | .exactly c => c
    | .atLeast c => c
    | _ => 1
  | none => 1

/-- `select_match_name` accepts `n`: there is at least one key (`per_place.is_empty()` returns
`None`), and every key place holds `n` at least once (the per-place index has an entry for `n`
only when a token projects to it) and at least at the required count. -/
def Selectable (T : NuTrans) (M : NM co) (n : ℕ) : Prop :=
  ∀ ks, T.keys = some ks → ks ≠ [] ∧ ∀ p ∈ ks, 1 ≤ cnt co M n p ∧ keyReq T p ≤ cnt co M n p

/-- The names of the tokens one input spec removes (`consume_for_firing`). -/
def SpecTakes (T : NuTrans) (M : NM co) (n : ℕ) (s : InSpec) (hs : List ℕ) : Prop :=
  if isKey T s.place = true then
    (if s.card.consumesAll = true then hs = List.replicate (cnt co M n s.place) n
     else hs = List.replicate s.card.required n)
  else
    (if s.card.consumesAll = true then ∀ u, hs.count u = cnt co M u s.place
     else hs.length = s.card.required)

/-- Tokens of name `u` the input specs remove from place `p`. -/
def rmvList : List InSpec → List (List ℕ) → PlaceId → ℕ → ℕ
  | s :: ss, h :: hs, p, u => (if s.place = p then h.count u else 0) + rmvList ss hs p u
  | _, _, _, _ => 0

/-- **The executor's name effect** of firing `T` with branch outcome `d`, by the runtime rules;
`K` constrains what the action writes (the contracts). -/
def ExecNames (T : NuTrans) (d : Deposit) (M M' : NM co)
    (K : ℕ → List (List ℕ) → (Fin co.length → List ℕ) → Prop) : Prop :=
  ∃ (n : ℕ) (hss : List (List ℕ)) (wr : Fin co.length → List ℕ),
    (T.keys.isSome = true → Selectable co T M n) ∧
    List.Forall₂ (SpecTakes co T M n) T.base.inputs hss ∧
    (∀ i u, rmvList T.base.inputs hss co[i.1] u ≤ M u i) ∧
    (∀ i, (wr i).length = d.count co[i.1]) ∧
    (T.keys.isSome = true → ∀ i, co[i.1] ∈ T.relays → ∀ w ∈ wr i, w = n) ∧
    K n hss wr ∧
    M' = fun u i => if T.base.resets.contains co[i.1] then (wr i).count u
      else M u i - rmvList T.base.inputs hss co[i.1] u + (wr i).count u

/-- The action contracts the runtime does not check (see the header). -/
def Contract (r : Role) (T : NuTrans) (M : NM co) :
    ℕ → List (List ℕ) → (Fin co.length → List ℕ) → Prop :=
  fun _ hss wr => match r with
  | .mint => ∃ f, (∀ i, M f i = 0) ∧ ∀ i, ∀ w ∈ wr i, w = f
  | .consume _ => ∀ i, ∀ w ∈ wr i, ∃ x ∈ T.base.inputs.zip hss,
      (idx co x.1.place).isSome = true ∧ w ∈ x.2
  | .ordinary => True
  | .join _ _ => True

/-- A card `classify` admits on a coloured input, consuming `r`. -/
def FixedCard (s : InSpec) (r : ℕ) : Prop := (s.card = .one ∧ r = 1) ∨ s.card = .exactly r

/-- What every role needs: no reset on a coloured place, one token per coloured fixed deposit,
and no drained forward into a coloured place (`classify` rule 2 rejects any coloured deposit
but `Deposit::Tokens(1)`). -/
structure Common (T : NuTrans) : Prop where
  noReset : ∀ p ∈ T.base.resets, idx co p = none
  unitDep : ∀ r ∈ T.rows, ∀ p ∈ r.fixed, (idx co p).isSome = true → r.fixed.count p = 1
  drainOff : ∀ r ∈ T.rows, ∀ x ∈ r.drains, idx co x.1 = none

/-- **The fragment conditions for a role.** `Classify.classifyT_inFragment` proves `classify`
establishes them, given the two join conditions it does not check: distinct keys
(`(cin.map Prod.fst).Nodup`) and at most one input spec per key place (the `= [s]`; `classify`
reads the first spec only). `TransitionBuilder::build` enforces both ([NU-020], [CORE-030] AC3;
`Classify.classifyS_inFragment`). -/
def InFragment (T : NuTrans) : Role → Prop
  | .ordinary => Common co T ∧ T.keys = none ∧ (∀ s ∈ T.base.inputs, idx co s.place = none) ∧
      ∀ r ∈ T.rows, ∀ p ∈ r.places, idx co p = none
  | .mint => Common co T ∧ T.keys = none ∧ ∀ s ∈ T.base.inputs, idx co s.place = none
  | .join cin rel => Common co T ∧ ∃ ks, T.keys = some ks ∧
      (∀ p, p ∈ ks ↔ p ∈ cin.map Prod.fst) ∧ (cin.map Prod.fst).Nodup ∧
      (∀ pr ∈ cin, (idx co pr.1).isSome = true ∧
        ∃ s, T.base.inputs.filter (fun s => s.place == pr.1) = [s] ∧ FixedCard s pr.2) ∧
      (∀ s ∈ T.base.inputs, (idx co s.place).isSome = true → s.place ∈ ks) ∧
      (∀ r ∈ T.rows, ∀ p ∈ r.places, (idx co p).isSome = true → p ∈ rel) ∧
      (∀ p ∈ rel, p ∈ T.relays)
  | .consume inp => Common co T ∧ T.keys = none ∧
      ∃ s, T.base.inputs.filter (fun s => (idx co s.place).isSome) = [s] ∧ s.place = inp ∧
        FixedCard s 1

variable {co nameOf}

theorem rmvList_zero : ∀ {ss : List InSpec} {hs : List (List ℕ)} {p : PlaceId} (u : ℕ),
    (∀ s ∈ ss, s.place ≠ p) → rmvList ss hs p u = 0
  | [], _, _, _, _ => by simp [rmvList]
  | _ :: _, [], _, _, _ => by simp [rmvList]
  | s :: ss, _ :: hs, p, u, h => by
    simp only [rmvList, if_neg (h s List.mem_cons_self), Nat.zero_add]
    exact rmvList_zero u fun s' hs' => h s' (List.mem_cons_of_mem _ hs')

/-- One spec satisfies `P`: its names are the only ones `P`-places lose. -/
theorem forall2_single {R : InSpec → List ℕ → Prop} {P : InSpec → Bool} {s0 : InSpec} :
    ∀ {ss : List InSpec} {hs : List (List ℕ)}, List.Forall₂ R ss hs → ss.filter P = [s0] →
      ∃ h0, R s0 h0 ∧ (∀ x ∈ ss.zip hs, P x.1 = true → x = (s0, h0)) ∧
        ∀ p u, (∀ s ∈ ss, s.place = p → P s = true) →
          rmvList ss hs p u = if s0.place = p then h0.count u else 0
  | [], [], List.Forall₂.nil, h => by simp at h
  | s :: ss, h :: hs, List.Forall₂.cons hR hrest, hf => by
    by_cases hP : P s = true
    · rw [List.filter_cons, if_pos hP] at hf
      obtain ⟨rfl, hnil⟩ := List.cons.inj hf
      rw [List.filter_eq_nil_iff] at hnil
      refine ⟨h, hR, fun x hx hPx => ?_, fun p u hpP => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hPx (hnil x.1 (List.of_mem_zip hx).1)
      · simp only [rmvList]
        rw [rmvList_zero u fun s' hs' he => hnil s' hs' (hpP s' (List.mem_cons_of_mem _ hs') he)]
        simp
    · rw [List.filter_cons, if_neg hP] at hf
      obtain ⟨h0, hR0, hzip, hrmv⟩ := forall2_single hrest hf
      refine ⟨h0, hR0, fun x hx hPx => ?_, fun p u hpP => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hPx hP
        · exact hzip x hx hPx
      · simp only [rmvList]
        have hsp : s.place ≠ p := fun e => hP (hpP s List.mem_cons_self e)
        rw [if_neg hsp, hrmv p u fun s' hs' => hpP s' (List.mem_cons_of_mem _ hs')]
        simp

theorem keyReq_of (T : NuTrans) {p : PlaceId} {s : InSpec} {r : ℕ}
    (hf : T.base.inputs.filter (fun s => s.place == p) = [s]) (hc : FixedCard s r) :
    keyReq T p = r := by
  unfold keyReq
  rw [← List.head?_filter, hf]
  rcases hc with ⟨hc, rfl⟩ | hc <;> simp [hc]

theorem count_replicate_eq (r n u : ℕ) :
    (List.replicate r n).count u = if u = n then r else 0 := by
  rw [List.count_replicate]
  by_cases h : u = n
  · simp [h]
  · have : (n == u) = false := by simp [Ne.symm h]
    simp [this, h]

theorem subAt_of_mem {co : List PlaceId} {cin : List (PlaceId × ℕ)} (hn : (cin.map Prod.fst).Nodup)
    {i : Fin co.length} {r : ℕ} (h : (co[i.1], r) ∈ cin) : subAt co cin i = r := by
  unfold subAt
  induction cin with
  | nil => simp at h
  | cons pr rest ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · have : rest.filter (fun pr => pr.1 == co[i.1]) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq he
        simp only [beq_iff_eq] at he
        exact hn.1 (by simpa [he] using List.mem_map_of_mem (f := Prod.fst) hq)
      simp [this]
    · have hne : pr.1 ≠ co[i.1] := fun e => hn.1 (e ▸ List.mem_map_of_mem (f := Prod.fst) h)
      have : (pr.1 == co[i.1]) = false := by simp [hne]
      simp only [List.filter_cons, this]
      exact ih hn.2 h

theorem subAt_of_not_mem {co : List PlaceId} {cin : List (PlaceId × ℕ)} {i : Fin co.length}
    (h : co[i.1] ∉ cin.map Prod.fst) : subAt co cin i = 0 := by
  unfold subAt
  have : cin.filter (fun pr => pr.1 == co[i.1]) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq he
    simp only [beq_iff_eq] at he
    exact h (he ▸ List.mem_map_of_mem hq)
  simp [this]

theorem wr_eq_of_len {w : List ℕ} {d : Deposit} {p : PlaceId} {x : ℕ}
    (hlen : w.length = d.count p) (hunit : p ∈ d → d.count p = 1) (hall : ∀ y ∈ w, y = x) (u : ℕ) :
    w.count u = if u = x ∧ p ∈ d then 1 else 0 := by
  by_cases hp : p ∈ d
  · rw [hunit hp] at hlen
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen
    have := hall y List.mem_cons_self
    subst this
    rw [List.count_singleton]
    by_cases hu : u = y
    · simp [hu, hp]
    · have : (y == u) = false := by simp [Ne.symm hu]
      simp [this, hu]
  · rw [List.count_eq_zero_of_not_mem hp] at hlen
    rw [List.length_eq_zero_iff.mp hlen]
    simp [hp]

theorem mem_colOut {co : List PlaceId} (hco : co.Nodup) {d : Deposit} {i : Fin co.length} :
    co[i.1] ∈ colOut co d ↔ co[i.1] ∈ d := by
  unfold colOut
  rw [List.mem_filter, List.mem_dedup, get_coloured hco]
  simp

theorem colOut_nodup {co : List PlaceId} {d : Deposit} : (colOut co d).Nodup :=
  List.Nodup.filter _ (List.nodup_dedup d)

theorem relOut_nodup {d : Deposit} {rel : List PlaceId} : (relOut d rel).Nodup :=
  List.Nodup.filter _ (List.nodup_dedup d)

theorem mem_relOut {d : Deposit} {rel : List PlaceId} {p : PlaceId} :
    p ∈ relOut d rel ↔ p ∈ d ∧ p ∈ rel := by
  unfold relOut
  rw [List.mem_filter, List.mem_dedup]
  simp

theorem not_reset (hco : co.Nodup) {T : NuTrans} (hcom : Common co T) (i : Fin co.length) :
    ¬ (T.base.resets.contains co[i.1] = true) := by
  rw [List.contains_iff_mem]
  exact fun hm => absurd (hcom.noReset _ hm) (by rw [idx_get hco]; simp)

/-- A drained forward never reaches a coloured place, so on a coloured place the resolved
deposit is the fixed one, whatever the drained counts. -/
theorem resolve_count_col {r : Row} (hr : ∀ x ∈ r.drains, idx co x.1 = none) {q : PlaceId}
    (hq : (idx co q).isSome = true) (k : PlaceId → ℕ) : (r.resolve k).count q = r.fixed.count q := by
  unfold Row.resolve
  have hn : q ∉ r.drains.flatMap fun x => List.replicate (k x.2) x.1 := by
    intro hm
    obtain ⟨x, hx, hqx⟩ := List.mem_flatMap.mp hm
    rw [List.eq_of_mem_replicate hqx, hr x hx] at hq
    exact absurd hq (by simp)
  rw [List.count_append, List.count_eq_zero_of_not_mem hn, Nat.add_zero]

theorem mem_places_col {r : Row} (hr : ∀ x ∈ r.drains, idx co x.1 = none) {q : PlaceId}
    (hq : (idx co q).isSome = true) : q ∈ r.places ↔ q ∈ r.fixed := by
  unfold Row.places
  rw [List.mem_append]
  refine ⟨fun h => h.elim id fun hm => ?_, Or.inl⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
  rw [hr x hx] at hq
  exact absurd hq (by simp)

theorem InFragment.common {T : NuTrans} {r : Role} (h : InFragment co T r) : Common co T := by
  cases r with
  | ordinary => exact h.1
  | mint => exact h.1
  | join _ _ => exact h.1
  | consume _ => exact h.1

/-- **The executor's name successor is a `name_successors` output, up to key.** The executor
writes the resolved deposit of the fired branch `r` (drained counts `k`); the graph reads the
branch's `places`. -/
theorem exec_names_step (hco : co.Nodup) {T : NuTrans} {r : Role} (hfr : InFragment co T r)
    {row : Row} (hd : row ∈ T.rows) {k : PlaceId → ℕ} {M M' : NM co}
    (hK : ExecNames co T (row.resolve k) M M' (Contract co r T M))
    {B c : ℕ} (hM : Supp M B) (hc : B ≤ c) :
    ∃ M'' ∈ nameSuccs co r M row.places B c, canonicalKey M'' = canonicalKey M' := by
  obtain ⟨n, hss, wr, hsel, hF2, hle, hlen0, hrel, hcon, rfl⟩ := hK
  have hcom := hfr.common
  have hdr := hcom.drainOff row hd
  have hlen : ∀ i : Fin co.length, (wr i).length = row.fixed.count co[i.1] := fun i => by
    rw [hlen0 i, resolve_count_col hdr (get_coloured hco i)]
  have hpl : ∀ i : Fin co.length, co[i.1] ∈ row.places ↔ co[i.1] ∈ row.fixed := fun i =>
    mem_places_col hdr (get_coloured hco i)
  cases r with
  | ordinary =>
    obtain ⟨-, -, hin, hout⟩ := hfr
    refine ⟨M, List.mem_singleton_self _, ?_⟩
    congr 1
    funext u i
    rw [if_neg (not_reset hco hcom i)]
    rw [rmvList_zero u fun s hs he => by
      have := hin s hs; rw [he, idx_get hco] at this; exact absurd this (by simp)]
    have hw : wr i = [] := by
      rw [← List.length_eq_zero_iff, hlen i]
      exact List.count_eq_zero_of_not_mem fun hm => by
        have := hout row hd _ ((hpl i).mpr hm); rw [idx_get hco] at this
        exact absurd this (by simp)
    simp [hw]
  | mint =>
    obtain ⟨-, -, hin⟩ := hfr
    obtain ⟨f, hf0, hfw⟩ := hcon
    refine ⟨mintStep co (colOut co row.places) c M, List.mem_singleton_self _, ?_⟩
    rw [mint_key (N := M) (σ := 1) (colOut co row.places) rfl (fun i => hM c hc i) hf0]
    congr 1
    funext u i
    rw [if_neg (not_reset hco hcom i)]
    rw [rmvList_zero u fun s hs he => by
      have := hin s hs; rw [he, idx_get hco] at this; exact absurd this (by simp)]
    unfold mintStep
    rw [foldl_add_apply hco f (colOut co row.places) colOut_nodup]
    simp only [mem_colOut hco, hpl i]
    rw [wr_eq_of_len (hlen i) (fun hp => hcom.unitDep row hd _ hp (get_coloured hco i)) (hfw i) u]
    simp
  | join cin rel =>
    obtain ⟨-, ks, hks, hmemks, hnd, hcin, hoff, hcol, hrelT⟩ := hfr
    obtain ⟨hne, hsel'⟩ := hsel (by rw [hks]; rfl) ks hks
    -- `n` is an enabling symbol.
    have hreq : ∀ pr ∈ cin, pr.2 ≤ cnt co M n pr.1 := by
      intro pr hpr
      obtain ⟨-, s, hfs, hfc⟩ := hcin pr hpr
      have := (hsel' pr.1 ((hmemks pr.1).mpr (List.mem_map_of_mem hpr))).2
      rwa [keyReq_of T hfs hfc] at this
    have hen : joinEnab co cin M n = true := by
      cases cin with
      | nil =>
        obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ks hne
        exact absurd ((hmemks p).mp hp) (by simp)
      | cons pr0 rest =>
        obtain ⟨p0, r0⟩ := pr0
        have h1 := (hsel' p0 ((hmemks p0).mpr (by simp))).1
        simp only [joinEnab, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, decide_eq_true_eq]
        exact ⟨by omega, hreq⟩
    have hnB : n < B := lt_of_live hM (joinEnab_live cin M n hen)
    obtain ⟨r', hr', hsig⟩ := (dsig_transversal (M := M) (E := joinEnab co cin M) (B := B)
      (fun s hs => lt_of_live hM (joinEnab_live cin M s hs))).cover n hen
    refine ⟨joinStep co cin (relOut row.places rel) r' M, List.mem_map_of_mem hr', ?_⟩
    rw [key_swap (joinStep_sym cin (relOut row.places rel)) (sig_eq_iff.mp hsig)]
    congr 1
    funext u i
    rw [if_neg (not_reset hco hcom i)]
    unfold joinStep
    rw [foldl_add_apply hco n (relOut row.places rel) relOut_nodup,
      foldl_remove_apply hco n cin hnd M hreq]
    -- the removal
    have hrm : rmvList T.base.inputs hss co[i.1] u = if u = n then subAt co cin i else 0 := by
      by_cases hk : co[i.1] ∈ ks
      · obtain ⟨pr, hpr, hpe⟩ := List.mem_map.mp ((hmemks _).mp hk)
        obtain ⟨-, s0, hfs, hfc⟩ := hcin pr hpr
        rw [hpe] at hfs
        obtain ⟨h0, hR0, -, hrmv⟩ := forall2_single (P := fun s => s.place == co[i.1]) hF2 hfs
        have hs0 : s0.place = co[i.1] := by
          have := List.mem_filter.mp (hfs ▸ List.mem_singleton_self s0 : s0 ∈ _)
          simpa using this.2
        rw [hrmv co[i.1] u (fun s _ he => by simp [he]), if_pos hs0]
        have hkey : isKey T s0.place = true := by
          unfold isKey; rw [hks, hs0]; simpa using hk
        unfold SpecTakes at hR0
        rw [if_pos hkey] at hR0
        have hca : s0.card.consumesAll = false := by
          rcases hfc with ⟨hc1, -⟩ | hc1 <;> rw [hc1] <;> rfl
        rw [if_neg (by simp [hca])] at hR0
        have hreq0 : s0.card.required = pr.2 := by
          rcases hfc with ⟨hc1, h1⟩ | hc1
          · rw [hc1]; simp [Card.required, h1]
          · rw [hc1]; simp [Card.required]
        rw [hR0, hreq0, count_replicate_eq, subAt_of_mem hnd (by rw [← hpe]; exact hpr)]
      · rw [rmvList_zero u fun s hs he => hk (by rw [← he]; exact hoff s hs (by rw [he]; exact get_coloured hco i)),
          subAt_of_not_mem (fun hm => hk ((hmemks _).mpr hm))]
        simp
    have hwr : (wr i).count u = if u = n ∧ co[i.1] ∈ relOut row.places rel then 1 else 0 := by
      by_cases hdi : co[i.1] ∈ row.fixed
      · have hin : co[i.1] ∈ rel := hcol row hd _ ((hpl i).mpr hdi) (get_coloured hco i)
        rw [wr_eq_of_len (hlen i) (fun hp => hcom.unitDep row hd _ hp (get_coloured hco i))
          (hrel (by rw [hks]; rfl) i (hrelT _ hin)) u]
        simp only [mem_relOut, hpl i]
        simp [hdi, hin]
      · have : (wr i).length = 0 := by rw [hlen i]; exact List.count_eq_zero_of_not_mem hdi
        rw [List.length_eq_zero_iff.mp this]
        simp only [mem_relOut, hpl i]
        simp [hdi]
    rw [hrm, hwr]
  | consume inp =>
    obtain ⟨-, hkn, s0, hfs, hs0, hfc⟩ := hfr
    obtain ⟨h0, hR0, hzip, hrmv⟩ := forall2_single (P := fun s => (idx co s.place).isSome) hF2 hfs
    have hnk : ∀ p, isKey T p = false := fun p => by unfold isKey; rw [hkn]
    unfold SpecTakes at hR0
    rw [if_neg (by simp [hnk])] at hR0
    have hca : s0.card.consumesAll = false := by
      rcases hfc with ⟨hc1, -⟩ | hc1 <;> rw [hc1] <;> rfl
    rw [if_neg (by simp [hca])] at hR0
    have hreq0 : s0.card.required = 1 := by
      rcases hfc with ⟨hc1, h1⟩ | hc1 <;> rw [hc1] <;> simp [Card.required]
    rw [hreq0] at hR0
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.mp hR0
    have hrm : ∀ (i : Fin co.length) (u : ℕ), rmvList T.base.inputs hss co[i.1] u =
        if u = h ∧ co[i.1] = inp then 1 else 0 := by
      intro i u
      rw [hrmv co[i.1] u (fun s _ he => by rw [he]; exact get_coloured hco i), hs0,
        List.count_singleton]
      by_cases hi : inp = co[i.1]
      · by_cases hu : u = h
        · simp [hi, hu]
        · have : (h == u) = false := by simp [Ne.symm hu]
          simp [hi, hu, this]
      · simp [hi, Ne.symm hi]
    -- `h` is resident in `inp`.
    have hinp : (idx co inp).isSome = true := by
      have := (List.mem_filter.mp (hfs ▸ List.mem_singleton_self s0 : s0 ∈ _)).2
      rwa [hs0] at this
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hinp
    have hgj := get_of_idx hj
    have hres1 : 1 ≤ cnt co M h inp := by
      have := hle j h
      rw [hrm j h, if_pos ⟨rfl, hgj⟩] at this
      unfold cnt; rw [hj]; exact this
    have hres : resident co inp M h = true := by
      unfold resident; simp only [bne_iff_ne, ne_eq]; omega
    obtain ⟨r', hr', hsig⟩ := (dsig_transversal (M := M) (E := resident co inp M) (B := B)
      (fun s hs => lt_of_live hM (resident_live inp M s hs))).cover h hres
    refine ⟨consumeStep co inp (colOut co row.places) r' M, List.mem_map_of_mem hr', ?_⟩
    rw [key_swap (consumeStep_sym inp (colOut co row.places)) (sig_eq_iff.mp hsig)]
    congr 1
    funext u i
    rw [if_neg (not_reset hco hcom i)]
    unfold consumeStep
    rw [foldl_add_apply hco h (colOut co row.places) colOut_nodup, removeAt_apply hco inp h 1 M hres1,
      hrm i u]
    simp only [mem_colOut hco, hpl i]
    have hall : ∀ w ∈ wr i, w = h := by
      intro w hw
      obtain ⟨x, hx, hxc, hwx⟩ := hcon i w hw
      rw [hzip x hx hxc] at hwx
      simpa using hwx
    rw [wr_eq_of_len (hlen i) (fun hp => hcom.unitDep row hd _ hp (get_coloured hco i)) hall u]

end Executor

end Libpetri.Novel.RouteB
