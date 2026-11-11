import Libpetri.Reference.Step

set_option linter.missingDocs true

/-!
# Situations: a firing sequence replayed step by step

A **situation** (`spec/situations/README.md`) is a net of the conformance corpus schema with a
list of steps, each naming a transition to fire and the outcome its firing ends with: an output
branch, numbered as [IO-016] enumerates them, or the timeout outcome ([IO-013]). The spec site
plays a situation back marking by marking; this file computes what it shows, on the reference
firing rule (`Semantics.lean`), and proves it.

`replaySituation net m0 steps` fires the steps in order from the canonical marking `m0`. For
each step it reports either the marking the firing leaves (`StepResult.fired`) or, for the first
step that cannot fire, why (`StepResult.blocked`), and stops there. The reasons (`Blocked`), each
with the requirement it cites (`Blocked.requirement`):

* `unknownTransition`: the net has no transition of that name ([CORE-020]);
* `inputShort p c need held`: input place `p` holds `held` tokens, fewer than the `need` its
  arc of cardinality `c` requires ([IO-001]–[IO-004], by cardinality);
* `inhibitorMarked p n`: inhibitor place `p` holds `n ≠ 0` tokens ([CORE-031]);
* `readEmpty p`: read place `p` is empty ([CORE-032]);
* `noSuchBranch ch`: the transition is enabled, but its output spec offers no outcome `ch`
  ([IO-016] for an action branch, [IO-013] for the timeout outcome).

The enablement reasons are checked in the order of [CORE-022]'s definition: inputs, then
inhibitors, then reads, each list in declaration order, so the first failing arc is reported.
Reset arcs never block ([CORE-034]).

**Soundness** (`replaySituation_sound`): the outcomes satisfy `Replays`. A fired step is a
`FiresWith` step of the named transition with the chosen outcome from the previous marking to
the reported one, hence a `Fires` and an `LStep` of the semantics (`firesWith_fires`,
`firesWith_lstep`); its marking is canonical. A blocked step's reason is true of the marking
(`Blocked.Holds`), the named transition has no `FiresWith` step with that outcome to any
marking, and for every reason but `noSuchBranch` no step of the semantics carries the
transition's label at all. The blocked direction needs transition names to be unique, which the
loader checks (`Load.parseNet`) and every builder enforces. `Replays.run` reads a fully fired
replay as a `Run` of the semantics.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam Libpetri.Novel.ForwardDeposit

variable {K : Type} [LinearOrder K]

/-- One step of a situation: the transition to fire, by name, and the outcome its firing ends
with (`.action i`: output branch `i` in [IO-016]'s enumeration, `0` for a transition without
an output spec; `.timedOut j`: the `j`-th timeout deposit, of which a spec has at most one). -/
structure SitStep where
  /-- The transition's name. -/
  fire   : String
  /-- The outcome the firing ends with. -/
  choice : Choice := .action 0

/-- Why a step cannot fire. -/
inductive Blocked (K : Type) where
  /-- The net has no transition of that name. -/
  | unknownTransition
  /-- Input place `place` holds `held` tokens, fewer than the `need` of its arc `card`. -/
  | inputShort (place : K) (card : Card) (need held : Nat)
  /-- Inhibitor place `place` holds `count ≠ 0` tokens. -/
  | inhibitorMarked (place : K) (count : Nat)
  /-- Read place `place` is empty. -/
  | readEmpty (place : K)
  /-- The transition is enabled but offers no outcome `choice`. -/
  | noSuchBranch (choice : Choice)

/-- The requirement a blocked step cites. -/
def Blocked.requirement : Blocked K → String
  | .unknownTransition => "CORE-020"
  | .inputShort _ .one _ _ => "IO-001"
  | .inputShort _ (.exactly _) _ _ => "IO-002"
  | .inputShort _ .all _ _ => "IO-003"
  | .inputShort _ (.atLeast _) _ _ => "IO-004"
  | .inhibitorMarked _ _ => "CORE-031"
  | .readEmpty _ => "CORE-032"
  | .noSuchBranch (.action _) => "IO-016"
  | .noSuchBranch (.timedOut _) => "IO-013"

/-- Whether the reason is that the transition is not enabled (every reason but
`noSuchBranch`). -/
def Blocked.gates : Blocked K → Bool
  | .noSuchBranch _ => false
  | _ => true

/-- What one step reports. -/
inductive StepResult (K : Type) where
  /-- The step fired and left this marking. -/
  | fired (m : Marking K)
  /-- The step could not fire, for this reason. -/
  | blocked (r : Blocked K)

/-- The first arc that keeps `t` from being enabled at `m`, in [CORE-022]'s order: inputs,
inhibitors, reads. `none` when `t` is enabled. -/
def enabledWhy (m : Marking K) (t : NTransition K) : Option (Blocked K) :=
  match t.inputs.find? (fun s => decide (get m s.place < s.card.required)) with
  | some s => some (.inputShort s.place s.card s.card.required (get m s.place))
  | none =>
    match t.inhibitors.find? (fun p => decide (get m p ≠ 0)) with
    | some p => some (.inhibitorMarked p (get m p))
    | none =>
      match t.reads.find? (fun p => decide (get m p = 0)) with
      | some p => some (.readEmpty p)
      | none => none

/-- One step from `m`: the marking it leaves, or why it cannot fire. The deposit `d` of the
chosen outcome is written as a bag of single tokens, so `fire` adds `d.count p` to each `p`. -/
def stepOnce (net : Net K) (m : Marking K) (s : SitStep) : Except (Blocked K) (Marking K) :=
  match net.transitions.find? (fun t => t.core.name == s.fire) with
  | none => .error .unknownTransition
  | some t =>
    match enabledWhy m t.core with
    | some r => .error r
    | none =>
      match deposit (nconsumed (get m) t.core) t.out s.choice with
      | none => .error (.noSuchBranch s.choice)
      | some d => .ok (fire m t.core (d.map fun p => (p, 1)))

/-- **The replay** of a situation: one outcome per step, up to and including the first step
that cannot fire. -/
def replaySituation (net : Net K) : Marking K → List SitStep → List (StepResult K)
  | _, [] => []
  | m, s :: ss =>
    match stepOnce net m s with
    | .ok m' => .fired m' :: replaySituation net m' ss
    | .error r => [.blocked r]

/-! ## What the outcomes mean -/

/-- One firing of `t` ending with the outcome `ch`: `Fires` with its outcome fixed. -/
def FiresWith (t : Trans K) (ch : Choice) (m : K → Nat) (d : List K) (m' : K → Nat) : Prop :=
  enabledNA m t.core = true ∧ deposit (nconsumed m t.core) t.out ch = some d ∧
    m' = fireNC m t.core (depProd d)

/-- What a reason claims of the count marking `m` for step `s`. -/
def Blocked.Holds (net : Net K) (m : K → Nat) (s : SitStep) : Blocked K → Prop
  | .unknownTransition => ∀ t ∈ net.transitions, t.core.name ≠ s.fire
  | .inputShort p c need held => ∃ t ∈ net.transitions, t.core.name = s.fire ∧
      ∃ i ∈ t.core.inputs, i.place = p ∧ i.card = c ∧ c.required = need ∧ m p = held ∧
        held < need
  | .inhibitorMarked p n => ∃ t ∈ net.transitions, t.core.name = s.fire ∧
      p ∈ t.core.inhibitors ∧ m p = n ∧ n ≠ 0
  | .readEmpty p => ∃ t ∈ net.transitions, t.core.name = s.fire ∧ p ∈ t.core.reads ∧ m p = 0
  | .noSuchBranch ch => ch = s.choice ∧ ∃ t ∈ net.transitions, t.core.name = s.fire ∧
      enabledNA m t.core = true ∧ deposit (nconsumed m t.core) t.out ch = none

/-- **A step blocked for reason `r`**: `r` is true, the named transition has no firing with the
chosen outcome, and a reason that gates enablement leaves no step with the label at all. -/
def BlockedAt (net : Net K) (m : K → Nat) (s : SitStep) (r : Blocked K) : Prop :=
  r.Holds net m s ∧
    (∀ t ∈ net.transitions, t.core.name = s.fire → ∀ d m', ¬ FiresWith t s.choice m d m') ∧
    (r.gates = true → ∀ m', ¬ LStep net s.fire m m')

/-- **What a replay reports**, step by step: a fired step is a `FiresWith` step of the named
transition to a canonical marking, and the replay goes on from it; a blocked step is
`BlockedAt` and ends the replay. -/
inductive Replays (net : Net K) : Marking K → List SitStep → List (StepResult K) → Prop
  /-- No step, no outcome. -/
  | nil (m : Marking K) : Replays net m [] []
  /-- The first step fired to `m'`; the rest replays from `m'`. -/
  | fired {m m' : Marking K} {s : SitStep} {ss : List SitStep} {os : List (StepResult K)} :
      Canon m' →
      (∃ t ∈ net.transitions, t.core.name = s.fire ∧ ∃ d, FiresWith t s.choice (get m) d (get m')) →
      Replays net m' ss os → Replays net m (s :: ss) (.fired m' :: os)
  /-- The first step is blocked; the replay ends with it. -/
  | blocked {m : Marking K} {s : SitStep} {ss : List SitStep} {r : Blocked K} :
      BlockedAt net (get m) s r → Replays net m (s :: ss) [.blocked r]

/-- A `FiresWith` step is a `Fires` step. -/
theorem firesWith_fires {t : Trans K} {ch : Choice} {m : K → Nat} {d : List K} {m' : K → Nat}
    (h : FiresWith t ch m d m') : Fires t m d m' :=
  ⟨h.1, ⟨ch, h.2.1⟩, h.2.2⟩

/-- A `Fires` step is a `FiresWith` step for some outcome. -/
theorem fires_iff_exists_firesWith {t : Trans K} {m : K → Nat} {d : List K}
    {m' : K → Nat} : Fires t m d m' ↔ ∃ ch, FiresWith t ch m d m' :=
  ⟨fun ⟨he, ⟨ch, hd⟩, hm⟩ => ⟨ch, he, hd, hm⟩, fun ⟨_, h⟩ => firesWith_fires h⟩

/-- A `FiresWith` step of a transition of the net is a labelled step. -/
theorem firesWith_lstep {net : Net K} {t : Trans K} (ht : t ∈ net.transitions)
    {ch : Choice} {m : K → Nat} {d : List K} {m' : K → Nat} (h : FiresWith t ch m d m') :
    LStep net t.core.name m m' :=
  ⟨t, ht, rfl, d, firesWith_fires h⟩

/-! ## Correctness of the executable pieces -/

/-- Single tokens count as the deposit list: `bagCount` of `d.map (·, 1)` is `depProd d`. -/
theorem bagCount_singles (d : List K) : bagCount (d.map fun p => (p, 1)) = depProd d := by
  funext q
  induction d with
  | nil => simp [bagCount, depProd]
  | cons a d ih =>
    simp only [List.map_cons, bagCount, depProd, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : a = q
    · subst h; simp; omega
    · have : (a == q) = false := by simpa using h
      simp [h, this]

/-- `enabledWhy` reports nothing exactly when the transition is enabled. -/
theorem enabledWhy_eq_none_iff {m : Marking K} {t : NTransition K} :
    enabledWhy m t = none ↔ enabledNA (get m) t = true := by
  unfold enabledWhy
  simp only [enabledNA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  split
  · rename_i s hs
    simp only [reduceCtorEq, false_iff]
    rintro ⟨⟨hi, _⟩, _⟩
    have h1 := List.find?_some hs
    have h2 := hi s (List.mem_of_find?_eq_some hs)
    simp only [decide_eq_true_eq] at h1
    omega
  · rename_i hs
    have hin : ∀ s ∈ t.inputs, s.card.required ≤ get m s.place := by
      intro s h
      have := List.find?_eq_none.mp hs s h
      simp only [decide_eq_true_eq, not_lt] at this
      exact this
    split
    · rename_i p hp
      simp only [reduceCtorEq, false_iff]
      rintro ⟨⟨_, hinh⟩, _⟩
      have h1 := List.find?_some hp
      have h2 := hinh p (List.mem_of_find?_eq_some hp)
      simp only [decide_eq_true_eq] at h1
      exact absurd h2 h1
    · rename_i hp
      have hinh : ∀ p ∈ t.inhibitors, get m p = 0 := by
        intro p h
        have := List.find?_eq_none.mp hp p h
        simpa using this
      split
      · rename_i r hr
        simp only [reduceCtorEq, false_iff]
        rintro ⟨_, hrd⟩
        have h1 := List.find?_some hr
        have h2 := hrd r (List.mem_of_find?_eq_some hr)
        simp only [decide_eq_true_eq] at h1
        omega
      · rename_i hr
        simp only [true_iff]
        refine ⟨⟨hin, hinh⟩, fun r h => ?_⟩
        have := List.find?_eq_none.mp hr r h
        simp only [decide_eq_true_eq] at this
        omega

/-- A reason `enabledWhy` reports is true of the marking, and gates enablement. -/
theorem enabledWhy_holds {net : Net K} {m : Marking K} {s : SitStep} {t : Trans K}
    (ht : t ∈ net.transitions) (hn : t.core.name = s.fire) {r : Blocked K}
    (h : enabledWhy m t.core = some r) : r.Holds net (get m) s ∧ r.gates = true := by
  unfold enabledWhy at h
  split at h
  · rename_i i hi
    cases h
    have h1 := List.find?_some hi
    simp only [decide_eq_true_eq] at h1
    refine ⟨⟨t, ht, hn, i, List.mem_of_find?_eq_some hi, rfl, rfl, rfl, rfl, h1⟩, ?_⟩
    cases i.card <;> rfl
  · split at h
    · rename_i p hp
      cases h
      have h1 := List.find?_some hp
      simp only [decide_eq_true_eq] at h1
      exact ⟨⟨t, ht, hn, List.mem_of_find?_eq_some hp, rfl, h1⟩, rfl⟩
    · split at h
      · rename_i p hp
        cases h
        have h1 := List.find?_some hp
        simp only [decide_eq_true_eq] at h1
        exact ⟨⟨t, ht, hn, List.mem_of_find?_eq_some hp, h1⟩, rfl⟩
      · cases h

omit [LinearOrder K] in
/-- With unique names, the transition `find?` returns is the only one with its name. -/
theorem find_name_unique {net : Net K} (hnd : (net.transitions.map (·.core.name)).Nodup)
    {l : String} {t : Trans K} (hf : net.transitions.find? (fun t => t.core.name == l) = some t)
    {t' : Trans K} (ht' : t' ∈ net.transitions) (hn' : t'.core.name = l) : t' = t := by
  have h1 := List.find?_some hf
  simp only [beq_iff_eq] at h1
  exact List.inj_on_of_nodup_map hnd ht' (List.mem_of_find?_eq_some hf) (by rw [hn', h1])

/-- **A fired step is a firing of the reference semantics**: the named transition, enabled at
`m`, ends with the chosen outcome and leaves the reported marking, which is canonical. -/
theorem stepOnce_ok {net : Net K} {m m' : Marking K} (hc : Canon m) {s : SitStep}
    (h : stepOnce net m s = .ok m') :
    Canon m' ∧ ∃ t ∈ net.transitions, t.core.name = s.fire ∧
      ∃ d, FiresWith t s.choice (get m) d (get m') := by
  unfold stepOnce at h
  split at h
  · cases h
  · rename_i t hf
    split at h
    · cases h
    · rename_i hw
      split at h
      · cases h
      · rename_i d hd
        cases h
        have h1 := List.find?_some hf
        simp only [beq_iff_eq] at h1
        obtain ⟨hc', hg⟩ := fire_spec hc t.core (d.map fun p => (p, 1))
        refine ⟨hc', t, List.mem_of_find?_eq_some hf, h1, d,
          enabledWhy_eq_none_iff.mp hw, hd, ?_⟩
        funext q
        rw [hg q, bagCount_singles]

/-- **A blocked step cannot fire**: with unique transition names, the reason is true, the named
transition has no firing with the chosen outcome, and a reason that gates enablement leaves no
step labelled with the transition's name. -/
theorem stepOnce_blocked {net : Net K} (hnd : (net.transitions.map (·.core.name)).Nodup)
    {m : Marking K} {s : SitStep} {r : Blocked K} (h : stepOnce net m s = .error r) :
    BlockedAt net (get m) s r := by
  unfold stepOnce at h
  split at h
  · rename_i hf
    cases h
    have hno : ∀ t ∈ net.transitions, t.core.name ≠ s.fire := by
      intro t ht hn
      have := List.find?_eq_none.mp hf t ht
      simp [hn] at this
    refine ⟨hno, fun t ht hn => absurd hn (hno t ht), fun _ m' ⟨t, ht, hn, _⟩ => hno t ht hn⟩
  · rename_i t hf
    have ht := List.mem_of_find?_eq_some hf
    have hn : t.core.name = s.fire := by
      have := List.find?_some hf
      simpa using this
    have uniq := fun {t'} (ht' : t' ∈ net.transitions) (hn' : t'.core.name = s.fire) =>
      find_name_unique hnd hf ht' hn'
    split at h
    · rename_i r' hw
      cases h
      obtain ⟨hr, hg⟩ := enabledWhy_holds ht hn hw
      have hdis : enabledNA (get m) t.core = false := by
        cases he : enabledNA (get m) t.core with
        | false => rfl
        | true => rw [enabledWhy_eq_none_iff.mpr he] at hw; cases hw
      refine ⟨hr, fun t' ht' hn' d m' hfw => ?_, fun _ m' hst => ?_⟩
      · obtain ⟨he, _⟩ := hfw
        rw [uniq ht' hn', hdis] at he
        exact Bool.false_ne_true he
      · obtain ⟨t', ht', hn', d, he, _⟩ := hst
        rw [uniq ht' hn', hdis] at he
        exact Bool.false_ne_true he
    · rename_i hw
      split at h
      · rename_i hd
        cases h
        refine ⟨⟨rfl, t, ht, hn, enabledWhy_eq_none_iff.mp hw, hd⟩, fun t' ht' hn' d m' hfw => ?_,
          fun hg => by simp [Blocked.gates] at hg⟩
        obtain ⟨_, hd', _⟩ := hfw
        rw [uniq ht' hn', hd] at hd'
        cases hd'
      · cases h

/-- **Soundness of the replay**: from a canonical marking, on a net with unique transition
names, every fired step is a firing of the reference semantics with the chosen outcome, to the
canonical marking reported, and the step that blocks, if any, cannot fire for the reason
reported. -/
theorem replaySituation_sound {net : Net K} (hnd : (net.transitions.map (·.core.name)).Nodup) :
    ∀ {m : Marking K} (ss : List SitStep), Canon m → Replays net m ss (replaySituation net m ss)
  | m, [], _ => .nil m
  | m, s :: ss, hc => by
    unfold replaySituation
    split
    · rename_i m' h
      obtain ⟨hc', hf⟩ := stepOnce_ok hc h
      exact .fired hc' hf (replaySituation_sound hnd ss hc')
    · rename_i r h
      exact .blocked (stepOnce_blocked hnd h)

/-- The marking a replay ends in: the last fired marking, or `m` when none fired. -/
def lastMarking : Marking K → List (StepResult K) → Marking K
  | m, [] => m
  | _, .fired m' :: os => lastMarking m' os
  | m, .blocked _ :: _ => m

/-- Whether every step of a replay fired. -/
def allFired : List (StepResult K) → Bool
  | [] => true
  | .fired _ :: os => allFired os
  | .blocked _ :: _ => false

/-- **A fully fired replay is a run**: when every step fired, the labels of the steps are a
firing sequence of the reference semantics from `m` to the last marking. -/
theorem Replays.run {net : Net K} {m : Marking K} {ss : List SitStep} {os : List (StepResult K)}
    (h : Replays net m ss os) (ha : allFired os = true) :
    Run net (ss.map (·.fire)) (get m) (get (lastMarking m os)) := by
  induction h with
  | nil m => exact .nil _
  | fired _ hf _ ih =>
    obtain ⟨t, ht, hn, d, hfw⟩ := hf
    have hs := firesWith_lstep ht hfw
    rw [hn] at hs
    exact .cons hs (ih ha)
  | blocked _ => simp [allFired] at ha

end Libpetri.Reference
