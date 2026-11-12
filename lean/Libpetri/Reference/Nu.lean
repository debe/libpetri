import Libpetri.Spec.GlossaryNu
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.Build

set_option linter.missingDocs true

/-!
# RefNu: the reference ν firing, the ν builders and the ν definition record

The queue-level reference of [NU-020] (and of [NU-021], [NU-022], [NU-054]'s run-time check),
built on RefQFire's vocabulary (`Reference/Queue.lean`) and the terms of `Spec/GlossaryNu.lean`.

* **Definitions.** `NuDef N A K` extends wave W2's `TransDef N A` with the match specification
  (`Reference/Build.lean`: "the ν-net model's `NuDef` extends it"); its firing view is
  `NuDef.toNuTrans`, a `NuTrans` wrapping `TransDef.toTrans`. Nothing adds a field to `TransDef`
  or to `Reference.Trans`. `NuCDef N A K` extends the composition record `CDef N A` of
  [MOD-021] the same way; it reads as a `NuDef` (`NuCDef.toNuDef`) with the same firing view
  (`NuCDef.toNuTrans_comp`). [NU-030]'s rebuild is over `NuDef`, [NU-060]'s merge over
  `NuCDef`.
* **Builders.** `refMatchBuild` is the match builder (ruling D37 (a): fewer than two keys, then a
  place keyed twice); `refNuBuild` is the transition builder with a match: `refBuild`'s checks,
  then a place keyed twice, then a key on a place that is not an input place, then per relay
  target "declared twice" before "not an output", the order of
  `rust/libpetri-core/src/transition.rs:513-556`. The spec fixes no message text for these checks;
  the messages here are Rust's, as stand-ins.
* **Firing.** `RefNuFire`: without a match it is `RefQFire` (`refNuFire_restrictsTo`). With a
  match the NU-022 selection picks the chosen name `n`, the transition is enabled on its counts,
  the emission is an outcome the output spec offers under the correlated takes of `n`, the relay
  check passes ([NU-054], on a completion the executor accepts), and delivery and result are the
  name-filtered queue operations (`nuDelivered`, `nuConsume`, then the tail append).
* **Net layer** for the blocks that run a ν net ([NU-040], [NU-050]): `RefNuStep`, `RefNuReach`,
  `NuRests` (VER-002's rest with "enabled" read name-aware).

The firing pass (a join whose correlated input took a same-pass deposit waits a cycle, EXEC-003
AC4) and the timed ν join (TIME-012's ν clause) are RefExec's, with the ν kernel; they are not
modelled here.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N A K V Nm : Type}

/-! ## The definition record -/

/-- A transition definition with a match specification: W2's `TransDef` and the match
(`none`: no match). -/
structure NuDef (N A K : Type) extends TransDef N A where
  /-- The match specification ([NU-020]); `none` = no match. -/
  mspec : Option (MatchSpec N K) := none

/-- The firing view of a ν definition: the firing view of its `TransDef`, with its match. -/
def NuDef.toNuTrans (d : NuDef N A K) : NuTrans N K := ⟨d.toTransDef.toTrans, d.mspec⟩

/-- A ν definition without a match fires as its `TransDef`. -/
theorem NuDef.toNuTrans_base (d : NuDef N A K) : d.toNuTrans.base = d.toTransDef.toTrans := rfl

/-- A transition definition as channel composition carries it ([MOD-021]: `CDef`, with the
declared-place correspondence of [MOD-031]), together with its ν-net match ([NU-020];
`none`: no match). The key type `K` is abstract: a composition pass never looks into a key. -/
structure NuCDef (N A K : Type) extends CDef N A where
  /-- The match specification; `none` = no match. -/
  mspec : Option (MatchSpec N K) := none

/-- A composition definition with the match `ms` attached. -/
def NuCDef.ofCDef (d : CDef N A) (ms : Option (MatchSpec N K)) : NuCDef N A K :=
  { toCDef := d, mspec := ms }

/-- A composition definition with its match, read as a ν definition: its `TransDef` and its
match, the correspondence of [MOD-031] dropped. -/
def NuCDef.toNuDef (d : NuCDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef, mspec := d.mspec }

/-- The firing view of a definition with a match: the firing view of its `TransDef`, with its
match (as `NuDef.toNuTrans`). -/
def NuCDef.toNuTrans (d : NuCDef N A K) : NuTrans N K := ⟨d.toTransDef.toTrans, d.mspec⟩

/-- A composition definition fires as the ν definition it reads as. -/
theorem NuCDef.toNuTrans_eq (d : NuCDef N A K) : d.toNuTrans = d.toNuDef.toNuTrans := rfl

/-- The two firing views agree: `NuCDef.toNuTrans` is `NuDef.toNuTrans ∘ NuCDef.toNuDef`. -/
theorem NuCDef.toNuTrans_comp :
    (NuCDef.toNuTrans : NuCDef N A K → NuTrans N K) = NuDef.toNuTrans ∘ NuCDef.toNuDef := rfl

/-! ## The builders -/

section Build
variable [DecidableEq N]

/-- The first element of `l` already seen (in `seen`, or earlier in `l`); `none` when there is
none. `firstRepeat [] l` is the first repeated element of `l`. -/
def firstRepeat : List N → List N → Option N
  | _, [] => none
  | seen, p :: ps => if p ∈ seen then some p else firstRepeat (p :: seen) ps

/-- `firstRepeat` finds nothing exactly when `l` has no repeat and meets no element of `seen`. -/
theorem firstRepeat_eq_none_iff : ∀ (seen l : List N),
    firstRepeat seen l = none ↔ l.Nodup ∧ ∀ p ∈ l, p ∉ seen
  | seen, [] => by simp [firstRepeat]
  | seen, p :: ps => by
    have ih := firstRepeat_eq_none_iff (p :: seen) ps
    by_cases h : p ∈ seen
    · simp only [firstRepeat, h, if_true, reduceCtorEq, false_iff, not_and]
      intro _ hall
      exact hall p List.mem_cons_self h
    · simp only [firstRepeat, h, if_false, ih, List.nodup_cons, List.mem_cons, not_or,
        forall_eq_or_imp]
      constructor
      · rintro ⟨hnd, hall⟩
        exact ⟨⟨fun hp => (hall p hp).1 rfl, hnd⟩, id, fun q hq => (hall q hq).2⟩
      · rintro ⟨⟨hp, hnd⟩, -, hall⟩
        exact ⟨hnd, fun q hq => ⟨fun e => hp (e ▸ hq), hall q hq⟩⟩

variable [ToString N]

/-- Building a match that keys place `p` twice: Rust's message, as a stand-in (the spec fixes
none). -/
def msgKeyTwice (p : N) : String :=
  "MatchSpec correlates input place '" ++ toString p ++ "' twice. A match names each correlated " ++
    "input once (NU-020); the input's cardinality sets how many tokens of the name it takes."

/-- Building a match from `n < 2` keys (ruling D37 (a)): Rust's message, as a stand-in. -/
def msgFewKeys (n : Nat) : String :=
  "MatchSpec must correlate at least 2 input places, got " ++ toString n

/-- Building transition `t` whose match keys place `p` twice: Rust's message, as a stand-in. -/
def msgTransKeyTwice (t : Trans N) (p : N) : String :=
  "Transition '" ++ t.core.name ++ "': " ++ msgKeyTwice p

/-- Building transition `t` whose match keys the non-input place `p`: Rust's message, as a
stand-in. -/
def msgKeyNonInput (t : Trans N) (p : N) : String :=
  "Transition '" ++ t.core.name ++ "': MatchSpec correlates non-input place '" ++ toString p ++ "'"

/-- Building transition `t` whose match declares relay target `p` twice ([NU-054]). -/
def msgRelayTwice (t : Trans N) (p : N) : String :=
  "Transition '" ++ t.core.name ++ "': relay target '" ++ toString p ++
    "' is declared twice (NU-054)"

/-- Building transition `t` whose relay target `p` is not an output place ([NU-054]). -/
def msgRelayNotOutput (t : Trans N) (p : N) : String :=
  "Transition '" ++ t.core.name ++ "': relay target '" ++ toString p ++
    "' is not an output of the transition (NU-054)"

/-- The relay checks of [NU-054], per relay target in declaration order: declared twice, then
not an output place. -/
def relayScan (t : Trans N) : List N → List N → Option String
  | _, [] => none
  | seen, p :: ps =>
    if p ∈ seen then some (msgRelayTwice t p)
    else if OutputArc t p then relayScan t (p :: seen) ps
    else some (msgRelayNotOutput t p)

/-- The relay checks pass exactly when the targets are distinct, meet no element of `seen`, and
are output places. -/
theorem relayScan_eq_none_iff (t : Trans N) : ∀ (seen l : List N),
    relayScan t seen l = none ↔ l.Nodup ∧ (∀ p ∈ l, p ∉ seen) ∧ ∀ p ∈ l, OutputArc t p
  | seen, [] => by simp [relayScan]
  | seen, p :: ps => by
    have ih := relayScan_eq_none_iff t (p :: seen) ps
    by_cases h : p ∈ seen
    · simp only [relayScan, h, if_true, reduceCtorEq, false_iff, not_and]
      intro _ hall
      exact absurd h (hall p List.mem_cons_self)
    · by_cases ho : OutputArc t p
      · simp only [relayScan, h, ho, if_true, if_false, ih, List.nodup_cons, List.mem_cons,
          not_or, forall_eq_or_imp]
        constructor
        · rintro ⟨hnd, hall, hout⟩
          exact ⟨⟨fun hp => (hall p hp).1 rfl, hnd⟩, ⟨id, fun q hq => (hall q hq).2⟩, trivial, hout⟩
        · rintro ⟨⟨hp, hnd⟩, ⟨-, hall⟩, -, hout⟩
          exact ⟨hnd, fun q hq => ⟨fun e => hp (e ▸ hq), hall q hq⟩, hout⟩
      · simp only [relayScan, h, ho, if_false, reduceCtorEq, false_iff, not_and]
        intro _ _ hout
        exact ho (hout p List.mem_cons_self)

/-- The match checks of a transition ([NU-020], [NU-054]), after every other build-time check: a
place keyed twice, then a key on a place that is not an input place, then the relay checks. -/
def nuChecks (t : NuTrans N K) : Option String :=
  match t.mspec with
  | none => none
  | some ms =>
    match firstRepeat [] ms.keyPlaces with
    | some p => some (msgTransKeyTwice t.base p)
    | none =>
      match ms.keyPlaces.find? (fun p => decide (p ∉ inPlaces t.base)) with
      | some p => some (msgKeyNonInput t.base p)
      | none => relayScan t.base [] ms.relayPlaces

/-- **The reference ν transition builder**: `refBuild`'s checks on the transition without its
match, then the match checks (`nuChecks`). `none`: the transition builds. -/
def refNuBuild (t : NuTrans N K) : Option String :=
  match refBuild t.base with
  | some e => some e
  | none => nuChecks t

/-- **The reference match builder** (ruling D37 (a)): fewer than two keys fail, then a place
keyed twice. `none`: the match builds. Relay targets are checked when the transition is built,
not here (`rust/libpetri-core/src/match_spec.rs:220-235`). -/
def refMatchBuild (ks : List (N × K)) : Option String :=
  if ks.length < 2 then some (msgFewKeys ks.length)
  else match firstRepeat [] (ks.map Prod.fst) with
    | some p => some (msgKeyTwice p)
    | none => none

end Build

/- The reference builders are the witness models of NU-020's build block. -/
#spec_witness refNuBuild
#spec_witness refMatchBuild

section BuildFacts
variable [DecidableEq N] [ToString N]

/-- The match checks pass exactly when the match keys distinct input places and its relay
targets pass [NU-054]'s checks. -/
theorem nuChecks_eq_none_iff (t : NuTrans N K) :
    nuChecks t = none ↔ ∀ ms, t.mspec = some ms →
      KeysDistinct ms ∧ KeysOnInputs t ms ∧ RelaysOK t ms := by
  unfold nuChecks
  cases hm : t.mspec with
  | none => simp
  | some ms =>
    simp only [Option.some.injEq, forall_eq']
    cases hr : firstRepeat [] ms.keyPlaces with
    | some p =>
      refine iff_of_false (by simp) (fun h => ?_)
      have := ((firstRepeat_eq_none_iff [] ms.keyPlaces).2 ⟨h.1, by simp⟩)
      rw [hr] at this; cases this
    | none =>
      have hd : KeysDistinct ms := ((firstRepeat_eq_none_iff [] ms.keyPlaces).1 hr).1
      simp only
      cases hf : ms.keyPlaces.find? (fun p => decide (p ∉ inPlaces t.base)) with
      | some p =>
        refine iff_of_false (by simp) (fun h => ?_)
        have hp := List.find?_some hf
        have hmem := List.mem_of_find?_eq_some hf
        simp only [decide_eq_true_eq] at hp
        exact hp (h.2.1 p hmem)
      | none =>
        rw [List.find?_eq_none] at hf
        have hk : KeysOnInputs t ms := fun p hp => by simpa using hf p hp
        simp only
        rw [relayScan_eq_none_iff]
        simp only [List.not_mem_nil, not_false_eq_true, implies_true, true_and]
        exact ⟨fun h => ⟨hd, hk, h⟩, fun h => h.2.2⟩

/-- **The reference ν builder accepts exactly the transitions that build** (`NuBuilds`). -/
theorem refNuBuild_eq_none_iff (t : NuTrans N K) : refNuBuild t = none ↔ NuBuilds t := by
  unfold refNuBuild NuBuilds
  cases hb : refBuild t.base with
  | some e =>
    refine iff_of_false (by simp) (fun h => ?_)
    have := (refBuild_eq_none_iff t.base).2 h.1
    rw [hb] at this; cases this
  | none =>
    simp only
    rw [nuChecks_eq_none_iff]
    exact ⟨fun h => ⟨(refBuild_eq_none_iff t.base).1 hb, h⟩, fun h => h.2⟩

/-- The reference ν builder extends the reference builder: it answers as `refBuild` on a
transition without a match and on one `refBuild` rejects. -/
theorem refNuBuild_extends : NuBuildExtends (refNuBuild (N := N) (K := K)) refBuild := by
  intro t h
  unfold refNuBuild
  cases hb : refBuild t.base with
  | some e => rfl
  | none =>
    rcases h with h | h
    · exact absurd hb h
    · simp [nuChecks, h]

/-- **The reference match builder accepts exactly** two or more keys on distinct places. -/
theorem refMatchBuild_eq_none_iff (ks : List (N × K)) :
    refMatchBuild ks = none ↔ 2 ≤ ks.length ∧ (ks.map Prod.fst).Nodup := by
  unfold refMatchBuild
  by_cases hl : ks.length < 2
  · rw [if_pos hl]; exact iff_of_false (by simp) (fun h => by omega)
  · rw [if_neg hl]
    cases hr : firstRepeat [] (ks.map Prod.fst) with
    | some p =>
      refine iff_of_false (by simp) (fun h => ?_)
      have := (firstRepeat_eq_none_iff [] _).2 ⟨h.2, by simp⟩
      rw [hr] at this; cases this
    | none =>
      exact iff_of_true rfl ⟨by omega, ((firstRepeat_eq_none_iff [] _).1 hr).1⟩

end BuildFacts

/-! ## The reference ν firing -/

section Fire
variable [DecidableEq N] [LinearOrder Nm]

/-- **RefNuFire, the reference ν firing.** Without a match: `RefQFire`, no chosen name. With a
match: the NU-022 selection on the marking picks `n`; the transition is enabled on its counts
([CORE-022]); the emission is an outcome the output spec offers under the correlated takes of `n`;
every token emitted to a relay target projects to `n` ([NU-054]); the action receives
`nuDelivered` (the first tokens of `n` on each correlated input, the FIFO prefix elsewhere, the
heads of the read places after the inputs are taken); and the firing leaves the consumed marking
with the emission appended at the tails ([EXEC-020]). -/
def RefNuFire : NuFireRel N V Nm := fun t M c δ e M' =>
  match t.mspec with
  | none => c = none ∧ RefQFire t.base M δ e M'
  | some ms => ∃ n, c = some n ∧ refSelect (matchIn ms t M) = some n ∧
      Enabled t.base (qCount M) ∧
      (∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst)) ∧
      RelayOk ms n e ∧ δ = nuDelivered ms t M n ∧ M' = qAppend (nuConsume ms t M n) e

end Fire

/- The reference ν firing is the witness model of the ν firing blocks. -/
#spec_witness RefNuFire

section FireFacts
variable [DecidableEq N] [LinearOrder Nm]

/-- A matched reference firing, unfolded. -/
theorem refNuFire_matched {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)}
    (h : t.mspec = some ms) (M : QMarking N (Stamped V)) (c δ e M') :
    RefNuFire t M c δ e M' ↔ ∃ n, c = some n ∧ refSelect (matchIn ms t M) = some n ∧
      Enabled t.base (qCount M) ∧
      (∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst)) ∧
      RelayOk ms n e ∧ δ = nuDelivered ms t M n ∧ M' = qAppend (nuConsume ms t M n) e := by
  unfold RefNuFire; rw [h]

/-- **Link (a)**: without a match, RefNuFire is RefQFire, so every queue and count block speaks
of the match-free ν firings. -/
theorem refNuFire_restrictsTo :
    NuRestrictsTo (RefNuFire (N := N) (V := V) (Nm := Nm)) RefQFire := by
  intro t h M c δ e M'
  unfold RefNuFire; rw [h]

/-- The chosen name of a reference firing is the reference selection's answer. -/
theorem refNuFire_selectsBy :
    NuSelectsBy (RefNuFire (N := N) (V := V) (Nm := Nm)) refSelect := by
  intro t ms h M c δ e M' hf
  obtain ⟨n, rfl, hs, -⟩ := (refNuFire_matched h M c δ e M').1 hf
  exact hs.symm

/-- **The reference covers**: every enabled matched transition fires under its selected name with
every offered, relay-checked emission. -/
theorem refNuFire_covers : NuCovers (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  intro t ms h M n hs hen e hdep hrel
  exact ⟨_, _, (refNuFire_matched h M _ _ e _).2
    ⟨n, rfl, refSelect_eq_some_iff.2 hs, hen, hdep, hrel, rfl, rfl⟩⟩

/-- A matched reference firing chooses a `Selected` name: eligible, and least by (earliest
stamp, name). -/
theorem refNuFire_selected {t : NuTrans N (KeyFn V Nm)} {ms : MatchSpec N (KeyFn V Nm)}
    (h : t.mspec = some ms) {M : QMarking N (Stamped V)} {c δ e M'}
    (hf : RefNuFire t M c δ e M') : ∃ n, c = some n ∧ Selected (matchIn ms t M) n := by
  obtain ⟨n, rfl, hs, -⟩ := (refNuFire_matched h M c δ e M').1 hf
  exact ⟨n, rfl, refSelect_eq_some_iff.1 hs⟩

/-- A reference firing is ν-enabled at its source marking. -/
theorem refNuFire_nuEnabled {t : NuTrans N (KeyFn V Nm)} {M : QMarking N (Stamped V)} {c δ e M'}
    (hf : RefNuFire t M c δ e M') : NuEnabled t M := by
  cases h : t.mspec with
  | none =>
    obtain ⟨-, hq⟩ := (refNuFire_restrictsTo t h M c δ e M').1 hf
    exact ⟨hq.1, fun ms hms => by rw [h] at hms; cases hms⟩
  | some ms =>
    obtain ⟨n, -, hs, hen, -⟩ := (refNuFire_matched h M c δ e M').1 hf
    refine ⟨hen, fun ms' hms' => ?_⟩
    rw [h] at hms'; cases hms'
    exact ⟨n, (refSelect_eq_some_iff.1 hs).1⟩

end FireFacts

/-! ## The net layer -/

section Net
variable [DecidableEq N] [LinearOrder Nm]

/-- One reference ν step of the transitions `X`: some transition of `X` fires. -/
def RefNuStep (X : List (NuTrans N (KeyFn V Nm))) (M M' : QMarking N (Stamped V)) : Prop :=
  ∃ t ∈ X, ∃ c δ e, RefNuFire t M c δ e M'

/-- Reference ν reachability: the reflexive transitive closure of `RefNuStep`. -/
def RefNuReach (X : List (NuTrans N (KeyFn V Nm))) :
    QMarking N (Stamped V) → QMarking N (Stamped V) → Prop :=
  Relation.ReflTransGen (RefNuStep X)

/-- **ν rest** ([VER-002]'s quiescence, "enabled" read name-aware): every transition of `X` that
is ν-enabled at `M` is reapable. -/
def NuRests (X : List (NuTrans N (KeyFn V Nm))) (M : QMarking N (Stamped V)) : Prop :=
  ∀ t ∈ X, NuEnabled t M → t.base.reapable = true

end Net

end Libpetri.Reference
