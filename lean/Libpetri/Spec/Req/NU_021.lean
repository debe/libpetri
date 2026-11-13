import Mathlib.Data.List.Forall2
import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Req.NU_020
import Libpetri.Spec.Text.NU_021

set_option linter.missingDocs true

/-!
# NU-021: Match as the sole per-token filter (`spec/12-nu-nets.md`)

NU-021 says that the name correlation of [NU-020] is the only test a firing applies to a token's
value. There is no unary value predicate on an input (guards were removed in [IO-006]), so which
tokens a firing takes is decided by queue position and, on a correlated input, by the name the
token's value projects to.

The block (kind B, over a ν firing relation `R`) has three lines:

* **Value-blindness.** Take two markings that hold tokens at the same queue positions with the
  same `createdAt`, whose values differ only by a pairing the transition's keys and relay targets
  cannot see (on each place, each key and each relay target there gives the two values of a pair
  the same name, or no name to both; on a place nothing reads, any values may be paired). Then a
  firing from the first marking is matched by a firing from the second with the same chosen name,
  for every emission that differs by the same pairing, and the tokens delivered and left differ
  again only by that pairing. The pairing `ρ` is a relation between values for each place, so the
  line covers both directions and non-injective relabellings at once.
* **Only the chosen name is delivered** on a correlated input (AC2, first half).
* **Every token of another name stays**, in its order, whatever its value (AC2, second half).

The first line is the case `σ = id` of the **equivariance lemma** `refNuFire_transfer`: the
reference ν firing commutes with every value correspondence `ρ` and every strictly monotone
renaming `σ` of names, when the keys of the second transition read off related values the
`σ`-image of what the first transition's keys read. NU-001's behaviour line (ruling D96 (a))
reuses it at `ρ` = equality.

The witness is `RefNuFire` (`Reference/Nu.lean`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Corresponding tokens, markings, emissions and deliveries -/

section Corr
variable {N V₁ V₂ Nm₁ Nm₂ : Type}

/-- Two stamped tokens correspond under `ρ`: their values are related and their `createdAt`
stamps are equal. -/
def NuTokRel (ρ : V₁ → V₂ → Prop) (x : Stamped V₁) (y : Stamped V₂) : Prop :=
  ρ x.val y.val ∧ x.stamp = y.stamp

/-- Two queue markings correspond under the pairing `ρ`, which may differ from place to place:
every place `p` holds as many tokens in both, and the tokens at the same queue position of `p`
correspond under `ρ p`. -/
def NuQRel (ρ : N → V₁ → V₂ → Prop) (M₁ : QMarking N (Stamped V₁))
    (M₂ : QMarking N (Stamped V₂)) : Prop :=
  ∀ p, List.Forall₂ (NuTokRel (ρ p)) (M₁ p) (M₂ p)

/-- Two emissions correspond under `ρ`: the same places in the same order, and the two tokens
sent to a place `p` correspond under `ρ p`. -/
def NuEmRel (ρ : N → V₁ → V₂ → Prop) (e₁ : List (N × Stamped V₁)) (e₂ : List (N × Stamped V₂)) :
    Prop :=
  List.Forall₂ (fun a b => a.1 = b.1 ∧ NuTokRel (ρ a.1) a.2 b.2) e₁ e₂

/-- Two deliveries correspond under `ρ`: per place, the delivered input tokens correspond, and so
do the read tokens. -/
def NuDelRel (ρ : N → V₁ → V₂ → Prop) (δ₁ : QDelivered N (Stamped V₁))
    (δ₂ : QDelivered N (Stamped V₂)) : Prop :=
  NuQRel ρ δ₁.inputs δ₂.inputs ∧ NuQRel ρ δ₁.reads δ₂.reads

/-- Two key projections correspond under `ρ` and the renaming `σ`: on related values the second
gives the `σ`-image of what the first gives (no name for no name). -/
def NuKeyFnRel (ρ : V₁ → V₂ → Prop) (σ : Nm₁ → Nm₂) (f₁ : KeyFn V₁ Nm₁) (f₂ : KeyFn V₂ Nm₂) :
    Prop :=
  ∀ v w, ρ v w → f₂ w = (f₁ v).map σ

/-- Two keys (or two relay targets) correspond: the same place, and projections that correspond
under the pairing of that place. -/
def NuKeyRel (ρ : N → V₁ → V₂ → Prop) (σ : Nm₁ → Nm₂) (k₁ : N × KeyFn V₁ Nm₁)
    (k₂ : N × KeyFn V₂ Nm₂) : Prop :=
  k₁.1 = k₂.1 ∧ NuKeyFnRel (ρ k₁.1) σ k₁.2 k₂.2

/-- `t₂` is `t₁` with its key projections renamed: the same transition without the match, both
without a match or both with one, and then the same keyed places and relay targets in the same
order with corresponding projections. -/
def NuRenames (ρ : N → V₁ → V₂ → Prop) (σ : Nm₁ → Nm₂) (t₁ : NuTrans N (KeyFn V₁ Nm₁))
    (t₂ : NuTrans N (KeyFn V₂ Nm₂)) : Prop :=
  t₁.base = t₂.base ∧
    Option.Rel (fun ms₁ ms₂ => List.Forall₂ (NuKeyRel ρ σ) ms₁.keys ms₂.keys ∧
      List.Forall₂ (NuKeyRel ρ σ) ms₁.relays ms₂.relays) t₁.mspec t₂.mspec

end Corr

/-- **The keys of `t` cannot tell values paired by `ρ` apart**: if `t` has a match, every key on
a place `p`, and every relay target at `p`, gives two values that `ρ p` pairs the same name, or no
name to both. On a place no key and no relay target reads, `ρ` may pair any values; a transition
without a match has no key, so every `ρ` qualifies. -/
def KeepsNames {N V Nm : Type} (t : NuTrans N (KeyFn V Nm)) (ρ : N → V → V → Prop) : Prop :=
  ∀ ms, t.mspec = some ms →
    (∀ k ∈ ms.keys, ∀ v w, ρ k.1 v w → k.2 v = k.2 w) ∧
      ∀ r ∈ ms.relays, ∀ v w, ρ r.1 v w → r.2 v = r.2 w

/-! ## List facts under a correspondence -/

section ListFacts
variable {α β : Type} {R : α → β → Prop}

/-- Every element of the right list has a partner in the left one. -/
theorem nu021_exists_left : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; exact absurd hb List.not_mem_nil
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Filters that agree on related elements keep related lists related. -/
theorem nu021_filter {P : α → Bool} {Q : β → Bool} (hPQ : ∀ a b, R a b → P a = Q b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.filter P) (l₂.filter Q) := by
  intro l₁ l₂ h
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hPQ a b hab]
    cases Q b
    · exact ih
    · exact .cons hab ih

/-- The heads of related lists are related. -/
theorem nu021_head {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    List.Forall₂ R l₁.head?.toList l₂.head?.toList := by
  cases h with
  | nil => exact .nil
  | cons hab _ => exact .cons hab .nil

/-- Repeating related lists keeps them related. -/
theorem nu021_replicate {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    ∀ k, List.Forall₂ R (List.replicate k l₁).flatten (List.replicate k l₂).flatten
  | 0 => by simp
  | k + 1 => by
    simp only [List.replicate_succ, List.flatten_cons]
    exact List.rel_append h (nu021_replicate h k)

end ListFacts

/-! ## The queue operations respect a correspondence -/

section QueueFacts
variable {N V₁ V₂ : Type} [DecidableEq N] {ρ : N → V₁ → V₂ → Prop}
  {M₁ : QMarking N (Stamped V₁)} {M₂ : QMarking N (Stamped V₂)}

omit [DecidableEq N] in
/-- Corresponding markings have the same token counts. -/
theorem nu021_qCount (hM : NuQRel ρ M₁ M₂) : qCount M₁ = qCount M₂ :=
  funext fun p => (hM p).length_eq

omit [DecidableEq N] in
/-- Corresponding emissions go to the same places. -/
theorem nu021_places {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)}
    (he : NuEmRel ρ e₁ e₂) : e₁.map Prod.fst = e₂.map Prod.fst := by
  induction he with
  | nil => rfl
  | cons hab _ ih => simp [hab.1, ih]

/-- Corresponding emissions put corresponding tokens on every place. -/
theorem nu021_emitted {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)}
    (he : NuEmRel ρ e₁ e₂) (p : N) :
    List.Forall₂ (NuTokRel (ρ p)) (qEmittedTo e₁ p) (qEmittedTo e₂ p) := by
  induction he with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    unfold qEmittedTo at ih ⊢
    rw [List.filter_cons, List.filter_cons, ← hab.1]
    by_cases h : a.1 = p
    · have h2 := hab.2
      rw [h] at h2
      simp only [h, decide_true, ↓reduceIte, List.map_cons]
      exact .cons h2 ih
    · simp only [h, decide_false]
      exact ih

/-- Appending corresponding emissions to corresponding markings. -/
theorem nu021_qAppend {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)}
    (hM : NuQRel ρ M₁ M₂) (he : NuEmRel ρ e₁ e₂) : NuQRel ρ (qAppend M₁ e₁) (qAppend M₂ e₂) :=
  fun p => by
    rw [qAppend_apply, qAppend_apply]
    exact List.rel_append (hM p) (nu021_emitted he p)

/-- Corresponding markings deliver corresponding read tokens. -/
theorem nu021_qReadsBag (hM : NuQRel ρ M₁ M₂) (reads : List N) :
    NuQRel ρ (qReadsBag M₁ reads) (qReadsBag M₂ reads) := fun p => by
  rw [qReadsBag_apply, qReadsBag_apply]
  exact nu021_replicate (nu021_head (hM p)) _

/-- Corresponding markings: the queue firing takes as many tokens from each place. -/
theorem nu021_qTake (hM : NuQRel ρ M₁ M₂) (t : Trans N) (p : N) : qTake M₁ t p = qTake M₂ t p := by
  unfold qTake; rw [nu021_qCount hM]

/-- **The queue firing is value-blind**: from a corresponding marking, with a corresponding
emission, the queue firing delivers corresponding tokens and leaves a corresponding marking. -/
theorem nu021_refQFire {t : Trans N} {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)}
    {δ₁ M₁'} (hM : NuQRel ρ M₁ M₂) (he : NuEmRel ρ e₁ e₂) (hf : RefQFire t M₁ δ₁ e₁ M₁') :
    ∃ δ₂ M₂', RefQFire t M₂ δ₂ e₂ M₂' ∧ NuDelRel ρ δ₁ δ₂ ∧ NuQRel ρ M₁' M₂' := by
  obtain ⟨hen, ⟨ch, hdep⟩, rfl, rfl⟩ := hf
  have hpost : NuQRel ρ (qPostInput M₁ t) (qPostInput M₂ t) := fun p => by
    unfold qPostInput; rw [nu021_qTake hM]; exact List.forall₂_drop _ (hM p)
  refine ⟨qDelivered M₂ t, qFire M₂ t e₂, ⟨?_, ⟨ch, ?_⟩, rfl, rfl⟩, ⟨fun p => ?_, ?_⟩, ?_⟩
  · rw [← nu021_qCount hM]; exact hen
  · rw [← nu021_qCount hM, ← nu021_places he]; exact hdep
  · show List.Forall₂ _ (qInputs M₁ t p) (qInputs M₂ t p)
    unfold qInputs; rw [nu021_qTake hM]; exact List.forall₂_take _ (hM p)
  · exact nu021_qReadsBag hpost _
  · refine nu021_qAppend (fun p => ?_) he
    unfold qConsume
    split
    · exact .nil
    · exact hpost p

end QueueFacts

/-! ## The name operations respect a correspondence and a renaming -/

section NameFacts
variable {N V₁ V₂ Nm₁ Nm₂ : Type} {ρ : N → V₁ → V₂ → Prop} {r : V₁ → V₂ → Prop}
  {σ : Nm₁ → Nm₂}

/-- Under an injective renaming, a renamed name is the renamed chosen name exactly when the name
is the chosen name. -/
theorem nu021_map_eq_some {σ : Nm₁ → Nm₂} (hσ : Function.Injective σ) (o : Option Nm₁) (n : Nm₁) :
    (o.map σ = some (σ n)) ↔ o = some n := by
  cases o <;> simp [hσ.eq_iff]

/-- The tokens of the chosen name correspond. -/
theorem nu021_named [DecidableEq Nm₁] [DecidableEq Nm₂] (hσ : Function.Injective σ)
    {f₁ : KeyFn V₁ Nm₁} {f₂ : KeyFn V₂ Nm₂} (hf : NuKeyFnRel r σ f₁ f₂) (n : Nm₁)
    {l₁ : List (Stamped V₁)} {l₂ : List (Stamped V₂)} (h : List.Forall₂ (NuTokRel r) l₁ l₂) :
    List.Forall₂ (NuTokRel r) (named f₁ n l₁) (named f₂ (σ n) l₂) :=
  nu021_filter (fun x y hxy => by
    simp only [hf _ _ hxy.1, nu021_map_eq_some hσ]) h

/-- Removing the first `k` tokens of the chosen name keeps corresponding queues corresponding. -/
theorem nu021_dropNamed [DecidableEq Nm₁] [DecidableEq Nm₂] (hσ : Function.Injective σ)
    {f₁ : KeyFn V₁ Nm₁} {f₂ : KeyFn V₂ Nm₂} (hf : NuKeyFnRel r σ f₁ f₂) (n : Nm₁)
    {l₁ : List (Stamped V₁)} {l₂ : List (Stamped V₂)} (h : List.Forall₂ (NuTokRel r) l₁ l₂) :
    ∀ k, List.Forall₂ (NuTokRel r) (dropNamed f₁ n k l₁) (dropNamed f₂ (σ n) k l₂) := by
  induction h with
  | nil => intro k; cases k <;> exact .nil
  | @cons x y xs ys hxy _ ih =>
    intro k
    cases k with
    | zero => simpa [dropNamed] using List.Forall₂.cons hxy (by simpa [dropNamed] using ih 0)
    | succ k =>
      have hp : f₂ y.val = some (σ n) ↔ f₁ x.val = some n := by
        rw [hf _ _ hxy.1, nu021_map_eq_some hσ]
      by_cases h1 : f₁ x.val = some n
      · have h2 : f₂ y.val = some (σ n) := hp.2 h1
        simp only [dropNamed, h1, h2, if_true]
        exact ih k
      · have h2 : ¬ f₂ y.val = some (σ n) := fun h => h1 (hp.1 h)
        simp only [dropNamed, h1, h2, if_false]
        exact .cons hxy (ih (k + 1))

/-- The first key on a place corresponds when the key lists correspond. -/
theorem nu021_find [DecidableEq N] {ks₁ : List (N × KeyFn V₁ Nm₁)} {ks₂ : List (N × KeyFn V₂ Nm₂)}
    (h : List.Forall₂ (NuKeyRel ρ σ) ks₁ ks₂) (p : N) :
    Option.Rel (NuKeyFnRel (ρ p) σ) ((ks₁.find? fun k => decide (k.1 = p)).map Prod.snd)
      ((ks₂.find? fun k => decide (k.1 = p)).map Prod.snd) := by
  induction h with
  | nil => exact .none
  | @cons k₁ k₂ _ _ hk _ ih =>
    rw [List.find?_cons, List.find?_cons, hk.1]
    by_cases hc : k₂.1 = p
    · have h2 := hk.2
      rw [hk.1, hc] at h2
      simp only [hc, decide_true]; exact .some h2
    · simp only [hc, decide_false]; exact ih

/-- The key of every place corresponds when the matches' keys correspond. -/
theorem nu021_keyAt [DecidableEq N] {ms₁ : MatchSpec N (KeyFn V₁ Nm₁)}
    {ms₂ : MatchSpec N (KeyFn V₂ Nm₂)} (h : List.Forall₂ (NuKeyRel ρ σ) ms₁.keys ms₂.keys)
    (p : N) : Option.Rel (NuKeyFnRel (ρ p) σ) (keyAt ms₁ p) (keyAt ms₂ p) :=
  nu021_find h p

/-- The selection input with every name renamed by `σ`. -/
def nuMapIn (σ : Nm₁ → Nm₂) (I : MatchIn Nm₁) : MatchIn Nm₂ :=
  ⟨I.keys.map fun k => (k.1.map fun x => (σ x.1, x.2), k.2)⟩

/-- Reading the names and stamps of corresponding queues through corresponding keys. -/
theorem nu021_filterMap {f₁ : KeyFn V₁ Nm₁} {f₂ : KeyFn V₂ Nm₂} (hf : NuKeyFnRel r σ f₁ f₂)
    {l₁ : List (Stamped V₁)} {l₂ : List (Stamped V₂)} (h : List.Forall₂ (NuTokRel r) l₁ l₂) :
    l₂.filterMap (fun x => (f₂ x.val).map fun n => (n, x.stamp)) =
      (l₁.filterMap (fun x => (f₁ x.val).map fun n => (n, x.stamp))).map
        (fun x => (σ x.1, x.2)) := by
  induction h with
  | nil => rfl
  | @cons x y _ _ hxy _ ih =>
    rw [List.filterMap_cons, List.filterMap_cons, hf _ _ hxy.1, ← hxy.2]
    cases f₁ x.val <;> simp [ih]

/-- **The selection input of corresponding markings** is the renamed selection input. -/
theorem nu021_matchIn [DecidableEq N] {t₁ : NuTrans N (KeyFn V₁ Nm₁)}
    {t₂ : NuTrans N (KeyFn V₂ Nm₂)} {ms₁ : MatchSpec N (KeyFn V₁ Nm₁)}
    {ms₂ : MatchSpec N (KeyFn V₂ Nm₂)} (hb : t₁.base = t₂.base)
    (hk : List.Forall₂ (NuKeyRel ρ σ) ms₁.keys ms₂.keys)
    {M₁ : QMarking N (Stamped V₁)} {M₂ : QMarking N (Stamped V₂)} (hM : NuQRel ρ M₁ M₂) :
    matchIn ms₂ t₂ M₂ = nuMapIn σ (matchIn ms₁ t₁ M₁) := by
  unfold matchIn nuMapIn
  simp only [List.map_map, MatchIn.mk.injEq]
  generalize ms₁.keys = ks₁ at hk
  generalize ms₂.keys = ks₂ at hk
  induction hk with
  | nil => rfl
  | @cons k₁ k₂ _ _ hk _ ih =>
    simp only [List.map_cons, ih, Function.comp_apply, List.cons.injEq, and_true]
    rw [← hk.1, nu021_filterMap hk.2 (hM k₁.1), hb]

end NameFacts

/-! ## The selection commutes with a strictly monotone renaming -/

section SelectMap
variable {Nm₁ Nm₂ : Type}

/-- The stamps of a renamed name in a renamed input are the stamps of the name. -/
theorem nu021_stamps [DecidableEq Nm₁] [DecidableEq Nm₂] {σ : Nm₁ → Nm₂}
    (hσ : Function.Injective σ) (q : List (Nm₁ × Int)) (n : Nm₁) :
    stamps (q.map fun x => (σ x.1, x.2)) (σ n) = stamps q n := by
  simp [stamps, List.filter_map, Function.comp_def, hσ.eq_iff]

/-- A renamed name is eligible in the renamed input exactly when the name is eligible. -/
theorem nu021_eligible [DecidableEq Nm₁] [DecidableEq Nm₂] {σ : Nm₁ → Nm₂}
    (hσ : Function.Injective σ) (I : MatchIn Nm₁) (n : Nm₁) :
    eligible (nuMapIn σ I) (σ n) = eligible I n := by
  simp [eligible, nuMapIn, List.all_map, Function.comp_def, nu021_stamps hσ]

/-- A renamed name has the stamp of the name in the renamed input. -/
theorem nu021_oldest [DecidableEq Nm₁] [DecidableEq Nm₂] {σ : Nm₁ → Nm₂}
    (hσ : Function.Injective σ) (I : MatchIn Nm₁) (n : Nm₁) :
    oldest (nuMapIn σ I) (σ n) = oldest I n := by
  simp [oldest, nuMapIn, List.flatMap_map, nu021_stamps hσ]

variable [LinearOrder Nm₁] [LinearOrder Nm₂]

/-- A strictly monotone renaming keeps the selection order. -/
theorem nu021_selKey {σ : Nm₁ → Nm₂} (hσ : StrictMono σ) (I : MatchIn Nm₁) (n m : Nm₁) :
    selKey (nuMapIn σ I) (σ n) ≤ selKey (nuMapIn σ I) (σ m) ↔ selKey I n ≤ selKey I m := by
  unfold selKey
  rw [Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_le_toLex, nu021_oldest hσ.injective,
    nu021_oldest hσ.injective, hσ.le_iff_le]

omit [LinearOrder Nm₁] in
/-- Every eligible name of a renamed input is a renamed name. -/
theorem nu021_eligible_image {σ : Nm₁ → Nm₂} (I : MatchIn Nm₁) {m : Nm₂}
    (h : eligible (nuMapIn σ I) m = true) : ∃ n, m = σ n := by
  have hm := mem_cands.2 h
  unfold cands nuMapIn at hm
  cases hk : I.keys with
  | nil => simp [hk] at hm
  | cons k ks =>
    simp only [hk, List.map_cons, List.head?_cons, Option.map_some, Option.getD_some,
      List.map_map, List.mem_filter, List.mem_map, Function.comp_apply] at hm
    obtain ⟨⟨x, -, rfl⟩, -⟩ := hm
    exact ⟨x.1, rfl⟩

/-- **The reference selection commutes with a strictly monotone renaming**: if it picks `n`, it
picks `σ n` on the renamed input. -/
theorem nu021_refSelect {σ : Nm₁ → Nm₂} (hσ : StrictMono σ) {I : MatchIn Nm₁} {n : Nm₁}
    (h : refSelect I = some n) : refSelect (nuMapIn σ I) = some (σ n) := by
  have hs := refSelect_eq_some_iff.1 h
  refine refSelect_eq_some_iff.2 ⟨by rw [nu021_eligible hσ.injective]; exact hs.1, fun m hm => ?_⟩
  obtain ⟨m', rfl⟩ := nu021_eligible_image I hm
  rw [nu021_eligible hσ.injective] at hm
  exact (nu021_selKey hσ I n m').2 (hs.2 m' hm)

end SelectMap

/-! ## The equivariance lemma -/

section Transfer
variable {N V₁ V₂ Nm₁ Nm₂ : Type} [DecidableEq N] [LinearOrder Nm₁] [LinearOrder Nm₂]
  {ρ : N → V₁ → V₂ → Prop} {σ : Nm₁ → Nm₂}
  {t₁ : NuTrans N (KeyFn V₁ Nm₁)} {t₂ : NuTrans N (KeyFn V₂ Nm₂)}
  {ms₁ : MatchSpec N (KeyFn V₁ Nm₁)} {ms₂ : MatchSpec N (KeyFn V₂ Nm₂)}
  {M₁ : QMarking N (Stamped V₁)} {M₂ : QMarking N (Stamped V₂)}

/-- The correlated take of a renamed name from a corresponding marking is the correlated take of
the name. -/
theorem nu021_corrTake (hσ : Function.Injective σ) (hb : t₁.base = t₂.base)
    (hk : List.Forall₂ (NuKeyRel ρ σ) ms₁.keys ms₂.keys) (hM : NuQRel ρ M₁ M₂) (n : Nm₁) :
    corrTake ms₂ t₂ M₂ (σ n) = corrTake ms₁ t₁ M₁ n := funext fun p => by
  have hr := nu021_keyAt hk p
  unfold corrTake
  cases h1 : keyAt ms₁ p with
  | none =>
    cases h2 : keyAt ms₂ p with
    | none => rw [hb, nu021_qTake hM]
    | some f₂ => rw [h1, h2] at hr; cases hr
  | some f₁ =>
    cases h2 : keyAt ms₂ p with
    | none => rw [h1, h2] at hr; cases hr
    | some f₂ =>
      rw [h1, h2] at hr
      cases hr with
      | some hf => dsimp only; rw [hb, (nu021_named hσ hf n (hM p)).length_eq]

/-- The tokens a firing takes from corresponding markings, for a name and its renaming,
correspond; so do the markings after the inputs are taken. -/
theorem nu021_nuInputs_nuPost (hσ : Function.Injective σ) (hb : t₁.base = t₂.base)
    (hk : List.Forall₂ (NuKeyRel ρ σ) ms₁.keys ms₂.keys) (hM : NuQRel ρ M₁ M₂) (n : Nm₁) :
    NuQRel ρ (nuInputs ms₁ t₁ M₁ n) (nuInputs ms₂ t₂ M₂ (σ n)) ∧
      NuQRel ρ (nuPost ms₁ t₁ M₁ n) (nuPost ms₂ t₂ M₂ (σ n)) := by
  have hc := nu021_corrTake hσ hb hk hM n
  refine ⟨fun p => ?_, fun p => ?_⟩
  · have hr := nu021_keyAt hk p
    unfold nuInputs
    rw [hc]
    cases h1 : keyAt ms₁ p with
    | none =>
      cases h2 : keyAt ms₂ p with
      | none => unfold qInputs; rw [hb, nu021_qTake hM]; exact List.forall₂_take _ (hM p)
      | some f₂ => rw [h1, h2] at hr; cases hr
    | some f₁ =>
      cases h2 : keyAt ms₂ p with
      | none => rw [h1, h2] at hr; cases hr
      | some f₂ =>
        rw [h1, h2] at hr
        cases hr with
        | some hf => exact List.forall₂_take _ (nu021_named hσ hf n (hM p))
  · have hr := nu021_keyAt hk p
    unfold nuPost
    rw [hc]
    cases h1 : keyAt ms₁ p with
    | none =>
      cases h2 : keyAt ms₂ p with
      | none => unfold qPostInput; rw [hb, nu021_qTake hM]; exact List.forall₂_drop _ (hM p)
      | some f₂ => rw [h1, h2] at hr; cases hr
    | some f₁ =>
      cases h2 : keyAt ms₂ p with
      | none => rw [h1, h2] at hr; cases hr
      | some f₂ =>
        rw [h1, h2] at hr
        cases hr with
        | some hf => exact nu021_dropNamed hσ hf n (hM p) _

omit [LinearOrder Nm₁] [LinearOrder Nm₂] in
/-- A relay check passed under a name passes under its renaming, for a corresponding emission. -/
theorem nu021_relayOk (hr : List.Forall₂ (NuKeyRel ρ σ) ms₁.relays ms₂.relays) {n : Nm₁}
    {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)} (he : NuEmRel ρ e₁ e₂)
    (h : RelayOk ms₁ n e₁) : RelayOk ms₂ (σ n) e₂ := by
  intro r₂ hr₂ y hy
  obtain ⟨r₁, hr₁, hkr⟩ := nu021_exists_left hr r₂ hr₂
  obtain ⟨x, hx, hxy⟩ := nu021_exists_left (nu021_emitted he r₂.1) y hy
  have hv := hxy.1
  rw [← hkr.1] at hv
  rw [hkr.2 _ _ hv, h r₁ hr₁ x (by rw [hkr.1]; exact hx)]
  rfl

/-- **The equivariance lemma.** Let `t₂` be `t₁` with its key projections renamed through the
value correspondence `ρ` and the strictly monotone name renaming `σ` (`NuRenames`). Then every
reference firing of `t₁` from `M₁` with chosen name `c` and emission `e₁` is matched, from every
corresponding marking `M₂` and for every corresponding emission `e₂`, by a reference firing of
`t₂` with chosen name `c` renamed, delivering corresponding tokens and leaving a corresponding
marking. -/
theorem refNuFire_transfer (hσ : StrictMono σ) (ht : NuRenames ρ σ t₁ t₂) (hM : NuQRel ρ M₁ M₂)
    {e₁ : List (N × Stamped V₁)} {e₂ : List (N × Stamped V₂)} (he : NuEmRel ρ e₁ e₂)
    {c δ₁ M₁'} (hf : RefNuFire t₁ M₁ c δ₁ e₁ M₁') :
    ∃ δ₂ M₂', RefNuFire t₂ M₂ (c.map σ) δ₂ e₂ M₂' ∧ NuDelRel ρ δ₁ δ₂ ∧ NuQRel ρ M₁' M₂' := by
  obtain ⟨hb, hms⟩ := ht
  revert hms
  cases h1 : t₁.mspec with
  | none =>
    cases h2 : t₂.mspec with
    | some _ => intro hms; cases hms
    | none =>
      intro _
      obtain ⟨rfl, hq⟩ := (refNuFire_restrictsTo t₁ h1 M₁ c δ₁ e₁ M₁').1 hf
      obtain ⟨δ₂, M₂', hq2, hd, hm⟩ := nu021_refQFire hM he hq
      rw [hb] at hq2
      exact ⟨δ₂, M₂', (refNuFire_restrictsTo t₂ h2 M₂ _ δ₂ e₂ M₂').2 ⟨rfl, hq2⟩, hd, hm⟩
  | some ms₁ =>
    cases h2 : t₂.mspec with
    | none => intro hms; cases hms
    | some ms₂ =>
      intro hms
      cases hms with
      | some hrel =>
      obtain ⟨hk, hr⟩ := hrel
      obtain ⟨n, rfl, hsel, hen, ⟨ch, hdep⟩, hrok, rfl, rfl⟩ :=
        (refNuFire_matched h1 M₁ c δ₁ e₁ M₁').1 hf
      obtain ⟨hin, hpost⟩ := nu021_nuInputs_nuPost hσ.injective hb hk hM n
      refine ⟨nuDelivered ms₂ t₂ M₂ (σ n), qAppend (nuConsume ms₂ t₂ M₂ (σ n)) e₂,
        (refNuFire_matched h2 M₂ _ _ e₂ _).2 ⟨σ n, rfl, ?_, ?_, ⟨ch, ?_⟩, ?_, rfl, rfl⟩,
        ⟨hin, ?_⟩, ?_⟩
      · rw [nu021_matchIn hb hk hM]; exact nu021_refSelect hσ hsel
      · rw [← hb, ← nu021_qCount hM]; exact hen
      · rw [nu021_corrTake hσ.injective hb hk hM n, ← hb, ← nu021_places he]; exact hdep
      · exact nu021_relayOk hr he hrok
      · show NuQRel ρ (qReadsBag _ _) (qReadsBag _ _)
        rw [← hb]; exact nu021_qReadsBag hpost _
      · refine nu021_qAppend (fun p => ?_) he
        unfold nuConsume
        rw [← hb]
        split
        · exact .nil
        · exact hpost p

end Transfer

/-! ## NU-021: Match as the Sole Per-Token Filter -/

requirement NU_021
  id "NU-021"
  title "Match as the Sole Per-Token Filter"
  kind B
  scope "every executor; one firing of any transition, with or without a match specification"
  source verbatim "spec/12-nu-nets.md"
  covers NU_021.s1, NU_021.s2, NU_021.s3
  reading "For every transition t and every pairing ρ, which gives for each place p a relation ρ p between token values, under which every key of t on a place p and every relay target of t at p gives two values that ρ p relates the same name, or no name to both (KeepsNames; on a place that no key and no relay target reads ρ p is free, and a transition without a match has no key, so every ρ qualifies): for every firing of t in R from M with chosen name c, delivery δ and emission e, leaving M', every marking M₂ that corresponds to M under ρ (every place p holds as many tokens in both, and the tokens at one queue position of p have values that ρ p relates and the same createdAt) and every emission e₂ that corresponds to e (the same places in the same order, the tokens sent to p related by ρ p with the same createdAt), R has a firing of t from M₂ with chosen name c and emission e₂ whose delivery corresponds to δ, place by place, and whose result corresponds to M'."
          "For every transition t with match specification ms and every firing of t in R with chosen name n: every token delivered from a correlated input p with key f has f(value) = n."
          "For every transition t with match specification ms and every firing of t in R from M to M' with chosen name n: for every correlated input p with key f that is not a reset place of t, the tokens of M' p whose key does not give n are the tokens of M p whose key does not give n, in order, followed by the tokens emitted to p whose key does not give n, in emission order."
  assumes "The model is a ν firing relation R over queue markings of stamped tokens (NuFireRel), as for NU_020_enable: R t M c δ e M' says that t fires from M with chosen name c (none without a match), delivers δ, the action emits e, and the firing leaves M'. 'Two markings differ only by a pairing a transition's keys and relay targets cannot tell apart' is a pairing ρ (a relation between values for each place) with KeepsNames and NuQRel. It is a relation and not a relabelling function, so that one line covers both directions (the graph of a relabelling g and its converse) and relabellings that merge values; a merging ρ is what rules out a firing that also compares payloads (NU_021_forbids_samePayload), which the graph of a function alone would not. It is given per place so that the values on a place no key reads are free: that rules out a name test on a plain input (NU_021_forbids_keyAll), which one pairing shared by every place would let through, since that pairing has to keep every key's name on every place."
          "'Token selection is determined by position and, on correlated inputs, by name equality, nothing else' is read with createdAt: the tie-break of NU-020 reads the earliest createdAt of each name (ruling D31 (a)), so the first line keeps createdAt fixed at every queue position and lets only values vary (nu-a map; editorial NUA-10 item 5 adds the tie-break to the sentence). A key projection is a function of the value (KeyFn); a projection whose answer changes between calls on one value is outside the model, and so is a key that throws: Python reads a raise as no name (make_py_projection in rust/libpetri-py/src/model.rs), Java catches only ClassCastException (MatchSpec.MatchKey.extract in java/src/main/java/org/libpetri/core/MatchSpec.java) and TypeScript catches nothing (typescript/src/runtime/match-engine.ts, buildNameIndex), so there a throwing key propagates out of the executor; whether the spec states this or a runtime defect is recorded is open (NU_020_enable's assumes). Ruling D37 (a): a token whose key yields no name has no name on that input, and the pairing must keep 'no name' as well, so whether a token has a name at all is the second per-token test the line allows, and the only other one."
          "The first line is the case σ = id of the equivariance lemma refNuFire_transfer, which also renames names by a strictly monotone σ; NU-001's behaviour line (ruling D96 (a)) uses it with ρ the equality of values. The line covers transitions without a match too, where it says that the queue firing reads no value at all (EXEC-010). A test on the content of a name rather than on a value, such as one that treats the name 0 or the empty name as no name, passes every pairing and so passes this line. It is ruled out by NU_020_enable's tie-break line when another name is eligible, by the conjunct NuCovers of the consistency theorem when no other name is, and it is the subject of NU-001's renaming line."
          "AC1, first half ('No input specification variant exposes a value predicate') is API shape, tested and not proven: the runtimes' input specifications carry a place and a cardinality only (enum In in rust/libpetri-core/src/input.rs, Arc.In in java/src/main/java/org/libpetri/core/Arc.java, type In in typescript/src/core/in.ts), and so does the model's: nu021_inSpecShape shows that an input arc of the model (Novel.Seam.NInSpec, Novel/Seam/Net.lean) is exactly a place and a cardinality. AC1, second half ('the enablement check evaluates no per-token predicate other than name equality on correlated inputs') is the first line: being enabled is having a firing, which the line carries to every corresponding marking. Because the pairing is free on a place no key reads, the line also forbids a name test on a plain input (NU_021_forbids_keyAll), as NU_020_frame's plain-input line does. The guarded firing that IO-006 removed meets every line of NU-020 (nu021_guarded_meets_NU_020) and the last two lines here, and only the first line rules it out (NU_021_mutant_noBlind_killed)."
          "AC2 ('A correlated input consumes only tokens carrying the chosen name; a same-place token of a different name is left behind regardless of its value.') is the second and third lines, with 'regardless of its value' carried by the first. Both lines follow from NU_020_take (the correlated take is a prefix of the tokens of the chosen name, and dropNamed keeps every other token in order); they are stated here because AC2 is NU-021's. A correlated input that is also a reset place ends holding only the deposited tokens (NU_020_frame), so the third line leaves it out. The second and third lines speak of firings with a chosen name; that every firing of a transition with a match has one is NU_020_enable's second line. The test derivation (a ν-join over a place holding tokens of two names) is NU_021_nonvacuous_ac2."
          "The paragraph on a future unary input filter (it would apply first, and the name correlation would run over the tokens that pass it) binds no implementation and has no observable today; it becomes a non-normative note (editorial NUA-10 item 3, ruling D20) and is not a line. The Depends-on line named the removed IO-006; it now names EXEC-010 and IO-007, which the body cites (NUA-10 item 4)."
          "Timing, priority and the firing pass are not in the model, as for NU-020. Event payloads carry token values (EVT), but they are observations of a firing, not part of the firing relation."
          "The first line is an existence clause ('it shall also fire ... for every emission that differs from its emission by the same pairing'), kept as a line as a recorded exception to the rule that offers go into coverage conjuncts: value-blindness is a relation between two firings, and the forbidden models it must rule out (a guard, a payload comparison, a name test on a plain input) only remove firings, so a 2-safety form (when both fire, they agree) would let every one of them through. The emission is the action's choice, so the line reads 'for every emission' as every emission of the action that differs by the pairing. The runtimes agree: the selection reads only names and createdAt (select_match_name in rust/libpetri-runtime/src/match_engine.rs, selectMatchName in typescript/src/runtime/match-engine.ts, java/src/main/java/org/libpetri/runtime/MatchEngine.java selectMatchName). Whether to split the line into a 2-safety line and a coverage conjunct is open."
  signoff "2026-11-13 dc8ec6a7e9585374 ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      (∀ t ρ, KeepsNames t ρ → ∀ c δ e,
        on (fun M M' => R t M c δ e M'), shall (fun M M' =>
          ∀ M₂ e₂, NuQRel ρ M M₂ → NuEmRel ρ e e₂ →
            ∃ δ₂ M₂', R t M₂ c δ₂ e₂ M₂' ∧ NuDelRel ρ δ δ₂ ∧ NuQRel ρ M' M₂')) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun _ _ =>
          ∀ p f, keyAt ms p = some f → ∀ x ∈ δ.inputs p, f x.val = some n)) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M M' =>
          ∀ p f, keyAt ms p = some f → p ∉ t.base.core.resets →
            (M' p).filter (fun x => !decide (f x.val = some n)) =
              (M p).filter (fun x => !decide (f x.val = some n)) ++
                (qEmittedTo e p).filter (fun x => !decide (f x.val = some n))))

/- The pinned readable form of NU-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_021 : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  (∀ (t : NuTrans N (KeyFn V Nm)) (ρ : N → V → V → Prop),
      KeepsNames t ρ →
        ∀ (c : Option Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
          on fun M M' => R t M c δ e M', shall fun M M' =>
            ∀ (M₂ : QMarking N (Stamped V)) (e₂ : List (N × Stamped V)),
              NuQRel ρ M M₂ → NuEmRel ρ e e₂ → ∃ δ₂ M₂', R t M₂ c δ₂ e₂ M₂' ∧ NuDelRel ρ δ δ₂ ∧ NuQRel ρ M' M₂') ∧
    (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
        t.mspec = some ms →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun x x_1 =>
              ∀ (p : N) (f : KeyFn V Nm), keyAt ms p = some f → ∀ x ∈ δ.inputs p, f x.val = some n) ∧
      ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
        t.mspec = some ms →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun M M' =>
              ∀ (p : N) (f : KeyFn V Nm),
                keyAt ms p = some f →
                  p ∉ t.base.core.resets →
                    List.filter (fun x => !decide (f x.val = some n)) (M' p) =
                      List.filter (fun x => !decide (f x.val = some n)) (M p) ++
                        List.filter (fun x => !decide (f x.val = some n)) (qEmittedTo e p)
-/
#guard_msgs in #print NU_021

/-! ## Holds -/

/-- Keys that cannot tell `ρ`-related values apart are their own renaming under `ρ` and the
identity on names. -/
theorem nu021_keepsNames_renames {N V Nm : Type} {t : NuTrans N (KeyFn V Nm)}
    {ρ : N → V → V → Prop} (h : KeepsNames t ρ) : NuRenames ρ id t t := by
  refine ⟨rfl, ?_⟩
  cases hm : t.mspec with
  | none => exact .none
  | some ms =>
    have hk := h ms hm
    exact .some ⟨List.forall₂_same.2 fun k hk' => ⟨rfl, fun v w hvw => by
        simp [(hk.1 k hk' v w hvw).symm]⟩,
      List.forall₂_same.2 fun r hr => ⟨rfl, fun v w hvw => by
        simp [(hk.2 r hr v w hvw).symm]⟩⟩

/-- ✓ RefNuFire satisfies NU-021: by the equivariance lemma at the identity renaming it fires
alike from markings its keys cannot tell apart, and by NU-020's correlated take it delivers only
tokens of the chosen name and keeps every other token in its order. -/
@[evidence holds NU_021]
theorem NU_021_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_021 (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun t ρ hk c δ e M M' hf M₂ e₂ hM he => ?_,
    fun t ms hm n δ e M M' hf p f hp x hx => ?_, fun t ms hm n δ e M M' hf p f hp hr => ?_⟩
  · obtain ⟨δ₂, M₂', h1, h2, h3⟩ :=
      refNuFire_transfer strictMono_id (nu021_keepsNames_renames hk) hM he hf
    simp only [Option.map_id, id_eq] at h1
    exact ⟨δ₂, M₂', h1, h2, h3⟩
  · rw [NU_020_take_reference.1 t ms hm n δ e M M' hf p f hp] at hx
    exact of_decide_eq_true (List.mem_filter.1 (List.mem_of_mem_take hx)).2
  · rw [NU_020_take_reference.2 t ms hm n δ e M M' hf p f hp hr, List.filter_append,
      dropNamed_filter_other]

/-! ## Examples: a key that reads the tens digit -/

/-- The tens key: a token's name is its value divided by ten, so 11 and 12 both have name 1. -/
def nu021_tens : KeyFn Nat Nat := fun v => some (v / 10)

/-- A match that keys places 0 and 1 with the tens key. -/
def nu021_ms : MatchSpec Nat (KeyFn Nat Nat) := { keys := [(0, nu021_tens), (1, nu021_tens)] }

/-- The join of places 0 and 1 (one token each), correlated by the tens key, depositing nothing. -/
def nu021_join : NuTrans Nat (KeyFn Nat Nat) :=
  { base := (nu020_join .one .one).base, mspec := some nu021_ms }

/-- The pairing that pairs, on every place, values with the same tens digit: the tens key cannot
tell them apart. -/
def nu021_sameTens (_p v w : Nat) : Prop := v / 10 = w / 10

/-- Place 0 holds 11@0, place 1 holds 11@1. -/
def nu021_M₁ : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 11 0] else if p = 1 then [nu020_tok 11 1] else []

/-- Place 0 holds 12@0, place 1 holds 11@1: `nu021_M₁` with the value at place 0 changed within
its tens. -/
def nu021_M₂ : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 12 0] else if p = 1 then [nu020_tok 11 1] else []

/-- The tens key cannot tell values with the same tens digit apart. -/
theorem nu021_keeps : KeepsNames nu021_join nu021_sameTens := by
  intro ms hm
  simp only [nu021_join, Option.some.injEq] at hm
  subst hm
  refine ⟨fun k hk v w hvw => ?_, fun r hr => ?_⟩
  · simp only [nu021_ms, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hvw' : v / 10 = w / 10 := hvw
    rcases hk with rfl | rfl <;> simp [nu021_tens, hvw']
  · simp [nu021_ms] at hr

/-- The two markings correspond under `nu021_sameTens`. -/
theorem nu021_rel : NuQRel nu021_sameTens nu021_M₁ nu021_M₂ := by
  intro p
  unfold nu021_M₁ nu021_M₂
  split_ifs <;> simp [NuTokRel, nu021_sameTens, nu020_tok]

/-- ✓ Worked example (value-blindness). Place 0 holds 11 in one marking and 12 in the other;
place 1 holds 11 in both, with the same stamps. The tens key gives 11 and 12 the same name 1, so
it cannot tell the markings apart, and the reference join fires from both with name 1. -/
@[evidence nonvacuous NU_021]
theorem NU_021_nonvacuous_blind :
    RefNuFire nu021_join nu021_M₁ (some 1) (nuDelivered nu021_ms nu021_join nu021_M₁ 1) []
        (qAppend (nuConsume nu021_ms nu021_join nu021_M₁ 1) []) ∧
      RefNuFire nu021_join nu021_M₂ (some 1) (nuDelivered nu021_ms nu021_join nu021_M₂ 1) []
        (qAppend (nuConsume nu021_ms nu021_join nu021_M₂ 1) []) ∧
      KeepsNames nu021_join nu021_sameTens ∧ NuQRel nu021_sameTens nu021_M₁ nu021_M₂ ∧
      nu021_M₁ 0 ≠ nu021_M₂ 0 :=
  ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩, fun r hr => by simp [nu021_ms] at hr, rfl, rfl⟩,
    ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩, fun r hr => by simp [nu021_ms] at hr, rfl, rfl⟩,
    nu021_keeps, nu021_rel, by decide⟩

/-- ✓ Worked example (AC2, the test derivation). Branch A holds X@0, Y@1, X@2 and is a correlated
`All`; branch B holds X@3. The join chooses X, takes both X tokens from A and leaves Y@1 there,
whatever its value. -/
@[evidence nonvacuous NU_021]
theorem NU_021_nonvacuous_ac2 :
    RefNuFire (nu020_join .all .one) nu020_ac3 (some 1)
        (nuDelivered nu020_ms (nu020_join .all .one) nu020_ac3 1) []
        (qAppend (nuConsume nu020_ms (nu020_join .all .one) nu020_ac3 1) []) ∧
      nuInputs nu020_ms (nu020_join .all .one) nu020_ac3 1 0 = [nu020_tok 1 0, nu020_tok 1 2] ∧
      qAppend (nuConsume nu020_ms (nu020_join .all .one) nu020_ac3 1) [] 0 = [nu020_tok 2 1] :=
  ⟨NU_020_ac3.1, by decide, by decide⟩

/-! ## Forbidden models -/

/-- The guarded firing (the guard [IO-006] removed): the reference firing, and every token it
takes from an input place passes the value test `P`. -/
def nu021_guarded (P : Nat → Bool) : NuFireRel Nat Nat Nat := fun t M c δ e M' =>
  RefNuFire t M c δ e M' ∧ ∀ s ∈ t.base.core.inputs, ∀ x ∈ δ.inputs s.place, P x.val = true

/-- A value test: the value ends in the digit 1. -/
def nu021_endsIn1 (v : Nat) : Bool := v % 10 == 1

/-- The reference join on `nu021_M₁`, as a guarded firing: both tokens it takes are 11, which
pass the guard. -/
theorem nu021_guarded_fires :
    nu021_guarded nu021_endsIn1 nu021_join nu021_M₁ (some 1)
      (nuDelivered nu021_ms nu021_join nu021_M₁ 1) []
      (qAppend (nuConsume nu021_ms nu021_join nu021_M₁ 1) []) :=
  ⟨NU_021_nonvacuous_blind.1, by decide⟩

/-- ✗ Worked example: a guard that accepts values ending in 1. The join fires on place 0 = [11@0],
place 1 = [11@1]. On place 0 = [12@0], place 1 = [11@1], which the tens key cannot tell apart, the
guard rejects 12, so the join cannot fire there; the first line fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_guard : ¬ NU_021 (nu021_guarded nu021_endsIn1) := by
  intro h
  obtain ⟨δ₂, M₂', ⟨hf₂, hg⟩, -, -⟩ := h.1 nu021_join nu021_sameTens nu021_keeps _ _ _ _ _
    nu021_guarded_fires nu021_M₂ [] nu021_rel .nil
  obtain ⟨n, hn, -, -, -, -, rfl, -⟩ :=
    (refNuFire_matched (t := nu021_join) (ms := nu021_ms) rfl _ _ _ _ _).1 hf₂
  cases hn
  revert hg
  decide

/-- The firing that also requires equal payloads: the reference firing, and every token it takes
has the same value. -/
def nu021_samePayload : NuFireRel Nat Nat Nat := fun t M c δ e M' =>
  RefNuFire t M c δ e M' ∧ ∀ s ∈ t.base.core.inputs, ∀ s' ∈ t.base.core.inputs,
    ∀ x ∈ δ.inputs s.place, ∀ y ∈ δ.inputs s'.place, x.val = y.val

/-- ✗ Worked example: a matcher that also requires the joined tokens to have equal values fires on
place 0 = [11@0], place 1 = [11@1], but not on place 0 = [12@0], place 1 = [11@1], although both
tokens there have name 1 too; the first line fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_samePayload : ¬ NU_021 nu021_samePayload := by
  intro h
  have hf : nu021_samePayload nu021_join nu021_M₁ (some 1)
      (nuDelivered nu021_ms nu021_join nu021_M₁ 1) []
      (qAppend (nuConsume nu021_ms nu021_join nu021_M₁ 1) []) :=
    ⟨NU_021_nonvacuous_blind.1, by decide⟩
  obtain ⟨δ₂, M₂', ⟨hf₂, hg⟩, -, -⟩ := h.1 nu021_join nu021_sameTens nu021_keeps _ _ _ _ _
    hf nu021_M₂ [] nu021_rel .nil
  obtain ⟨n, hn, -, -, -, -, rfl, -⟩ :=
    (refNuFire_matched (t := nu021_join) (ms := nu021_ms) rfl _ _ _ _ _).1 hf₂
  cases hn
  revert hg
  decide

/-- The delivery of a bag keyed by value: the first token of each value, in order. -/
def nu021_dedup (l : List (Stamped Nat)) : List (Stamped Nat) :=
  l.foldr (fun x acc => x :: acc.filter (fun y => y.val != x.val)) []

/-- The reference with every delivered input list de-duplicated by value: the slip of keying the
per-place input bag by token value (a `Set` or a `Map` keyed by `token.value`) instead of a list
of tokens. -/
def nu021_dedupMut : NuMut where
  deliver ms t M n := ⟨fun p => nu021_dedup (nuInputs ms t M n p),
    qReadsBag (nuPost ms t M n) t.base.core.reads⟩

/-- The tens join with a correlated `All` on place 0. -/
def nu021_allJoin : NuTrans Nat (KeyFn Nat Nat) :=
  { base := (nu020_join .all .one).base, mspec := some nu021_ms }

/-- A = [11@0, 11@1], B = [11@2]. -/
def nu021_twin : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 11 0, nu020_tok 11 1] else if p = 1 then [nu020_tok 11 2] else []

/-- A = [11@0, 12@1], B = [11@2]: the second token of A changed within its tens. -/
def nu021_twin₂ : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 11 0, nu020_tok 12 1] else if p = 1 then [nu020_tok 11 2] else []

/-- ✗ Worked example: a delivery that collapses equal values. The tens join takes every token of
name 1 from A. On A = [11@0, 11@1], B = [11@2] the de-duplicated bag hands the action one token
from A; on A = [11@0, 12@1], B = [11@2], which the tens key cannot tell apart, it hands two. Which
tokens reach the action depends on payload equality, so the first line fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_dedup : ¬ NU_021 nu021_dedupMut.fire := by
  intro h
  have hk : KeepsNames nu021_allJoin nu021_sameTens := by
    intro ms hm
    simp only [nu021_allJoin, Option.some.injEq] at hm
    subst hm
    refine ⟨fun k hk v w hvw => ?_, fun r hr => ?_⟩
    · simp only [nu021_ms, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hvw' : v / 10 = w / 10 := hvw
      rcases hk with rfl | rfl <;> simp [nu021_tens, hvw']
    · simp [nu021_ms] at hr
  have hrel : NuQRel nu021_sameTens nu021_twin nu021_twin₂ := by
    intro p
    unfold nu021_twin nu021_twin₂
    split_ifs <;> simp [NuTokRel, nu021_sameTens, nu020_tok]
  have hf : nu021_dedupMut.fire nu021_allJoin nu021_twin (some 1)
      (nu021_dedupMut.deliver nu021_ms nu021_allJoin nu021_twin 1) []
      (qAppend (nuConsume nu021_ms nu021_allJoin nu021_twin 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu021_ms] at hr, rfl, rfl⟩
  obtain ⟨δ₂, M₂', hf₂, hd, -⟩ := h.1 nu021_allJoin nu021_sameTens hk _ _ _ _ _ hf nu021_twin₂ []
    hrel .nil
  obtain ⟨n, hn, -, -, -, -, rfl, -⟩ := hf₂
  cases hn
  have := (hd.1 0).length_eq
  revert this
  decide

/-- ✗ Worked example: a correlated input that takes its head whatever its name. On branch A =
[X@0, Y@1], branch B = [Y@0, X@1] the join chooses X but takes Y@0 from B; the second line
fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_headAnyName :
    ¬ NU_021 (NuMut.fire { deliver := fun _ t M _ => qDelivered M t.base }) := by
  intro h
  have hf : NuMut.fire { deliver := fun _ t M _ => qDelivered M t.base } (nu020_join .one .one)
      nu020_ac1 (some 1) (qDelivered nu020_ac1 (nu020_join .one .one).base) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.1 (nu020_join .one .one) nu020_ms rfl _ _ _ _ _ hf 1 nu020_key rfl
  revert this
  decide

/-- ✗ Worked example: a correlated `All` that empties its place. On branch A = [X@0, Y@1, X@2],
branch B = [X@3] the join chooses X and A ends empty, so Y@1, of another name, is not left behind;
the third line fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_drain : ¬ NU_021 nu020_drain.fire := by
  intro h
  have hf : nu020_drain.fire (nu020_join .all .one) nu020_ac3 (some 1)
      (nuDelivered nu020_ms (nu020_join .all .one) nu020_ac3 1) []
      (nu020_drain.result nu020_ms (nu020_join .all .one) nu020_ac3 1 []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.2 (nu020_join .all .one) nu020_ms rfl _ _ _ _ _ hf 0 nu020_key rfl (by decide)
  revert this
  decide

/-- The match with every input place of `t` keyed too, the plain ones by the match's first key: the
slip of a consume loop that falls back to the first key when an input arc has none. -/
def nu021_keyAllMs (t : NuTrans Nat (KeyFn Nat Nat)) (ms : MatchSpec Nat (KeyFn Nat Nat)) :
    MatchSpec Nat (KeyFn Nat Nat) :=
  { keys := ms.keys ++ (t.base.core.inputs.map (·.place)).filterMap
      (fun p => ms.keys.head?.map fun k => (p, k.2)),
    relays := ms.relays }

/-- The firing that treats every input of a join as correlated: the reference firing of `t` with
`nu021_keyAllMs` as its match. -/
def nu021_keyAll : NuFireRel Nat Nat Nat := fun t =>
  RefNuFire { t with mspec := t.mspec.map (nu021_keyAllMs t) }

/-- The join of correlated places 0 and 1 (keyed by the value) with a plain input 2, one token
each. -/
def nu021_plainJoin : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩, ⟨2, .one⟩],
                        inhibitors := [], reads := [], resets := [] }, out := none }
    mspec := some nu020_ms }

/-- Place 0 holds X@0, place 1 holds X@1 and the plain place 2 holds Y@0, X@1 (X = 1, Y = 2), or,
with `x` = 2, Y@0, Y@1. -/
def nu021_plainM (x : Nat) : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0] else if p = 1 then [nu020_tok 1 1]
  else if p = 2 then [nu020_tok 2 0, nu020_tok x 1] else []

/-- The pairing that pairs equal values on the keyed places 0 and 1 and any two values on the
plain place 2. -/
def nu021_anyOn2 (p v w : Nat) : Prop := p = 2 ∨ v = w

/-- ✗ Worked example: a join whose plain input is also filtered by the name. On place 0 = [X@0],
place 1 = [X@1] and plain place 2 = [Y@0, X@1] it fires with X and takes X@1 from place 2, not its
head Y@0. No key reads place 2, so the first line lets its values change freely: with place 2 =
[Y@0, Y@1] the join must fire with X again, but this firing finds no X on place 2 and cannot fire;
the first line fails. -/
@[evidence forbids NU_021]
theorem NU_021_forbids_keyAll : ¬ NU_021 nu021_keyAll := by
  intro h
  have hm : ({ nu021_plainJoin with
      mspec := nu021_plainJoin.mspec.map (nu021_keyAllMs nu021_plainJoin) } :
        NuTrans Nat (KeyFn Nat Nat)).mspec = some (nu021_keyAllMs nu021_plainJoin nu020_ms) := rfl
  have hf : nu021_keyAll nu021_plainJoin (nu021_plainM 1) (some 1)
      (nuDelivered (nu021_keyAllMs nu021_plainJoin nu020_ms) _ (nu021_plainM 1) 1) []
      (qAppend (nuConsume (nu021_keyAllMs nu021_plainJoin nu020_ms) _ (nu021_plainM 1) 1) []) :=
    (refNuFire_matched hm _ _ _ _ _).2 ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu021_keyAllMs, nu020_ms] at hr, rfl, rfl⟩
  have hk : KeepsNames nu021_plainJoin nu021_anyOn2 := by
    intro ms hms
    simp only [nu021_plainJoin, Option.some.injEq] at hms
    subst hms
    refine ⟨fun k hk v w hvw => ?_, fun r hr => by simp [nu020_ms] at hr⟩
    simp only [nu020_ms, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> rcases hvw with h | rfl <;> simp_all
  have hM : NuQRel nu021_anyOn2 (nu021_plainM 1) (nu021_plainM 2) := by
    intro p
    unfold nu021_plainM
    split_ifs <;> simp_all [NuTokRel, nu021_anyOn2, nu020_tok]
  obtain ⟨δ₂, M₂', hf₂, -⟩ := h.1 nu021_plainJoin nu021_anyOn2 hk _ _ _ _ _ hf
    (nu021_plainM 2) [] hM .nil
  obtain ⟨n, hn, hsel, -⟩ := (refNuFire_matched hm _ _ _ _ _).1 hf₂
  cases hn
  revert hsel
  decide

/-! ## The input arc carries no value predicate -/

/-- An input arc of the model is a place and a cardinality and nothing else: there is no field
for a value test that a firing could read (AC1, first half; the runtimes' input specifications
have the same two fields). -/
def nu021_inSpecShape {N : Type} : NInSpec N ≃ N × Card where
  toFun s := (s.place, s.card)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## A mutant: the block without value-blindness -/

/-- The guarded firing meets every line of NU-020: it is the reference firing with an extra
condition, and every NU-020 firing line constrains only the firings that happen. -/
theorem nu021_guarded_meets_NU_020 (P : Nat → Bool) :
    NU_020_enable (nu021_guarded P) ∧ NU_020_take (nu021_guarded P) ∧
      NU_020_frame (nu021_guarded P) := by
  obtain ⟨e1, e2, e3⟩ := NU_020_enable_reference (N := Nat) (V := Nat) (Nm := Nat)
  obtain ⟨t1, t2⟩ := NU_020_take_reference (N := Nat) (V := Nat) (Nm := Nat)
  obtain ⟨f1, f2, f3, f4, f5⟩ := NU_020_frame_reference (N := Nat) (V := Nat) (Nm := Nat)
  exact ⟨⟨fun t ms hm c δ e M M' hf => e1 t ms hm c δ e M M' hf.1,
      fun t ms hm c δ e M M' hf => e2 t ms hm c δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => e3 t ms hm n δ e M M' hf.1⟩,
    ⟨fun t ms hm n δ e M M' hf => t1 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => t2 t ms hm n δ e M M' hf.1⟩,
    ⟨fun t ms hm n δ e M M' hf => f1 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f2 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f3 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f4 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => f5 t ms hm n δ e M M' hf.1⟩⟩

/-- NU-021 without its first line: only the chosen name is delivered and other names stay. -/
def NU_021_mutant_noBlind {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (R : NuFireRel N V Nm) : Prop :=
  (∀ t ms, t.mspec = some ms → ∀ n δ e,
    on (fun M M' => R t M (some n) δ e M'), shall (fun _ _ =>
      ∀ p f, keyAt ms p = some f → ∀ x ∈ δ.inputs p, f x.val = some n)) ∧
  (∀ t ms, t.mspec = some ms → ∀ n δ e,
    on (fun M M' => R t M (some n) δ e M'), shall (fun M M' =>
      ∀ p f, keyAt ms p = some f → p ∉ t.base.core.resets →
        (M' p).filter (fun x => !decide (f x.val = some n)) =
          (M p).filter (fun x => !decide (f x.val = some n)) ++
            (qEmittedTo e p).filter (fun x => !decide (f x.val = some n))))

/-- ✗ Worked example: the guarded firing takes only tokens of the chosen name and leaves the others
in order, so it meets the last two lines (and every line of NU-020, `nu021_guarded_meets_NU_020`),
yet it refuses to fire on 12 where it fires on 11 although the key gives both the same name. Only
the value-blindness line rules out a value test on inputs. -/
@[evidence mutant NU_021]
theorem NU_021_mutant_noBlind_killed :
    NU_021_mutant_noBlind (nu021_guarded nu021_endsIn1) ∧ ¬ NU_021 (nu021_guarded nu021_endsIn1) :=
  ⟨⟨fun t ms hm n δ e M M' hf => NU_021_reference.2.1 t ms hm n δ e M M' hf.1,
      fun t ms hm n δ e M M' hf => NU_021_reference.2.2 t ms hm n δ e M M' hf.1⟩,
    NU_021_forbids_guard⟩

end Libpetri.Spec
