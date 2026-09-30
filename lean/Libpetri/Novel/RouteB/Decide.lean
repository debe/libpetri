import Libpetri.Interning
import Mathlib.Data.List.Basic

/-!
# Route B's build loop and verdict: truncation never proves, prefix violations stand

Model of `NameStateClassGraph::build_until` and `verify_via_name_scg` / `decide`
(`nu_scg_verifier.rs`, the shared predicate `graph_decision.rs::decide_over_classes`) over any
`Interning.lean` explorer `E`:

* the stored classes `cls` are the first-seen representatives (`intern_base` / `intern_names` /
  `index_of`: a successor whose key is stored is not stored again, and exploration continues from
  the stored object);
* the queue is FIFO over indices in discovery order and every new class is appended to both the
  class list and the queue, so the queue is always `cls.drop exp`, where `exp` is `expanded`: the
  loop pops `cls[exp]`, and `expanded` is advanced only after a full expansion. That is how the
  model represents the queue, and why "expanded" is exactly `index < expanded_count` — the premise
  `Enumeration.lean` had to assume;
* the budget check (`classes.len() >= max_classes`) precedes each expansion and truncates; the
  total budget / cancellation (`total_budget::cut`) is an oracle `cut` and stops; running out of
  Lean fuel counts as a stop;
* `stopAt`: the early stop of [VER-012] AC5 — the first *fresh* class the predicate holds for ends
  the build, the parent not counted as expanded (the initial class is tested first);
* the mint counter `c` only grows and is fresh for every stored class (`Inv.bound`);
* `quiescentAt reap i`: `NameClasses::is_quiescent`, that is `i < expanded_count` and every successor
  of class `i` is labelled by a reapable transition (`reap`, membership in the reapable set,
  [TIME-013], [VER-002]). The Rust has two branches: with an empty reapable set
  (`fires_unreapable = None`) it asks for no successor at all, otherwise for `!fires_unreapable[i]`,
  "no edge out of `i` names a transition outside the set". Both are the one `all` of the model:
  with `reap` constantly false it is the no-successor test (`quiescentAt_noReap`). The Rust reads
  the edges recorded while expanding class `i` (one per successor, fresh or already stored, each
  carrying the fired transition's name); the model reads the successor list under the class's
  own bound, whose labels by `Equivariant` are the same under any fresh counter
  (`rests_transfer`; `succ_nil_iff` is the empty case).

Results:
* `build_reach`: every stored class is plainly reachable — complete, truncated, stopped or
  early-stopped alike.
* `build_closed`: every expanded class has a stored key-twin of each of its successors.
* **`truncated_never_proven`**: a `Proven` comes only from a complete, unstopped build.
* **`prefix_safety_sound`**, **`prefix_quiescence_sound`**: a `Violated` read off any build is
  witnessed by a reachable class — for a safety predicate any stored class, for a quiescence
  predicate only an expanded class, all of whose successors under any fresh counter are
  reapable (none, with nothing reapable).
* **`complete_proven_safety`**, **`complete_proven_quiescence`**: on a complete build, `Proven`
  holds of every reachable state (quiescence: of every reachable state all of whose successors
  are reapable), for key-invariant predicates, under `Equivariant`.
-/

namespace Libpetri.Novel.RouteB.Decide

open Libpetri

variable {S K L : Type} (E : Explorer S K L)

/-- The result of a build. -/
structure Out (S : Type) where
  cls : List S
  exp : ℕ
  complete : Bool
  stopped : Bool
  early : Bool

open Classical in
/-- One expansion: every successor whose key is not stored is appended; with the early stop, a
fresh one satisfying `bad` ends the build (flag `true`). -/
noncomputable def expandB (bad : S → Bool) (stopAt : Bool) : List S → List (L × S) → List S × Bool
  | cls, [] => (cls, false)
  | cls, (_, y) :: ys =>
    if ∃ z ∈ cls, E.key z = E.key y then expandB bad stopAt cls ys
    else if stopAt && bad y then (cls ++ [y], true)
    else expandB bad stopAt (cls ++ [y]) ys

/-- The counter after an expansion: at least every successor's bound. -/
def nextC (c : ℕ) (ys : List (L × S)) : ℕ := ys.foldl (fun acc ly => max acc (E.bound ly.2)) c

/-- The worklist loop. -/
noncomputable def loop (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) :
    ℕ → List S → ℕ → ℕ → Out S
  | 0, cls, exp, _ => ⟨cls, exp, false, true, false⟩
  | fuel + 1, cls, exp, c =>
    match cls[exp]? with
    | none => ⟨cls, exp, true, false, false⟩
    | some x =>
      if maxClasses ≤ cls.length then ⟨cls, exp, false, false, false⟩
      else if cut fuel then ⟨cls, exp, false, true, false⟩
      else
        match expandB E bad stopAt cls (E.succ c x) with
        | (cls', true) => ⟨cls', exp, false, false, true⟩
        | (cls', false) => loop maxClasses cut bad stopAt fuel cls' (exp + 1) (nextC E c (E.succ c x))

/-- `build_until`: the initial class, tested first, then the loop. -/
noncomputable def build (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool)
    (fuel : ℕ) (x0 : S) : Out S :=
  if stopAt && bad x0 then ⟨[x0], 0, false, false, true⟩
  else loop E maxClasses cut bad stopAt fuel [x0] 0 (E.bound x0)

/-! ## The verdict -/

/-- The property kinds `decide_over_classes` distinguishes. A quiescence property carries the
reapable set (`reap`, over transition labels) its `is_quiescent` reads (`NameClasses::new`
builds `fires_unreapable` from it). `verify_via_name_scg` is a wrapper that calls
`verify_via_name_scg_reaping` with empty sets. That function takes the caller's reapable set
(`SmtVerifier::reapable_set`: the explicit `reapable_transitions` override, or the net's
`deadline` and `window` transitions, and empty under `assume_no_reaping`), keeps the names that
are transitions of the net, and passes it to the quiescence properties only; a marking property
gets the empty set (`rests_on`). -/
inductive Prop' (S L : Type) where
  | safety (bad : S → Bool)
  | quiescence (bad : S → Bool) (reap : L → Bool)

/-- `NameClasses::is_quiescent`: expanded, and every firing out of the class is of a reapable
transition (`!fires_unreapable[i]`). With nothing reapable, no successor at all
(`quiescentAt_noReap`). -/
def quiescentAt (reap : L → Bool) (o : Out S) (i : ℕ) : Bool :=
  decide (i < o.exp) && match o.cls[i]? with
    | some x => (E.succ (E.bound x) x).all fun ly => reap ly.1
    | none => false

/-- The `fires_unreapable = None` branch: with an empty reapable set, `is_quiescent` is
"expanded and no successor". -/
theorem quiescentAt_noReap (o : Out S) (i : ℕ) :
    quiescentAt E (fun _ => false) o i = (decide (i < o.exp) && match o.cls[i]? with
      | some x => (E.succ (E.bound x) x).isEmpty
      | none => false) := by
  unfold quiescentAt
  cases o.cls[i]? with
  | none => rfl
  | some x =>
    simp only
    generalize E.succ (E.bound x) x = ys
    cases ys <;> simp

/-- The predicate `decide_over_classes` applies to class `i`. -/
def violatesAt (o : Out S) : Prop' S L → ℕ → Bool
  | .safety bad, i => match o.cls[i]? with
    | some x => bad x
    | none => false
  | .quiescence bad reap, i => quiescentAt E reap o i && match o.cls[i]? with
    | some x => bad x
    | none => false

inductive Verdict where
  | proven
  | violated (i : ℕ)
  | unknown
  deriving DecidableEq

/-- `verify_via_name_scg`: nothing off a stopped build; the first violating class, prefix or not;
else `Proven` only on a complete graph. -/
def verdict (o : Out S) (p : Prop' S L) : Verdict :=
  if o.stopped then .unknown
  else match (List.range o.cls.length).find? (violatesAt E o p) with
    | some i => .violated i
    | none => if o.complete then .proven else .unknown

/-- **A truncated graph never yields `Proven`** ([VER-012] AC3): neither does a stopped one. -/
theorem truncated_never_proven (o : Out S) (p : Prop' S L) (h : verdict E o p = .proven) :
    o.complete = true ∧ o.stopped = false := by
  unfold verdict at h
  split at h
  · cases h
  · rename_i hs
    split at h
    · cases h
    · split at h
      · exact ⟨by assumption, by simpa using hs⟩
      · cases h

/-! ## The loop invariant -/

/-- Stored classes are reachable, the counter is fresh for all of them, and each expanded class
has a stored key-twin of every successor under some fresh counter. -/
structure Inv (x0 : S) (cls : List S) (exp c : ℕ) : Prop where
  reach : ∀ z ∈ cls, Explorer.Reach E x0 z
  bound : ∀ z ∈ cls, E.bound z ≤ c
  exp_le : exp ≤ cls.length
  closed : ∀ i x, i < exp → cls[i]? = some x →
    ∃ c', E.bound x ≤ c' ∧ ∀ ly ∈ E.succ c' x, ∃ z ∈ cls, E.key z = E.key ly.2

theorem expandB_spec (bad : S → Bool) (stopAt : Bool) :
    ∀ (ys : List (L × S)) (cls : List S),
      (∃ t, (expandB E bad stopAt cls ys).1 = cls ++ t ∧ ∀ z ∈ t, ∃ l, (l, z) ∈ ys) ∧
      ((expandB E bad stopAt cls ys).2 = false →
        ∀ ly ∈ ys, ∃ z ∈ (expandB E bad stopAt cls ys).1, E.key z = E.key ly.2)
  | [], cls => by simp [expandB]
  | (l, y) :: ys, cls => by
    classical
    unfold expandB
    by_cases hk : ∃ z ∈ cls, E.key z = E.key y
    · rw [if_pos hk]
      obtain ⟨⟨t, ht, htm⟩, hcl⟩ := expandB_spec bad stopAt ys cls
      refine ⟨⟨t, ht, fun z hz => ?_⟩, fun hf ly hly => ?_⟩
      · obtain ⟨l', hl'⟩ := htm z hz
        exact ⟨l', List.mem_cons_of_mem _ hl'⟩
      · rcases List.mem_cons.mp hly with rfl | hly
        · obtain ⟨z, hz, hkz⟩ := hk
          exact ⟨z, by rw [ht]; exact List.mem_append_left _ hz, hkz⟩
        · exact hcl hf ly hly
    · rw [if_neg hk]
      by_cases hb : (stopAt && bad y) = true
      · rw [if_pos hb]
        refine ⟨⟨[y], rfl, fun z hz => ⟨l, by rw [List.mem_singleton.mp hz]; exact List.mem_cons_self⟩⟩,
          fun hf => by simp at hf⟩
      · rw [if_neg hb]
        obtain ⟨⟨t, ht, htm⟩, hcl⟩ := expandB_spec bad stopAt ys (cls ++ [y])
        refine ⟨⟨[y] ++ t, by rw [ht, List.append_assoc], fun z hz => ?_⟩, fun hf ly hly => ?_⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact ⟨l, by rw [List.mem_singleton.mp hz]; exact List.mem_cons_self⟩
          · obtain ⟨l', hl'⟩ := htm z hz
            exact ⟨l', List.mem_cons_of_mem _ hl'⟩
        · rcases List.mem_cons.mp hly with rfl | hly
          · exact ⟨y, by rw [ht]; simp, rfl⟩
          · exact hcl hf ly hly

theorem le_nextC_start (c : ℕ) : ∀ (ys : List (L × S)), c ≤ nextC E c ys := by
  intro ys
  induction ys generalizing c with
  | nil => exact Nat.le_refl _
  | cons ly ys ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_nextC (c : ℕ) : ∀ (ys : List (L × S)), ∀ ly ∈ ys, E.bound ly.2 ≤ nextC E c ys := by
  intro ys
  induction ys generalizing c with
  | nil => intro ly h; exact absurd h List.not_mem_nil
  | cons ly' ys ih =>
    intro ly h
    unfold nextC
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_nextC_start E _ ys)
    · exact ih _ ly h

theorem getElem?_append_of_lt {cls t : List S} {i : ℕ} (h : i < cls.length) :
    (cls ++ t)[i]? = cls[i]? := by
  rw [List.getElem?_append_left h]

/-- The invariant survives an expansion that did not stop early. -/
theorem inv_step {x0 : S} {cls : List S} {exp c : ℕ} {x : S} (hinv : Inv E x0 cls exp c)
    (hx : cls[exp]? = some x) {bad : S → Bool} {stopAt : Bool}
    (hf : (expandB E bad stopAt cls (E.succ c x)).2 = false) :
    Inv E x0 (expandB E bad stopAt cls (E.succ c x)).1 (exp + 1) (nextC E c (E.succ c x)) := by
  obtain ⟨⟨t, ht, htm⟩, hcl⟩ := expandB_spec E bad stopAt (E.succ c x) cls
  have hxmem : x ∈ cls := List.mem_of_getElem? hx
  have hxlt : exp < cls.length := by
    rcases Nat.lt_or_ge exp cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  have hxr : Explorer.Reach E x0 x := hinv.reach x hxmem
  have hxb : E.bound x ≤ c := hinv.bound x hxmem
  rw [ht]
  refine ⟨fun z hz => ?_, fun z hz => ?_, ?_, fun i y hi hy => ?_⟩
  · rcases List.mem_append.mp hz with hz | hz
    · exact hinv.reach z hz
    · obtain ⟨l, hl⟩ := htm z hz
      exact Explorer.Reach.step hxr hxb hl
  · rcases List.mem_append.mp hz with hz | hz
    · exact Nat.le_trans (hinv.bound z hz) (le_nextC_start E c _)
    · obtain ⟨l, hl⟩ := htm z hz
      exact le_nextC E c _ (l, z) hl
  · rw [List.length_append]; omega
  · have hilt : i < cls.length := by omega
    rw [getElem?_append_of_lt hilt] at hy
    rcases Nat.lt_or_ge i exp with h | h
    · obtain ⟨c', hc', hall⟩ := hinv.closed i y h hy
      exact ⟨c', hc', fun ly hly => by
        obtain ⟨z, hz, hk⟩ := hall ly hly
        exact ⟨z, List.mem_append_left _ hz, hk⟩⟩
    · have : i = exp := by omega
      subst this
      rw [hx] at hy
      cases hy
      refine ⟨c, hxb, fun ly hly => ?_⟩
      have := hcl hf ly hly
      rwa [ht] at this

/-- What every loop result satisfies. -/
theorem loop_spec (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool) (x0 : S) :
    ∀ fuel cls exp c, Inv E x0 cls exp c →
      let o := loop E maxClasses cut bad stopAt fuel cls exp c
      (∀ z ∈ o.cls, Explorer.Reach E x0 z) ∧
      (∀ i x, i < o.exp → o.cls[i]? = some x →
        ∃ c', E.bound x ≤ c' ∧ ∀ ly ∈ E.succ c' x, ∃ z ∈ o.cls, E.key z = E.key ly.2) ∧
      o.exp ≤ o.cls.length ∧
      (o.complete = true → o.exp = o.cls.length)
  | 0, cls, exp, c, hinv => by
    simp only [loop]
    exact ⟨hinv.reach, hinv.closed, hinv.exp_le, fun h => by cases h⟩
  | fuel + 1, cls, exp, c, hinv => by
    simp only [loop]
    split
    · rename_i hnone
      refine ⟨hinv.reach, hinv.closed, hinv.exp_le, fun _ => ?_⟩
      have := hinv.exp_le
      have h2 : cls.length ≤ exp := by
        by_contra h; rw [List.getElem?_eq_getElem (by omega)] at hnone; cases hnone
      show exp = cls.length
      omega
    · rename_i x hx
      split
      · exact ⟨hinv.reach, hinv.closed, hinv.exp_le, fun h => by cases h⟩
      · split
        · exact ⟨hinv.reach, hinv.closed, hinv.exp_le, fun h => by cases h⟩
        · split
          · rename_i cls' heq
            obtain ⟨⟨t, ht, htm⟩, -⟩ := expandB_spec E bad stopAt (E.succ c x) cls
            rw [heq] at ht
            simp only at ht
            have hxmem : x ∈ cls := List.mem_of_getElem? hx
            have hxr : Explorer.Reach E x0 x := hinv.reach x hxmem
            have hxb : E.bound x ≤ c := hinv.bound x hxmem
            refine ⟨fun z hz => ?_, fun i y hi hy => ?_, ?_, fun h => by cases h⟩
            · rw [ht] at hz
              rcases List.mem_append.mp hz with hz | hz
              · exact hinv.reach z hz
              · obtain ⟨l, hl⟩ := htm z hz
                exact Explorer.Reach.step hxr hxb hl
            · have hilt : i < cls.length := Nat.lt_of_lt_of_le hi hinv.exp_le
              rw [ht, getElem?_append_of_lt hilt] at hy
              obtain ⟨c', hc', hall⟩ := hinv.closed i y hi hy
              exact ⟨c', hc', fun ly hly => by
                obtain ⟨z, hz, hk⟩ := hall ly hly
                exact ⟨z, by rw [ht]; exact List.mem_append_left _ hz, hk⟩⟩
            · show exp ≤ cls'.length
              rw [ht, List.length_append]; have := hinv.exp_le; omega
          · rename_i cls' heq
            have hf : (expandB E bad stopAt cls (E.succ c x)).2 = false := by rw [heq]
            have hinv' := inv_step E hinv hx hf
            rw [heq] at hinv'
            exact loop_spec maxClasses cut bad stopAt x0 fuel cls' (exp + 1) _ hinv'

theorem build_spec (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool)
    (fuel : ℕ) (x0 : S) :
    let o := build E maxClasses cut bad stopAt fuel x0
    (∀ z ∈ o.cls, Explorer.Reach E x0 z) ∧
    (∀ i x, i < o.exp → o.cls[i]? = some x →
      ∃ c', E.bound x ≤ c' ∧ ∀ ly ∈ E.succ c' x, ∃ z ∈ o.cls, E.key z = E.key ly.2) ∧
    o.exp ≤ o.cls.length ∧
    (o.complete = true → o.exp = o.cls.length) := by
  simp only [build]
  split
  · refine ⟨fun z hz => ?_, fun i x hi _ => absurd hi (Nat.not_lt_zero _), by simp,
      fun h => by cases h⟩
    rw [List.mem_singleton.mp hz]
    exact Explorer.Reach.init
  · apply loop_spec
    refine ⟨fun z hz => ?_, fun z hz => ?_, by simp, fun i x hi _ => absurd hi (Nat.not_lt_zero _)⟩
    · rw [List.mem_singleton.mp hz]; exact Explorer.Reach.init
    · rw [List.mem_singleton.mp hz]; exact Nat.le_refl _

/-- **Every stored class is reachable**, whatever ended the build. -/
theorem build_reach {maxClasses : ℕ} {cut : ℕ → Bool} {bad : S → Bool} {stopAt : Bool}
    {fuel : ℕ} {x0 : S} {z : S} (h : z ∈ (build E maxClasses cut bad stopAt fuel x0).cls) :
    Explorer.Reach E x0 z :=
  (build_spec E maxClasses cut bad stopAt fuel x0).1 z h

/-! ## Verdicts -/

variable {E}

/-- Under `Equivariant`, whether a class has a successor does not depend on the fresh counter. -/
theorem succ_nil_iff (hE : E.Equivariant) {x : S} {c c' : ℕ} (hc : E.bound x ≤ c)
    (hc' : E.bound x ≤ c') : E.succ c x = [] ↔ E.succ c' x = [] := by
  have h := (hE.key_succ x x c c' rfl hc hc').length_eq
  rw [List.length_map, List.length_map] at h
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, h]

/-- Under `Equivariant`, whether every successor is reapable depends only on the key, not on the
class or the fresh counter: the `(label, key)` successor lists are permutations of each other. -/
theorem rests_transfer (hE : E.Equivariant) (reap : L → Bool) {a b : S} {c c' : ℕ}
    (hk : E.key a = E.key b) (hc : E.bound a ≤ c) (hc' : E.bound b ≤ c')
    (h : ∀ ly ∈ E.succ c a, reap ly.1 = true) : ∀ ly ∈ E.succ c' b, reap ly.1 = true := by
  intro ly hly
  have hperm := hE.key_succ a b c c' hk hc hc'
  have hin : E.keyed ly ∈ (E.succ c a).map E.keyed :=
    hperm.mem_iff.mpr (List.mem_map_of_mem hly)
  obtain ⟨ly', hly', he⟩ := List.mem_map.mp hin
  have hl : ly'.1 = ly.1 := by
    have h1 := congrArg (fun p : L × K => p.1) he
    simpa [Explorer.keyed] using h1
  rw [← hl]
  exact h ly' hly'

theorem find?_violated {o : Out S} {p : Prop' S L} {i : ℕ}
    (h : (List.range o.cls.length).find? (violatesAt E o p) = some i) :
    violatesAt E o p i = true := List.find?_some h

/-- **A safety `Violated` stands**, off a complete, truncated or early-stopped build: the class it
names is stored, reachable and bad. -/
theorem prefix_safety_sound {maxClasses : ℕ} {cut : ℕ → Bool} {stopBad bad : S → Bool}
    {stopAt : Bool} {fuel : ℕ} {x0 : S} {i : ℕ}
    (h : verdict E (build E maxClasses cut stopBad stopAt fuel x0) (.safety bad) = .violated i) :
    ∃ x, (build E maxClasses cut stopBad stopAt fuel x0).cls[i]? = some x ∧
      Explorer.Reach E x0 x ∧ bad x = true := by
  unfold verdict at h
  split at h
  · cases h
  · split at h
    · rename_i j hj
      cases h
      have hv := find?_violated hj
      simp only [violatesAt] at hv
      split at hv
      · rename_i x hx
        exact ⟨x, hx, build_reach E (List.mem_of_getElem? hx), hv⟩
      · cases hv
    · split at h <;> cases h

/-- **A quiescence `Violated` stands**: the class it names is stored, reachable, expanded, bad,
and every successor under any fresh counter is a firing of a reapable transition, so it really
rests in the graph (with nothing reapable: it has no successor, `succ_nil_iff`). -/
theorem prefix_quiescence_sound (hE : E.Equivariant) {maxClasses : ℕ} {cut : ℕ → Bool}
    {stopBad bad : S → Bool} {reap : L → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S} {i : ℕ}
    (h : verdict E (build E maxClasses cut stopBad stopAt fuel x0) (.quiescence bad reap) =
      .violated i) :
    ∃ x, (build E maxClasses cut stopBad stopAt fuel x0).cls[i]? = some x ∧
      i < (build E maxClasses cut stopBad stopAt fuel x0).exp ∧
      Explorer.Reach E x0 x ∧ bad x = true ∧
      ∀ c, E.bound x ≤ c → ∀ ly ∈ E.succ c x, reap ly.1 = true := by
  unfold verdict at h
  split at h
  · cases h
  · split at h
    · rename_i j hj
      cases h
      have hv := find?_violated hj
      simp only [violatesAt, quiescentAt, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hlt, hq⟩, hb⟩ := hv
      split at hq
      · rename_i x hx
        simp only [hx] at hb
        refine ⟨x, hx, hlt, build_reach E (List.mem_of_getElem? hx), hb, fun c hc => ?_⟩
        refine rests_transfer hE reap rfl (Nat.le_refl _) hc fun ly hly => ?_
        exact List.all_eq_true.mp hq ly hly
      · cases hq
    · split at h <;> cases h

theorem complete_twin (hE : E.Equivariant) {o : Out S} {x0 : S} (hx0 : x0 ∈ o.cls)
    (hclosed : ∀ i x, i < o.exp → o.cls[i]? = some x →
      ∃ c', E.bound x ≤ c' ∧ ∀ ly ∈ E.succ c' x, ∃ z ∈ o.cls, E.key z = E.key ly.2)
    (hall : o.exp = o.cls.length) :
    ∀ y, Explorer.Reach E x0 y → ∃ z ∈ o.cls, E.key z = E.key y := by
  intro y hy
  induction hy with
  | init => exact ⟨x0, hx0, rfl⟩
  | @step a c l s _ hb hmem ih =>
    obtain ⟨z, hz, hkz⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
    have hilt : i < o.cls.length := by
      rcases Nat.lt_or_ge i o.cls.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hi; cases hi
    obtain ⟨c', hc', hcl⟩ := hclosed i z (hall ▸ hilt) hi
    have hperm := hE.key_succ a z c c' hkz.symm hb hc'
    have hin : (l, E.key s) ∈ (E.succ c' z).map E.keyed :=
      hperm.mem_iff.mp (List.mem_map.mpr ⟨(l, s), hmem, rfl⟩)
    obtain ⟨s', hs', hks'⟩ := Explorer.exists_succ_of_keyed hin
    obtain ⟨w, hw, hkw⟩ := hcl (l, s') hs'
    exact ⟨w, hw, hkw.trans hks'⟩

theorem x0_mem_build (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (stopAt : Bool)
    (fuel : ℕ) (x0 : S) : x0 ∈ (build E maxClasses cut bad stopAt fuel x0).cls := by
  simp only [build]
  split
  · exact List.mem_singleton_self _
  · suffices ∀ fuel cls exp c, x0 ∈ cls → x0 ∈ (loop E maxClasses cut bad stopAt fuel cls exp c).cls from
      this fuel [x0] 0 _ (List.mem_singleton_self _)
    intro fuel
    induction fuel with
    | zero => intro cls exp c h; simpa [loop] using h
    | succ fuel ih =>
      intro cls exp c h
      simp only [loop]
      split
      · exact h
      · rename_i x _
        split
        · exact h
        · split
          · exact h
          · obtain ⟨⟨t, ht, -⟩, -⟩ := expandB_spec E bad stopAt (E.succ c x) cls
            split
            · rename_i cls' heq
              rw [heq] at ht
              simp only at ht ⊢
              rw [ht]; exact List.mem_append_left _ h
            · rename_i cls' heq
              rw [heq] at ht
              simp only at ht
              exact ih _ _ _ (by rw [ht]; exact List.mem_append_left _ h)

/-- **A complete `Proven` of a safety predicate holds on every reachable state**, for a predicate
that reads only the key (a property reads the base marking, which the key carries). -/
theorem complete_proven_safety (hE : E.Equivariant) {bad : S → Bool}
    (hbad : ∀ a b, E.key a = E.key b → bad a = bad b) {maxClasses : ℕ} {cut : ℕ → Bool}
    {stopBad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (h : verdict E (build E maxClasses cut stopBad stopAt fuel x0) (.safety bad) = .proven) :
    ∀ y, Explorer.Reach E x0 y → bad y = false := by
  obtain ⟨hcomp, hns⟩ := truncated_never_proven (E := E) _ _ h
  obtain ⟨-, hclosed, -, hall⟩ := build_spec E maxClasses cut stopBad stopAt fuel x0
  intro y hy
  obtain ⟨z, hz, hkz⟩ := complete_twin hE (x0_mem_build _ _ _ _ _ x0) hclosed (hall hcomp) y hy
  rw [← hbad z y hkz]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hilt : i < (build E maxClasses cut stopBad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (build E maxClasses cut stopBad stopAt fuel x0).cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  unfold verdict at h
  rw [if_neg (by simp [hns])] at h
  split at h
  · cases h
  · rename_i hnone
    have := List.find?_eq_none.mp hnone i (List.mem_range.mpr hilt)
    simp only [violatesAt, hi] at this
    simpa using this

/-- **A complete `Proven` of a quiescence predicate holds on every reachable resting state**: every
reachable state all of whose successors are reapable firings (with nothing reapable: every dead
one) is not bad. -/
theorem complete_proven_quiescence (hE : E.Equivariant) {bad : S → Bool} {reap : L → Bool}
    (hbad : ∀ a b, E.key a = E.key b → bad a = bad b) {maxClasses : ℕ} {cut : ℕ → Bool}
    {stopBad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (h : verdict E (build E maxClasses cut stopBad stopAt fuel x0) (.quiescence bad reap) =
      .proven) :
    ∀ y, Explorer.Reach E x0 y →
      (∃ c, E.bound y ≤ c ∧ ∀ ly ∈ E.succ c y, reap ly.1 = true) → bad y = false := by
  obtain ⟨hcomp, hns⟩ := truncated_never_proven (E := E) _ _ h
  obtain ⟨-, hclosed, -, hall⟩ := build_spec E maxClasses cut stopBad stopAt fuel x0
  intro y hy ⟨c, hc, hdead⟩
  obtain ⟨z, hz, hkz⟩ := complete_twin hE (x0_mem_build _ _ _ _ _ x0) hclosed (hall hcomp) y hy
  rw [← hbad z y hkz]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hilt : i < (build E maxClasses cut stopBad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (build E maxClasses cut stopBad stopAt fuel x0).cls.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  -- z rests too
  have hzdead : (E.succ (E.bound z) z).all (fun ly => reap ly.1) = true :=
    List.all_eq_true.mpr (rests_transfer hE reap hkz.symm hc (Nat.le_refl _) hdead)
  unfold verdict at h
  rw [if_neg (by simp [hns])] at h
  split at h
  · cases h
  · rename_i hnone
    have := List.find?_eq_none.mp hnone i (List.mem_range.mpr hilt)
    simp only [violatesAt, quiescentAt, hi, hzdead] at this
    rw [hall hcomp] at this
    simpa [hilt] using this

end Libpetri.Novel.RouteB.Decide
