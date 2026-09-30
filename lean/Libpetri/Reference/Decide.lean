import Libpetri.Reference.Step
import Libpetri.Reference.Search

/-!
# Exploring a net and deciding its properties

`exploreNet net cap m0` is the breadth-first search of `Search.lean` over the executable
successor function `succ` of `Step.lean`, from the canonical initial marking `m0`.
`verdict` reads a property off the discovered markings:

* no discovered marking violates it: `proven` if the search completed, else `unknown "cap"`;
* some does: the shallowest one's recorded path is replayed (`replayViolates`), and reported as
  `violated` with its labels. A path that did not replay would be reported `unknown`; it never
  happens, but the theorem below needs no proof of that, only of the replay.

A violation read off an incomplete search is still real: every discovered marking is reachable,
and `violatesB` decides the property on the marking itself (quiescence included), not on the
recorded edges.

Headlines:
* (b) **`explored_eq_reachable`**: a completed search discovers exactly the reachable markings,
  each once, canonically; `explored_sound` holds even when it did not complete.
* (c) **`verdict_proven_iff`**: the verdict is `proven` iff the search completed and no
  reachable marking violates the property.
* (d) **`verdict_violated_run`**: a `violated` verdict's labels are a firing sequence from the
  initial marking to a violating marking.
* **`replayViolates_iff`**: the replay accepts a trace iff some firing sequence with those
  labels ends in a violating marking; `replay_ne_nil_iff`: iff some firing sequence has them.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Novel.Seam

variable {K : Type} [LinearOrder K]

/-! ## Reachability over canonical markings -/

/-- Reachability in the list graph of `succ` is the semantic reachability. -/
theorem search_reach_sound {net : Net K} {m0 : Marking K} (hc : Canon m0) {y : Marking K}
    (h : Search.Reach (succ net) m0 y) : Canon y ∧ Reach net (get m0) (get y) := by
  induction h with
  | refl => exact ⟨hc, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hc', hl⟩ := mem_succ ih.1 (l := e.1) (m' := e.2) he
    exact ⟨hc', Relation.ReflTransGen.tail ih.2 ⟨e.1, hl⟩⟩

theorem search_reach_complete {net : Net K} {m0 : Marking K} (hc : Canon m0) {f : K → Nat}
    (h : Reach net (get m0) f) : ∃ y, Canon y ∧ get y = f ∧ Search.Reach (succ net) m0 y := by
  induction h with
  | refl => exact ⟨m0, hc, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨y, hcy, rfl, hr⟩ := ih
    obtain ⟨l, hl⟩ := hs
    obtain ⟨m', hm, hg⟩ := succ_complete hcy hl
    exact ⟨m', (mem_succ hcy hm).1, hg,
      Relation.ReflTransGen.tail hr (List.mem_map.mpr ⟨(l, m'), hm, rfl⟩)⟩

/-! ## Deciding a property on one marking -/

/-- Every enabled transition is reapable (reap-quiescence, [VER-002], [TIME-013]). -/
def quiescentB (net : Net K) (m : Marking K) : Bool :=
  net.transitions.all fun t => t.reapable || !enabledNA (get m) t.core

/-- The property's violation, evaluated on a canonical marking. -/
def violatesB (net : Net K) : Property K → Marking K → Bool
  | .deadlockFree sinks, m => quiescentB net m && m.any (fun e => !decide (e.1 ∈ sinks))
  | .terminatesAtSink sinks, m => quiescentB net m && sinks.all (fun s => get m s == 0)
  | .placeBound p k, m => decide (k < get m p)
  | .mutualExclusion ps, m => decide (2 ≤ (ps.filter (fun p => get m p != 0)).length)
  | .unreachable ps, m => ps.all (fun p => get m p != 0)
  | .quiescentCount ps lo hi, m =>
    quiescentB net m &&
      (decide ((ps.map (get m)).sum < lo) || hi.any (fun h => decide (h < (ps.map (get m)).sum)))

theorem quiescentB_iff (net : Net K) (m : Marking K) :
    quiescentB net m = true ↔ ReapQuiescent net (get m) := by
  simp only [quiescentB, ReapQuiescent, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine forall_congr' fun t => forall_congr' fun _ => ?_
  cases t.reapable <;> cases enabledNA (get m) t.core <;> simp

/-- **`violatesB` decides `Violates`** on canonical markings. -/
theorem violatesB_iff (net : Net K) (φ : Property K) {m : Marking K} (hc : Canon m) :
    violatesB net φ m = true ↔ Violates net φ (get m) := by
  cases φ with
  | deadlockFree sinks =>
    simp only [violatesB, Violates, Bool.and_eq_true, quiescentB_iff]
    refine and_congr Iff.rfl ⟨fun h => ?_, fun ⟨n, hn, hs⟩ => ?_⟩
    · obtain ⟨e, he, hs⟩ := List.any_eq_true.mp h
      refine ⟨e.1, ?_, by simpa using hs⟩
      rw [get_of_mem hc (show (e.1, e.2) ∈ m from he)]
      exact hc.2 e he
    · exact List.any_eq_true.mpr ⟨_, mem_of_get_ne_zero hn, by simpa using hs⟩
  | terminatesAtSink sinks =>
    simp [violatesB, Violates, quiescentB_iff, List.all_eq_true]
  | placeBound p k => simp [violatesB, Violates]
  | mutualExclusion ps => simp [violatesB, Violates]
  | unreachable ps => simp [violatesB, Violates, List.all_eq_true]
  | quiescentCount ps lo hi =>
    simp only [violatesB, Violates, Bool.and_eq_true, quiescentB_iff, Bool.or_eq_true,
      decide_eq_true_eq]
    refine and_congr Iff.rfl (or_congr Iff.rfl ?_)
    cases hi <;> simp

/-! ## Replaying a trace -/

/-- Add `y` unless present. -/
def addNew (acc : List (Marking K)) (y : Marking K) : List (Marking K) :=
  if y ∈ acc then acc else y :: acc

/-- Every marking one step labelled `l` from one of `ms`. -/
def stepLabel (net : Net K) (l : String) (ms : List (Marking K)) : List (Marking K) :=
  (ms.flatMap fun m => (succ net m).filterMap fun e => if e.1 = l then some e.2 else none).foldl
    addNew []

/-- Every marking the labels `tr` lead to from one of `ms`. -/
def replay (net : Net K) : List String → List (Marking K) → List (Marking K)
  | [], ms => ms
  | l :: ls, ms => replay net ls (stepLabel net l ms)

/-- Some firing sequence labelled `tr` ends in a violating marking. -/
def replayViolates (net : Net K) (φ : Property K) (m0 : Marking K) (tr : List String) : Bool :=
  (replay net tr [m0]).any (violatesB net φ)

theorem mem_foldl_addNew : ∀ (L acc : List (Marking K)) (y : Marking K),
    y ∈ L.foldl addNew acc ↔ y ∈ L ∨ y ∈ acc
  | [], acc, y => by simp
  | x :: xs, acc, y => by
    rw [List.foldl_cons, mem_foldl_addNew xs, List.mem_cons]
    unfold addNew
    split
    · rename_i hx
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((rfl | h) | h)
        · exact Or.inr hx
        · exact Or.inl h
        · exact Or.inr h
    · rw [List.mem_cons]
      tauto

theorem mem_stepLabel {net : Net K} {l : String} {ms : List (Marking K)} {y : Marking K} :
    y ∈ stepLabel net l ms ↔ ∃ m ∈ ms, (l, y) ∈ succ net m := by
  unfold stepLabel
  rw [mem_foldl_addNew]
  simp only [List.mem_flatMap, List.mem_filterMap, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨m, hm, e, he, hy⟩
    split at hy
    · rename_i hl
      obtain rfl := Option.some.inj hy
      exact ⟨m, hm, by rw [← hl]; exact he⟩
    · exact absurd hy (by simp)
  · rintro ⟨m, hm, hy⟩
    exact ⟨m, hm, (l, y), hy, by simp⟩

theorem run_nil_eq {net : Net K} {a b : K → Nat} (h : Run net [] a b) : a = b := by
  cases h; rfl

theorem run_cons_inv {net : Net K} {l : String} {ls : List String} {a b : K → Nat}
    (h : Run net (l :: ls) a b) : ∃ a1, LStep net l a a1 ∧ Run net ls a1 b := by
  cases h with
  | cons hs hr => exact ⟨_, hs, hr⟩

theorem replay_canon {net : Net K} : ∀ (tr : List String) (ms : List (Marking K)),
    (∀ m ∈ ms, Canon m) → ∀ y ∈ replay net tr ms, Canon y
  | [], _, h => h
  | l :: ls, ms, h => by
    apply replay_canon ls
    intro y hy
    obtain ⟨m, hm, hs⟩ := mem_stepLabel.mp hy
    exact (mem_succ (h m hm) hs).1

/-- **The replay is exact**: a canonical marking is among the replay's markings iff a firing
sequence labelled `tr` leads to it from one of `ms`. -/
theorem mem_replay_iff {net : Net K} : ∀ (tr : List String) (ms : List (Marking K)),
    (∀ m ∈ ms, Canon m) → ∀ {y : Marking K}, Canon y →
      (y ∈ replay net tr ms ↔ ∃ m ∈ ms, Run net tr (get m) (get y))
  | [], ms, hms, y, hy => by
    simp only [replay]
    constructor
    · intro h; exact ⟨y, h, Run.nil _⟩
    · rintro ⟨m, hm, hr⟩
      have := ext (hms m hm) hy (fun q => congrFun (run_nil_eq hr) q)
      exact this ▸ hm
  | l :: ls, ms, hms, y, hy => by
    have hms' : ∀ m ∈ stepLabel net l ms, Canon m := fun m hm => by
      obtain ⟨m', hm', hs⟩ := mem_stepLabel.mp hm
      exact (mem_succ (hms m' hm') hs).1
    simp only [replay]
    rw [mem_replay_iff ls _ hms' hy]
    constructor
    · rintro ⟨m1, hm1, hr⟩
      obtain ⟨m, hm, hs⟩ := mem_stepLabel.mp hm1
      exact ⟨m, hm, Run.cons (mem_succ (hms m hm) hs).2 hr⟩
    · rintro ⟨m, hm, hr⟩
      obtain ⟨a1, hs, hr'⟩ := run_cons_inv hr
      obtain ⟨m1, hm1, hg⟩ := succ_complete (hms m hm) hs
      exact ⟨m1, mem_stepLabel.mpr ⟨m, hm, hm1⟩, hg ▸ hr'⟩

/-- A firing sequence from a canonical marking ends at a canonical marking's counts. -/
theorem run_canon {net : Net K} : ∀ {tr : List String} {m : Marking K} {f : K → Nat},
    Canon m → Run net tr (get m) f → ∃ y, Canon y ∧ get y = f
  | [], m, f, hc, h => ⟨m, hc, run_nil_eq h⟩
  | l :: ls, m, f, hc, h => by
    obtain ⟨a1, hs, hr⟩ := run_cons_inv h
    obtain ⟨m1, hm1, hg⟩ := succ_complete hc hs
    exact run_canon (mem_succ hc hm1).1 (hg ▸ hr)

/-- The replay of `tr` is nonempty iff some firing sequence is labelled `tr`: every label is
enabled at its step. -/
theorem replay_ne_nil_iff {net : Net K} {m0 : Marking K} (hc : Canon m0) (tr : List String) :
    replay net tr [m0] ≠ [] ↔ ∃ f, Run net tr (get m0) f := by
  have h1 : ∀ m ∈ [m0], Canon m := by simpa using hc
  constructor
  · intro h
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨m, hm, hr⟩ := (mem_replay_iff tr [m0] h1 (replay_canon tr [m0] h1 y hy)).mp hy
    rw [List.mem_singleton.mp hm] at hr
    exact ⟨_, hr⟩
  · rintro ⟨f, hr⟩
    obtain ⟨y, hcy, rfl⟩ := run_canon hc hr
    exact List.ne_nil_of_mem ((mem_replay_iff tr [m0] h1 hcy).mpr ⟨m0, by simp, hr⟩)

/-- **The replay check is exact**: it accepts `tr` iff some firing sequence labelled `tr` from
`m0` ends in a marking violating `φ`. -/
theorem replayViolates_iff {net : Net K} {m0 : Marking K} (hc : Canon m0) (φ : Property K)
    (tr : List String) :
    replayViolates net φ m0 tr = true ↔ ∃ f, Run net tr (get m0) f ∧ Violates net φ f := by
  have h1 : ∀ m ∈ [m0], Canon m := by simpa using hc
  unfold replayViolates
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hv⟩
    have hcy := replay_canon tr [m0] h1 y hy
    obtain ⟨m, hm, hr⟩ := (mem_replay_iff tr [m0] h1 hcy).mp hy
    rw [List.mem_singleton.mp hm] at hr
    exact ⟨_, hr, (violatesB_iff net φ hcy).mp hv⟩
  · rintro ⟨f, hr, hv⟩
    obtain ⟨y, hcy, rfl⟩ := run_canon hc hr
    exact ⟨y, (mem_replay_iff tr [m0] h1 hcy).mpr ⟨m0, by simp, hr⟩,
      (violatesB_iff net φ hcy).mpr hv⟩

/-- A firing sequence is a path of the reachability relation. -/
theorem run_reach {net : Net K} : ∀ {tr : List String} {a b : K → Nat},
    Run net tr a b → Reach net a b
  | [], _, _, h => run_nil_eq h ▸ Relation.ReflTransGen.refl
  | _ :: _, _, _, h => by
    obtain ⟨_, hs, hr⟩ := run_cons_inv h
    exact Relation.ReflTransGen.head ⟨_, hs⟩ (run_reach hr)

/-! ## The exploration -/

variable [Hashable K]

/-- **The reference exploration** of `net` from `m0`, at most `cap` markings. -/
def exploreNet (net : Net K) (cap : Nat) (m0 : Marking K) : Search.Seen (Marking K) × Bool :=
  Search.explore (succ net) cap m0

/-- Every discovered marking is canonical and reachable, complete or not. -/
theorem explored_sound {net : Net K} {cap : Nat} {m0 : Marking K} (hc : Canon m0)
    {y : Marking K} (hy : y ∈ (exploreNet net cap m0).1) :
    Canon y ∧ Reach net (get m0) (get y) :=
  search_reach_sound hc (Search.explore_reach hy)

/-- **Headline (b).** When the exploration completes, the markings it discovered are exactly the
reachable ones: every discovered marking is canonical, and a count function is reachable iff
some discovered marking holds it (and then only one does, by `ext`). -/
theorem explored_eq_reachable {net : Net K} {cap : Nat} {m0 : Marking K} (hc : Canon m0)
    (h : (exploreNet net cap m0).2 = true) :
    (∀ y, y ∈ (exploreNet net cap m0).1 → Canon y) ∧
    ∀ f : K → Nat, (∃ y, y ∈ (exploreNet net cap m0).1 ∧ get y = f) ↔ Reach net (get m0) f := by
  refine ⟨fun y hy => (explored_sound hc hy).1, fun f => ⟨?_, fun hf => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact (explored_sound hc hy).2
  · obtain ⟨y, _, hg, hr⟩ := search_reach_complete hc hf
    exact ⟨y, (Search.explore_complete_iff h y).mpr hr, hg⟩

/-! ## The verdict -/

/-- A verdict. -/
inductive Verdict where
  | proven
  | violated (trace : List String)
  | unknown (reason : String)
  deriving Repr, DecidableEq

/-- **The verdict** read off an exploration `r` of `net` from `m0`. -/
def verdict (net : Net K) (φ : Property K) (m0 : Marking K) (cap : Nat)
    (r : Search.Seen (Marking K) × Bool) : Verdict :=
  match r.1.keys.filter (violatesB net φ) with
  | [] => if r.2 then .proven else .unknown (if cap ≤ r.1.size then "cap" else "fuel")
  | z :: zs =>
    let depth := Search.depthOf r.1
    let best := zs.foldl (fun b y => if depth y < depth b then y else b) z
    let tr := Search.traceTo r.1 (r.1.size + 1) best []
    if replayViolates net φ m0 tr then .violated tr
    else .unknown "internal: the recorded path does not replay"

/-- **Headline (c).** The verdict is `proven` iff the exploration completed and no reachable
marking violates the property. -/
theorem verdict_proven_iff {net : Net K} {cap : Nat} {m0 : Marking K} (hc : Canon m0)
    (φ : Property K) :
    verdict net φ m0 cap (exploreNet net cap m0) = .proven ↔
      (exploreNet net cap m0).2 = true ∧ ∀ f, Reach net (get m0) f → ¬ Violates net φ f := by
  unfold verdict
  split
  · rename_i hbad
    have hnone : ∀ y, y ∈ (exploreNet net cap m0).1 → violatesB net φ y = false := by
      intro y hy
      cases hv : violatesB net φ y with
      | false => rfl
      | true =>
        have : y ∈ (exploreNet net cap m0).1.keys.filter (violatesB net φ) :=
          List.mem_filter.mpr ⟨Std.HashMap.mem_keys.mpr hy, hv⟩
        rw [hbad] at this
        exact absurd this List.not_mem_nil
    split
    · rename_i hcomp
      refine ⟨fun _ => ⟨hcomp, fun f hf hv => ?_⟩, fun _ => rfl⟩
      obtain ⟨y, hy, rfl⟩ := ((explored_eq_reachable hc hcomp).2 f).mpr hf
      have := (violatesB_iff net φ (explored_sound hc hy).1).mpr hv
      rw [hnone y hy] at this
      exact Bool.false_ne_true this
    · rename_i hcomp
      simp only [reduceCtorEq, false_iff, not_and]
      intro h
      exact absurd h hcomp
  · rename_i z zs hbad
    have hz : z ∈ (exploreNet net cap m0).1.keys.filter (violatesB net φ) := by
      rw [hbad]; exact List.mem_cons_self
    obtain ⟨hzk, hzv⟩ := List.mem_filter.mp hz
    have hzm := Std.HashMap.mem_keys.mp hzk
    obtain ⟨hcz, hrz⟩ := explored_sound hc hzm
    have hnot : ¬ ∀ f, Reach net (get m0) f → ¬ Violates net φ f :=
      fun h => h _ hrz ((violatesB_iff net φ hcz).mp hzv)
    constructor
    · intro h
      simp only at h
      split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    · rintro ⟨_, h⟩
      exact absurd h hnot

/-- **Headline (d).** A `violated` verdict's trace is a firing sequence from the initial marking
that ends in a marking violating the property. -/
theorem verdict_violated_run {net : Net K} {φ : Property K} {m0 : Marking K} {cap : Nat}
    {r : Search.Seen (Marking K) × Bool} (hc : Canon m0) {tr : List String}
    (h : verdict net φ m0 cap r = .violated tr) :
    ∃ f, Run net tr (get m0) f ∧ Violates net φ f := by
  unfold verdict at h
  split at h
  · split at h <;> simp at h
  · simp only at h
    split at h
    · rename_i hr
      obtain rfl := Verdict.violated.inj h
      exact (replayViolates_iff hc φ _).mp hr
    · simp at h

end Libpetri.Reference
