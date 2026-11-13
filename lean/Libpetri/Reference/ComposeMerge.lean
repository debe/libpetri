import Libpetri.Reference.Fuse

set_option linter.missingDocs true

/-!
# RefCompose: channel merge

The channel-merge slice of the composition model ([MOD-021]). When a composition binding maps an
interface channel to a caller-side transition, the caller's definition `c` and the instance's
channel definition `i` (both already rewritten through the port binding) become one definition.
The reference `refMerge Build sq cm` does what Rust (`rust/libpetri-core/src/rewriter.rs`
`merge_transitions`), Java (`SubnetRewriter.mergeTransitions`) and TypeScript
(`subnet-rewriter.ts` `mergeTransitions`) do, in Rust's order:

1. **timing**: `rtMergeTiming` (ruling D77 (a), the runtimes' rule): `Immediate` yields to the
   other side, equal timings collapse, any other pair rejects with a message naming both timings;
2. **correspondence** ([MOD-031]): the correspondence merge `cm`, a model parameter (the
   witness instance is `MOD_031`'s `refCorrOps.merge`); its rejection is passed on;
3. **arc kinds** (rule (d), set reading): on a place where both sides have an input, inhibitor,
   read or reset arc, the two sides' sets of arc kinds must be equal (`KindsAgree`); otherwise
   the merge rejects naming the place and both kind sets. Output places are not read here;
4. **input arcs** (rules (b), (c)): the caller's input arcs, then the instance's, merged by the
   table `mergeCard` at the first-seen slot (`mergeInputsE`, shared with fusion); an off-table
   pair rejects with the rule (c) diagnostic whose seam is `Channel composition '<caller name>'`
   (`fuseMsg`, `chanSeam`);
5. **the merged definition** (`mergedDef`): the caller's name and priority; read, inhibitor and
   reset arcs the duplicate-free union, caller first (rule (a)); the output specification
   `And(caller, instance)`, or the one side that has one (`mergeOut`); the merged timing; the
   action `sq caller instance` (`seqAct` is the runtimes' sequential composition with the
   passthrough elided); the merged correspondence;
6. **the transition builder**: the merged definition goes through `Build`, whose rejection is
   passed on (a merged output that names one place twice in one AND branch is one, [IO-011]).

Java checks the arc kinds before the timing; which message a merge with two faults reports is
therefore not stated by the blocks (composition design, skeptic correction S3): every lemma that
names a message carries the premise that the earlier checks pass.

What the blocks read: `refMerge_ok_iff` characterises success; the field lemma
`refMerge_ok_fields` gives name, priority, timing, action, output and arcs of a success; the
rejection lemmas (`refMerge_timing`, `refMerge_corr`, `refMerge_kinds`, `refMerge_offTable`,
`refMerge_buildFails`) and the acceptance lemma `refMerge_accepts` give the B lines of [MOD-021];
`mergeInputsE_cardAt` and `mergeInputsE_ok_iff` state the input-arc merge per place, through the
table, without the list function.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N A : Type}

/-! ## The function types -/

/-- A channel merge function ([MOD-021]): the caller-side definition and the instance-side channel
definition give the merged definition, or a rejection with a message. -/
abbrev MergeFn (N A : Type) := CDef N A → CDef N A → Except String (CDef N A)

/-- A correspondence merge ([MOD-031]): the caller-side and the instance-side definition give the
merged declared-to-actual place correspondence, or a rejection with a message. -/
abbrev CorrMergeFn (N A : Type) := CDef N A → CDef N A → Except String (Option (List (N × N)))

/-! ## Timing -/

/-- **The merged timing** (ruling D77 (a); Rust `merge_timings` in `rewriter.rs`, Java
`mergeTimings`, TypeScript `mergeTimings`): `Immediate` yields to the other side, two equal
timings collapse, any other pair has no merge (`none`). -/
def rtMergeTiming : Timing → Timing → Option Timing
  | .immediate, i => some i
  | c, .immediate => some c
  | c, i => if c = i then some c else none

/-- A timing as the merge diagnostic renders it. -/
def timingStr : Timing → String
  | .immediate => "Immediate"
  | .deadline b => s!"Deadline({b})"
  | .delayed a => s!"Delayed({a})"
  | .window e l => s!"Window({e}, {l})"
  | .exact a => s!"Exact({a})"

/-- The rejection of two timings with no merge, naming the channel and both timings ([MOD-021]
clause 2). The text is a stand-in for the runtimes' (only its parts are stated). -/
def timingMsg (name : String) (c i : Timing) : String :=
  s!"Channel composition '{name}': conflicting non-Immediate timings, caller-side {timingStr c} vs instance-side {timingStr i}. Resolve explicitly by aligning the timings on either side (MOD-021)."

/-! ## Action -/

/-- **Sequential composition of two actions** (all three runtimes, `compose_actions` /
`composeActions`): the caller's action, then the instance's, as `sq`; the built-in passthrough on
one side is elided, and two passthroughs stay passthrough. -/
def seqAct (sq : A → A → A) : Act A → Act A → Act A
  | .passthrough, i => i
  | c, .passthrough => c
  | .other a, .other b => .other (sq a b)

/-! ## Arc kinds on a place (rule (d)) -/

/-- The kinds of arc a transition has on one place: input, inhibitor, read, reset (outputs are
not arcs of this check). -/
structure ArcKinds where
  /-- An input arc. -/
  input     : Bool
  /-- An inhibitor arc. -/
  inhibitor : Bool
  /-- A read arc. -/
  read      : Bool
  /-- A reset arc. -/
  reset     : Bool
  deriving DecidableEq, Repr

/-- Some arc. -/
def ArcKinds.any (k : ArcKinds) : Bool := k.input || k.inhibitor || k.read || k.reset

/-- An arc-kind set as the rule (d) diagnostic renders it, sorted as Rust's `BTreeSet` and Java's
and TypeScript's sorted sets: `[inhibitor, input, read, reset]`. -/
def ArcKinds.str (k : ArcKinds) : String :=
  "[" ++ ", ".intercalate
    ((if k.inhibitor then ["inhibitor"] else []) ++ (if k.input then ["input"] else []) ++
      (if k.read then ["read"] else []) ++ (if k.reset then ["reset"] else [])) ++ "]"

/-- The places of a definition's input, inhibitor, read and reset arcs, in that order (no output
place). -/
def kindPlaces (d : TransDef N A) : List N :=
  d.core.inputs.map (·.place) ++ d.core.inhibitors ++ d.core.reads ++ d.core.resets

/-- The kinds of arc a definition has on place `p`. -/
def arcKinds [DecidableEq N] (d : TransDef N A) (p : N) : ArcKinds :=
  ⟨decide (p ∈ d.core.inputs.map (·.place)), decide (p ∈ d.core.inhibitors),
    decide (p ∈ d.core.reads), decide (p ∈ d.core.resets)⟩

/-- **The arc kinds agree** ([MOD-021] rule (d), set reading): on every place where both sides
have an input, inhibitor, read or reset arc, the two sides have the same set of arc kinds. Two
sides that each read and reset one place agree; one side's input and the other's reset do not. -/
def KindsAgree [DecidableEq N] (c i : TransDef N A) : Prop :=
  ∀ p ∈ kindPlaces c, p ∈ kindPlaces i → arcKinds c p = arcKinds i p

/-- The first place of the instance side (in its arc order) where both sides have arcs of
different kinds. Which offender a rejection names when there are several is not stated. -/
def kindConflict [DecidableEq N] (c i : TransDef N A) : Option N :=
  (kindPlaces i).find? fun p => (arcKinds c p).any && decide (arcKinds c p ≠ arcKinds i p)

/-- The rule (d) rejection, naming the channel, the place and both kind sets ([MOD-021] AC7). The
text is a stand-in for the runtimes' (only its parts are stated). -/
def kindMsg [ToString N] (name : String) (p : N) (kc ki : ArcKinds) : String :=
  s!"Channel composition '{name}': conflicting arc kinds on place '{p}', caller-side {kc.str} vs instance-side {ki.str}. Different arc types on one place cannot be merged (MOD-021 rule (d)). Resolve explicitly."

/-! ## The merged definition -/

/-- The seam of a channel-merge diagnostic: `Channel composition '<name>'`, the caller's name, for
every place. -/
def chanSeam (name : String) : N → String := fun _ => "Channel composition '" ++ name ++ "'"

/-- The duplicate-free union of two arc lists, caller first, first occurrence kept (Rust
`union_arcs`, Java `unionArcs`, TypeScript `unionArcs`; rule (a)). -/
def unionArcs [DecidableEq N] (xs ys : List N) : List N := (xs ++ ys).eraseDups

/-- The merged output specification: `And(caller, instance)` when both sides have one, the one
side's when only one has, none when neither has (all three runtimes, `merge_outputs`). -/
def mergeOut : Option (Out N) → Option (Out N) → Option (Out N)
  | none, none => none
  | some c, none => some c
  | none, some i => some i
  | some c, some i => some (.and c i)

/-- **The merged definition** from the merged input arcs `ins`, the merged timing `tm` and the
merged correspondence `corr`: the caller's name and priority, the union of read, inhibitor and
reset arcs, the merged output specification and the action `sq caller instance`. -/
def mergedDef [DecidableEq N] (sq : Act A → Act A → Act A) (c i : CDef N A) (tm : Timing)
    (ins : List (NInSpec N)) (corr : Option (List (N × N))) : CDef N A where
  core := ⟨c.core.name, ins, unionArcs c.core.inhibitors i.core.inhibitors,
    unionArcs c.core.reads i.core.reads, unionArcs c.core.resets i.core.resets⟩
  out := mergeOut c.out i.out
  timing := tm
  priority := c.priority
  action := sq c.action i.action
  corr := corr

/-! ## The input-arc merge per place -/

/-- The cardinality of the first input arc on `p` in a list of input arcs (`none`: no arc). -/
def cardAt [DecidableEq N] (xs : List (NInSpec N)) (p : N) : Option Card :=
  (xs.find? fun s => decide (s.place = p)).map (·.card)

/-- Two sides' arcs on one place merged: the one side's when only one has an arc, the table's
merge when both have. -/
def mergeAt : Option Card → Option Card → Option Card
  | none, b => b
  | a, none => a
  | some a, some b => mergeCard a b

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N A : Type}

section Merge

variable [DecidableEq N] [ToString N]

/-- **The reference channel merge** ([MOD-021]): merge the timings, the correspondences, check the
arc kinds, merge the input arcs by the table, assemble the merged definition and pass it through
the transition builder's check `Build`, in Rust's order; the first failure rejects. -/
def refMerge (Build : Trans N → Option String) (sq : Act A → Act A → Act A)
    (cm : CorrMergeFn N A) : MergeFn N A := fun c i =>
  match rtMergeTiming c.timing i.timing with
  | none => .error (timingMsg c.core.name c.timing i.timing)
  | some tm =>
    match cm c i with
    | .error m => .error m
    | .ok corr =>
      match kindConflict c.toTransDef i.toTransDef with
      | some p => .error (kindMsg c.core.name p (arcKinds c.toTransDef p) (arcKinds i.toTransDef p))
      | none =>
        match mergeInputsE (c.core.inputs ++ i.core.inputs) with
        | .error col => .error (fuseMsg (chanSeam c.core.name) col)
        | .ok ins =>
          match Build (mergedDef sq c i tm ins corr).toTrans with
          | some m => .error m
          | none => .ok (mergedDef sq c i tm ins corr)

/- The reference channel merge is the witness model of the merge block. -/
#spec_witness refMerge

end Merge

/-! ## Lemmas: timing -/

section TimingLemmas

/-- The merged timing is always one of the two sides' timings. -/
theorem rtMergeTiming_side {c i r : Timing} (h : rtMergeTiming c i = some r) : r = c ∨ r = i := by
  cases c <;> cases i <;> simp [rtMergeTiming] at h <;>
    first
    | (subst h; simp)
    | (obtain ⟨-, rfl⟩ := h; simp)

/-- The timing merge is symmetric. -/
theorem rtMergeTiming_comm (c i : Timing) : rtMergeTiming c i = rtMergeTiming i c := by
  cases c <;> cases i <;> simp only [rtMergeTiming] <;> (try split_ifs) <;> simp_all [eq_comm]

/-- Two timings have no merge exactly when neither is `Immediate` and they differ. -/
theorem rtMergeTiming_eq_none_iff {c i : Timing} :
    rtMergeTiming c i = none ↔ c ≠ .immediate ∧ i ≠ .immediate ∧ c ≠ i := by
  cases c <;> cases i <;> simp [rtMergeTiming]

/-- `Immediate` yields to the other side. -/
theorem rtMergeTiming_immediate_left (i : Timing) : rtMergeTiming .immediate i = some i := rfl

/-- `Immediate` yields to the other side. -/
theorem rtMergeTiming_immediate_right (c : Timing) : rtMergeTiming c .immediate = some c := by
  cases c <;> rfl

/-- Equal timings collapse. -/
theorem rtMergeTiming_self (c : Timing) : rtMergeTiming c c = some c := by
  cases c <;> simp [rtMergeTiming]

/-- The merged timing of two valid timings is valid ([TIME-001] AC4). -/
theorem rtMergeTiming_valid {c i r : Timing} (hc : c.Valid) (hi : i.Valid)
    (h : rtMergeTiming c i = some r) : r.Valid := by
  rcases rtMergeTiming_side h with rfl | rfl
  · exact hc
  · exact hi

/-- The merged timing is reapable exactly when one of the sides is ([TIME-006]): the merge never
turns a deadline into a soft bound or the reverse. -/
theorem rtMergeTiming_reapable {c i r : Timing} (h : rtMergeTiming c i = some r) :
    r.reapable = (c.reapable || i.reapable) := by
  cases c <;> cases i <;> simp [rtMergeTiming] at h <;> (try obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h) <;>
    simp [Timing.reapable]

end TimingLemmas

/-! ## Lemmas: action, arcs, output -/

section PartLemmas

/-- A passthrough caller action yields to the instance's. -/
theorem seqAct_passthrough_left (sq : A → A → A) (i : Act A) : seqAct sq .passthrough i = i := rfl

/-- A passthrough instance action yields to the caller's. -/
theorem seqAct_passthrough_right (sq : A → A → A) (c : Act A) : seqAct sq c .passthrough = c := by
  cases c <;> rfl

/-- Two non-passthrough actions run caller first. -/
theorem seqAct_other (sq : A → A → A) (a b : A) :
    seqAct sq (.other a) (.other b) = .other (sq a b) := rfl

variable [DecidableEq N]

/-- The union of two arc lists holds exactly the arcs of either. -/
theorem mem_unionArcs {xs ys : List N} {p : N} : p ∈ unionArcs xs ys ↔ p ∈ xs ∨ p ∈ ys := by
  simp [unionArcs, List.mem_eraseDups]

omit [DecidableEq N] in
/-- Both sides have an output specification: the merged one is `And(caller, instance)`. -/
theorem mergeOut_both (o o' : Out N) : mergeOut (some o) (some o') = some (.and o o') := rfl

omit [DecidableEq N] in
/-- Only one side has an output specification: the merged one is that side's. -/
theorem mergeOut_one (o : Out N) : mergeOut (some o) none = some o ∧ mergeOut none (some o) = some o :=
  ⟨rfl, rfl⟩

omit [DecidableEq N] in
/-- The places of the merged output specification are the caller's, then the instance's. -/
theorem outPlaces_mergeOut (o o' : Option (Out N)) :
    ((mergeOut o o').map outPlaces).getD [] = (o.map outPlaces).getD [] ++ (o'.map outPlaces).getD [] := by
  cases o <;> cases o' <;> simp [mergeOut, outPlaces]

/-- Some arc on `p` exactly when `p` is a place of an input, inhibitor, read or reset arc. -/
theorem arcKinds_any_iff {d : TransDef N A} {p : N} :
    (arcKinds d p).any = true ↔ p ∈ kindPlaces d := by
  simp [ArcKinds.any, arcKinds, kindPlaces, or_assoc]

/-- No kind conflict is found exactly when the arc kinds agree. -/
theorem kindConflict_eq_none_iff {c i : TransDef N A} :
    kindConflict c i = none ↔ KindsAgree c i := by
  unfold kindConflict KindsAgree
  rw [List.find?_eq_none]
  constructor
  · intro h p hc hi
    have := h p hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, arcKinds_any_iff, not_and, not_not] at this
    exact this hc
  · intro h p hi hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, arcKinds_any_iff] at hp
    exact hp.2 (h p hp.1 hi)

/-- A kind conflict found is a place where both sides have arcs, of different kinds. -/
theorem kindConflict_some {c i : TransDef N A} {p : N} (h : kindConflict c i = some p) :
    p ∈ kindPlaces c ∧ p ∈ kindPlaces i ∧ arcKinds c p ≠ arcKinds i p := by
  unfold kindConflict at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, arcKinds_any_iff] at hp
  exact ⟨hp.1, hm, hp.2⟩

/-- **The sole offender is named**: when `p` is the only place where both sides have arcs of
different kinds, the conflict found is `p`. -/
theorem kindConflict_sole {c i : TransDef N A} {p : N} (hpc : p ∈ kindPlaces c)
    (hpi : p ∈ kindPlaces i) (hne : arcKinds c p ≠ arcKinds i p)
    (hsole : ∀ q ∈ kindPlaces c, q ∈ kindPlaces i → arcKinds c q ≠ arcKinds i q → q = p) :
    kindConflict c i = some p := by
  cases h : kindConflict c i with
  | none => exact absurd (kindConflict_eq_none_iff.1 h p hpc hpi) hne
  | some q =>
    obtain ⟨h1, h2, h3⟩ := kindConflict_some h
    rw [hsole q h1 h2 h3]

/-- The places the merged definition names: the caller's and the instance's (the merge names no
new place and drops none), when the input arcs merged to `ins`. -/
theorem mergedDef_namedPlaces {sq : Act A → Act A → Act A} {c i : CDef N A} {tm : Timing}
    {ins : List (NInSpec N)} {corr : Option (List (N × N))}
    (hins : ∀ p, p ∈ ins.map (·.place) ↔ p ∈ (c.core.inputs ++ i.core.inputs).map (·.place))
    (q : N) :
    q ∈ (mergedDef sq c i tm ins corr).namedPlaces ↔ q ∈ c.namedPlaces ∨ q ∈ i.namedPlaces := by
  have ho := outPlaces_mergeOut c.out i.out
  simp only [TransDef.namedPlaces, mergedDef] at ho ⊢
  rw [ho]
  simp only [List.mem_append, mem_unionArcs]
  rw [hins q]
  simp only [List.map_append, List.mem_append]
  tauto

end PartLemmas

/-! ## Lemmas: the input-arc merge -/

section InputLemmas

variable [DecidableEq N]

/-- An arc on a place the list does not hold is appended. -/
theorem insertInE_fresh :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N), s.place ∉ acc.map (·.place) →
      insertInE acc s = .ok (acc ++ [s])
  | [], _, _ => rfl
  | a :: rest, s, h => by
    have ha : a.place ≠ s.place := fun e => h (by simp [e])
    have hr : s.place ∉ rest.map (·.place) := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [insertInE, if_neg ha, insertInE_fresh rest s hr]
    rfl

/-- Arcs on pairwise distinct places, none held already, are appended. -/
theorem foldlM_insertInE_fresh :
    ∀ (xs acc : List (NInSpec N)), (acc.map (·.place) ++ xs.map (·.place)).Nodup →
      xs.foldlM insertInE acc = .ok (acc ++ xs)
  | [], acc, _ => by simp [pure, Except.pure]
  | x :: xs, acc, h => by
    have hx : x.place ∉ acc.map (·.place) := by
      intro hm
      simp only [List.map_cons, List.nodup_append, List.nodup_cons] at h
      exact h.2.2 _ hm _ List.mem_cons_self rfl
    rw [List.foldlM_cons, insertInE_fresh acc x hx]
    simp only [bind, Except.bind]
    rw [foldlM_insertInE_fresh xs (acc ++ [x]) (by simpa using h)]
    simp

/-- **Arcs on distinct places pass through unchanged** ([MOD-021] AC1): a list of input arcs on
pairwise distinct places merges to itself. -/
theorem mergeInputsE_nodup {xs : List (NInSpec N)} (h : (xs.map (·.place)).Nodup) :
    mergeInputsE xs = .ok xs := by
  unfold mergeInputsE
  simpa using foldlM_insertInE_fresh xs [] (by simpa using h)

/-- Two arcs on one place merge by the table, or collide. -/
theorem mergeInputsE_pair (p : N) (a b : Card) :
    mergeInputsE [⟨p, a⟩, ⟨p, b⟩] =
      match mergeCard a b with
      | some m => .ok [⟨p, m⟩]
      | none => .error ⟨p, a, b⟩ := by
  cases h : mergeCard a b <;>
    simp [mergeInputsE, insertInE, h, List.foldlM, bind, Except.bind, pure, Except.pure]

/-- The first arc on `p` of a list whose head is on `p`. -/
theorem cardAt_cons_self (s : NInSpec N) (rest : List (NInSpec N)) :
    cardAt (s :: rest) s.place = some s.card := by
  simp [cardAt]

/-- The first arc on `p` of a list whose head is on another place. -/
theorem cardAt_cons_other (s : NInSpec N) (rest : List (NInSpec N)) {p : N} (h : s.place ≠ p) :
    cardAt (s :: rest) p = cardAt rest p := by
  simp [cardAt, h]

/-- A list has an arc on `p` exactly when `p` is one of its places. -/
theorem cardAt_isSome_iff (xs : List (NInSpec N)) (p : N) :
    (cardAt xs p).isSome ↔ p ∈ xs.map (·.place) := by
  induction xs with
  | nil => simp [cardAt]
  | cons s rest ih =>
    by_cases h : s.place = p
    · subst h; simp [cardAt_cons_self]
    · rw [cardAt_cons_other s rest h, ih]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

/-- **One insertion, per place** (for a list holding at most one arc per place): an arc on `p`
already held merges with it by the table, an arc on a new place is added, every other place keeps
its arc; the insertion fails exactly when the held arc and the new one have no merge. -/
theorem insertInE_cardAt :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N), (acc.map (·.place)).Nodup →
      (∀ acc', insertInE acc s = .ok acc' →
        (acc'.map (·.place)).Nodup ∧ ∀ p, cardAt acc' p = if p = s.place then mergeAt (cardAt acc p) (some s.card) else cardAt acc p) ∧
      ((∃ col, insertInE acc s = .error col) ↔ ∃ a, cardAt acc s.place = some a ∧ mergeCard a s.card = none)
  | [], s, _ => by
    refine ⟨fun acc' h => ?_, ?_⟩
    · simp only [insertInE, Except.ok.injEq] at h
      subst h
      refine ⟨by simp, fun p => ?_⟩
      by_cases hp : p = s.place
      · subst hp; simp [cardAt, mergeAt]
      · simp [cardAt, hp, Ne.symm hp]
    · simp [insertInE, cardAt]
  | a :: rest, s, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases he : a.place = s.place
    · cases hm : mergeCard a.card s.card with
      | none =>
        refine ⟨fun acc' h => ?_, ?_⟩
        · simp [insertInE, he, hm] at h
        · refine iff_of_true ⟨⟨s.place, a.card, s.card⟩, by simp [insertInE, he, hm]⟩ ?_
          exact ⟨a.card, by rw [← he, cardAt_cons_self], hm⟩
      | some m =>
        refine ⟨fun acc' h => ?_, ?_⟩
        · simp only [insertInE, if_pos he, hm, Except.ok.injEq] at h
          subst h
          refine ⟨by simpa using hnd, fun p => ?_⟩
          by_cases hp : p = s.place
          · subst hp
            rw [← he, cardAt_cons_self, cardAt_cons_self]
            simp [mergeAt, hm]
          · rw [if_neg hp, cardAt_cons_other _ _ (by simpa [he] using Ne.symm hp),
              cardAt_cons_other _ _ (by simpa [he] using Ne.symm hp)]
        · refine iff_of_false (fun ⟨col, hcol⟩ => by simp [insertInE, he, hm] at hcol) ?_
          rintro ⟨x, hx, hx'⟩
          rw [← he, cardAt_cons_self] at hx
          cases hx
          rw [hm] at hx'
          cases hx'
    · obtain ⟨ih1, ih2⟩ := insertInE_cardAt rest s hnd.2
      refine ⟨fun acc' h => ?_, ?_⟩
      · simp only [insertInE, if_neg he] at h
        obtain ⟨r, hr, rfl⟩ := except_map_ok_iff.1 h
        obtain ⟨hnd', hcard⟩ := ih1 r hr
        refine ⟨?_, fun p => ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨fun hm => ?_, hnd'⟩
          rcases List.mem_map.1 hm with ⟨y, hy, hye⟩
          rcases insertInE_places rest s r hr y hy with h1 | h1
          · exact he (hye ▸ h1)
          · exact hnd.1 (hye ▸ h1)
        · by_cases hp : a.place = p
          · subst hp
            rw [cardAt_cons_self, cardAt_cons_self, if_neg he]
          · rw [cardAt_cons_other _ _ hp, cardAt_cons_other _ _ hp, hcard p]
      · rw [cardAt_cons_other _ _ he, ← ih2]
        simp only [insertInE, if_neg he]
        constructor
        · rintro ⟨col, hcol⟩
          cases hr : insertInE rest s with
          | ok r => rw [hr] at hcol; cases hcol
          | error e => exact ⟨e, rfl⟩
        · rintro ⟨col, hcol⟩
          exact ⟨col, by rw [hcol]; rfl⟩

/-- A failed insertion names the place of the new arc, the arc held on it and the new arc's
cardinality, and the two have no merge. -/
theorem insertInE_error :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N) (col : Collision N), insertInE acc s = .error col →
      col.place = s.place ∧ cardAt acc s.place = some col.left ∧ col.right = s.card ∧
        mergeCard col.left col.right = none
  | [], s, col, h => by simp [insertInE] at h
  | a :: rest, s, col, h => by
    by_cases he : a.place = s.place
    · cases hm : mergeCard a.card s.card with
      | none =>
        simp only [insertInE, if_pos he, hm, Except.error.injEq] at h
        subst h
        refine ⟨rfl, ?_, rfl, hm⟩
        rw [← he, cardAt_cons_self]
      | some m => simp [insertInE, he, hm] at h
    · simp only [insertInE, if_neg he] at h
      cases hr : insertInE rest s with
      | ok r => rw [hr] at h; cases h
      | error e =>
        rw [hr] at h
        simp only [Except.map, Except.error.injEq] at h
        subst h
        obtain ⟨h1, h2, h3, h4⟩ := insertInE_error rest s _ hr
        exact ⟨h1, (by rw [cardAt_cons_other _ _ he]; exact h2), h3, h4⟩

/-- Two sides merged: with no arc on one side the other side's arc is kept. -/
theorem mergeAt_none_right (a : Option Card) : mergeAt a none = a := by
  cases a <;> rfl

/-- **Inserting arcs on pairwise distinct places, per place**: into a list holding at most one
arc per place, the arcs `ys` (at most one per place) are merged place by place: the result holds
on `p` the table's merge of the arc held on `p` and the arc of `ys` on `p`, at most one arc per
place, and every place where both have an arc has a merge; a failure names a place where both
have an arc, the two cardinalities, and the two have no merge. -/
theorem foldlM_insertInE_cardAt :
    ∀ (ys acc : List (NInSpec N)), (acc.map (·.place)).Nodup → (ys.map (·.place)).Nodup →
      (∀ zs, ys.foldlM insertInE acc = .ok zs →
        (zs.map (·.place)).Nodup ∧ (∀ p, cardAt zs p = mergeAt (cardAt acc p) (cardAt ys p)) ∧
        ∀ p a b, cardAt acc p = some a → cardAt ys p = some b → mergeCard a b ≠ none) ∧
      (∀ col, ys.foldlM insertInE acc = .error col →
        cardAt acc col.place = some col.left ∧ cardAt ys col.place = some col.right ∧
          mergeCard col.left col.right = none)
  | [], acc, hacc, _ => by
    refine ⟨fun zs h => ?_, fun col h => ?_⟩
    · simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨hacc, fun p => ?_, fun p a b _ hb => ?_⟩
      · simp [cardAt, mergeAt_none_right]
      · simp [cardAt] at hb
    · simp [pure, Except.pure] at h
  | y :: ys, acc, hacc, hys => by
    simp only [List.map_cons, List.nodup_cons] at hys
    have hyn : cardAt ys y.place = none := by
      cases h : cardAt ys y.place with
      | none => rfl
      | some b => exact absurd ((cardAt_isSome_iff ys y.place).1 (by simp [h])) hys.1
    obtain ⟨hins, hinsE⟩ := insertInE_cardAt acc y hacc
    rw [List.foldlM_cons]
    cases hy : insertInE acc y with
    | error e =>
      simp only [bind, Except.bind]
      refine ⟨fun zs h => (by cases h), fun col h => ?_⟩
      simp only [Except.error.injEq] at h
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := insertInE_error acc y _ hy
      refine ⟨(by rw [h1]; exact h2), ?_, h4⟩
      rw [h1, h3]; exact cardAt_cons_self y ys
    | ok acc1 =>
      simp only [bind, Except.bind]
      obtain ⟨hnd1, hcard1⟩ := hins acc1 hy
      have hnoErr : ∀ a, cardAt acc y.place = some a → mergeCard a y.card ≠ none := by
        intro a ha hm
        obtain ⟨col, hcol⟩ := hinsE.2 ⟨a, ha, hm⟩
        rw [hy] at hcol; cases hcol
      have hacc1 : ∀ p, p ≠ y.place → cardAt acc1 p = cardAt acc p := fun p hp => by
        rw [hcard1 p, if_neg hp]
      obtain ⟨ih1, ih2⟩ := foldlM_insertInE_cardAt ys acc1 hnd1 hys.2
      refine ⟨fun zs h => ?_, fun col h => ?_⟩
      · obtain ⟨hz1, hz2, hz3⟩ := ih1 zs h
        refine ⟨hz1, fun p => ?_, fun p a b ha hb => ?_⟩
        · rw [hz2 p]
          by_cases hp : p = y.place
          · subst hp
            rw [hyn, mergeAt_none_right, hcard1, if_pos rfl, cardAt_cons_self]
          · rw [hacc1 p hp, cardAt_cons_other _ _ (Ne.symm hp)]
        · by_cases hp : p = y.place
          · subst hp
            rw [cardAt_cons_self] at hb
            cases hb
            exact hnoErr a ha
          · rw [cardAt_cons_other _ _ (Ne.symm hp)] at hb
            exact hz3 p a b (by rw [hacc1 p hp]; exact ha) hb
      · obtain ⟨h1, h2, h3⟩ := ih2 col h
        have hne : col.place ≠ y.place := by
          intro e; rw [e, hyn] at h2; cases h2
        refine ⟨by rw [← hacc1 _ hne]; exact h1, ?_, h3⟩
        rw [cardAt_cons_other _ _ (Ne.symm hne)]; exact h2

/-- **The input-arc merge, per place** ([MOD-021] rule (b)): when each side holds at most one input
arc per place (every built transition does, [CORE-030]), a successful merge of the caller's arcs
followed by the instance's holds at most one arc per place, and on every place the table's merge
of the two sides' arcs there: one side's arc when only one side has one, `mergeCard` of the two
when both have. For example `one()` on `P` from each side gives a single `exactly(2)` on `P`. -/
theorem mergeInputsE_cardAt {xs ys zs : List (NInSpec N)} (hx : (xs.map (·.place)).Nodup)
    (hy : (ys.map (·.place)).Nodup) (h : mergeInputsE (xs ++ ys) = .ok zs) :
    (zs.map (·.place)).Nodup ∧ ∀ p, cardAt zs p = mergeAt (cardAt xs p) (cardAt ys p) := by
  unfold mergeInputsE at h
  rw [List.foldlM_append, foldlM_insertInE_fresh xs [] (by simpa using hx)] at h
  simp only [List.nil_append, bind, Except.bind] at h
  obtain ⟨h1, h2, -⟩ := (foldlM_insertInE_cardAt ys xs hx hy).1 zs h
  exact ⟨h1, h2⟩

/-- **A failed input-arc merge names a real collision** ([MOD-021] rule (c)): when each side holds
at most one input arc per place, a failure names a place where both sides have an input arc, the
caller's cardinality first and the instance's second, and the table has no merge for the pair. -/
theorem mergeInputsE_error {xs ys : List (NInSpec N)} {col : Collision N}
    (hx : (xs.map (·.place)).Nodup) (hy : (ys.map (·.place)).Nodup)
    (h : mergeInputsE (xs ++ ys) = .error col) :
    cardAt xs col.place = some col.left ∧ cardAt ys col.place = some col.right ∧
      mergeCard col.left col.right = none := by
  unfold mergeInputsE at h
  rw [List.foldlM_append, foldlM_insertInE_fresh xs [] (by simpa using hx)] at h
  simp only [List.nil_append, bind, Except.bind] at h
  exact (foldlM_insertInE_cardAt ys xs hx hy).2 col h

/-- **When the input-arc merge succeeds** ([MOD-021] rules (b), (c)): when each side holds at most
one input arc per place, the merge succeeds exactly when every place where both sides have an
input arc has a merge in the table. -/
theorem mergeInputsE_ok_iff {xs ys : List (NInSpec N)} (hx : (xs.map (·.place)).Nodup)
    (hy : (ys.map (·.place)).Nodup) :
    (∃ zs, mergeInputsE (xs ++ ys) = .ok zs) ↔
      ∀ p a b, cardAt xs p = some a → cardAt ys p = some b → mergeCard a b ≠ none := by
  have hfold : mergeInputsE (xs ++ ys) = ys.foldlM insertInE xs := by
    unfold mergeInputsE
    rw [List.foldlM_append, foldlM_insertInE_fresh xs [] (by simpa using hx)]
    rfl
  obtain ⟨hok, herr⟩ := foldlM_insertInE_cardAt ys xs hx hy
  rw [hfold]
  constructor
  · rintro ⟨zs, h⟩
    exact (hok zs h).2.2
  · intro h
    cases hr : ys.foldlM insertInE xs with
    | ok zs => exact ⟨zs, rfl⟩
    | error col =>
      obtain ⟨h1, h2, h3⟩ := herr col hr
      exact absurd h3 (h _ _ _ h1 h2)

end InputLemmas

/-! ## Lemmas: the reference merge -/

section MergeLemmas

variable [DecidableEq N] [ToString N] {Build : Trans N → Option String}
  {sq : Act A → Act A → Act A} {cm : CorrMergeFn N A}

/-- **When the reference merge succeeds**: the timings merge, the correspondences merge, the arc
kinds agree, the input arcs merge by the table, and the transition builder accepts the merged
definition, which is the result. -/
theorem refMerge_ok_iff {c i d : CDef N A} :
    refMerge Build sq cm c i = .ok d ↔
      ∃ tm corr ins, rtMergeTiming c.timing i.timing = some tm ∧ cm c i = .ok corr ∧
        KindsAgree c.toTransDef i.toTransDef ∧
        mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins ∧
        d = mergedDef sq c i tm ins corr ∧ Build d.toTrans = none := by
  unfold refMerge
  cases ht : rtMergeTiming c.timing i.timing with
  | none => simp
  | some tm =>
    cases hc : cm c i with
    | error m => simp
    | ok corr =>
      cases hk : kindConflict c.toTransDef i.toTransDef with
      | some p =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨_, _, _, _, _, hka, _⟩
        rw [← kindConflict_eq_none_iff, hk] at hka
        cases hka
      | none =>
        have hka := kindConflict_eq_none_iff.1 hk
        cases hi : mergeInputsE (c.core.inputs ++ i.core.inputs) with
        | error col => simp
        | ok ins =>
          cases hb : Build (mergedDef sq c i tm ins corr).toTrans with
          | some m =>
            simp only [hb, reduceCtorEq, false_iff]
            rintro ⟨tm', corr', ins', h1, h2, -, h4, rfl, h6⟩
            cases h1; cases h2; cases h4
            rw [hb] at h6; cases h6
          | none =>
            simp only [hb, Except.ok.injEq]
            constructor
            · rintro rfl; exact ⟨tm, corr, ins, rfl, rfl, hka, rfl, rfl, hb⟩
            · rintro ⟨tm', corr', ins', h1, h2, -, h4, rfl, -⟩
              cases h1; cases h2; cases h4; rfl

/-- **What a successful merge holds** ([MOD-021] clauses 1 to 5): the caller's name and priority,
the action `sq caller instance`, the merged output specification, the union of inhibitor, read
and reset arcs, the merged timing, the input arcs merged by the table, the merged
correspondence; the arc kinds agree and the transition builder accepts the result. -/
theorem refMerge_ok_fields {c i d : CDef N A} (h : refMerge Build sq cm c i = .ok d) :
    d.core.name = c.core.name ∧ d.priority = c.priority ∧ d.action = sq c.action i.action ∧
      d.out = mergeOut c.out i.out ∧
      d.core.inhibitors = unionArcs c.core.inhibitors i.core.inhibitors ∧
      d.core.reads = unionArcs c.core.reads i.core.reads ∧
      d.core.resets = unionArcs c.core.resets i.core.resets ∧
      rtMergeTiming c.timing i.timing = some d.timing ∧
      mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok d.core.inputs ∧
      cm c i = .ok d.corr ∧ KindsAgree c.toTransDef i.toTransDef ∧ Build d.toTrans = none := by
  obtain ⟨tm, corr, ins, h1, h2, h3, h4, rfl, h6⟩ := refMerge_ok_iff.1 h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h1, h4, h2, h3, h6⟩

/-- **Timings with no merge reject** ([MOD-021] AC2), naming the channel and both timings. The
reference checks the timing first (Rust's order); Java checks the arc kinds first, so a block that
claims this message adds the premise that the arc kinds agree. -/
theorem refMerge_timing {c i : CDef N A} (h : rtMergeTiming c.timing i.timing = none) :
    refMerge Build sq cm c i = .error (timingMsg c.core.name c.timing i.timing) := by
  simp only [refMerge, h]

/-- A correspondence merge that rejects rejects the channel merge with its message ([MOD-031]),
when the timings merge. -/
theorem refMerge_corr {c i : CDef N A} {tm : Timing} {m : String}
    (ht : rtMergeTiming c.timing i.timing = some tm) (hc : cm c i = .error m) :
    refMerge Build sq cm c i = .error m := by
  simp only [refMerge, ht, hc]

/-- **Different arc kinds on one place reject** ([MOD-021] rule (d), AC7), naming a place where
both sides have arcs of different kinds and both kind sets, when the timings and the
correspondences merge. -/
theorem refMerge_kinds {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    (ht : rtMergeTiming c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : ¬ KindsAgree c.toTransDef i.toTransDef) :
    ∃ p, p ∈ kindPlaces c.toTransDef ∧ p ∈ kindPlaces i.toTransDef ∧
      arcKinds c.toTransDef p ≠ arcKinds i.toTransDef p ∧
      refMerge Build sq cm c i =
        .error (kindMsg c.core.name p (arcKinds c.toTransDef p) (arcKinds i.toTransDef p)) := by
  cases h : kindConflict c.toTransDef i.toTransDef with
  | none => exact absurd (kindConflict_eq_none_iff.1 h) hk
  | some p =>
    obtain ⟨h1, h2, h3⟩ := kindConflict_some h
    exact ⟨p, h1, h2, h3, by simp only [refMerge, ht, hc, h]⟩

/-- **The sole kind conflict is named**: when `p` is the only place where both sides have arcs of
different kinds, the merge rejects naming `p` and both kind sets. -/
theorem refMerge_kinds_sole {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))} {p : N}
    (ht : rtMergeTiming c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hpc : p ∈ kindPlaces c.toTransDef) (hpi : p ∈ kindPlaces i.toTransDef)
    (hne : arcKinds c.toTransDef p ≠ arcKinds i.toTransDef p)
    (hsole : ∀ q ∈ kindPlaces c.toTransDef, q ∈ kindPlaces i.toTransDef →
      arcKinds c.toTransDef q ≠ arcKinds i.toTransDef q → q = p) :
    refMerge Build sq cm c i =
      .error (kindMsg c.core.name p (arcKinds c.toTransDef p) (arcKinds i.toTransDef p)) := by
  simp only [refMerge, ht, hc, kindConflict_sole hpc hpi hne hsole]

/-- **An off-table pair of input arcs rejects** ([MOD-021] rule (c), AC8) with the shared
diagnostic, seam `Channel composition '<caller name>'`, when the timings and the correspondences
merge and the arc kinds agree. -/
theorem refMerge_offTable {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {col : Collision N} (ht : rtMergeTiming c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : KindsAgree c.toTransDef i.toTransDef)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .error col) :
    refMerge Build sq cm c i = .error (fuseMsg (chanSeam c.core.name) col) := by
  simp only [refMerge, ht, hc, kindConflict_eq_none_iff.2 hk, hi]

/-- **The sole off-table pair is named** ([MOD-021] AC8): when each side holds at most one input
arc per place and `P` is the only place where the caller's arc (`a`) and the instance's (`b`) have
no merge, the rejection is the rule (c) diagnostic naming the caller, `a`, `b` and `P`. -/
theorem refMerge_offTable_sole {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {p : N} {a b : Card} (ht : rtMergeTiming c.timing i.timing = some tm) (hc : cm c i = .ok corr)
    (hk : KindsAgree c.toTransDef i.toTransDef)
    (hx : (c.core.inputs.map (·.place)).Nodup) (hy : (i.core.inputs.map (·.place)).Nodup)
    (ha : cardAt c.core.inputs p = some a) (hb : cardAt i.core.inputs p = some b)
    (hab : mergeCard a b = none)
    (hsole : ∀ q a' b', cardAt c.core.inputs q = some a' → cardAt i.core.inputs q = some b' →
      mergeCard a' b' = none → q = p) :
    refMerge Build sq cm c i = .error (fuseMsg (chanSeam c.core.name) ⟨p, a, b⟩) := by
  cases hi : mergeInputsE (c.core.inputs ++ i.core.inputs) with
  | ok zs =>
    exact absurd hab ((mergeInputsE_ok_iff hx hy).1 ⟨zs, hi⟩ p a b ha hb)
  | error col =>
    obtain ⟨h1, h2, h3⟩ := mergeInputsE_error hx hy hi
    have hp := hsole _ _ _ h1 h2 h3
    rw [hp, ha] at h1
    rw [hp, hb] at h2
    cases h1; cases h2
    obtain ⟨q, l, r⟩ := col
    simp only at hp
    subst hp
    exact refMerge_offTable ht hc hk hi

/-- **A merged definition the transition builder rejects rejects the merge** with the builder's
message, when every earlier check passes. -/
theorem refMerge_buildFails {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {ins : List (NInSpec N)} {m : String} (ht : rtMergeTiming c.timing i.timing = some tm)
    (hc : cm c i = .ok corr) (hk : KindsAgree c.toTransDef i.toTransDef)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins)
    (hb : Build (mergedDef sq c i tm ins corr).toTrans = some m) :
    refMerge Build sq cm c i = .error m := by
  simp only [refMerge, ht, hc, kindConflict_eq_none_iff.2 hk, hi, hb]

/-- **Acceptance** ([MOD-021], skeptic correction S2): when the timings merge, the
correspondences merge, the arc kinds agree, the input arcs merge by the table and the transition
builder accepts the merged definition, the merge succeeds with it. -/
theorem refMerge_accepts {c i : CDef N A} {tm : Timing} {corr : Option (List (N × N))}
    {ins : List (NInSpec N)} (ht : rtMergeTiming c.timing i.timing = some tm)
    (hc : cm c i = .ok corr) (hk : KindsAgree c.toTransDef i.toTransDef)
    (hi : mergeInputsE (c.core.inputs ++ i.core.inputs) = .ok ins)
    (hb : Build (mergedDef sq c i tm ins corr).toTrans = none) :
    refMerge Build sq cm c i = .ok (mergedDef sq c i tm ins corr) := by
  simp only [refMerge, ht, hc, kindConflict_eq_none_iff.2 hk, hi, hb]

/-- **The merged input arcs, per place** ([MOD-021] rule (b), AC6): when each side holds at most
one input arc per place, a successful merge holds at most one input arc per place, and on every
place the table's merge of the two sides' arcs there. -/
theorem refMerge_cardAt {c i d : CDef N A} (h : refMerge Build sq cm c i = .ok d)
    (hx : (c.core.inputs.map (·.place)).Nodup) (hy : (i.core.inputs.map (·.place)).Nodup) :
    (d.core.inputs.map (·.place)).Nodup ∧
      ∀ p, cardAt d.core.inputs p = mergeAt (cardAt c.core.inputs p) (cardAt i.core.inputs p) :=
  mergeInputsE_cardAt hx hy (refMerge_ok_fields h).2.2.2.2.2.2.2.2.1

/-- **The places of a merged definition** are the caller's and the instance's: the merge names
no new place and drops none ([MOD-021] clause 1, AC1). -/
theorem refMerge_namedPlaces {c i d : CDef N A} (h : refMerge Build sq cm c i = .ok d)
    (hx : (c.core.inputs.map (·.place)).Nodup) (hy : (i.core.inputs.map (·.place)).Nodup)
    (q : N) : q ∈ d.namedPlaces ↔ q ∈ c.namedPlaces ∨ q ∈ i.namedPlaces := by
  obtain ⟨tm, corr, ins, -, -, -, hi, rfl, -⟩ := refMerge_ok_iff.1 h
  refine mergedDef_namedPlaces (fun p => ?_) q
  obtain ⟨-, hcard⟩ := mergeInputsE_cardAt hx hy hi
  have hall := (mergeInputsE_ok_iff hx hy).1 ⟨ins, hi⟩ p
  rw [List.map_append, List.mem_append, ← cardAt_isSome_iff ins, ← cardAt_isSome_iff c.core.inputs,
    ← cardAt_isSome_iff i.core.inputs, hcard p]
  cases ha : cardAt c.core.inputs p with
  | none => cases cardAt i.core.inputs p <;> simp [mergeAt]
  | some a =>
    cases hb : cardAt i.core.inputs p with
    | none => simp [mergeAt]
    | some b => simpa [mergeAt, Option.isSome_iff_ne_none] using hall a b ha hb

end MergeLemmas

/-! ## Examples -/

section Examples

/-- An example definition over named places with a list of strings as its action: name, input
arcs, output specification, then optionally inhibitor, read and reset arcs, timing, priority and
action. -/
def mergeExDef (nm : String) (ins : List (NInSpec String)) (out : Option (Out String))
    (inh reads resets : List String := []) (tm : Timing := .immediate) (prio : Int := 0)
    (act : Act (List String) := .passthrough) : CDef String (List String) :=
  { core := ⟨nm, ins, inh, reads, resets⟩, out := out, timing := tm, priority := prio,
    action := act }

/-- The example merge: the reference transition builder, actions run caller first (list
append, which is not commutative), and a correspondence merge that records none. -/
def mergeEx : MergeFn String (List String) :=
  refMerge refBuild (seqAct (· ++ ·)) (fun _ _ => .ok none)

/-- What a successful example merge holds: name, input arcs, output places and timing. -/
def mergeExView (d : CDef String (List String)) :
    String × List (String × Card) × Option (List String) × Timing :=
  (d.core.name, d.core.inputs.map (fun s => (s.place, s.card)), d.out.map outPlaces, d.timing)

/-- The message of a rejection, `none` for a success. -/
def mergeExMsg (r : Except String (CDef String (List String))) : Option String :=
  match r with
  | .error m => some m
  | .ok _ => none

/-- **Arcs on different places are unioned** ([MOD-021] AC1): caller `T` (input `P`, output `Q`)
merged with channel transition `C` (input `R`, output `S`) gives one transition named `T` that
takes from `P` and `R`, puts into `Q` and `S`, and is `Immediate`. -/
theorem mergeEx_union :
    (mergeEx (mergeExDef "T" [⟨"P", .one⟩] (some (.place "Q")))
        (mergeExDef "C" [⟨"R", .one⟩] (some (.place "S")))).toOption.map mergeExView =
      some ("T", [("P", .one), ("R", .one)], some ["Q", "S"], .immediate) := by
  decide

/-- **Two `one()` arcs on one place merge to `exactly(2)`** ([MOD-021] AC6), and the other rows:
`all()` with `all()` gives `all()`, `atLeast(1)` with `atLeast(3)` gives `atLeast(3)`. -/
theorem mergeEx_table :
    (mergeEx (mergeExDef "T" [⟨"P", .one⟩] none) (mergeExDef "C" [⟨"P", .one⟩] none)).toOption.map
        (fun d => d.core.inputs.map fun s => (s.place, s.card)) = some [("P", .exactly 2)] ∧
    (mergeEx (mergeExDef "T" [⟨"P", .all⟩] none) (mergeExDef "C" [⟨"P", .all⟩] none)).toOption.map
        (fun d => d.core.inputs.map fun s => (s.place, s.card)) = some [("P", .all)] ∧
    (mergeEx (mergeExDef "T" [⟨"P", .atLeast 1⟩] none)
        (mergeExDef "C" [⟨"P", .atLeast 3⟩] none)).toOption.map
        (fun d => d.core.inputs.map fun s => (s.place, s.card)) = some [("P", .atLeast 3)] := by
  decide

set_option maxRecDepth 20000 in
/-- **An off-table pair rejects with the shared diagnostic** ([MOD-021] AC8): caller `T` takes one
token from `P`, the channel transition takes every token from `P`; the merge fails naming the
seam `Channel composition 'T'`, both cardinalities and the place. -/
theorem mergeEx_offTable :
    mergeExMsg (mergeEx (mergeExDef "T" [⟨"P", .one⟩] none) (mergeExDef "C" [⟨"P", .all⟩] none)) =
      some "Channel composition 'T': input arcs one() and all() collide on place 'P' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)." := by
  decide

set_option maxRecDepth 20000 in
/-- **Different arc kinds on one place reject** ([MOD-021] AC7): caller `T` consumes from `P`, the
channel transition resets `P`; the merge fails naming the place and both kind sets. -/
theorem mergeEx_kinds :
    mergeExMsg (mergeEx (mergeExDef "T" [⟨"P", .one⟩] none) (mergeExDef "C" [] none [] [] ["P"])) =
      some "Channel composition 'T': conflicting arc kinds on place 'P', caller-side [input] vs instance-side [reset]. Different arc types on one place cannot be merged (MOD-021 rule (d)). Resolve explicitly." := by
  decide

/-- **The same arc kinds on both sides are no conflict** ([MOD-021] rule (d)): both sides read and
reset `P`; the merge keeps one read arc and one reset arc on `P` (rule (a)). -/
theorem mergeEx_sameKinds :
    (mergeEx (mergeExDef "T" [] none [] ["P"] ["P"]) (mergeExDef "C" [] none [] ["P"] ["P"])).toOption.map
        (fun d => (d.core.reads, d.core.resets)) = some (["P"], ["P"]) := by
  decide

set_option maxRecDepth 20000 in
/-- **Timings with no merge reject, naming both** ([MOD-021] AC2): `Delayed(100)` against
`Deadline(50)`. -/
theorem mergeEx_timings :
    mergeExMsg (mergeEx (mergeExDef "T" [] none (tm := .delayed 100))
        (mergeExDef "C" [] none (tm := .deadline 50))) =
      some "Channel composition 'T': conflicting non-Immediate timings, caller-side Delayed(100) vs instance-side Deadline(50). Resolve explicitly by aligning the timings on either side (MOD-021)." := by
  decide

/-- **The runtimes' timing rule** (ruling D77 (a)): `Immediate` yields to `Deadline(5)`; two equal
windows collapse; `Deadline(100)` against `Delayed(50)`, two different non-`Immediate` timings,
is rejected (the interval rule of the markdown before D77 would give `Window(50, 100)`). -/
theorem mergeEx_timingRule :
    (mergeEx (mergeExDef "T" [] none) (mergeExDef "C" [] none (tm := .deadline 5))).toOption.map
        (·.timing) = some (.deadline 5) ∧
    (mergeEx (mergeExDef "T" [] none (tm := .window 10 100))
        (mergeExDef "C" [] none (tm := .window 10 100))).toOption.map (·.timing) =
      some (.window 10 100) ∧
    (mergeEx (mergeExDef "T" [] none (tm := .deadline 100))
        (mergeExDef "C" [] none (tm := .delayed 50))).toOption.isNone = true := by
  decide

/-- **The caller's priority wins and its action runs first** ([MOD-021] clauses 3 and 4, AC4):
caller priority 3 against instance priority 7 gives 3; caller action `c` and instance action `i`
give the action `c` then `i`; a passthrough side is dropped. -/
theorem mergeEx_priorityAction :
    (mergeEx (mergeExDef "T" [] none (prio := 3) (act := .other ["c"]))
        (mergeExDef "C" [] none (prio := 7) (act := .other ["i"]))).toOption.map
        (fun d => (d.priority, d.action)) = some (3, .other ["c", "i"]) ∧
    (mergeEx (mergeExDef "T" [] none) (mergeExDef "C" [] none (act := .other ["i"]))).toOption.map
        (·.action) = some (.other ["i"]) := by
  decide

/-- **A merge the transition builder rejects fails** ([IO-011]): caller and channel transition
both put a token into `Q`; the merged output `And(Q, Q)` names `Q` twice in one AND branch. -/
theorem mergeEx_buildFails :
    (mergeEx (mergeExDef "T" [] (some (.place "Q")))
        (mergeExDef "C" [] (some (.place "Q")))).toOption.isNone = true := by
  decide

end Examples

end Libpetri.Reference
