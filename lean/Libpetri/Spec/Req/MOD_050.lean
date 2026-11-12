import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.ComposeBuild
import Libpetri.Reference.Decide

set_option linter.missingDocs true

/-!
# MOD-050: Verification pass-through on a composed flat net (`spec/11-modular-composition.md`)

MOD-050 says that the verifier needs no knowledge of composition: a net that `build()` returned
is verified as the hand-written net with the same places, transitions and terminal places.

A composed net is a `ComposedNet` (`Reference/ComposeBuild.lean`): core's built net (places,
transition definitions in order, terminal places) plus what composition leaves behind, the place
correspondence of each transition ([MOD-031]) and the subnet membership map ([MOD-026]). A
hand-written net carries neither (`handWritten`). The requirement is a predicate over a pair
`(F, V)` of a verification facility, for any result type `R`:

* `F : BuiltNet N A → R`, the facility as section 07 specifies it on a flat net (a property
  check, the P-invariant computation, a structural analysis, the untimed abstraction, the state
  class graph);
* `V : ComposedNet N A → R`, the same facility as the implementation runs it on a net that
  `build()` returned.

Line 1: on a hand-written net, `V` gives what `F` gives. Line 2: `V` gives one result on two nets
with the same built net, whatever correspondence and membership they carry. Together they say
`V c = F c.toBuiltNet` for every net (`mod050_iff_factor`). The witness is `refPassThrough F`,
the facility applied to the built net, and the block holds for every facility `F`.

Consequences, for every model of the block: a composed pipeline and its hand-written equivalent
get the same result (`mod050_ac2`); a net re-declared by hand from a built net gets the same
result from every facility that does not depend on the order in which places are listed
(`mod050_handWritten`, through [MOD-023] line 2), and a facility that indexes places sorted by
name, as the three runtimes' flat nets do, is such a facility (`mod050_sortIdx_orderFree`,
`mod050_pinvColumns`); at the reference verdict of `Reference/Decide.lean`, a composed net is
`Proven` exactly when the search over its flat net completed and no reachable marking violates
the property (`mod050_proven_iff`); every model accepts a composed net whenever section 07's
facility accepts its built net (`mod050_accepts`, the coverage side of the prose). Wrong
verifiers are killed: one that leaves out the places a subnet owns (reads membership), one that
reports places under their declared names (reads the correspondence), one that refuses nets
carrying a correspondence, and one that leaves out the transitions of subnet instances (adapts to
composition by name). A pass that copies the correspondence into a rebuilt net, as the runtimes'
rebuilding passes do, is allowed: its result does not depend on what it copies.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

section Model

variable {N A R : Type}

/-- **A built net as a hand-written net carries it**: the same places, transitions and terminal
places, no place correspondence on any transition ([MOD-031]) and no subnet membership
([MOD-026]). -/
def handWritten (b : BuiltNet N A) : ComposedNet N A :=
  { toBuiltNet := b, corrs := b.trans.map (fun _ => none), member := fun _ => none }

/-- **The reference pass-through**: a verification facility runs on a composed net by running
on its built net, reading neither the correspondence nor the membership map. -/
def refPassThrough (F : BuiltNet N A → R) : ComposedNet N A → R := fun c => F c.toBuiltNet

/- The pass-through is the witness model of MOD-050. -/
#spec_witness refPassThrough

end Model

/-! ## MOD-050: Verification Pass-Through on Composed Flat Net -/

requirement MOD_050
  id "MOD-050"
  title "Verification Pass-Through on Composed Flat Net"
  kind B
  scope "every verification facility of section 07, on every net build() returns"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* a verification facility specified in section 07 (VER) runs on a net that `build()` returned, it *shall* give the result that section 07 specifies for the hand-written net with the same name, the same places in the same order, the same transitions in the same order with the same names, arcs, output specifications, timing, priorities and actions, and the same terminal places in the same order."
        "The result of a verification facility specified in section 07 (VER) *shall not* depend on which subnet a place or transition belongs to ([MOD-026]) or on the place correspondence of a transition ([MOD-031])."
  reading "For every result type R, every facility F on built nets (the facility as section 07 specifies it) and every facility V on the nets build() returns:"
          "on the hand-written net of every built net b (no correspondence, no membership), V gives what F gives on b;"
          "on two nets c and c' with the same built net (the same places, transitions and terminal places, in the same order), V gives the same result, whatever correspondence and membership each carries."
  assumes "A net that build() returned is a ComposedNet (Reference/ComposeBuild.lean): core's BuiltNet (places, transition definitions in order, each with its name, arcs, output specification, timing, priority and action, terminal places) and the two things composition leaves on a net, the place correspondence of each transition (MOD-031: Rust local_name_map, Java and TypeScript placeAlias) and the membership map (MOD-026: Rust subnet_membership, rust/libpetri-core/src/petri_net.rs:40). A hand-written net is a ComposedNet with neither (handWritten), as buildScript builds it from place, trans and terminal calls (Op.ofBOp gives every transition the correspondence none; only direct composition records membership). A facility is a function of the net it runs on; its inputs other than the net (the property, the initial marking, the environment mode, the options) are part of the facility, so each choice of them is one F."
          "The net's name is not modelled. The first quoted sentence names it ('the same name') only so that the hand-written net it speaks of is one net; a facility whose result shows the name (a report title) gets the composed net's name on both sides. The model therefore covers the facilities whose result does not show the name, which are the ones items 1 to 5 list."
          "The statement is stronger than the sentences in one respect: it ranges over every ComposedNet value, not only the nets build() returns. Line 1 also speaks of hand-written nets the net builder would reject (two places with one name, a terminal clash of EXEC-042 AC5), and line 2 of values no script builds (a correspondence list whose length differs from the transitions', membership of a name the net does not hold). A verifier is only ever handed a built net, so the strengthening excludes only a verifier that is right on every buildable net and inconsistent on a value no runtime constructs; the reference meets the stronger form (MOD_050_reference)."
          "The first quoted sentence is lines 1 and 2 together: V c = F c.toBuiltNet for every net c (mod050_iff_factor), since c and handWritten c.toBuiltNet have the same built net. The places, the transitions and the terminal places are lists, and two built nets are equal when the three lists are, so the sentence says 'in the same order' of each. The line does not claim that a facility ignores the order: place order is non-normative (ruling D32), and composition does not fix it (Rust adds an instance's renamed places in hash-map order, rust/libpetri-core/src/rewriter.rs:84-96). The runtimes' verifiers do not see that order, because every flat net indexes its places sorted by name (rust/libpetri-verification/src/net_flattener.rs:101-104, typescript/src/verification/encoding/net-flattener.ts:82, java/src/main/java/org/libpetri/smt/encoding/NetFlattener.java:104), and the incidence matrix of the P-invariant computation and the SMT encodings are built from the flat net (IncidenceMatrix.from(FlatNet) in all three); such a facility is order-free (mod050_sortIdx_orderFree)."
          "The second quoted sentence is line 2: two nets that differ only in correspondence and membership get one result. It is about the result, not about which fields a facility touches. No verifier result depends on either. A grep of rust/libpetri-verification/src, java/src/main/java/org/libpetri/smt, java/src/main/java/org/libpetri/analysis and typescript/src/verification finds no read of subnet membership or subnetOf. The correspondence is read only where a verifier pass rebuilds a transition and copies it through unchanged: rust/libpetri-verification/src/reaping.rs:122-123, rust/libpetri-verification/src/in_flight.rs:404-405, java/src/main/java/org/libpetri/smt/Reaping.java:116, java/src/main/java/org/libpetri/analysis/InFlight.java:434, typescript/src/verification/reaping.ts:86, typescript/src/verification/in-flight.ts:370 and typescript/src/verification/terminal-places.ts:57. Such a pass meets the line (MOD_050_allows_copyThrough). The same line carries MOD-031's sentence that the correspondence is not consulted by the verifier (mod050_sameStructure cites it)."
          "A helper whose result is the rebuilt net itself (TypeScript relaxLate, exported at typescript/src/verification/index.ts:20; Java Reaping.relaxLate, java/src/main/java/org/libpetri/smt/Reaping.java:90; Rust relax_late, rust/libpetri-verification/src/reaping.rs:84) is not a facility of section 07, which names no such helper. Its result keeps the correspondence, so it would fail line 2 if it were one; the block does not range over it, and the verdicts computed on its net are facilities of the lines."
          "The prose sentence 'All verification facilities specified in section 07 (VER) MUST operate on a composed flat net per [MOD-023] without any composition-aware adaptation' is the two lines on its safety side: a verifier that adapts to composition by reading the leftovers breaks line 2 (MOD_050_forbids_readsMembership, MOD_050_forbids_readsCorr), and one that adapts by recognising subnet transitions in the names of the flat net breaks line 1 (MOD_050_mutant_structureOnly_killed). Its offer side, that the verifier runs on a composed net at all and does not refuse it, is a coverage theorem and no line: Mod050Covers asks that a composed net is accepted whenever section 07's facility accepts its built net, every model of the block meets it (mod050_accepts, the reference included), and a verifier that refuses every net carrying a correspondence is killed (MOD_050_forbids_refusesComposed). 'The verifier sees the composed net as a normal PetriNet' is lines 1 and 2; 'no modular extension to the verifier API is required' is API shape, not modelled: V and F take the same arguments by typing."
          "Items 1 to 5 name the facilities F the lines range over; each is specified by its own block on flat nets, and line 1 hands it the built net. Item 1 (VER-002) is instantiated at the reference verdict (mod050_proven_iff, cited for VER-002) and item 2 (VER-005) at the place index the incidence matrix is built over (mod050_pinvColumns, cited for VER-005). Items 3 to 5 (VER-020, VER-021, VER-004, VER-010) are linked through the free F only: no theorem here instantiates F with their blocks (open item). 'Where supported' in item 5 is configuration (kind N): an implementation without a state class graph has no such F."
          "AC1 (verification of a composed pipeline completes with a result of the same shape as for a hand-written net) is covered in part. 'The same shape' is the type of the lines: V and F have one result type R. 'Completes' is not modelled (a Lean function is total), and neither is the SMT route: AC1 is reached at the reference verdict only (Reference.verdict of Reference/Decide.lean over the flat net's toNet), where mod050_proven_iff reads the result on a composed net: Proven exactly when the search completed and no reachable marking violates the property (verdict_proven_iff)."
          "AC2 is reworded in the markdown to agree with the first quoted sentence: the results match on the hand-written equivalent that lists its places in the composed net's order, and a result that does not depend on the order of places matches on every hand-written equivalent per MOD-023. The first half is lines 1 and 2: on the test derivation's pipeline (a producer, a buffer instance with its input port bound to the host place, a consumer) the composed and the hand-written scripts build the same built net and different correspondences, and every model of the block gives them one result (mod050_ac2). The second half is mod050_handWritten: MOD-023 line 2 (buildScript_redeclare) gives the hand re-declaration the same transitions in order, the same places in some order and the same terminal places, so every model gives it the same result from every OrderFree facility. The runtimes' P-invariant computation and SMT encodings are OrderFree (above); mod050_pinvColumns shows the composed pipeline with its places in another order, as a Rust build may return it, and the hand-written pipeline getting one result. A facility that reports over the raw place order (mod050_placeIndex) is not OrderFree, and AC2 does not claim it matches a hand-written equivalent that lists its places in another order."
          "MOD-023 AC4 is the second half of AC2: MOD-023's block says its AC4 is MOD-050's line, which takes MOD-023 line 2 as its premise, and the link is the cites tag on mod050_handWritten. MOD-023's block is not imported here; its line 2 holds of the reference build script (mod023_buildScript), and spec_consistent_compose conjoins MOD_023 with this block on one model."
          "AC3 (P-invariant computation on a composed net succeeds and is over the composed, prefixed place names) is covered in part. By line 1 the computation runs on the built net, whose places carry the prefixed names (MOD-010, mod010_placeName; MOD-020 for bound ports). MOD_050_nonvacuous shows the place index on the composed pipeline (answer/OUT, not OUT), and mod050_pinvColumns the sorted index the incidence matrix is built over (A_IN, answer/OUT, done, src); a verifier that reports places under the names the subnet declared is killed (MOD_050_forbids_readsCorr). 'Succeeds' is not modelled, and these are stand-in facilities: VER-005's computation is over the numbered rows of the flat net (its InvFn), and no theorem here plugs that function into F (open item)."
          "The tests listed for MOD-050 in spec/00-index.md (Java SubnetVerifyTest, TypeScript subnet-verify.test.ts, Rust subnet_verify) verify subnets through MOD-051's harness, which composes a synthetic net and runs the standard verifier on it; they exercise line 1, not the comparison of AC2. No test in any language cites MOD-050 (spec/coverage-matrix.md:276, every language column empty), and none compares a composed net with its hand-written equivalent."
  signoff "pending"
  statement : ∀ {N A R : Type}, (BuiltNet N A → R) → (ComposedNet N A → R) → Prop :=
    fun F V =>
      (∀ b, V (handWritten b) = F b) ∧
      (∀ c c', c.toBuiltNet = c'.toBuiltNet → V c = V c')

/- The pinned readable form of MOD-050: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_050 : {N A R : Type} → (BuiltNet N A → R) → (ComposedNet N A → R) → Prop :=
fun {N A R} F V =>
  (∀ (b : BuiltNet N A), V (handWritten b) = F b) ∧
    ∀ (c c' : ComposedNet N A), c.toBuiltNet = c'.toBuiltNet → V c = V c'
-/
#guard_msgs in #print MOD_050

/-! ### The two lines, named (for the mutants) -/

section Lines

variable {N A R : Type}

/-- Line 1 of MOD-050: on a hand-written net the facility gives what section 07 specifies. -/
def mod050_line1 (F : BuiltNet N A → R) (V : ComposedNet N A → R) : Prop :=
  ∀ b : BuiltNet N A, V (handWritten b) = F b

/-- Line 2 of MOD-050: the correspondence and the membership map change no result. -/
def mod050_line2 (V : ComposedNet N A → R) : Prop :=
  ∀ c c' : ComposedNet N A, c.toBuiltNet = c'.toBuiltNet → V c = V c'

/-- MOD-050 is its two lines. -/
theorem mod050_iff (F : BuiltNet N A → R) (V : ComposedNet N A → R) :
    MOD_050 F V ↔ mod050_line1 F V ∧ mod050_line2 V :=
  Iff.rfl

/-- The hand-written net of a built net has that built net. -/
@[simp] theorem handWritten_toBuiltNet (b : BuiltNet N A) : (handWritten b).toBuiltNet = b :=
  rfl

/-- **The first quoted sentence.** A facility meets MOD-050 exactly when it runs on every net
as section 07's facility runs on that net's built net: a composed pipeline is verified as the
places, transitions and terminal places it holds, nothing else. -/
theorem mod050_iff_factor (F : BuiltNet N A → R) (V : ComposedNet N A → R) :
    MOD_050 F V ↔ ∀ c : ComposedNet N A, V c = F c.toBuiltNet := by
  constructor
  · rintro ⟨h1, h2⟩ c
    rw [h2 c (handWritten c.toBuiltNet) rfl, h1]
  · intro h
    refine ⟨fun b => by rw [h]; rfl, fun c c' hcc => by rw [h, h, hcc]⟩

end Lines

/-! ### The reference -/

/-- ✓ The pass-through meets MOD-050 for every facility. A net composed from the subnet `answer`
and the same net written by hand build the same places and transitions; the verifier is handed
that built net in both cases, so it gives one answer, whatever correspondence and membership
records the composed net carries beside it. -/
@[evidence holds MOD_050]
theorem MOD_050_reference {N A R : Type} (F : BuiltNet N A → R) :
    MOD_050 F (refPassThrough F) :=
  ⟨fun _ => rfl, fun c c' h => by simp only [refPassThrough, h]⟩

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A R : Type}

/-- **No composition leftover changes a result.** In every model of MOD-050, two nets with the
same places, transitions and terminal places get one result, whatever place correspondence and
membership each carries: a buffer instance composed into a pipeline is verified as the same
transitions written by hand. -/
@[evidence cites "MOD-031" "the correspondence is not consulted by the verifier: in every model of the MOD-050 block, two nets with the same built net get one result from every verification facility, whatever correspondence they carry"]
theorem mod050_sameStructure {F : BuiltNet N A → R} {V : ComposedNet N A → R}
    (h : MOD_050 F V) {c c' : ComposedNet N A} (hcc : c.toBuiltNet = c'.toBuiltNet) :
    V c = V c' :=
  h.2 c c' hcc

/-- A facility whose result does not depend on the order in which the places and the terminal
places of a built net are listed: two built nets with the same transitions in order, the same
places in some order and the same terminal places get one result. -/
def OrderFree (F : BuiltNet N A → R) : Prop :=
  ∀ b b' : BuiltNet N A, b.trans = b'.trans → b.places.Perm b'.places →
    (∀ p, p ∈ b.terminals ↔ p ∈ b'.terminals) → F b = F b'

/-- **AC2 through [MOD-023] line 2.** In every model of MOD-050, when a script builds a net `c`
(through the reference build script with any merge that only returns built definitions),
re-declaring `c` by hand (its places, then its transitions, then its terminal places) builds a
net that gets the same result as `c` from every facility that does not depend on the order of
places: the composed net and its hand-written equivalent verify alike. -/
@[evidence cites "MOD-023" "AC4: running verification on the composed net and on its hand-written equivalent gives identical results, for every model of the MOD-050 block and every verification facility that does not depend on the order of places, the hand-written net being the re-declaration of buildScript_redeclare"]
theorem mod050_handWritten [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
    {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}
    (hM : MergeBuilds Build Mg) {F : BuiltNet N A → R} {V : ComposedNet N A → R}
    (h : MOD_050 F V) (hF : OrderFree F) {ops : List (Op N A)} {c : ComposedNet N A}
    (hc : buildScript Nm tyOf Build Mg ops = .ok c) :
    ∃ c', buildScript Nm tyOf Build Mg ((redeclareOps c).map Op.ofBOp) = .ok c' ∧
      V c' = V c := by
  obtain ⟨c', hc', ht, hp, hterm⟩ := buildScript_redeclare hM hc
  refine ⟨c', hc', ?_⟩
  rw [(mod050_iff_factor F V).1 h, (mod050_iff_factor F V).1 h]
  exact hF _ _ ht hp hterm

/-- The flat net's view of a built net, as the three runtimes' flatteners build it before a
verifier reads it: the places sorted by name, the transitions in order, the terminal places in
the sorted order of the places. -/
def mod050_sortIdx [LinearOrder N] (b : BuiltNet N A) : BuiltNet N A :=
  let ps := b.places.insertionSort (· ≤ ·)
  { places := ps, trans := b.trans, terminals := ps.filter fun p => decide (p ∈ b.terminals) }

/-- **A facility that reads the sorted flat net is order-free**: whatever it computes from the
places sorted by name (the incidence matrix of the P-invariant computation, an SMT encoding), it
computes the same thing from every listing of the same places. So a net and every hand-written
equivalent of it per [MOD-023] get one result from it (`mod050_handWritten`). -/
theorem mod050_sortIdx_orderFree [LinearOrder N] (G : BuiltNet N A → R) :
    OrderFree (fun b => G (mod050_sortIdx b)) := by
  intro b b' ht hp hterm
  have hs : b.places.insertionSort (· ≤ ·) = b'.places.insertionSort (· ≤ ·) :=
    List.Perm.eq_of_sortedLE List.sortedLE_insertionSort List.sortedLE_insertionSort
      (((List.perm_insertionSort _ _).trans hp).trans (List.perm_insertionSort _ _).symm)
  have hf : (b.places.insertionSort (· ≤ ·)).filter (fun p => decide (p ∈ b.terminals)) =
      (b'.places.insertionSort (· ≤ ·)).filter (fun p => decide (p ∈ b'.terminals)) := by
    rw [hs]
    exact List.filter_congr fun p _ => by simp only [hterm p]
  show G (mod050_sortIdx b) = G (mod050_sortIdx b')
  dsimp only [mod050_sortIdx]
  rw [hf, hs, ht]

/-- **The coverage clause of the prose's offer**: the verifier runs on a composed net. Whenever
section 07's facility accepts a built net (its result passes `Acc`, the facility's own notion of
"not a refusal"), the facility run on a composed net with that built net accepts it too. -/
def Mod050Covers (Acc : R → Prop) (F : BuiltNet N A → R) (V : ComposedNet N A → R) : Prop :=
  ∀ c : ComposedNet N A, Acc (F c.toBuiltNet) → Acc (V c)

/-- **Every model of MOD-050 meets the coverage clause**: a verifier that meets the block never
refuses a composed net whose built net section 07's facility would verify. For a deadlock check,
a composed producer/buffer/consumer pipeline is verified exactly when the same three transitions
written by hand are. -/
@[evidence cites "MOD-050" "all verification facilities specified in section 07 (VER) operate on a composed flat net: in every model of the block, a composed net is accepted whenever section 07's facility accepts its built net, the reference pass-through included"]
theorem mod050_accepts {F : BuiltNet N A → R} {V : ComposedNet N A → R} (h : MOD_050 F V)
    (Acc : R → Prop) : Mod050Covers Acc F V := by
  intro c hc
  rw [(mod050_iff_factor F V).1 h c]
  exact hc

/-- The reference verdict as a facility on built nets: the verdict of `Reference/Decide.lean`
for property `φ` from the initial marking `m0` with search cap `cap`, on the built net's
untimed net. -/
def mod050_verdictF {K : Type} [LinearOrder K] [Hashable K] (φ : Property K) (m0 : Marking K)
    (cap : Nat) : BuiltNet K A → Verdict :=
  fun b => verdict b.toNet φ m0 cap (exploreNet b.toNet cap m0)

/-- **AC1 at the reference verdict.** In every model of MOD-050 whose facility is the reference
verdict, a composed net is `Proven` exactly when the search over its flat net completed and no
marking reachable in its flat net violates the property: the verdict on a composed pipeline
means what it means on the hand-written pipeline. -/
@[evidence cites "VER-002" "property checks (deadlock freedom, place bounds, mutual exclusion, unreachability) on a net that build() returned: in every model of the MOD-050 block whose facility is the reference verdict, a composed net is Proven exactly when the search over its flat net completed and no reachable marking of the flat net violates the property"]
theorem mod050_proven_iff {K : Type} [LinearOrder K] [Hashable K] {φ : Property K}
    {m0 : Marking K} {cap : Nat} {V : ComposedNet K A → Verdict}
    (h : MOD_050 (mod050_verdictF φ m0 cap) V) (hc : Canon m0) (c : ComposedNet K A) :
    V c = .proven ↔ (exploreNet c.toNet cap m0).2 = true ∧
      ∀ f, Reach c.toNet (get m0) f → ¬ Violates c.toNet φ f := by
  rw [(mod050_iff_factor _ V).1 h c]
  exact verdict_proven_iff hc φ

end Consequences

/-! ### Worked examples -/

section Examples

/-- The net a script builds, or the empty net when the script fails. -/
def mod050_build (ops : List (Op String Unit)) : ComposedNet String Unit :=
  match buildExScript ops with
  | .ok c => c
  | .error _ => { toBuiltNet := ⟨[], [], []⟩, corrs := [], member := fun _ => none }

/-- The composed pipeline of the test derivation: a producer from `src` to `A_IN`, the buffer
instance `answer` (`work` from `IN` to `OUT`) with its input port bound to `A_IN`, and a consumer
from `answer/OUT` to `done`. -/
def mod050_pipeOps : List (Op String Unit) :=
  [.trans (buildExDef "produce" [⟨"src", .one⟩] (some (.place "A_IN"))),
   .compose buildExInst [("in", "A_IN")] [],
   .trans (buildExDef "consume" [⟨"answer/OUT", .one⟩] (some (.place "done")))]

/-- The hand-written equivalent of the pipeline: the same three transitions added by hand. -/
def mod050_handOps : List (Op String Unit) :=
  [.trans (buildExDef "produce" [⟨"src", .one⟩] (some (.place "A_IN"))),
   .trans (buildExDef "answer/work" [⟨"A_IN", .one⟩] (some (.place "answer/OUT"))),
   .trans (buildExDef "consume" [⟨"answer/OUT", .one⟩] (some (.place "done")))]

/-- Two subnets composed directly, so that the net carries membership entries: `s/one` (`t1`
from `a` to `pipe`) and `two` (`t2` from `pipe` to `b`). -/
def mod050_directOps : List (Op String Unit) :=
  [.composeDirect buildExOne, .composeDirect buildExTwo]

/-- The place index a facility is computed over (the P-invariant weights and the SMT encodings
are indexed by it): the built net's places, in order. -/
def mod050_placeIndex {N A : Type} : BuiltNet N A → List N := fun b => b.places

/-- The transition index a facility is computed over: the built net's transition names, in
order. -/
def mod050_transIndex {N A : Type} : BuiltNet N A → List String :=
  fun b => b.trans.map (·.core.name)

set_option maxRecDepth 20000 in
/-- The composed pipeline and its hand-written equivalent build the same built net. -/
theorem mod050_pipe_hand :
    (mod050_build mod050_pipeOps).toBuiltNet = (mod050_build mod050_handOps).toBuiltNet := by
  rfl

/-- **AC2 and the test derivation.** Every model of MOD-050 gives the composed pipeline and its
hand-written equivalent the same result, from every facility: the deadlock-freedom verdict on
the pipeline with the buffer instance is the verdict on the same three transitions written by
hand. -/
theorem mod050_ac2 {R : Type} {F : BuiltNet String Unit → R} {V : ComposedNet String Unit → R}
    (h : MOD_050 F V) : V (mod050_build mod050_pipeOps) = V (mod050_build mod050_handOps) :=
  h.2 _ _ mod050_pipe_hand

/-- The composed pipeline as a Rust build may return it: the same transitions, correspondence and
membership, its places listed in another order (Rust adds an instance's renamed places in
hash-map order, and place order is non-normative). -/
def mod050_reorderedPipe : ComposedNet String Unit :=
  { mod050_build mod050_pipeOps with
    toBuiltNet := { (mod050_build mod050_pipeOps).toBuiltNet with
                    places := ["done", "answer/OUT", "A_IN", "src"] } }

set_option maxRecDepth 20000 in
/-- **AC2 and AC3 at the place index of the incidence matrix.** In every model of MOD-050 whose
facility reads the flat net with its places sorted by name (as the P-invariant computation of
every runtime does), the pipeline composed with its places in another order and the pipeline
written by hand get the same result, and the matrix columns are the prefixed names `A_IN`,
`answer/OUT`, `done`, `src`, not the buffer's own `IN` and `OUT`. -/
@[evidence cites "VER-005" "the P-invariant computation on a net that build() returned: in every model of the MOD-050 block whose facility reads the flat net with its places sorted by name, the composed pipeline with its places in any order and its hand-written equivalent get the same result, over the composed, prefixed place names"]
theorem mod050_pinvColumns {R : Type} {G : BuiltNet String Unit → R}
    {V : ComposedNet String Unit → R} (h : MOD_050 (fun b => G (mod050_sortIdx b)) V) :
    V mod050_reorderedPipe = V (mod050_build mod050_handOps) ∧
      (mod050_sortIdx mod050_reorderedPipe.toBuiltNet).places =
        ["A_IN", "answer/OUT", "done", "src"] := by
  refine ⟨?_, by decide⟩
  rw [(mod050_iff_factor _ V).1 h, (mod050_iff_factor _ V).1 h]
  refine mod050_sortIdx_orderFree G _ _ (by rfl) (by decide) (fun p => ?_)
  rw [show mod050_reorderedPipe.terminals = (mod050_build mod050_handOps).terminals by rfl]

set_option maxRecDepth 20000 in
/-- ✓ Both lines are exercised by the reference. On the composed pipeline the place index is
`src`, `A_IN`, `answer/OUT`, `done` (the prefixed names, AC3), the same as on the pipeline
written by hand, although the composed `answer/work` carries the correspondence `IN` to `A_IN`,
`OUT` to `answer/OUT` and the hand-written one none; with two subnets composed directly, `a` is
owned by `s_one`, and the place index still lists `a`, `pipe` and `b`, as on the same net
written by hand. -/
@[evidence nonvacuous MOD_050]
theorem MOD_050_nonvacuous :
    refPassThrough mod050_placeIndex (mod050_build mod050_pipeOps) =
        ["src", "A_IN", "answer/OUT", "done"] ∧
      refPassThrough mod050_placeIndex (mod050_build mod050_handOps) =
        ["src", "A_IN", "answer/OUT", "done"] ∧
      (mod050_build mod050_pipeOps).corrs =
        [none, some [("IN", "A_IN"), ("OUT", "answer/OUT")], none] ∧
      (mod050_build mod050_handOps).corrs = [none, none, none] ∧
      (mod050_build mod050_directOps).member "a" = some "s_one" ∧
      refPassThrough mod050_placeIndex (mod050_build mod050_directOps) =
        refPassThrough mod050_placeIndex (handWritten (mod050_build mod050_directOps).toBuiltNet) := by
  decide

end Examples

/-! ### Wrong verifiers -/

section Wrong

variable {N A R : Type}

/-- A verifier that reads membership: it leaves out every place a subnet owns, as if the
subnet's private places were outside the analysed net. -/
def mod050_readsMembership (F : BuiltNet String A → R) : ComposedNet String A → R :=
  fun c => F { c.toBuiltNet with places := c.places.filter fun p => (c.member p).isNone }

/-- The declared name of a place: the declared place a correspondence of some transition maps
to it, the place itself when none does. -/
def mod050_declared [DecidableEq N] (c : ComposedNet N A) (p : N) : N :=
  (((c.corrs.filterMap id).flatten.find? fun e => decide (e.2 = p)).map (·.1)).getD p

/-- A verifier that reads the correspondence: it reports every place under the name the subnet
declared for it, as a P-invariant computation that reports `OUT` for `answer/OUT` would. -/
def mod050_readsCorr [DecidableEq N] (F : BuiltNet N A → R) : ComposedNet N A → R :=
  fun c => F { c.toBuiltNet with places := c.places.map (mod050_declared c) }

/-- A verifier that adapts to composition by name: it leaves out every transition whose name
holds `/`, as if the transitions of subnet instances were a black box. -/
def mod050_subnetBlind (F : BuiltNet N A → R) : ComposedNet N A → R :=
  fun c => F { c.toBuiltNet with trans := c.trans.filter fun d => '/' ∉ d.core.name.toList }

set_option maxRecDepth 20000 in
/-- ✗ A verifier that reads membership violates MOD-050 (line 2): with `s/one` and `two`
composed directly, `a` belongs to `s_one` and `b` to `two`, so it reports the place `pipe`
only, while on the hand-written net with the same places and transitions it reports `a`, `pipe`
and `b`. -/
@[evidence forbids MOD_050]
theorem MOD_050_forbids_readsMembership :
    ¬ MOD_050 mod050_placeIndex (mod050_readsMembership (A := Unit) mod050_placeIndex) := by
  intro h
  have := h.2 (mod050_build mod050_directOps)
    (handWritten (mod050_build mod050_directOps).toBuiltNet) rfl
  revert this
  decide

set_option maxRecDepth 20000 in
/-- ✗ A verifier that reads the correspondence violates MOD-050 (line 2, and AC3): on the
composed pipeline it reports the places `src`, `IN`, `OUT`, `done`, the names the buffer
declared, while on the hand-written pipeline it reports `src`, `A_IN`, `answer/OUT`, `done`. -/
@[evidence forbids MOD_050]
theorem MOD_050_forbids_readsCorr :
    ¬ MOD_050 mod050_placeIndex (mod050_readsCorr (N := String) (A := Unit) mod050_placeIndex) := by
  intro h
  have := mod050_ac2 h
  revert this
  decide

/-- A verifier that refuses composed nets: it answers `none` (no result) on every net in which
some transition carries a place correspondence, and runs section 07's facility otherwise. -/
def mod050_refusesComposed (F : BuiltNet N A → Option R) : ComposedNet N A → Option R :=
  fun c => if c.corrs.any Option.isSome then none else F c.toBuiltNet

set_option maxRecDepth 20000 in
/-- ✗ A verifier that refuses composed nets violates MOD-050 (the offer of the prose, through
line 2): it verifies the hand-written pipeline and lists `src`, `A_IN`, `answer/OUT`, `done`, but
gives no result on the composed pipeline, whose `answer/work` carries the correspondence `IN` to
`A_IN`, `OUT` to `answer/OUT`. -/
@[evidence forbids MOD_050]
theorem MOD_050_forbids_refusesComposed :
    ¬ MOD_050 (fun b => some (mod050_placeIndex b))
      (mod050_refusesComposed (N := String) (A := Unit) fun b => some (mod050_placeIndex b)) := by
  intro h
  have := mod050_ac2 h
  revert this
  decide

/-- A verifier pass that rebuilds the net before it runs the facility, copying each transition's
place correspondence into the rebuilt net and dropping the membership map, as the runtimes'
reaping and in-flight passes do. -/
def mod050_copyThrough (c : ComposedNet N A) : ComposedNet N A :=
  { toBuiltNet := ⟨c.places, c.trans, c.terminals⟩, corrs := c.corrs, member := fun _ => none }

/-- The facility run on the net the copy-through pass rebuilt. -/
def mod050_copyThroughV (F : BuiltNet N A → R) : ComposedNet N A → R :=
  fun c => F (mod050_copyThrough c).toBuiltNet

set_option maxRecDepth 20000 in
/-- ✓ MOD-050 allows a pass that copies the correspondence through: it reads the correspondence
of `answer/work` on the composed pipeline (`IN` to `A_IN`, `OUT` to `answer/OUT`) and puts it on
the rebuilt net, but the facility's result depends only on the places, transitions and terminal
places, so the block holds for every facility. -/
@[evidence allows MOD_050]
theorem MOD_050_allows_copyThrough {R : Type} (F : BuiltNet String Unit → R) :
    MOD_050 F (mod050_copyThroughV F) ∧
      (mod050_copyThrough (mod050_build mod050_pipeOps)).corrs =
        [none, some [("IN", "A_IN"), ("OUT", "answer/OUT")], none] :=
  ⟨⟨fun _ => rfl, fun c c' hcc => by
      simp only [mod050_copyThroughV, mod050_copyThrough]; rw [← hcc]⟩, by decide⟩

/-- Mutant reading: MOD-050 without line 2, so a verifier need only be right on hand-written
nets and may read what composition leaves on a net. -/
def MOD_050_mutant_handWrittenOnly (F : BuiltNet N A → R) (V : ComposedNet N A → R) : Prop :=
  mod050_line1 F V

/-- The verifier that reads the correspondence kills the mutant: on a hand-written net no
transition carries a correspondence, so it reports every place under its own name (the mutant
holds), but on the composed pipeline it reports the declared names (line 2 fails). -/
@[evidence mutant MOD_050]
theorem MOD_050_mutant_handWrittenOnly_killed :
    MOD_050_mutant_handWrittenOnly mod050_placeIndex
        (mod050_readsCorr (N := String) (A := Unit) mod050_placeIndex) ∧
      ¬ MOD_050 mod050_placeIndex (mod050_readsCorr (N := String) (A := Unit) mod050_placeIndex) := by
  refine ⟨fun b => ?_, MOD_050_forbids_readsCorr⟩
  have hnil : (handWritten b).corrs.filterMap id = [] := by simp [handWritten]
  have hd : ∀ p, mod050_declared (handWritten b) p = p := fun p => by
    simp only [mod050_declared, hnil]; rfl
  show b.places.map (mod050_declared (handWritten b)) = b.places
  rw [show mod050_declared (handWritten b) = id from funext hd, List.map_id]

/-- Mutant reading: MOD-050 without line 1, so a verifier need only give one result on nets with
one built net, and may give another result than section 07 specifies. -/
def MOD_050_mutant_structureOnly (_F : BuiltNet N A → R) (V : ComposedNet N A → R) : Prop :=
  mod050_line2 V

set_option maxRecDepth 20000 in
/-- The verifier that leaves out the transitions of subnet instances kills the mutant: it reads
only the built net, so two nets with one built net get one result (the mutant holds), but on the
hand-written pipeline it reports the transitions `produce` and `consume` without `answer/work`,
which section 07's facility lists (line 1 fails). -/
@[evidence mutant MOD_050]
theorem MOD_050_mutant_structureOnly_killed :
    MOD_050_mutant_structureOnly mod050_transIndex
        (mod050_subnetBlind (N := String) (A := Unit) mod050_transIndex) ∧
      ¬ MOD_050 mod050_transIndex (mod050_subnetBlind (N := String) (A := Unit) mod050_transIndex) := by
  refine ⟨fun c c' hcc => ?_, fun h => ?_⟩
  · simp only [mod050_subnetBlind, hcc]
  · have := h.1 (mod050_build mod050_handOps).toBuiltNet
    revert this
    decide

end Wrong

end Libpetri.Spec
