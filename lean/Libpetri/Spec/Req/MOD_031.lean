import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.CORE_060
import Libpetri.Spec.Req.CORE_062
import Libpetri.Spec.Text.MOD_031

set_option linter.missingDocs true

/-!
# MOD-031: Action place resolution under composition (`spec/11-modular-composition.md`)

MOD-031 is a pure-function requirement (kind F) over the correspondence operations of a
composition implementation, `O : CorrOps N A`: one rewrite pass of a transition definition
through a place map and a name map (instantiation, port binding, fusion), the lookup that
resolves a declared place through a correspondence, the merge of a caller's and an instance's
correspondence in a channel merge, and the binding of an action. A transition definition is
`CDef` (`Spec/GlossaryCompose.lean`): RefNetBuild's `TransDef` plus `corr`, the correspondence
from declared places to the places the arcs now name (`none`: the transition carries none).

The statement has five lines (line 6, the context operations, is the second block of this file,
`MOD_031_ctx`; "firing, the verifier and the exporter never read the correspondence" is MOD-050's
line):

1. through any sequence of rewrite passes on a transition that carries no correspondence, every
   place its arcs and output specification name resolves to the place the same sequence of place
   maps sends it to, and every other place resolves to itself (AC1, AC3, AC8, AC9);
2. a pass sends the places of each arc kind (input, inhibitor, read, reset) and of the output
   specification through its place map, each kind on its own, the input places as a set (a
   fusion merges two input arcs it sends onto one place, MOD-061), so discovery returns the
   actual places (AC5); with line 1 the resolved place is a place the arcs name
   (`mod031_resolves_to_named`);
3. a transition that carries no correspondence resolves every place to itself (AC4);
4. the merge fails exactly on a place that both sides resolve elsewhere and to different
   places; a success resolves each place as the side that moves it does (AC10);
5. binding an action keeps the correspondence, the arcs and the output specification (AC7).

The witness is `refCorrOps`: the pass `CDef.map` (the correspondence chained, keys kept), the
lookup through the correspondence first, a merge that keeps the key set complete, and an action
binding that changes the action only; the runtimes merge the same way. A wrong merge that takes a
side's correspondence whole when the other side carries none also satisfies the block; after one
more pass it loses the caller's declared places (`MOD_031_mergeThenPass_undecided`, ruling
D69 (a)).

**Line 6, the context operations** (`MOD_031_ctx`, ruling D69 (a), map ruling R-MC3 (a)): a
predicate over a value projection, the correspondence operations `O` and a family `R` of transition
contexts (`Ctx`, `Spec/GlossaryContext.lean`), one for each correspondence a transition can carry.
The context of a transition that carries the correspondence `c` answers every call (`inputs`,
`input`, `inputToken`, `read`, `output`) on a place `p` as the context without a correspondence
answers it on `O.look c p`. So the declared-place check and the read or write of the token store
both use the resolved place. The witness is `refResCtx`, the reference context `refCtx` called
with the resolved place (Java, TypeScript and the Python binding adapter). With lines 1, 2 and 5
and the context rules of [CORE-060] and [CORE-062], an action's call on a declared place after
any sequence of passes, or after a late bind, answers on the place the passes sent it to
(`mod031ctx_after_passes`,
`mod031ctx_inputs_after_passes`, `mod031ctx_output_after_passes`, `mod031ctx_lateBind`). Wrong
contexts: one that does not resolve (forbidden), an adapter that tries the name first,
one that resolves for the check only, and ones that leave `output`, `read`, or `input` and
`inputToken` unresolved (one mutant each). `mod031ctx_collision` shows the case the order matters
for: a discovered place that is also a declared place the correspondence moved.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The correspondence operations -/

/-- **The correspondence operations** of a composition implementation ([MOD-031]). A
correspondence is a list of (declared place, actual place) pairs, `none` when the transition
carries none. -/
structure CorrOps (N A : Type) where
  /-- One rewrite pass of a definition through a place map and a name map (instantiation, port
  binding, fusion). -/
  pass : (N → N) → (String → String) → CDef N A → CDef N A
  /-- Resolve a declared place through a correspondence. -/
  look : Option (List (N × N)) → N → N
  /-- Merge the correspondences of a caller's and an instance's transition in a channel merge
  (caller first): the merged correspondence, or a rejection. -/
  merge : CDef N A → CDef N A → Except String (Option (List (N × N)))
  /-- Bind or rebind the action of a definition. -/
  rebind : CDef N A → Act A → CDef N A

section Model

variable {N A : Type}

/-- A sequence of rewrite passes, the first applied first. -/
def corrPasses (O : CorrOps N A) (ss : List ((N → N) × (String → String))) (d : CDef N A) :
    CDef N A :=
  ss.foldl (fun d s => O.pass s.1 s.2 d) d

/-- Where the place maps of a sequence of passes send a place, the first applied first. -/
def corrChain (ss : List ((N → N) × (String → String))) (p : N) : N :=
  ss.foldl (fun q s => s.1 q) p

/-- Place-set discovery, inputs: the places of a definition's input arcs (`inputPlaces`). -/
def discIn (d : TransDef N A) : List N := d.core.inputs.map (·.place)

/-- Place-set discovery, outputs: the places of a definition's output specification
(`outputPlaces`). -/
def discOut (d : TransDef N A) : List N := (d.out.map outPlaces).getD []

end Model

/-! ## MOD-031: Action Place Resolution under Composition -/

requirement MOD_031
  id "MOD-031"
  title "Action Place Resolution under Composition (declared → actual correspondence)"
  kind F
  scope "the declared-to-actual place correspondence of every composed transition, through rewrite passes, channel merges and action binding"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_031.s1, MOD_031.s2, MOD_031.s3, MOD_031.s4, MOD_031.s5, MOD_031.s6, MOD_031.s7
  reading "For every set of correspondence operations O (a rewrite pass, a lookup, a channel merge, an action binding):"
          "for every transition definition d that carries no correspondence and every sequence of passes ss (each a place map and a name map), every place p that d names resolves, through the correspondence of d after the passes, to the place the passes' place maps send p to, and every place x that d does not name resolves to x;"
          "for every pass (place map σ, name map g) and every d, the passed definition's input places are, as a set, d's input places mapped by σ, and, each kind on its own and in order, its inhibitor places, read places, reset places and output places are d's places of that kind mapped by σ;"
          "the lookup resolves every place to itself through no correspondence;"
          "for every caller definition c and instance definition i: if some place x resolves, through c's and through i's correspondence, to places other than x that differ, the merge fails; if no place does, the merge succeeds; and if the merge returns m, every place x resolves through m to what c's correspondence resolves it to when that is not x, and otherwise to what i's correspondence resolves it to;"
          "for every d and every action a, binding a to d keeps d's correspondence, its arcs and its output specification."
  assumes "The model (ruling D69 (a)). A correspondence is a list of (declared place, actual place) pairs, looked up first entry first; every runtime keeps it in a hash map keyed by the declared place, so a key has one entry (rust/libpetri-core/src/rewriter.rs build_local_name_map, java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java buildPlaceAlias). A rewrite pass is any place map: instantiation (MOD-010), port binding (MOD-020) and fusion (MOD-061), which all three runtimes run through the same rebuild (rust/libpetri-core/src/rewriter.rs rebuild_with_name, which apply_fusion calls directly or through substitute_places). The lookup is the correspondence's own lookup, correspondence first and the place itself when it has no entry, as Java and TypeScript resolve (java/src/main/java/org/libpetri/core/TransitionContext.java and typescript/src/core/transition-context.ts, resolve in each). How the context operations input, inputs, read and output use it, the Rust native context that does not resolve (rust/libpetri-core/src/context.rs, TransitionContext::input, the binding-hosted MAY) and the Python binding adapter, which resolves through the correspondence first (rust/libpetri-py/src/action.rs resolve), are line 6, the block MOD_031_ctx in this file."
          "Ruling D69 (a), single-valued and not 1:1: the correspondence maps each declared place to one actual place, and two declared places may map to one actual place when two ports are bound to one caller place (MOD-020) or two places are fused (MOD-061); MOD_031_allows_shared shows the reference doing so. The body sentence that calls the correspondence 1:1 is reworded to single-valued."
          "Ruling D69 (a), scope: line 1 covers transitions that no channel merge has joined, and so do the body's MUSTs on nested instantiation and on key-set completeness through every rewrite pass; for a transition that a channel merge joined no line states them. Rust, Java and TypeScript read a side of a channel merge that carries no correspondence as an identity entry for every place it names, take the union of the keys of both sides and drop the result as a whole when every entry is the identity (rust/libpetri-core/src/rewriter.rs merge_local_name_maps and side_map, called from merge_transitions; java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java mergeTransitions with sideAlias and mergePlaceAlias; typescript/src/core/internal/subnet-rewriter.ts mergeTransitions with sideAlias and mergePlaceAlias). The Python binding builds its nets through the Rust rewriter. That is the reference's key-complete merge (corrMergeVia corrSideFull), with AC9's drop, so the caller's declared places stay keys and a later pass that renames one of them (fusion at build, or instantiating the retrofitted net, MOD-014) moves it. A wrong merge that keeps the instance side's correspondence whole when the caller side carries none (carriedCorrOps, the behaviour RD-23 recorded) also satisfies the block, and the two differ after one more pass (MOD_031_mergeThenPass_undecided). The block does not kill carriedCorrOps: that needs a sentence on key-set completeness for a transition a channel merge joined, which the spec does not state (ruling D69 (a)), so MOD_031_mergeThenPass_undecided stays undecided although no runtime merges that way."
          "Line 1 has two halves. The first resolves every place the transition names before the passes; the second is the body's key-set MUST read from above: the chained pass does not re-derive keys from the arcs, whose names are intermediate-pass names the author never declared, so a place the transition did not name resolves to itself. A chained pass that carries the declared entries and also records each intermediate arc name behind them meets the first half and fails the second (MOD_031_mutant_lowerOnly_killed): a port-agnostic action that asks for an output place it discovered would be sent to an input place. The second half holds of the reference, of carriedCorrOps and of the pass that drops an all-identity correspondence (AC9)."
          "Line 2 names the places of every arc kind, not only the input and output places that discovery returns, and states each kind on its own: the relative clause of the line 1 sentence ('which is the place that the same arc or output now names') is line 1 with line 2 (mod031_resolves_to_named, through mod031_line2_namedPlaces), and the context operation read resolves through the correspondence (line 6, MOD_031_ctx). A pass that maps the input arcs and the output specification and leaves the inhibitor, read and reset arcs on their old places meets discovery and fails line 2 (MOD_031_mutant_discoveryOnly_killed). A pass that maps every place and then rebuilds each inhibitor arc as a read arc keeps the list of all named places and fails line 2, since an inhibitor turned into a read arc is an enabling condition (MOD_031_mutant_namedOnly_killed). Every runtime rebuilds each arc kind from the same kind, in order (rust/libpetri-core/src/rewriter.rs rebuild_with_name). Line 2 reads the input places as a set, as the sentence's 'place-set discovery' does, because of fusion: when a fusion (MOD-061) sends two input arcs of one transition onto one place, every runtime merges them into one arc by the merge table of MOD-021 (rust/libpetri-core/src/rewriter.rs apply_fusion with merge_input_arcs, java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java applyFusion with mergeInputArcs, typescript/src/core/internal/subnet-rewriter.ts applyFusion with normalizeInputArcs), so the input list holds that place once where the mapped list holds it twice, and the set of input places is still the mapped set, which is what discovery returns. So line 2 holds of that merge with no premise (MOD_031_allows_mergeInputs: a pass that keeps one input arc for each place after the place map satisfies the block, and on a fusion of two input places it leaves one input arc where the mapped list holds the place twice); the merged arc, its cardinality and its position are MOD-061's lines. Read, inhibitor and reset arcs that land on one place are kept as they are (MOD-061), so those kinds and the output specification are mapped as lists, in order. The reference pass maps the input list in order (TransDef.map), which meets the set reading; a pass that drops an input place or adds one fails it (MOD_031_forbids_extraInput: a pass that adds an input arc on a fresh place). The derived consequences (mod031_resolves_to_named, mod031_lateBind, mod031ctx_inputs_after_passes) need only membership and hold with no premise. The shape of the output specification and the input cardinalities are not places: the rewrite keeps them as MOD-010 line 3 and MOD-020 line 1 state (TransDef.map)."
          "Line 4 states the merge rule of the body (identity carries no assertion) as resolution: an entry that resolves a place to itself, and an absent entry, are both the identity, so the line quantifies over every place and a place that neither side holds as a key is one that both sides resolve to itself. After a channel merge one correspondence serves the actions of two authors: when the caller's hand-written transition and the instance's channel transition both declare one place name for two different places, the merged correspondence resolves it as the instance side does, and no single correspondence is right for both (clash mod-c#6); the block states the body's rule and no line claims more. The merge here is the correspondence part of a channel merge: the channel merge's other rejections (timing, match specification, arc kinds, the input-arc table) are MOD-021's, so line 4's success is the success of the correspondence part. Only failure is stated, not the message (Rust panics listing every conflict sorted by declared name, rust/libpetri-core/src/rewriter.rs merge_local_name_maps; Java and TypeScript throw). A merge that writes the instance side's entries last, so that an identity entry overwrites the caller's move, meets the rejection and success halves and fails the result half (MOD_031_mutant_noMergeResult_killed)."
          "Line 3 follows from line 1 at zero passes (mod031_line3_of_line1), so no model kills line 3 alone; it is kept as the line of AC4 and is a restatement, not an independent check. The 'directly-composed transition carries the identity correspondence' half of AC4 is direct composition adding a definition unchanged (MOD-025, not modelled here): such a definition carries no correspondence and line 3 applies."
          "AC1 (instance plus port binding, then ctx.input(declaredIn) and ctx.output(declaredOut) work) is line 1 at two passes, an instantiation and a port binding; that the context operation then passes its declared-place check and answers on the actual places is line 6 (MOD_031_ctx with mod031ctx_inputs_after_passes and mod031ctx_output_after_passes); that the transition then fires and deposits is EXEC's and CORE-062's. AC2 (Out.xor(aDecl, bDecl), the action selects aDecl, exactly one token on the actual a) is line 1 on the output place aDecl; the exactly-one-production check is EXEC's, and that output(aDecl, v) writes on the actual a is line 6 (mod031ctx_output_after_passes). AC3 (nested instantiation resolves to outer/inner/x) is line 1 at three passes; MOD_031_nonvacuous resolves the declared y to b/a/y; that the action's calls answer there is line 6 (mod031ctx_after_passes). AC5's first half (discovery returns the actual composed places) is line 2; its second half (port-agnostic actions written against discovery continue to work) is a claim about running actions and is line 6: a call on a discovered place that the correspondence resolves to itself answers for that place (mod031ctx_fixed), and a discovered place that is also a declared place the correspondence moved is resolved too (mod031ctx_collision)."
          "AC6 (structural equivalence per MOD-023: place index, transition count, arc topology, bitmap masks, timing arrays, without the correspondence) and the sentence that the correspondence is not consulted by enablement, firing, the verifier, the exporter or the event subsystem are MOD-050's line (wave W8) and MOD-023's: the firing view TransDef.toTrans and the structure read none of corr. 'Purely structural, fixed for the lifetime of the composed net' holds of the model's immutable values."
          "AC7 (an action bound after instantiation resolves as a baked-in action does) is line 5; mod031_lateBind derives, for every model of the block, that after a late bind every declared place resolves where the passes sent it and that place is still named by the transition's arcs or output specification. Line 5 keeps the arcs and the output specification as CORE-042's line 1 does on built nets. Rust rebuild_with_action carries local_name_map forward (rust/libpetri-core/src/transition.rs rebuild_with_action), and Java and TypeScript rebuildWithAction carry placeAlias (typescript/src/core/petri-net.ts rebuildWithAction). What the binding does to the action is CORE-042's and MOD-030's; that the late-bound action's calls answer on the places the passes sent its declared places to is line 6 (mod031ctx_lateBind). A binding that keeps the correspondence and drops the read arcs fails line 5 (MOD_031_mutant_corrOnlyRebind_killed)."
          "AC8 (identity round-trip across three passes) is line 1 at three passes: MOD_031_nonvacuous binds the port x to a caller place of its own name while y is prefixed, then instantiates again and resolves both; a pass that drops identity entries one by one violates it (MOD_031_forbids_entryDrop). The third pass is the instantiation of the retrofitted net (MOD-014). That the failure would be consume-then-throw, so the tokens are lost (EXEC-031), is the reason for the requirement, not a line."
          "AC9 (an implementation that drops an all-identity correspondence wholesale still satisfies AC8) is MOD_031_allows_dropAllIdentity: the pass that drops it, as Rust, Java and TypeScript do (rust/libpetri-core/src/rewriter.rs wholesale_drop_if_all_identity, java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java compactIdentityAlias, typescript/src/core/internal/subnet-rewriter.ts dropIfAllIdentity), satisfies the block. The reference pass does not take this MAY."
          "AC10 (identity never conflicts on merge) is line 4: X to X against X to Y succeeds and yields X to Y, two differing non-identity mappings fail (MOD_031_nonvacuous); a merge that rejects any two differing entries is the mutant MOD_031_mutant_anyDifference."
          "AC11 (the identity test agrees with the lookup) holds by construction: the identity test and the lookup both use the equality of the place type N. Under name-only places (TypeScript, Rust, Python: N = String, strNaming) X to X is the identity whatever the token types; under places by name and token type (Java: N = String × Ty, typedNaming) a mapping from X of one token type to X of another is a retained entry. This is the MOD-024 divergence, carried by CORE-002."
  signoff "2026-11-13 55511c0dc98c1231 ai"
  statement : ∀ {N A : Type}, CorrOps N A → Prop :=
    fun {N A} O =>
      (∀ (d : CDef N A) (ss : List ((N → N) × (String → String))), d.corr = none →
        (∀ p ∈ d.namedPlaces, O.look (corrPasses O ss d).corr p = corrChain ss p) ∧
        (∀ x, x ∉ d.namedPlaces → O.look (corrPasses O ss d).corr x = x)) ∧
      (∀ (σ : N → N) (g : String → String) (d : CDef N A),
        (∀ p, p ∈ discIn (O.pass σ g d).toTransDef ↔ p ∈ (discIn d.toTransDef).map σ) ∧
        (O.pass σ g d).core.inhibitors = d.core.inhibitors.map σ ∧
        (O.pass σ g d).core.reads = d.core.reads.map σ ∧
        (O.pass σ g d).core.resets = d.core.resets.map σ ∧
        discOut (O.pass σ g d).toTransDef = (discOut d.toTransDef).map σ) ∧
      (∀ p : N, O.look none p = p) ∧
      (∀ c i : CDef N A,
        ((∃ x, O.look c.corr x ≠ x ∧ O.look i.corr x ≠ x ∧ O.look c.corr x ≠ O.look i.corr x) →
          ∃ msg, O.merge c i = .error msg) ∧
        ((∀ x, O.look c.corr x = x ∨ O.look i.corr x = x ∨ O.look c.corr x = O.look i.corr x) →
          ∃ m, O.merge c i = .ok m) ∧
        (∀ m, O.merge c i = .ok m → ∀ x,
          (O.look c.corr x ≠ x → O.look m x = O.look c.corr x) ∧
          (O.look c.corr x = x → O.look m x = O.look i.corr x))) ∧
      (∀ (d : CDef N A) (a : Act A),
        (O.rebind d a).corr = d.corr ∧ (O.rebind d a).core = d.core ∧ (O.rebind d a).out = d.out)

/- The pinned readable form of MOD-031: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_031 : {N A : Type} → CorrOps N A → Prop :=
fun {N A} O =>
  (∀ (d : CDef N A) (ss : List ((N → N) × (String → String))),
      d.corr = none →
        (∀ p ∈ d.namedPlaces, O.look (corrPasses O ss d).corr p = corrChain ss p) ∧
          ∀ x ∉ d.namedPlaces, O.look (corrPasses O ss d).corr x = x) ∧
    (∀ (σ : N → N) (g : String → String) (d : CDef N A),
        (∀ (p : N), p ∈ discIn (O.pass σ g d).toTransDef ↔ p ∈ List.map σ (discIn d.toTransDef)) ∧
          (O.pass σ g d).core.inhibitors = List.map σ d.core.inhibitors ∧
            (O.pass σ g d).core.reads = List.map σ d.core.reads ∧
              (O.pass σ g d).core.resets = List.map σ d.core.resets ∧
                discOut (O.pass σ g d).toTransDef = List.map σ (discOut d.toTransDef)) ∧
      (∀ (p : N), O.look none p = p) ∧
        (∀ (c i : CDef N A),
            ((∃ x, O.look c.corr x ≠ x ∧ O.look i.corr x ≠ x ∧ O.look c.corr x ≠ O.look i.corr x) →
                ∃ msg, O.merge c i = Except.error msg) ∧
              ((∀ (x : N), O.look c.corr x = x ∨ O.look i.corr x = x ∨ O.look c.corr x = O.look i.corr x) →
                  ∃ m, O.merge c i = Except.ok m) ∧
                ∀ (m : Option (List (N × N))),
                  O.merge c i = Except.ok m →
                    ∀ (x : N),
                      (O.look c.corr x ≠ x → O.look m x = O.look c.corr x) ∧
                        (O.look c.corr x = x → O.look m x = O.look i.corr x)) ∧
          ∀ (d : CDef N A) (a : Act A),
            (O.rebind d a).corr = d.corr ∧ (O.rebind d a).core = d.core ∧ (O.rebind d a).out = d.out
-/
#guard_msgs in #print MOD_031

/-! ### The five lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- The first half of line 1: through any sequence of passes, a transition that carried no
correspondence resolves every place it names to where the passes sent it. -/
def mod031_line1lower (O : CorrOps N A) : Prop :=
  ∀ (d : CDef N A) (ss : List ((N → N) × (String → String))), d.corr = none →
    ∀ p ∈ d.namedPlaces, O.look (corrPasses O ss d).corr p = corrChain ss p

/-- Line 1 of MOD-031: the first half, and every place the transition did not name resolves to
itself. -/
def mod031_line1 (O : CorrOps N A) : Prop :=
  ∀ (d : CDef N A) (ss : List ((N → N) × (String → String))), d.corr = none →
    (∀ p ∈ d.namedPlaces, O.look (corrPasses O ss d).corr p = corrChain ss p) ∧
    (∀ x, x ∉ d.namedPlaces → O.look (corrPasses O ss d).corr x = x)

/-- Discovery under a pass: the input places (as a set) and the output places go through the
place map. -/
def mod031_disc (O : CorrOps N A) : Prop :=
  ∀ (σ : N → N) (g : String → String) (d : CDef N A),
    (∀ p, p ∈ discIn (O.pass σ g d).toTransDef ↔ p ∈ (discIn d.toTransDef).map σ) ∧
    discOut (O.pass σ g d).toTransDef = (discOut d.toTransDef).map σ

/-- Line 2 of MOD-031: a pass sends the places of each arc kind and of the output specification
through its place map, each kind on its own, the input places as a set. -/
def mod031_line2 (O : CorrOps N A) : Prop :=
  ∀ (σ : N → N) (g : String → String) (d : CDef N A),
    (∀ p, p ∈ discIn (O.pass σ g d).toTransDef ↔ p ∈ (discIn d.toTransDef).map σ) ∧
    (O.pass σ g d).core.inhibitors = d.core.inhibitors.map σ ∧
    (O.pass σ g d).core.reads = d.core.reads.map σ ∧
    (O.pass σ g d).core.resets = d.core.resets.map σ ∧
    discOut (O.pass σ g d).toTransDef = (discOut d.toTransDef).map σ

/-- Line 2 sends the named places through the place map: a place is named after the pass
exactly when it is the image of a place named before it. -/
theorem mod031_line2_namedPlaces {O : CorrOps N A} (h : mod031_line2 O) (σ : N → N)
    (g : String → String) (d : CDef N A) (p : N) :
    p ∈ (O.pass σ g d).namedPlaces ↔ p ∈ d.namedPlaces.map σ := by
  obtain ⟨hi, hh, hr, hs, ho⟩ := h σ g d
  show p ∈ discIn (O.pass σ g d).toTransDef ++ (O.pass σ g d).core.inhibitors ++
      (O.pass σ g d).core.reads ++ (O.pass σ g d).core.resets ++
      discOut (O.pass σ g d).toTransDef ↔
    p ∈ (discIn d.toTransDef ++ d.core.inhibitors ++ d.core.reads ++ d.core.resets ++
      discOut d.toTransDef).map σ
  rw [hh, hr, hs, ho]
  simp only [List.map_append, List.mem_append, hi p]

/-- Line 3 of MOD-031: no correspondence resolves every place to itself. -/
def mod031_line3 (O : CorrOps N A) : Prop := ∀ p : N, O.look none p = p

/-- The rejection half of line 4: a genuine conflict fails the merge. -/
def mod031_line4reject (O : CorrOps N A) : Prop :=
  ∀ c i : CDef N A,
    (∃ x, O.look c.corr x ≠ x ∧ O.look i.corr x ≠ x ∧ O.look c.corr x ≠ O.look i.corr x) →
      ∃ msg, O.merge c i = .error msg

/-- The success half of line 4: without a conflict the merge succeeds. -/
def mod031_line4succeed (O : CorrOps N A) : Prop :=
  ∀ c i : CDef N A,
    (∀ x, O.look c.corr x = x ∨ O.look i.corr x = x ∨ O.look c.corr x = O.look i.corr x) →
      ∃ m, O.merge c i = .ok m

/-- The result half of line 4: a success resolves each place as the side that moves it does. -/
def mod031_line4result (O : CorrOps N A) : Prop :=
  ∀ (c i : CDef N A) m, O.merge c i = .ok m → ∀ x,
    (O.look c.corr x ≠ x → O.look m x = O.look c.corr x) ∧
    (O.look c.corr x = x → O.look m x = O.look i.corr x)

/-- Line 4 of MOD-031: the merge. -/
def mod031_line4 (O : CorrOps N A) : Prop :=
  ∀ c i : CDef N A,
    ((∃ x, O.look c.corr x ≠ x ∧ O.look i.corr x ≠ x ∧ O.look c.corr x ≠ O.look i.corr x) →
      ∃ msg, O.merge c i = .error msg) ∧
    ((∀ x, O.look c.corr x = x ∨ O.look i.corr x = x ∨ O.look c.corr x = O.look i.corr x) →
      ∃ m, O.merge c i = .ok m) ∧
    (∀ m, O.merge c i = .ok m → ∀ x,
      (O.look c.corr x ≠ x → O.look m x = O.look c.corr x) ∧
      (O.look c.corr x = x → O.look m x = O.look i.corr x))

/-- Line 5 of MOD-031: binding an action keeps the correspondence, the arcs and the output
specification. -/
def mod031_line5 (O : CorrOps N A) : Prop :=
  ∀ (d : CDef N A) (a : Act A),
    (O.rebind d a).corr = d.corr ∧ (O.rebind d a).core = d.core ∧ (O.rebind d a).out = d.out

/-- MOD-031 is its five lines. -/
theorem mod031_iff (O : CorrOps N A) :
    MOD_031 O ↔ mod031_line1 O ∧ mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4 O ∧
      mod031_line5 O :=
  Iff.rfl

/-- The definition with one input arc on `p` and nothing else. -/
def mod031_single (p : N) : CDef N A :=
  { core := ⟨"t", [⟨p, .one⟩], [], [], []⟩, out := none, timing := .immediate, priority := 0,
    action := .passthrough }

/-- **Line 3 follows from line 1** at zero passes: a transition with one input arc on `p` and
no correspondence must resolve `p` to itself. So no model can break line 3 alone. -/
theorem mod031_line3_of_line1 {O : CorrOps N A} (h : mod031_line1 O) : mod031_line3 O := by
  intro p
  exact (h (mod031_single p) [] rfl).1 p (by simp [mod031_single, TransDef.namedPlaces])

/-- Under line 2, a sequence of passes sends the named places through the chain of place
maps: a place is named after the passes exactly when it is the image of a place named before
them. -/
theorem mod031_namedPlaces_passes {O : CorrOps N A} (h : mod031_line2 O)
    (ss : List ((N → N) × (String → String))) :
    ∀ (d : CDef N A) (p : N),
      p ∈ (corrPasses O ss d).namedPlaces ↔ p ∈ d.namedPlaces.map (corrChain ss) := by
  induction ss with
  | nil =>
    intro d p
    have e : corrChain ([] : List ((N → N) × (String → String))) = id := rfl
    simp [corrPasses, e]
  | cons s rest ih =>
    intro d p
    have e := ih (O.pass s.1 s.2 d) p
    simp only [corrPasses, List.foldl_cons] at e ⊢
    rw [e]
    have ec : corrChain (s :: rest) = corrChain rest ∘ s.1 := rfl
    rw [ec, ← List.map_map]
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact List.mem_map.2 ⟨q, (mod031_line2_namedPlaces h s.1 s.2 d q).1 hq, rfl⟩
    · intro hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact List.mem_map.2 ⟨q, (mod031_line2_namedPlaces h s.1 s.2 d q).2 hq, rfl⟩

/-- **The resolved place is a place the arcs name.** Take a transition with an input arc on `x`
and an output on `y`, instantiate it and bind its port: `x` and `y` resolve to the places the
passes sent them to, and those are exactly the places the rewritten arcs and output now name.
This holds for every model of the block. -/
theorem mod031_resolves_to_named {O : CorrOps N A} (h : MOD_031 O) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (hd : d.corr = none) :
    ∀ p ∈ d.namedPlaces, O.look (corrPasses O ss d).corr p ∈ (corrPasses O ss d).namedPlaces := by
  intro p hp
  rw [(h.1 d ss hd).1 p hp, mod031_namedPlaces_passes h.2.1 ss d]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

/-- Binding keeps the named places when it keeps the arcs and the output specification. -/
theorem mod031_rebind_namedPlaces {O : CorrOps N A} (h : mod031_line5 O) (d : CDef N A)
    (a : Act A) : (O.rebind d a).namedPlaces = d.namedPlaces := by
  obtain ⟨-, hc, ho⟩ := h d a
  simp only [TransDef.namedPlaces] at hc ho ⊢
  rw [hc, ho]

/-- **AC7 for every model of the block.** Bind an action to a transition after any sequence of
passes: every declared place still resolves where the passes sent it, and that place is still
named by the transition's arcs or output, so the late-bound action finds it as a baked-in action
does. -/
theorem mod031_lateBind {O : CorrOps N A} (h : MOD_031 O) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (a : Act A) (hd : d.corr = none) :
    ∀ p ∈ d.namedPlaces,
      O.look (O.rebind (corrPasses O ss d) a).corr p = corrChain ss p ∧
      O.look (O.rebind (corrPasses O ss d) a).corr p ∈
        (O.rebind (corrPasses O ss d) a).namedPlaces := by
  intro p hp
  rw [(h.2.2.2.2 (corrPasses O ss d) a).1, mod031_rebind_namedPlaces h.2.2.2.2]
  exact ⟨(h.1 d ss hd).1 p hp, mod031_resolves_to_named h d ss hd p hp⟩

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N]

/-- **Resolution through a correspondence** (Java and TypeScript): the correspondence first, the
place itself when it has no entry or there is no correspondence. -/
def corrResolve (c : Option (List (N × N))) (p : N) : N :=
  match c with
  | none => p
  | some al => (corrLookup al p).getD p

/-- A definition resolves its places through its correspondence. -/
theorem CDef.resolve_eq_corrResolve (d : CDef N A) (p : N) :
    d.resolve p = corrResolve d.corr p := rfl

/-- The side of a merge as the reference reads it: the correspondence it carries, or, when it
carries none, an identity entry for every place it names, so the key set stays complete. -/
def corrSideFull (d : CDef N A) : List (N × N) :=
  d.corr.getD (d.namedPlaces.map fun p => (p, p))

/-- The side of a merge as the wrong merge `carriedCorrOps` reads it: the correspondence it
carries, or nothing. -/
def corrSideCarried (d : CDef N A) : List (N × N) := d.corr.getD []

/-- The declared places of a merge: the keys of both sides. -/
def corrMergeKeys (side : CDef N A → List (N × N)) (c i : CDef N A) : List N :=
  (side c).map Prod.fst ++ (side i).map Prod.fst

/-- The merged resolution of `x`: the caller side's when it moves `x`, else the instance
side's. -/
def corrPick (c i : CDef N A) (x : N) : N :=
  if corrResolve c.corr x ≠ x then corrResolve c.corr x else corrResolve i.corr x

/-- A merge reading its sides through `side` and its conflicts through `clash x a b` (`a`, `b`
the two sides' resolutions of `x`): reject when some key clashes, else one entry per key with
the merged resolution. -/
def corrMergeVia (side : CDef N A → List (N × N)) (clash : N → N → N → Bool) (c i : CDef N A) :
    Except String (Option (List (N × N))) :=
  if (corrMergeKeys side c i).any (fun x => clash x (corrResolve c.corr x) (corrResolve i.corr x))
  then .error "conflicting declared-to-actual place correspondences"
  else .ok (some ((corrMergeKeys side c i).map fun x => (x, corrPick c i x)))

/-- The conflict of the body's merge rule: both sides move `x`, to different places. -/
def corrRefClash (x a b : N) : Bool := decide (a ≠ x) && decide (b ≠ x) && decide (a ≠ b)

/-- Binding an action: the action replaced, everything else kept. -/
def corrRebind (d : CDef N A) (a : Act A) : CDef N A := { d with action := a }

/-- **The reference correspondence operations**: the pass `CDef.map` (the correspondence chained,
keys kept, never dropped), the lookup `corrResolve`, the key-complete merge, and the binding
that changes the action only. -/
def refCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/- The reference correspondence operations are the witness model of MOD-031. -/
#spec_witness refCorrOps

/-- A wrong merge: a side that carries no correspondence contributes no key, so the other side's
correspondence is taken whole (the behaviour RD-23 recorded; the runtimes read such a side as the
reference does, through `corrSideFull`). -/
def carriedCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrMergeVia corrSideCarried corrRefClash, corrRebind⟩

omit [DecidableEq N] in
/-- The reference binding keeps the correspondence, the arcs and the output specification. -/
theorem line5_corrRebind (P : (N → N) → (String → String) → CDef N A → CDef N A)
    (lk : Option (List (N × N)) → N → N)
    (mg : CDef N A → CDef N A → Except String (Option (List (N × N)))) :
    mod031_line5 (⟨P, lk, mg, corrRebind⟩ : CorrOps N A) :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

/-! #### Lookup lemmas -/

theorem corrLookup_map_snd (al : List (N × N)) (g : N → N) (p : N) :
    corrLookup (al.map fun e => (e.1, g e.2)) p = (corrLookup al p).map g := by
  induction al with
  | nil => rfl
  | cons a rest ih =>
    simp only [corrLookup, List.map_cons, List.find?_cons] at ih ⊢
    by_cases h : a.1 = p
    · simp [h]
    · simpa [h] using ih

theorem corrLookup_graph (ps : List N) (g : N → N) {p : N} (hp : p ∈ ps) :
    corrLookup (ps.map fun q => (q, g q)) p = some (g p) := by
  induction ps with
  | nil => cases hp
  | cons a rest ih =>
    simp only [corrLookup, List.map_cons, List.find?_cons]
    by_cases h : a = p
    · simp [h]
    · have : p ∈ rest := by
        rcases List.mem_cons.1 hp with rfl | h'
        · exact absurd rfl h
        · exact h'
      simpa [corrLookup, h] using ih this

theorem corrLookup_graph_none (ps : List N) (g : N → N) {p : N} (hp : p ∉ ps) :
    corrLookup (ps.map fun q => (q, g q)) p = none := by
  induction ps with
  | nil => rfl
  | cons a rest ih =>
    simp only [corrLookup, List.map_cons, List.find?_cons]
    have h : a ≠ p := fun h => hp (h ▸ List.mem_cons_self ..)
    simpa [corrLookup, h] using ih (fun h' => hp (List.mem_cons_of_mem _ h'))

/-- A place that is no key has no entry. -/
theorem corrLookup_not_key {al : List (N × N)} {x : N} (hx : x ∉ al.map Prod.fst) :
    corrLookup al x = none := by
  unfold corrLookup
  cases hf : al.find? (fun e => decide (e.1 = x)) with
  | none => rfl
  | some e =>
    exfalso; apply hx
    exact List.mem_map.2 ⟨e, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- A correspondence that moves `x` holds `x` as a key. -/
theorem corrResolve_ne {c : Option (List (N × N))} {x : N} (h : corrResolve c x ≠ x) :
    ∃ al, c = some al ∧ x ∈ al.map Prod.fst := by
  cases c with
  | none => exact absurd rfl h
  | some al =>
    refine ⟨al, rfl, ?_⟩
    cases hf : al.find? (fun e => decide (e.1 = x)) with
    | none => simp [corrResolve, corrLookup, hf] at h
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hk : e.1 = x := by simpa using List.find?_some hf
      exact List.mem_map.2 ⟨e, he, hk⟩

/-! #### Line 1: the invariants -/

/-- The invariant of line 1: `ps` the declared places, `f` the composed place map so far. A
definition without a correspondence still names `ps` and `f` fixes them; a correspondence
holds every declared place as a key, resolved to `f` of it. -/
def CorrInv (ps : List N) (f : N → N) (d : CDef N A) : Prop :=
  match d.corr with
  | none => d.namedPlaces = ps ∧ ∀ p ∈ ps, f p = p
  | some al => ∀ p ∈ ps, corrLookup al p = some (f p)

/-- The key invariant of line 1: the keys are exactly the declared places `ps`, which a
definition without a correspondence names. -/
def CorrKeys (ps : List N) (d : CDef N A) : Prop :=
  match d.corr with
  | none => d.namedPlaces = ps
  | some al => al.map Prod.fst = ps

theorem corrInv_pass {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).corr = some (corrPass σ d)) {ps : List N} {f : N → N}
    {d : CDef N A} (σ : N → N) (g : String → String) (h : CorrInv ps f d) :
    CorrInv ps (σ ∘ f) (P σ g d) := by
  unfold CorrInv at h ⊢
  rw [hP]
  intro p hp
  cases hc : d.corr with
  | none =>
    rw [hc] at h
    simp only [corrPass, hc]
    rw [h.1, corrLookup_graph ps σ hp, Function.comp_apply, h.2 p hp]
  | some al =>
    rw [hc] at h
    simp only [corrPass, hc]
    rw [corrLookup_map_snd, h p hp]
    rfl

omit [DecidableEq N] in
/-- The keys of a chained correspondence are the keys before the pass. -/
theorem corrPass_keys {ps : List N} {d : CDef N A} (σ : N → N) (h : CorrKeys ps d) :
    (corrPass σ d).map Prod.fst = ps := by
  unfold CorrKeys at h
  cases hc : d.corr with
  | none => rw [hc] at h; simp [corrPass, hc, List.map_map, Function.comp_def, h]
  | some al => rw [hc] at h; simp [corrPass, hc, List.map_map, Function.comp_def, h]

omit [DecidableEq N] in
theorem corrKeys_pass {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).corr = some (corrPass σ d)) {ps : List N} {d : CDef N A}
    (σ : N → N) (g : String → String) (h : CorrKeys ps d) : CorrKeys ps (P σ g d) := by
  unfold CorrKeys
  rw [hP]
  exact corrPass_keys σ h

theorem corrResolve_of_inv {ps : List N} {f : N → N} {d : CDef N A} (h : CorrInv ps f d) :
    ∀ p ∈ ps, corrResolve d.corr p = f p := by
  intro p hp
  unfold CorrInv at h
  cases hc : d.corr with
  | none => rw [hc] at h; exact (h.2 p hp).symm
  | some al => rw [hc] at h; simp [corrResolve, h p hp]

/-- Under the key invariant a place that is not declared resolves to itself. -/
theorem corrResolve_of_keys {ps : List N} {d : CDef N A} (h : CorrKeys ps d) :
    ∀ x, x ∉ ps → corrResolve d.corr x = x := by
  intro x hx
  unfold CorrKeys at h
  cases hc : d.corr with
  | none => rfl
  | some al =>
    rw [hc] at h
    simp only [corrResolve, corrLookup_not_key (h ▸ hx : x ∉ al.map Prod.fst), Option.getD_none]

theorem corrInv_fold {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).corr = some (corrPass σ d)) {ps : List N}
    (ss : List ((N → N) × (String → String))) :
    ∀ (f : N → N) (d : CDef N A), CorrInv ps f d →
      CorrInv ps (fun p => corrChain ss (f p)) (ss.foldl (fun d s => P s.1 s.2 d) d) := by
  induction ss with
  | nil => intro f d h; exact h
  | cons s rest ih =>
    intro f d h
    exact ih (s.1 ∘ f) (P s.1 s.2 d) (corrInv_pass hP s.1 s.2 h)

omit [DecidableEq N] in
theorem corrKeys_fold {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).corr = some (corrPass σ d)) {ps : List N}
    (ss : List ((N → N) × (String → String))) :
    ∀ d : CDef N A, CorrKeys ps d → CorrKeys ps (ss.foldl (fun d s => P s.1 s.2 d) d) := by
  induction ss with
  | nil => intro d h; exact h
  | cons s rest ih => intro d h; exact ih _ (corrKeys_pass hP s.1 s.2 h)

/-- Line 1 holds of every pass that chains the correspondence as `corrPass` does, with the
lookup `corrResolve`, whatever the pass does to the arcs. -/
theorem line1_of_corrPass {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).corr = some (corrPass σ d))
    (mg : CDef N A → CDef N A → Except String (Option (List (N × N))))
    (rb : CDef N A → Act A → CDef N A) : mod031_line1 (⟨P, corrResolve, mg, rb⟩ : CorrOps N A) := by
  intro d ss hd
  have h0 : CorrInv d.namedPlaces id d := by
    unfold CorrInv; rw [hd]; exact ⟨rfl, fun _ _ => rfl⟩
  have k0 : CorrKeys d.namedPlaces d := by
    unfold CorrKeys; rw [hd]
  exact ⟨corrResolve_of_inv (corrInv_fold hP ss id d h0),
    corrResolve_of_keys (corrKeys_fold hP ss d k0)⟩

end Reference

section Reference2

variable {N A : Type} [DecidableEq N]

/-! #### Line 2: the named places and discovery -/

omit [DecidableEq N] in
theorem outPlaces_mapOut {M : Type} (f : N → M) (o : Out N) :
    outPlaces (mapOut f o) = (outPlaces o).map f := by
  induction o with
  | place p => rfl
  | and l r ihl ihr => simp [mapOut, outPlaces, ihl, ihr]
  | xor l r ihl ihr => simp [mapOut, outPlaces, ihl, ihr]
  | timeout c ih => simpa [mapOut, outPlaces] using ih
  | forward a b => rfl

omit [DecidableEq N] in
/-- A mapped definition's discovery is the mapped discovery. -/
theorem disc_map (σ : N → N) (g : String → String) (d : TransDef N A) :
    discIn (d.map σ g) = (discIn d).map σ ∧ discOut (d.map σ g) = (discOut d).map σ := by
  constructor
  · simp [discIn, TransDef.map, mapCore, mapIn, List.map_map, Function.comp_def]
  · cases ho : d.out <;> simp [discOut, TransDef.map, ho, outPlaces_mapOut]

omit [DecidableEq N] in
/-- A mapped definition names the mapped places. -/
theorem namedPlaces_map (σ : N → N) (g : String → String) (d : TransDef N A) :
    (d.map σ g).namedPlaces = d.namedPlaces.map σ := by
  cases ho : d.out <;>
    simp [TransDef.namedPlaces, TransDef.map, mapCore, mapIn, ho, outPlaces_mapOut,
      List.map_append, List.map_map, Function.comp_def]

omit [DecidableEq N] in
/-- Line 2 holds of every pass whose definition part is `TransDef.map`. -/
theorem line2_of_map {P : (N → N) → (String → String) → CDef N A → CDef N A}
    (hP : ∀ σ g d, (P σ g d).toTransDef = d.toTransDef.map σ g)
    (lk : Option (List (N × N)) → N → N)
    (mg : CDef N A → CDef N A → Except String (Option (List (N × N))))
    (rb : CDef N A → Act A → CDef N A) : mod031_line2 (⟨P, lk, mg, rb⟩ : CorrOps N A) := by
  intro σ g d
  show (∀ p, p ∈ discIn (P σ g d).toTransDef ↔ _) ∧ (P σ g d).toTransDef.core.inhibitors = _ ∧
    (P σ g d).toTransDef.core.reads = _ ∧ (P σ g d).toTransDef.core.resets = _ ∧
    discOut (P σ g d).toTransDef = _
  rw [hP]
  exact ⟨fun p => by rw [(disc_map σ g d.toTransDef).1], rfl, rfl, rfl,
    (disc_map σ g d.toTransDef).2⟩

/-! #### Line 4: the merge -/

/-- A side reading holds every place its correspondence moves as a key. -/
def CorrSideKeys (side : CDef N A → List (N × N)) : Prop :=
  ∀ (d : CDef N A) x, corrResolve d.corr x ≠ x → x ∈ (side d).map Prod.fst

theorem corrSideFull_keys : CorrSideKeys (corrSideFull (N := N) (A := A)) := by
  intro d x h
  obtain ⟨al, hal, hx⟩ := corrResolve_ne h
  simpa [corrSideFull, hal] using hx

theorem corrSideCarried_keys : CorrSideKeys (corrSideCarried (N := N) (A := A)) := by
  intro d x h
  obtain ⟨al, hal, hx⟩ := corrResolve_ne h
  simpa [corrSideCarried, hal] using hx

theorem corrMergeVia_resolve {side : CDef N A → List (N × N)} {clash : N → N → N → Bool}
    (hs : CorrSideKeys side) {c i : CDef N A} {m : Option (List (N × N))}
    (h : corrMergeVia side clash c i = .ok m) : ∀ x, corrResolve m x = corrPick c i x := by
  unfold corrMergeVia at h
  split at h
  · cases h
  · cases h
    intro x
    by_cases hx : x ∈ corrMergeKeys side c i
    · simp [corrResolve, corrLookup_graph _ _ hx]
    · have hc : corrResolve c.corr x = x := by
        by_contra hne; exact hx (List.mem_append_left _ (hs c x hne))
      have hi : corrResolve i.corr x = x := by
        by_contra hne; exact hx (List.mem_append_right _ (hs i x hne))
      have h0 : corrResolve (some ((corrMergeKeys side c i).map fun x => (x, corrPick c i x))) x
          = x := by simp [corrResolve, corrLookup_graph_none _ _ hx]
      rw [h0]; simp [corrPick, hc, hi]

theorem corrMergeVia_error {side : CDef N A → List (N × N)} {clash : N → N → N → Bool}
    {c i : CDef N A} {x : N} (hx : x ∈ corrMergeKeys side c i)
    (hcl : clash x (corrResolve c.corr x) (corrResolve i.corr x) = true) :
    ∃ msg, corrMergeVia side clash c i = .error msg := by
  have hany : (corrMergeKeys side c i).any
      (fun x => clash x (corrResolve c.corr x) (corrResolve i.corr x)) = true :=
    List.any_eq_true.2 ⟨x, hx, hcl⟩
  exact ⟨_, by unfold corrMergeVia; rw [if_pos hany]⟩

theorem corrMergeVia_ok {side : CDef N A → List (N × N)} {clash : N → N → N → Bool}
    {c i : CDef N A}
    (hcl : ∀ x ∈ corrMergeKeys side c i, clash x (corrResolve c.corr x) (corrResolve i.corr x) = false) :
    ∃ m, corrMergeVia side clash c i = .ok m := by
  have hany : (corrMergeKeys side c i).any
      (fun x => clash x (corrResolve c.corr x) (corrResolve i.corr x)) = false :=
    List.any_eq_false.2 (fun x hx => by rw [hcl x hx]; decide)
  exact ⟨_, by unfold corrMergeVia; rw [if_neg (by rw [hany]; decide)]⟩

/-- The result half of line 4 holds of every side reading that keeps the moved places as keys,
under every conflict test. -/
theorem line4result_of_via {side : CDef N A → List (N × N)} (hs : CorrSideKeys side)
    (clash : N → N → N → Bool) (P : (N → N) → (String → String) → CDef N A → CDef N A)
    (rb : CDef N A → Act A → CDef N A) :
    mod031_line4result (⟨P, corrResolve, corrMergeVia side clash, rb⟩ : CorrOps N A) := by
  intro c i m h x
  have hr := corrMergeVia_resolve hs h x
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · change corrResolve c.corr x ≠ x at hne
    show corrResolve m x = corrResolve c.corr x
    rw [hr]; simp [corrPick, hne]
  · change corrResolve c.corr x = x at heq
    show corrResolve m x = corrResolve i.corr x
    rw [hr]; simp [corrPick, heq]

/-- Line 4 holds of the body's conflict test under every side reading that keeps the moved
places as keys. -/
theorem line4_of_via {side : CDef N A → List (N × N)} (hs : CorrSideKeys side)
    (P : (N → N) → (String → String) → CDef N A → CDef N A)
    (rb : CDef N A → Act A → CDef N A) :
    mod031_line4 (⟨P, corrResolve, corrMergeVia side corrRefClash, rb⟩ : CorrOps N A) := by
  intro c i
  dsimp only
  refine ⟨fun ⟨x, h1, h2, h3⟩ => ?_, fun hno => ?_, line4result_of_via hs corrRefClash P rb c i⟩
  · exact corrMergeVia_error (List.mem_append_left _ (hs c x h1)) (by simp [corrRefClash, h1, h2, h3])
  · exact corrMergeVia_ok fun x _ => by
      rcases hno x with h | h | h <;> simp [corrRefClash, h]

/-! #### The reference and the wrong merge `carriedCorrOps` satisfy MOD-031 -/

/-- MOD-031 holds of the passes `CDef.map`, the lookup `corrResolve`, the action binding
`corrRebind` and the body's merge rule under every side reading that keeps the moved places as
keys. -/
theorem mod031_of_side {side : CDef N A → List (N × N)} (hs : CorrSideKeys side) :
    MOD_031 (⟨CDef.map, corrResolve, corrMergeVia side corrRefClash, corrRebind⟩ : CorrOps N A) :=
  ⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, line4_of_via hs _ _, line5_corrRebind _ _ _⟩

end Reference2

/-- ✓ The reference correspondence operations satisfy MOD-031 at every place type. A subnet
transition reads its declared place `in`. Instantiate the subnet under `s`, which moves `in` to
`s/in`, then bind the port to the caller place `X`: the transition's action still asks for `in`
and gets `X`, the place its arc now names, and a place it never declared resolves to itself. When
a channel merges two transitions, a place only one side moved goes where that side moved it, and
two sides that moved one declared place to different places are refused. Binding an action
changes neither the correspondence nor the arcs. -/
@[evidence holds MOD_031]
theorem MOD_031_reference {N A : Type} [DecidableEq N] : MOD_031 (refCorrOps (N := N) (A := A)) :=
  mod031_of_side corrSideFull_keys

/-- The wrong merge, which reads only the correspondences the sides carry, satisfies MOD-031
too. -/
theorem MOD_031_carried {N A : Type} [DecidableEq N] : MOD_031 (carriedCorrOps (N := N) (A := A)) :=
  mod031_of_side corrSideCarried_keys

/-! ### AC9: dropping an all-identity correspondence as a whole -/

section DropAll

variable {N A : Type} [DecidableEq N]

/-- The MAY of the body: `none` when every entry is the identity. -/
def corrDropAllId (al : List (N × N)) : Option (List (N × N)) :=
  if al.all (fun e => decide (e.1 = e.2)) then none else some al

/-- The pass of Rust, Java and TypeScript: `CDef.map`, with an all-identity correspondence
dropped as a whole. -/
def corrDropPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d.toTransDef.map σ g with corr := corrDropAllId (corrPass σ d) }

/-- The correspondence operations with the dropping pass. -/
def dropCorrOps : CorrOps N A :=
  ⟨corrDropPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- An all-identity correspondence resolves each of its keys to itself. -/
theorem corrLookup_allId {al : List (N × N)} (h : al.all (fun e => decide (e.1 = e.2)) = true)
    {p q : N} (hl : corrLookup al p = some q) : q = p := by
  unfold corrLookup at hl
  cases hf : al.find? (fun e => decide (e.1 = p)) with
  | none => simp [hf] at hl
  | some e =>
    have he : e ∈ al := List.mem_of_find?_eq_some hf
    have hk : e.1 = p := by simpa using List.find?_some hf
    have hid : e.1 = e.2 := by simpa using List.all_eq_true.1 h e he
    simp [hf] at hl
    rw [← hl, ← hid, hk]

/-- The invariant of the dropping pass: the arcs name the image of the declared places, and the
correspondence (when carried) holds every declared place as a key. -/
def CorrInv2 (ps : List N) (f : N → N) (d : CDef N A) : Prop :=
  d.namedPlaces = ps.map f ∧
  match d.corr with
  | none => ∀ p ∈ ps, f p = p
  | some al => ∀ p ∈ ps, corrLookup al p = some (f p)

theorem corrInv2_pass {ps : List N} {f : N → N} {d : CDef N A} (σ : N → N) (g : String → String)
    (h : CorrInv2 ps f d) : CorrInv2 ps (σ ∘ f) (corrDropPass σ g d) := by
  obtain ⟨hn, hc⟩ := h
  have hL : ∀ p ∈ ps, corrLookup (corrPass σ d) p = some (σ (f p)) := by
    intro p hp
    cases hd : d.corr with
    | none =>
      rw [hd] at hc
      have hid : ps.map f = ps := by
        conv => rhs; rw [← List.map_id ps]
        exact List.map_congr_left (fun p hp => by simpa using hc p hp)
      simp only [corrPass, hd]
      rw [hn, hid, corrLookup_graph ps σ hp, hc p hp]
    | some al =>
      rw [hd] at hc
      simp only [corrPass, hd]
      rw [corrLookup_map_snd, hc p hp]
      rfl
  refine ⟨?_, ?_⟩
  · show (d.toTransDef.map σ g).namedPlaces = _
    rw [namedPlaces_map, hn, List.map_map]
  · show (match corrDropAllId (corrPass σ d) with
      | none => ∀ p ∈ ps, (σ ∘ f) p = p
      | some al => ∀ p ∈ ps, corrLookup al p = some ((σ ∘ f) p))
    by_cases hall : (corrPass σ d).all (fun e => decide (e.1 = e.2)) = true
    · rw [show corrDropAllId (corrPass σ d) = none by simp [corrDropAllId, hall]]
      intro p hp
      exact corrLookup_allId hall (hL p hp)
    · rw [show corrDropAllId (corrPass σ d) = some (corrPass σ d) by simp [corrDropAllId, hall]]
      exact hL

/-- The key invariant survives the dropping pass: a dropped correspondence leaves arcs that
name exactly the declared places, so the next pass rebuilds the same keys from them. -/
theorem corrKeys_dropPass {ps : List N} {f : N → N} {d : CDef N A} (σ : N → N)
    (g : String → String) (h2 : CorrInv2 ps f d) (hk : CorrKeys ps d) :
    CorrKeys ps (corrDropPass σ g d) := by
  have hkeys := corrPass_keys σ hk
  obtain ⟨hn', hc'⟩ := corrInv2_pass σ g h2
  unfold CorrKeys
  show (match corrDropAllId (corrPass σ d) with
    | none => (corrDropPass σ g d).namedPlaces = ps
    | some al => al.map Prod.fst = ps)
  by_cases hall : (corrPass σ d).all (fun e => decide (e.1 = e.2)) = true
  · have hnone : corrDropAllId (corrPass σ d) = none := by simp [corrDropAllId, hall]
    have hfix : ∀ p ∈ ps, (σ ∘ f) p = p := by
      have hc'' : (match corrDropAllId (corrPass σ d) with
          | none => ∀ p ∈ ps, (σ ∘ f) p = p
          | some al => ∀ p ∈ ps, corrLookup al p = some ((σ ∘ f) p)) := hc'
      rw [hnone] at hc''
      exact hc''
    rw [hnone]
    show (corrDropPass σ g d).namedPlaces = ps
    rw [hn']
    conv => rhs; rw [← List.map_id ps]
    exact List.map_congr_left (fun p hp => by simpa using hfix p hp)
  · rw [show corrDropAllId (corrPass σ d) = some (corrPass σ d) by simp [corrDropAllId, hall]]
    exact hkeys

theorem corrResolve_of_inv2 {ps : List N} {f : N → N} {d : CDef N A} (h : CorrInv2 ps f d) :
    ∀ p ∈ ps, corrResolve d.corr p = f p := by
  intro p hp
  obtain ⟨-, hc⟩ := h
  cases hd : d.corr with
  | none => rw [hd] at hc; exact (hc p hp).symm
  | some al => rw [hd] at hc; simp [corrResolve, hc p hp]

theorem corrInv2_fold (ss : List ((N → N) × (String → String))) {ps : List N} :
    ∀ (f : N → N) (d : CDef N A), CorrInv2 ps f d → CorrKeys ps d →
      CorrInv2 ps (fun p => corrChain ss (f p)) (ss.foldl (fun d s => corrDropPass s.1 s.2 d) d) ∧
      CorrKeys ps (ss.foldl (fun d s => corrDropPass s.1 s.2 d) d) := by
  induction ss with
  | nil => intro f d h hk; exact ⟨h, hk⟩
  | cons s rest ih =>
    intro f d h hk
    exact ih (s.1 ∘ f) (corrDropPass s.1 s.2 d) (corrInv2_pass s.1 s.2 h)
      (corrKeys_dropPass s.1 s.2 h hk)

end DropAll

/-- ✓ AC9: an implementation that drops a correspondence as a whole when every entry is the
identity, as Rust, Java and TypeScript do, satisfies MOD-031. A transition whose places all keep
their names at one pass loses its correspondence, and the next pass rebuilds it from the arcs,
whose names are still the declared ones; so its keys stay exactly the declared places. -/
@[evidence allows MOD_031]
theorem MOD_031_allows_dropAllIdentity {N A : Type} [DecidableEq N] :
    MOD_031 (dropCorrOps (N := N) (A := A)) := by
  refine ⟨?_, line2_of_map (fun _ _ _ => rfl) _ _ _, fun _ => rfl,
    line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩
  intro d ss hd
  have h0 : CorrInv2 d.namedPlaces id d := by
    refine ⟨(List.map_id _).symm, ?_⟩
    rw [hd]; exact fun _ _ => rfl
  have k0 : CorrKeys d.namedPlaces d := by
    unfold CorrKeys; rw [hd]
  obtain ⟨h2, hk⟩ := corrInv2_fold ss id d h0 k0
  exact ⟨corrResolve_of_inv2 h2, corrResolve_of_keys hk⟩

/-! ### Examples -/

/-- The example transition `t`: an input arc on the port place `x` and the output place `y`. -/
def mod031_ex : CDef String Unit :=
  { core := ⟨"t", [⟨"x", .one⟩], [], [], []⟩, out := some (.place "y"), timing := .immediate,
    priority := 0, action := .passthrough }

/-- The port binding of the example: the port place `a/x` bound to a caller place named `x`. -/
def mod031_bind (p : String) : String := if p = "a/x" then "x" else p

/-- The three passes of AC8: instantiate under `a`, bind the port `a/x` to the caller place `x`
(a place of its own declared name), then instantiate the retrofitted net under `b`. -/
def mod031_ac8 : List ((String → String) × (String → String)) :=
  [(preS "a", preS "a"), (mod031_bind, id), (preS "b", preS "b")]

/-- A caller transition over `x` whose correspondence maps `x` to itself. -/
def mod031_callerId : CDef String Unit :=
  { mod031_single "x" with corr := some [("x", "x")] }

/-- An instance transition whose correspondence maps `x` to `s/x`. -/
def mod031_instMoves : CDef String Unit :=
  { mod031_single "s/x" with corr := some [("x", "s/x")] }

/-- A caller transition whose correspondence maps `x` to `c/x`. -/
def mod031_callerMoves : CDef String Unit :=
  { mod031_single "c/x" with corr := some [("x", "c/x")] }

/-- ✓ The reference exercises every line. AC8 and AC3: after instantiating under `a`, binding
the port to a caller place named `x` and instantiating the result under `b`, the declared `x`
resolves to `b/x` and the declared `y` to `b/a/y`, the arcs name exactly those places (AC5),
and the intermediate name `a/x`, which the author never declared, resolves to itself. AC10: a
caller entry `x → x` merged with an instance entry `x → s/x` succeeds and resolves `x` to
`s/x`; `x → c/x` against `x → s/x` fails. AC7: binding an action after the passes keeps the
correspondence and the arcs. -/
@[evidence nonvacuous MOD_031]
theorem MOD_031_nonvacuous :
    corrResolve (corrPasses refCorrOps mod031_ac8 mod031_ex).corr "x" = "b/x" ∧
    corrResolve (corrPasses refCorrOps mod031_ac8 mod031_ex).corr "y" = "b/a/y" ∧
    corrResolve (corrPasses refCorrOps mod031_ac8 mod031_ex).corr "a/x" = "a/x" ∧
    (corrPasses refCorrOps mod031_ac8 mod031_ex).namedPlaces = ["b/x", "b/a/y"] ∧
    discIn (corrPasses refCorrOps mod031_ac8 mod031_ex).toTransDef = ["b/x"] ∧
    discOut (corrPasses refCorrOps mod031_ac8 mod031_ex).toTransDef = ["b/a/y"] ∧
    (∃ m, refCorrOps.merge mod031_callerId mod031_instMoves = .ok m ∧ corrResolve m "x" = "s/x") ∧
    (∃ msg, refCorrOps.merge mod031_callerMoves mod031_instMoves = .error msg) ∧
    (refCorrOps.rebind (corrPasses refCorrOps mod031_ac8 mod031_ex) (.other ())).corr =
      (corrPasses refCorrOps mod031_ac8 mod031_ex).corr ∧
    (refCorrOps.rebind (corrPasses refCorrOps mod031_ac8 mod031_ex) (.other ())).core =
      (corrPasses refCorrOps mod031_ac8 mod031_ex).core := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, rfl, by decide⟩,
    ⟨_, rfl⟩, rfl, rfl⟩

/-- Two declared places `p` and `q` of one transition, both bound to the caller place `r`. -/
def mod031_two : CDef String Unit :=
  { core := ⟨"t", [⟨"p", .one⟩], [], [], []⟩, out := some (.place "q"), timing := .immediate,
    priority := 0, action := .passthrough }

/-- ✓ The correspondence is single-valued, not one-to-one (ruling D69 (a)): binding an input port
`p` and an output port `q` to one caller place `r` (MOD-020 allows it) resolves both declared
places to `r`, and the reference still satisfies MOD-031. -/
@[evidence allows MOD_031]
theorem MOD_031_allows_shared :
    MOD_031 (refCorrOps (N := String) (A := Unit)) ∧
    corrResolve (refCorrOps.pass (fun _ => "r") id mod031_two).corr "p" = "r" ∧
    corrResolve (refCorrOps.pass (fun _ => "r") id mod031_two).corr "q" = "r" :=
  ⟨MOD_031_reference, by decide, by decide⟩

/-! ### Fusion: two input arcs merged onto one place -/

section MergeIn

variable {N A : Type} [DecidableEq N]

/-- The input arcs with one arc for each place: an arc is dropped when a later arc names its
place. The cardinality is not a place: which arc is kept and the merged cardinality are MOD-061's
and MOD-021's lines, not this block's. -/
def corrMergeIn : List (NInSpec N) → List (NInSpec N)
  | [] => []
  | a :: as =>
    if (corrMergeIn as).any (fun b => decide (b.place = a.place)) then corrMergeIn as
    else a :: corrMergeIn as

/-- Merging the input arcs keeps the set of input places. -/
theorem corrMergeIn_mem (l : List (NInSpec N)) (p : N) :
    p ∈ (corrMergeIn l).map (·.place) ↔ p ∈ l.map (·.place) := by
  induction l with
  | nil => exact Iff.rfl
  | cons a as ih =>
    simp only [corrMergeIn]
    split
    · rename_i h
      rw [ih]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · obtain ⟨b, hb, hbe⟩ := List.any_eq_true.1 h
          exact ih.1 (List.mem_map.2 ⟨b, hb, of_decide_eq_true hbe⟩)
        · exact h'
    · simp only [List.map_cons, List.mem_cons, ih]

/-- A fusion-like pass: every place mapped as the reference does, then the input arcs that the
place map sent onto one place merged into one arc, as every runtime merges them (MOD-061). -/
def corrMergeInPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  let d' := CDef.map σ g d
  { d' with core := { d'.core with inputs := corrMergeIn d'.core.inputs } }

/-- The reference with the input-merging pass. -/
def mergeInCorrOps : CorrOps N A :=
  ⟨corrMergeInPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The input-merging pass satisfies MOD-031 at every place type: line 2 reads the input places
as a set, and the merge keeps that set. -/
theorem mod031_mergeIn : MOD_031 (mergeInCorrOps (N := N) (A := A)) := by
  refine ⟨line1_of_corrPass (P := corrMergeInPass) (fun _ _ _ => rfl) _ _, fun σ g d => ?_,
    fun _ => rfl, line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩
  obtain ⟨hi, hh, hr, hs, ho⟩ :=
    line2_of_map (P := CDef.map) (fun _ _ _ => rfl) (corrResolve (N := N))
      (corrMergeVia corrSideFull corrRefClash) (corrRebind (A := A)) σ g d
  exact ⟨fun p => (corrMergeIn_mem _ p).trans (hi p), hh, hr, hs, ho⟩

end MergeIn

/-- A transition with input arcs on `0` and `1` and an output on `2`. -/
def mod031_twoIn : CDef Nat Unit :=
  { core := ⟨"t", [⟨0, .one⟩, ⟨1, .one⟩], [], [], []⟩, out := some (.place 2),
    timing := .immediate, priority := 0, action := .passthrough }

/-- A fusion of the places `0` and `1` onto `5`. -/
def mod031_fuse (p : Nat) : Nat := if p = 0 ∨ p = 1 then 5 else p

/-- ✓ Line 2 reads the input places as a set, so a fusion that merges two input arcs onto one
place satisfies it (MOD-061). Fusing the input places `0` and `1` of a transition onto `5`: the
mapped input list is `[5, 5]`, the pass leaves one input arc on `5`, discovery returns the actual
place `5`, and both declared places resolve to it. The pass satisfies the whole block. -/
@[evidence allows MOD_031]
theorem MOD_031_allows_mergeInputs :
    MOD_031 (mergeInCorrOps (N := Nat) (A := Unit)) ∧
    (discIn mod031_twoIn.toTransDef).map mod031_fuse = [5, 5] ∧
    discIn (mergeInCorrOps.pass mod031_fuse id mod031_twoIn).toTransDef = [5] ∧
    corrResolve (mergeInCorrOps.pass mod031_fuse id mod031_twoIn).corr 0 = 5 ∧
    corrResolve (mergeInCorrOps.pass mod031_fuse id mod031_twoIn).corr 1 = 5 :=
  ⟨mod031_mergeIn, by decide, by decide, by decide, by decide⟩

/-! ### Merge, then pass: the case the block leaves open -/

/-- A hand-written caller transition over `h`. -/
def mod031_caller : CDef String Unit := mod031_single "h"

/-- The merged transition of the channel merge: arcs on the caller's `h` and the instance's
`s/x`, with the merged correspondence `m`. -/
def mod031_merged (m : Option (List (String × String))) : CDef String Unit :=
  { core := ⟨"call", [⟨"h", .one⟩, ⟨"s/x", .one⟩], [], [], []⟩, out := none,
    timing := .immediate, priority := 0, action := .passthrough, corr := m }

/-- A later pass that moves the caller's place `h` (a fusion onto `f`, or a new prefix). -/
def mod031_later (p : String) : String := if p = "h" then "f" else p

/-- ? Merge, then pass (ruling D69 (a): line 1 covers transitions no channel merge joined). The
key-complete merge of the reference, which the runtimes follow, and the wrong merge
`carriedCorrOps` (the behaviour RD-23 recorded) both satisfy MOD-031: no sentence of MOD-031
states key-set completeness for a transition a channel merge joined, so the block cannot tell
them apart. Merging the hand-written caller over `h` with an instance transition mapping `x` to
`s/x`, then moving `h` to `f` in one more pass: after the reference's merge the caller's `h`
resolves to `f`; after the wrong merge it resolves to `h`, a place no arc of the transition names
any more, so the caller's action would fail its declared-place check after consuming its
inputs. -/
@[evidence undecided MOD_031]
theorem MOD_031_mergeThenPass_undecided :
    MOD_031 (refCorrOps (N := String) (A := Unit)) ∧
    MOD_031 (carriedCorrOps (N := String) (A := Unit)) ∧
    (∃ m, refCorrOps.merge mod031_caller mod031_instMoves = .ok m ∧
      corrResolve (CDef.map mod031_later id (mod031_merged m)).corr "h" = "f") ∧
    (∃ m, carriedCorrOps.merge mod031_caller mod031_instMoves = .ok m ∧
      corrResolve (CDef.map mod031_later id (mod031_merged m)).corr "h" = "h" ∧
      "h" ∉ (CDef.map mod031_later id (mod031_merged m)).namedPlaces) :=
  ⟨MOD_031_reference, MOD_031_carried, ⟨_, rfl, by decide⟩, ⟨_, rfl, by decide, by decide⟩⟩

/-! ### Wrong correspondence operations -/

section Wrong

variable {N A : Type} [DecidableEq N]

/-- The defect AC8 describes: every pass drops the identity entries one by one. -/
def corrEntryDropPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d.toTransDef.map σ g with
    corr := match (corrPass σ d).filter (fun e => decide (e.1 ≠ e.2)) with
      | [] => none
      | l => some l }

/-- A chained pass that re-derives the keys from the arcs, whose names are the previous pass's. -/
def corrRederivePass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d.toTransDef.map σ g with corr := some (d.namedPlaces.map fun p => (p, σ p)) }

/-- A chained pass that carries the declared entries and then also records every place the arcs
name before the pass (intermediate names the author never declared), behind the carried
entries. The slip the comment in `build_local_name_map` (`rust/libpetri-core/src/rewriter.rs`) warns
against. -/
def corrLeakPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d.toTransDef.map σ g with corr := some (corrPass σ d ++ d.namedPlaces.map fun p => (p, σ p)) }

/-- A pass that records the rename in the correspondence and leaves the arcs on the declared
places (only the transition's name is renamed). -/
def corrAliasOnlyPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d with core := { d.core with name := g d.core.name }, corr := some (corrPass σ d) }

/-- A pass that maps the name, the input arcs and the output specification, keeps the
inhibitor, read and reset arcs on their old places, and chains the correspondence: a rebuild
that copies only the discovery lists through the place map. -/
def corrReadsKeptPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d with core := { d.core with name := g d.core.name, inputs := d.core.inputs.map (mapIn σ) },
           out := d.out.map (mapOut σ), corr := some (corrPass σ d) }

/-- A pass that maps every place as the reference does and then rebuilds each inhibitor arc as a
read arc: a copy slip in a per-arc-kind rebuild. The list of all named places is unchanged. -/
def corrKindSwapPass (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  let d' := CDef.map σ g d
  { d' with core := { d'.core with inhibitors := [], reads := d'.core.inhibitors ++ d'.core.reads } }

/-- A pass that maps every place as the reference does and then adds an input arc on a fresh
place, one past the largest place the mapped transition names. -/
def corrExtraInputPass (σ : Nat → Nat) (g : String → String) (d : CDef Nat A) : CDef Nat A :=
  let d' := CDef.map σ g d
  { d' with core := { d'.core with
      inputs := d'.core.inputs ++ [⟨d'.namedPlaces.foldr max 0 + 1, .one⟩] } }

/-- A merge in which any two different entries conflict, identities included. -/
def corrAnyDiffClash (_ a b : N) : Bool := decide (a ≠ b)

/-- A merge with the body's conflict test that builds the result with the instance side's
entries first, so that an instance identity entry hides the caller's move. -/
def corrInstWinsMerge (c i : CDef N A) : Except String (Option (List (N × N))) :=
  match corrMergeVia corrSideFull corrRefClash c i with
  | .error e => .error e
  | .ok _ => .ok (some (corrSideFull i ++ corrSideFull c))

/-- An action binding that rebuilds the transition without its correspondence. -/
def corrDropRebind (d : CDef N A) (a : Act A) : CDef N A := { d with action := a, corr := none }

/-- An action binding that keeps the correspondence and drops the read arcs. -/
def corrReadDropRebind (d : CDef N A) (a : Act A) : CDef N A :=
  { d with action := a, core := { d.core with reads := [] } }

/-- The reference with the entry-dropping pass. -/
def entryDropCorrOps : CorrOps N A :=
  ⟨corrEntryDropPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the re-deriving pass. -/
def rederiveCorrOps : CorrOps N A :=
  ⟨corrRederivePass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the pass that leaks intermediate names into the keys. -/
def leakCorrOps : CorrOps N A :=
  ⟨corrLeakPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the alias-only pass. -/
def aliasOnlyCorrOps : CorrOps N A :=
  ⟨corrAliasOnlyPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the pass that keeps the inhibitor, read and reset arcs. -/
def readsKeptCorrOps : CorrOps N A :=
  ⟨corrReadsKeptPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the pass that turns inhibitor arcs into read arcs. -/
def kindSwapCorrOps : CorrOps N A :=
  ⟨corrKindSwapPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the pass that adds an input arc on a fresh place. -/
def extraInputCorrOps : CorrOps Nat A :=
  ⟨corrExtraInputPass, corrResolve, corrMergeVia corrSideFull corrRefClash, corrRebind⟩

/-- The reference with the merge in which identities conflict. -/
def anyDiffCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrMergeVia corrSideFull corrAnyDiffClash, corrRebind⟩

/-- The reference with the merge in which the instance side wins. -/
def instWinsCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrInstWinsMerge, corrRebind⟩

/-- The reference with a merge that rejects everything. -/
def rejectMergeCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, fun _ _ => .error "rejected", corrRebind⟩

/-- The reference with the binding that drops the correspondence. -/
def dropRebindCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrMergeVia corrSideFull corrRefClash, corrDropRebind⟩

/-- The reference with the binding that drops the read arcs. -/
def readDropRebindCorrOps : CorrOps N A :=
  ⟨CDef.map, corrResolve, corrMergeVia corrSideFull corrRefClash, corrReadDropRebind⟩

theorem corrLookup_append {l1 l2 : List (N × N)} {p q : N} (h : corrLookup l1 p = some q) :
    corrLookup (l1 ++ l2) p = some q := by
  unfold corrLookup at *
  rw [List.find?_append]
  cases hf : l1.find? (fun e => decide (e.1 = p)) <;> simp_all

theorem corrInv_leakPass {ps : List N} {f : N → N} {d : CDef N A} (σ : N → N)
    (g : String → String) (h : CorrInv ps f d) : CorrInv ps (σ ∘ f) (corrLeakPass σ g d) := by
  have h' := corrInv_pass (P := CDef.map) (fun _ _ _ => rfl) σ g h
  change ∀ p ∈ ps, corrLookup (corrPass σ d) p = some ((σ ∘ f) p) at h'
  change ∀ p ∈ ps, corrLookup (corrPass σ d ++ d.namedPlaces.map fun p => (p, σ p)) p =
    some ((σ ∘ f) p)
  exact fun p hp => corrLookup_append (h' p hp)

theorem corrInv_leakFold {ps : List N} (ss : List ((N → N) × (String → String))) :
    ∀ (f : N → N) (d : CDef N A), CorrInv ps f d →
      CorrInv ps (fun p => corrChain ss (f p)) (ss.foldl (fun d s => corrLeakPass s.1 s.2 d) d) := by
  induction ss with
  | nil => intro f d h; exact h
  | cons s rest ih =>
    intro f d h; exact ih (s.1 ∘ f) (corrLeakPass s.1 s.2 d) (corrInv_leakPass s.1 s.2 h)

end Wrong

/-- The AC8 example as the passes of the transition over `x` and `y` with numbers: `x = 0` is the
port, `y = 1` internal. -/
def mod031_s1 (p : Nat) : Nat := if p = 1 then 11 else p

/-- The later pass of the AC8 example: both places renamed. -/
def mod031_s2 (p : Nat) : Nat := if p = 0 then 20 else if p = 11 then 21 else p

/-- The transition over `0` (input) and `1` (output). -/
def mod031_exNat : CDef Nat Unit :=
  { core := ⟨"t", [⟨0, .one⟩], [], [], []⟩, out := some (.place 1), timing := .immediate,
    priority := 0, action := .passthrough }

/-- A transition with an input arc on `0` and a read arc on `1`. -/
def mod031_readEx : CDef Nat Unit :=
  { core := ⟨"t", [⟨0, .one⟩], [], [1], []⟩, out := none, timing := .immediate, priority := 0,
    action := .passthrough }

/-- A transition with an inhibitor arc on `0` and nothing else. -/
def mod031_inhEx : CDef Nat Unit :=
  { core := ⟨"t", [], [0], [], []⟩, out := none, timing := .immediate, priority := 0,
    action := .passthrough }

/-- Leak example, first pass: bind the port `0` to the place `5`. -/
def mod031_l1 (p : Nat) : Nat := if p = 0 then 5 else p

/-- Leak example, second pass: rename `5` to `7` and `1` to `5`. -/
def mod031_l2 (p : Nat) : Nat := if p = 5 then 7 else if p = 1 then 5 else p

/-- ✗ A pass that drops identity entries one by one violates MOD-031 (line 1, AC8): the port
`0` is bound to a place of its own name at the first pass, so its entry is dropped; the second
pass renames it to `20`, and the transition resolves `0` to `0`, which no arc names. -/
@[evidence forbids MOD_031]
theorem MOD_031_forbids_entryDrop : ¬ MOD_031 (entryDropCorrOps (N := Nat) (A := Unit)) := by
  intro h
  have := (h.1 mod031_exNat [(mod031_s1, id), (mod031_s2, id)] rfl).1 0 (by decide)
  revert this
  decide

/-- ✗ A merge that rejects everything violates MOD-031 (line 4): `x → x` against `x → s/x` must
merge. -/
@[evidence forbids MOD_031]
theorem MOD_031_forbids_rejectMerge : ¬ MOD_031 (rejectMergeCorrOps (N := String) (A := Unit)) := by
  intro h
  obtain ⟨m, hm⟩ := (h.2.2.2.1 mod031_callerId mod031_instMoves).2.1 (fun x => by
    by_cases hx : x = "x"
    · subst hx; left; decide
    · left; simp [rejectMergeCorrOps, mod031_callerId, corrResolve, corrLookup, Ne.symm hx])
  cases hm

/-- ✗ A pass that adds an input arc on a fresh place violates MOD-031 (line 2): the transition
with an input arc on `0` and an output on `1` comes out of an identity pass with a second input
arc on `2`, so discovery returns a place that is not the image of an input place before the
pass. -/
@[evidence forbids MOD_031]
theorem MOD_031_forbids_extraInput : ¬ MOD_031 (extraInputCorrOps (A := Unit)) := by
  intro h
  have := ((h.2.1 id id mod031_exNat).1 2).1 (by decide)
  revert this
  decide

/-! ### Mutants, one per load-bearing line -/

section Mutants

variable {N A : Type}

/-- Mutant reading of line 1: each pass resolves correctly on a transition that carries no
correspondence, read for one pass only (the chain through several passes dropped). -/
def MOD_031_mutant_onePass (O : CorrOps N A) : Prop :=
  (∀ (d : CDef N A) σ g, d.corr = none →
    (∀ p ∈ d.namedPlaces, O.look (O.pass σ g d).corr p = σ p) ∧
    (∀ x, x ∉ d.namedPlaces → O.look (O.pass σ g d).corr x = x)) ∧
  mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4 O ∧ mod031_line5 O

/-- Mutant reading of line 1 without its second half: the declared places resolve, and nothing
is said of the other places, so the key set is bounded from below only. -/
def MOD_031_mutant_lowerOnly (O : CorrOps N A) : Prop :=
  mod031_line1lower O ∧ mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4 O ∧ mod031_line5 O

/-- Mutant reading: MOD-031 without line 2, so a pass need not rewrite the arcs. -/
def MOD_031_mutant_noDiscovery (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_line3 O ∧ mod031_line4 O ∧ mod031_line5 O

/-- Mutant reading of line 2 as discovery only: the input and output places go through the
place map, and nothing is said of the inhibitor, read and reset arcs. -/
def MOD_031_mutant_discoveryOnly (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_disc O ∧ mod031_line3 O ∧ mod031_line4 O ∧ mod031_line5 O

/-- Mutant reading of line 2 over all named places at once: the places the arcs and the output
specification name, as a set (the conclusion of `mod031_line2_namedPlaces`), and the input
places as a set and the output places go through the place map, and nothing keeps an arc of one
kind from coming out as an arc of another kind. -/
def MOD_031_mutant_namedOnly (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧
  (∀ (σ : N → N) (g : String → String) (d : CDef N A),
    (∀ p, p ∈ (O.pass σ g d).namedPlaces ↔ p ∈ d.namedPlaces.map σ) ∧
    (∀ p, p ∈ discIn (O.pass σ g d).toTransDef ↔ p ∈ (discIn d.toTransDef).map σ) ∧
    discOut (O.pass σ g d).toTransDef = (discOut d.toTransDef).map σ) ∧
  mod031_line3 O ∧ mod031_line4 O ∧ mod031_line5 O

/-- Mutant reading of line 4 without the identity rule: two different entries for one declared
place conflict, and a merge without such entries succeeds. -/
def MOD_031_mutant_anyDifference (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_line2 O ∧ mod031_line3 O ∧
  (∀ c i : CDef N A, (∃ x, O.look c.corr x ≠ O.look i.corr x) → ∃ msg, O.merge c i = .error msg) ∧
  (∀ c i : CDef N A, (∀ x, O.look c.corr x = O.look i.corr x) → ∃ m, O.merge c i = .ok m) ∧
  mod031_line4result O ∧ mod031_line5 O

/-- Mutant reading of line 4 without its result half: conflicts fail and the rest succeeds, and
nothing is said of what a successful merge resolves. -/
def MOD_031_mutant_noMergeResult (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4reject O ∧
  mod031_line4succeed O ∧ mod031_line5 O

/-- Mutant reading: MOD-031 without line 5, so binding an action may rebuild the transition
without its correspondence. -/
def MOD_031_mutant_noRebind (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4 O

/-- Mutant reading of line 5 as the correspondence only: binding an action keeps the
correspondence, and nothing is said of the arcs. -/
def MOD_031_mutant_corrOnlyRebind (O : CorrOps N A) : Prop :=
  mod031_line1 O ∧ mod031_line2 O ∧ mod031_line3 O ∧ mod031_line4 O ∧
  (∀ (d : CDef N A) (a : Act A), (O.rebind d a).corr = d.corr)

end Mutants

/-- The re-deriving pass kills the one-pass reading: from a transition without a
correspondence one pass is exactly the reference's, but at the AC8 example's second pass it
reads the keys `0` and `11` off the arcs, and the declared `1` resolves to `1` instead of `21`. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_onePass_killed :
    MOD_031_mutant_onePass (rederiveCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (rederiveCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨fun d σ g hd => ⟨fun p hp => ?_, fun x hx => ?_⟩, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · show corrResolve (some (d.namedPlaces.map fun p => (p, σ p))) p = σ p
    simp [corrResolve, corrLookup_graph _ _ hp]
  · show corrResolve (some (d.namedPlaces.map fun p => (p, σ p))) x = x
    simp [corrResolve, corrLookup_graph_none _ _ hx]
  · have := (h.1 mod031_exNat [(mod031_s1, id), (mod031_s2, id)] rfl).1 1 (by decide)
    revert this
    decide

/-- The leaking pass kills the reading of line 1 without its second half. Take a transition
with input `0` and output `1`; the first pass binds `0` to `5`, the second renames `5` to `7`
and `1` to `5`. Every declared place still resolves, but the leaked key `5 → 7` sends the
discovered output `5` to the input place `7`, where the reference resolves `5` to itself. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_lowerOnly_killed :
    MOD_031_mutant_lowerOnly (leakCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (leakCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨fun d ss hd p hp => ?_, line2_of_map (fun _ _ _ => rfl) _ _ _, fun _ => rfl,
    line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · have h0 : CorrInv d.namedPlaces id d := by
      unfold CorrInv; rw [hd]; exact ⟨rfl, fun _ _ => rfl⟩
    exact corrResolve_of_inv (corrInv_leakFold ss id d h0) p hp
  · have := (h.1 mod031_exNat [(mod031_l1, id), (mod031_l2, id)] rfl).2 5 (by decide)
    revert this
    decide

/-- The alias-only pass kills the reading without line 2: it chains the correspondence as the
reference does, so every declared place resolves, but the example's input arc stays on `0`
after the pass that renames `0` to `20`. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_noDiscovery_killed :
    MOD_031_mutant_noDiscovery (aliasOnlyCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (aliasOnlyCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, fun _ => rfl,
    line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  have := ((h.2.1 mod031_s2 id mod031_exNat).1 20).2 (by decide)
  revert this
  decide

/-- The pass that keeps the read arcs kills the discovery-only reading of line 2. Take a
transition with an input arc on `0` and a read arc on `1`, and a pass that adds 10: the declared
read place `1` resolves to `11` and discovery returns `10`, but the read arc stays on `1`, so
`ctx.read(1)` would fail its declared-place check. The reference moves the read arc to `11`. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_discoveryOnly_killed :
    MOD_031_mutant_discoveryOnly (readsKeptCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (readsKeptCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, fun σ g d => ⟨?_, ?_⟩, fun _ => rfl,
    line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · intro p
    simp [readsKeptCorrOps, corrReadsKeptPass, discIn, mapIn, List.map_map, Function.comp_def]
  · cases ho : d.out <;> simp [readsKeptCorrOps, corrReadsKeptPass, discOut, ho, outPlaces_mapOut]
  · have := (h.2.1 (· + 10) id mod031_readEx).2.2.1
    revert this
    decide

/-- The kind-swapping pass kills the reading of line 2 over all named places at once. It maps
every place as the reference does, so the list of named places, discovery and every
correspondence come out right, but the transition with an inhibitor arc on `0` comes out with a
read arc on `0` and no inhibitor arc: it now needs a token on `0` where it needed `0` empty. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_namedOnly_killed :
    MOD_031_mutant_namedOnly (kindSwapCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (kindSwapCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (P := corrKindSwapPass) (fun _ _ _ => rfl) _ _, fun σ g d => ?_,
    fun _ => rfl, line4_of_via corrSideFull_keys _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · obtain ⟨hi, -, -, -, ho⟩ :=
      line2_of_map (P := CDef.map) (fun _ _ _ => rfl) (corrResolve (N := Nat))
        (corrMergeVia corrSideFull corrRefClash) (corrRebind (A := Unit)) σ g d
    have hn : (corrKindSwapPass σ g d).toTransDef.namedPlaces = d.namedPlaces.map σ := by
      rw [← namedPlaces_map σ g d.toTransDef]
      show (corrKindSwapPass σ g d).toTransDef.namedPlaces =
        (CDef.map σ g d).toTransDef.namedPlaces
      simp [corrKindSwapPass, TransDef.namedPlaces, List.append_assoc]
    exact ⟨fun p => Iff.of_eq (congrArg (p ∈ ·) hn), hi, ho⟩
  · have := (h.2.1 id id mod031_inhEx).2.1
    revert this
    decide

/-- The merge in which identities conflict kills the reading of line 4 without the identity
rule: it rejects exactly the merges with two different entries, but `x → x` against
`x → s/x` must succeed (AC10). -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_anyDifference_killed :
    MOD_031_mutant_anyDifference (anyDiffCorrOps (N := String) (A := Unit)) ∧
      ¬ MOD_031 (anyDiffCorrOps (N := String) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, fun c i ⟨x, hx⟩ => ?_, fun c i hno => ?_,
    line4result_of_via corrSideFull_keys _ _ _, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · change corrResolve c.corr x ≠ corrResolve i.corr x at hx
    have hmem : x ∈ corrMergeKeys corrSideFull c i := by
      by_cases hc : corrResolve c.corr x = x
      · exact List.mem_append_right _ (corrSideFull_keys i x (fun hi => hx (hc.trans hi.symm)))
      · exact List.mem_append_left _ (corrSideFull_keys c x hc)
    exact corrMergeVia_error hmem (by simp [corrAnyDiffClash, hx])
  · exact corrMergeVia_ok fun x _ => by
      have hx := hno x
      change corrResolve c.corr x = corrResolve i.corr x at hx
      simp [corrAnyDiffClash, hx]
  · obtain ⟨m, hm⟩ := (h.2.2.2.1 mod031_callerId mod031_instMoves).2.1 (fun x => by
      by_cases hx : x = "x"
      · subst hx; left; decide
      · left; simp [anyDiffCorrOps, mod031_callerId, corrResolve, corrLookup, Ne.symm hx])
    have he : anyDiffCorrOps.merge mod031_callerId mod031_instMoves =
        .error "conflicting declared-to-actual place correspondences" := rfl
    rw [he] at hm
    cases hm

/-- The merge in which the instance side wins kills the reading of line 4 without its result
half. The caller maps `x` to `c/x` and the instance carries the identity entry `x → x`: the
merge rightly succeeds, but it resolves `x` to `x`, where the caller's move must win and give
`c/x` (AC10). -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_noMergeResult_killed :
    MOD_031_mutant_noMergeResult (instWinsCorrOps (N := String) (A := Unit)) ∧
      ¬ MOD_031 (instWinsCorrOps (N := String) (A := Unit)) := by
  have href := line4_of_via (N := String) (A := Unit) corrSideFull_keys CDef.map corrRebind
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, fun c i hx => ?_, fun c i hno => ?_, line5_corrRebind _ _ _⟩, fun h => ?_⟩
  · obtain ⟨msg, hm⟩ := (href c i).1 hx
    change corrMergeVia corrSideFull corrRefClash c i = _ at hm
    exact ⟨msg, by show corrInstWinsMerge c i = _; unfold corrInstWinsMerge; rw [hm]⟩
  · obtain ⟨m, hm⟩ := (href c i).2.1 hno
    change corrMergeVia corrSideFull corrRefClash c i = _ at hm
    exact ⟨_, by show corrInstWinsMerge c i = _; unfold corrInstWinsMerge; rw [hm]⟩
  · have hr := (h.2.2.2.1 mod031_callerMoves mod031_callerId).2.2
      (some ([("x", "x")] ++ [("x", "c/x")])) rfl "x"
    revert hr
    decide

/-- The binding that drops the correspondence kills the reading without line 5: binding an
action to the example after its passes leaves it without a correspondence. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_noRebind_killed :
    MOD_031_mutant_noRebind (dropRebindCorrOps (N := String) (A := Unit)) ∧
      ¬ MOD_031 (dropRebindCorrOps (N := String) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, line4_of_via corrSideFull_keys _ _⟩, fun h => ?_⟩
  have := (h.2.2.2.2 mod031_callerId .passthrough).1
  revert this
  decide

/-- The binding that drops the read arcs kills the reading of line 5 as the correspondence
only. Binding an action to a transition with a read arc on `1` keeps its correspondence but
leaves it with no read arc, so a late-bound action that reads `1` would fail. -/
@[evidence mutant MOD_031]
theorem MOD_031_mutant_corrOnlyRebind_killed :
    MOD_031_mutant_corrOnlyRebind (readDropRebindCorrOps (N := Nat) (A := Unit)) ∧
      ¬ MOD_031 (readDropRebindCorrOps (N := Nat) (A := Unit)) := by
  refine ⟨⟨line1_of_corrPass (fun _ _ _ => rfl) _ _, line2_of_map (fun _ _ _ => rfl) _ _ _,
    fun _ => rfl, line4_of_via corrSideFull_keys _ _, fun _ _ => rfl⟩, fun h => ?_⟩
  have := congrArg NTransition.reads (h.2.2.2.2 mod031_readEx .passthrough).2.1
  revert this
  decide

/-! ## Line 6: the context operations resolve through the correspondence -/

/-- **The contexts of a composed transition** ([MOD-031] line 6): for each correspondence a
transition can carry (`none`: it carries none), the transition context its action calls. -/
abbrev CorrCtx (N T V : Type) := Option (List (N × N)) → Ctx N T V

section CtxModel

variable {N T V : Type}

/-- **Resolve, then call** (Java and TypeScript): every context operation first resolves the
place it is given through the lookup `look`, then answers as the context `C` does for the
resolved place. -/
def ctxVia (look : Option (List (N × N)) → N → N) (C : Ctx N T V) : CorrCtx N T V :=
  fun c =>
  { inputs := fun t δ p => C.inputs t δ (look c p)
    input := fun t δ p => C.input t δ (look c p)
    inputToken := fun t δ p => C.inputToken t δ (look c p)
    read := fun t δ p => C.read t δ (look c p)
    output := fun t e p vs => C.output t e (look c p) vs }

variable [DecidableEq N]

/-- **The reference contexts of composed transitions**: the reference context `refCtx`, called
with the place the correspondence resolves the given place to. -/
def refResCtx (value : T → V) : CorrCtx N T V := ctxVia corrResolve (refCtx value)

/- The reference contexts of composed transitions are the witness model of MOD-031 line 6. -/
#spec_witness refResCtx

/-- With no correspondence, the reference context of a composed transition is the reference
context. -/
theorem refResCtx_none (value : T → V) : refResCtx (N := N) value none = refCtx value := rfl

end CtxModel

requirement MOD_031_ctx
  id "MOD-031"
  title "Action Place Resolution under Composition (the context operations)"
  kind F
  scope "the context operations of implementations that resolve a declared place in their context operations: Java and TypeScript in the context API (inputToken where it exists) and the Python binding adapter; not the Rust native context, which hands the correspondence to native actions"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_031.s8
  reading "For every value projection value, every set of correspondence operations O and every family R of transition contexts, one for each correspondence a transition can carry:"
          "for every correspondence c, transition t, delivery δ, output buffer e, place p and list of values vs, the calls inputs, input, inputToken and read on t, δ and p and the output call on t, e, p and vs of the context R c give what the same calls of the context R none give with p replaced by O.look c p, the place c resolves p to; results are compared whole, so a call reports an error (none) exactly when that call does."
  assumes "The model is the triple (value, O, R). O is the correspondence operations of the first block, and line 6 resolves through its lookup O.look, the lookup that lines 1 to 4 constrain, so a context resolves a place the way the correspondence's own lookup does (AC11). R gives, for each correspondence a transition can carry (none: it carries none), the transition context (Ctx, Spec/GlossaryContext.lean) its action calls: inputs, input, inputToken and read take the transition, the delivery and a place and return none when the call reports an error; output takes the transition, the buffer written so far, a place and the values of one call. R none is the context of a transition without a correspondence, the context CORE-060 to CORE-063 constrain, and line 6 says that R c is R none behind the lookup. The value projection value is not used by the line; it keeps the block on the model of CORE-060. The witness is refResCtx, refCtx called with the place corrResolve gives (refResCtx_none: without a correspondence it is refCtx), and mod031ctx_joint_ref gives MOD-031, line 6, CORE-060 and CORE-062 on the reference together."
          "Alone, line 6 says nothing about where a place resolves: an identity lookup with a context that ignores the correspondence meets it. Where a declared place resolves is lines 1 to 5, so the line is read with the first block. mod031ctx_after_passes derives, for every model of both with one O, that after any sequence of passes every call on a place the transition named before the passes answers what the call without a correspondence answers on the place the passes sent it to; mod031ctx_inputs_after_passes and mod031ctx_output_after_passes add CORE-060 line 1 and CORE-062 line 1, so inputs answers the values consumed from the actual place and an output call writes on the actual place, which the rewritten arcs name. Against the reference lookup a context that does not resolve is forbidden (MOD_031_ctx_forbids_noResolve). mod031ctx_joint_ref joins the two blocks with one O on the reference."
          "Scope, ruling D69 (a) with map ruling R-MC3 (a): the line holds of implementations that resolve in their context operations, in the context API or in a binding adapter. Java resolves through placeAlias.getOrDefault(place, place) (java/src/main/java/org/libpetri/core/TransitionContext.java resolve) before the declared-place check of input, inputs, inputToken, inputTokens, read, reads and every output form an action calls, and TypeScript through placeAlias.get(place.name) (typescript/src/core/transition-context.ts resolve, called by the same accessors); both are refResCtx. The Rust native context does not resolve: input and inputs look the given name up in the delivered map (rust/libpetri-core/src/context.rs, TransitionContext::input and inputs), and the correspondence is handed to bindings and native actions through local_name_map (the accessor of the same name in context.rs). The MAY paragraph of the markdown allows that for a binding-hosted implementation and says that a native action then resolves a declared place through the exposed correspondence itself, and that AC1, AC2, AC3 and AC7 hold of a native action that does. Read as a resolving context the Rust native context is the forbidden model above, so it is out of the block's scope."
          "The Python binding resolves in its binding adapter, correspondence first: resolve sends the given name through local_name_map and keeps it when it is no key, and resolve_lookup_key and require_output look up only the resolved name in the delivered input or read map or the allowed outputs, never the given name after it (rust/libpetri-py/src/action.rs, PyActionContext::resolve, resolve_lookup_key and require_output). With key presence read as arc membership, which agree on a firing's delivery (CORE-063 assumes), that is refResCtx. A wrong adapter that tries the given name first and falls back through the correspondence (litFirstCtx, nameFirstResCtx over the reference; the behaviour RD-30 recorded, which no runtime's adapter does) meets line 6 on every place that is not itself a place of the call's kind, and breaks it on such a place that the correspondence resolves to another place; it does on the collision example (MOD_031_ctx_mutant_literalFirst_killed, mod031ctx_collision). The spec asks for correspondence first (R-MC3 (a), and the MAY paragraph asks a binding adapter for the same order)."
          "'Before the declared-set check and before reading or writing the token store': a context that resolves the place for the check and then reads or writes the store at the place it was given reports an error exactly when the reference does, and still breaks the line (MOD_031_ctx_mutant_checkOnly_killed); the converse, a check on the given place and the store access on the resolved place, is forbidden too (MOD_031_ctx_forbids_checkGiven). Each accessor is load-bearing: contexts that leave output, read, or input and inputToken unresolved are killed (MOD_031_ctx_mutant_noOutput_killed, MOD_031_ctx_mutant_noRead_killed, MOD_031_ctx_mutant_inputsOnly_killed), and inputs is the conjunct the check-only and name-first contexts break. Resolving through the lookup once, and with the place itself as the default, is load-bearing as well: a context whose input resolves twice and one that reports an error for a place without an entry both pass the AC8 example and break the line on the collision example (MOD_031_ctx_forbids_resolveTwice, MOD_031_ctx_forbids_noDefault)."
          "The quoted sentence names inputToken beside the four operations of the body because Java and TypeScript resolve it too; Rust and Python have no inputToken. 'The single or bulk output': both calls are one Ctx field (CORE-062), a call with one value or with several. The body's 'all overloads' also covers the plural accessors and the other forms an action calls (reads, inputTokens, outputToken), which are not fields of Ctx; Java and TypeScript resolve each of them the same way (the sites above), which is a description of the code, not a line. outputToHarvest and forwardToHarvest are executor machinery, not action calls (the last paragraph)."
          "Discovery and the declared style meet on a collision: when a discovered place has the name of a declared place of the same transition that the correspondence moved (a port bound to a caller place that has the name of another declared place), the line resolves the discovered place too, so a port-agnostic action that passes it gets the answer of the moved place (mod031ctx_collision). No lookup order serves both styles there; a name-first order would serve the port-agnostic one. On every other discovered place the call answers for that place (mod031ctx_fixed), which is AC5's second half as the markdown words it."
          "AC1 (ctx.input(declaredIn) and ctx.output(declaredOut) after instancing and port binding, the transition fires and produces on the actual resp with no declared-place error) is mod031ctx_inputs_after_passes and mod031ctx_output_after_passes at the passes of instancing and binding; MOD_031_ctx_nonvacuous works the AC8 passes. That the firing then deposits what the action wrote is ctx_deposits_outputs (Spec/GlossaryContext.lean) with refActionFire. AC2 (Out.xor(aDecl, bDecl), the action selects aDecl, exactly one token on the actual a) is mod031ctx_output_after_passes on the output place aDecl; the exactly-one-production validator is EXEC-021's. AC3 (nested instantiation, the declared place resolves to outer/inner/x and the action fires) is mod031ctx_after_passes at the passes of the nesting. AC4 (a hand-written or directly composed transition behaves as before) is line 6 at the correspondence none, where R none answers for the place itself, with line 3. AC5's second half is the previous sentence. AC7 (a late-bound action resolves as a baked-in one) is mod031ctx_lateBind. AC8 asks to assert on the executor run; the block gives the calls (mod031ctx_after_passes at the three passes, MOD_031_ctx_nonvacuous), and the run is a test (Q), as is the test derivation. AC6, AC9, AC10 and AC11 are the first block's and MOD-050's."
          "A type mismatch between the place and the value is API shape and not modelled (V is one type of values). Calls made after a timeout severed the firing's output (IO-013) are out of scope, as for CORE-062. The executor's own deposit of the timeout branch is not an action's call either. Java and TypeScript make it from produceTimeoutOutput (java/src/main/java/org/libpetri/runtime/ExecutorSupport.java produceTimeoutOutputRecursive, typescript/src/runtime/executor-support.ts produceTimeoutOutput) through outputToHarvest and forwardToHarvest of the transition context (java/src/main/java/org/libpetri/core/TransitionContext.java, typescript/src/core/transition-context.ts) with the places the rewritten output specification names, which are already the actual places, and use them as given, without the correspondence; the forwarded tokens are read from the actual from place through the raw input (Java in produceTimeoutOutputRecursive, TypeScript in forwardToHarvest). Rust deposits the timeout branch on those places as given (timeout_outputs in the runtime's executor core). A wrong executor whose outputToHarvest and forwardToHarvest resolve those places through the correspondence a second time (the behaviour RD-31 recorded) writes the timeout token on another place on a collision: with port a bound to the caller place b and port b bound to c, the token meant for b lands on c (mod031ctx_timeout_resolveTwice), which IO-013 forbids; that is IO-013's matter, not a line of this block."
  signoff "2026-11-13 356933814782357b ai"
  statement : ∀ {N A T V : Type}, (T → V) → CorrOps N A → CorrCtx N T V → Prop :=
    fun {N _A T V} _value O R =>
      ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N)
        (vs : List V),
        (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
        (R c).input t δ p = (R none).input t δ (O.look c p) ∧
        (R c).inputToken t δ p = (R none).inputToken t δ (O.look c p) ∧
        (R c).read t δ p = (R none).read t δ (O.look c p) ∧
        (R c).output t e p vs = (R none).output t e (O.look c p) vs

/- The pinned readable form of MOD-031 line 6: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_031_ctx : {N A T V : Type} → (T → V) → CorrOps N A → CorrCtx N T V → Prop :=
fun {N _A T V} _value O R =>
  ∀ (c : Option (List (N × N))) (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N) (vs : List V),
    (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
      (R c).input t δ p = (R none).input t δ (O.look c p) ∧
        (R c).inputToken t δ p = (R none).inputToken t δ (O.look c p) ∧
          (R c).read t δ p = (R none).read t δ (O.look c p) ∧
            (R c).output t e p vs = (R none).output t e (O.look c p) vs
-/
#guard_msgs in #print MOD_031_ctx

section CtxLemmas

variable {N A T V : Type}

/-- Line 6 holds of every resolve-then-call context whose lookup resolves every place to itself
through no correspondence (MOD-031 line 3). -/
theorem mod031ctx_of_via (value : T → V) (O : CorrOps N A) (C : Ctx N T V)
    (h3 : ∀ p : N, O.look none p = p) : MOD_031_ctx value O (ctxVia O.look C) := by
  intro c t δ e p vs
  simp [ctxVia, h3]

/-- Under line 6, a call on a place the correspondence resolves to itself answers as the call
without a correspondence does: a port-agnostic action that passes such a discovered place gets
that place's answer. -/
theorem mod031ctx_fixed {value : T → V} {O : CorrOps N A} {R : CorrCtx N T V}
    (h : MOD_031_ctx value O R) (c : Option (List (N × N))) (q : N) (hq : O.look c q = q)
    (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (vs : List V) :
    (R c).inputs t δ q = (R none).inputs t δ q ∧ (R c).input t δ q = (R none).input t δ q ∧
    (R c).inputToken t δ q = (R none).inputToken t δ q ∧ (R c).read t δ q = (R none).read t δ q ∧
    (R c).output t e q vs = (R none).output t e q vs := by
  have := h c t δ e q vs
  rw [hq] at this
  exact this

/-- Under line 2, a sequence of passes sends the input places (as a set) and the output places
through the chain of place maps. -/
theorem mod031_disc_passes {O : CorrOps N A} (h : mod031_line2 O)
    (ss : List ((N → N) × (String → String))) :
    ∀ d : CDef N A,
      (∀ p, p ∈ discIn (corrPasses O ss d).toTransDef ↔ p ∈ (discIn d.toTransDef).map (corrChain ss)) ∧
      discOut (corrPasses O ss d).toTransDef = (discOut d.toTransDef).map (corrChain ss) := by
  induction ss with
  | nil =>
    intro d
    have e : corrChain ([] : List ((N → N) × (String → String))) = id := rfl
    simp [corrPasses, e]
  | cons s rest ih =>
    intro d
    have e := ih (O.pass s.1 s.2 d)
    simp only [corrPasses, List.foldl_cons] at e ⊢
    have ec : corrChain (s :: rest) = corrChain rest ∘ s.1 := rfl
    refine ⟨fun p => ?_, ?_⟩
    · rw [e.1 p, ec, ← List.map_map]
      constructor
      · intro hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact List.mem_map.2 ⟨q, ((h s.1 s.2 d).1 q).1 hq, rfl⟩
      · intro hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact List.mem_map.2 ⟨q, ((h s.1 s.2 d).1 q).2 hq, rfl⟩
    · rw [e.2, (h s.1 s.2 d).2.2.2.2, List.map_map, ec]

/-- **The context operations after the passes** (AC1, AC3, AC8): take a transition that carries
no correspondence through any sequence of rewrite passes. Every call its action makes on a place
the transition named before the passes answers what the call without a correspondence answers
for the place the passes sent it to. -/
theorem mod031ctx_after_passes {value : T → V} {O : CorrOps N A} {R : CorrCtx N T V}
    (h : MOD_031 O) (h6 : MOD_031_ctx value O R) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (hd : d.corr = none) (p : N)
    (hp : p ∈ d.namedPlaces) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (vs : List V) :
    let c := (corrPasses O ss d).corr
    (R c).inputs t δ p = (R none).inputs t δ (corrChain ss p) ∧
    (R c).input t δ p = (R none).input t δ (corrChain ss p) ∧
    (R c).inputToken t δ p = (R none).inputToken t δ (corrChain ss p) ∧
    (R c).read t δ p = (R none).read t δ (corrChain ss p) ∧
    (R c).output t e p vs = (R none).output t e (corrChain ss p) vs := by
  intro c
  have := h6 c t δ e p vs
  rw [(h.1 d ss hd).1 p hp] at this
  exact this

/-- **A late-bound action resolves as a baked-in one** (AC7): binding an action after the passes
keeps the correspondence (line 5), so the calls of the late-bound action answer as after the
passes. -/
theorem mod031ctx_lateBind {value : T → V} {O : CorrOps N A} {R : CorrCtx N T V}
    (h : MOD_031 O) (h6 : MOD_031_ctx value O R) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (a : Act A) (hd : d.corr = none) (p : N)
    (hp : p ∈ d.namedPlaces) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (vs : List V) :
    let c := (O.rebind (corrPasses O ss d) a).corr
    (R c).inputs t δ p = (R none).inputs t δ (corrChain ss p) ∧
    (R c).input t δ p = (R none).input t δ (corrChain ss p) ∧
    (R c).inputToken t δ p = (R none).inputToken t δ (corrChain ss p) ∧
    (R c).read t δ p = (R none).read t δ (corrChain ss p) ∧
    (R c).output t e p vs = (R none).output t e (corrChain ss p) vs := by
  intro c
  have hc : c = (corrPasses O ss d).corr := (h.2.2.2.2 (corrPasses O ss d) a).1
  rw [hc]
  exact mod031ctx_after_passes h h6 d ss hd p hp t δ e vs

variable [DecidableEq N]

/-- **Output on a declared place after the passes** (AC1, AC2, AC3): with MOD-031 and the
output rule of [CORE-062] for the context without a correspondence, an output call on a place the
transition's output specification named before the passes succeeds and writes its values on the
place the passes sent it to, which the rewritten output specification names. -/
theorem mod031ctx_output_after_passes {value : T → V} {O : CorrOps N A} {R : CorrCtx N T V}
    (h : MOD_031 O) (h6 : MOD_031_ctx value O R) (h62 : CORE_062 value (R none)) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (hd : d.corr = none) (y : N)
    (hy : y ∈ discOut d.toTransDef) (e : List (N × V)) (vs : List V) :
    (R (corrPasses O ss d).corr).output (corrPasses O ss d).toTransDef.toTrans e y vs =
      some (e ++ vs.map fun v => (corrChain ss y, v)) := by
  have hn : y ∈ d.namedPlaces := by
    show y ∈ d.toTransDef.namedPlaces
    unfold discOut at hy
    simp only [TransDef.namedPlaces, List.mem_append]
    exact Or.inr hy
  rw [(mod031ctx_after_passes h h6 d ss hd y hn (corrPasses O ss d).toTransDef.toTrans
    ⟨fun _ => [], fun _ => []⟩ e vs).2.2.2.2]
  apply h62.1
  have hq : corrChain ss y ∈ discOut (corrPasses O ss d).toTransDef := by
    rw [(mod031_disc_passes h.2.1 ss d).2]
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  unfold discOut at hq
  cases ho : (corrPasses O ss d).toTransDef.out with
  | none => rw [ho] at hq; cases hq
  | some o =>
    rw [ho] at hq
    exact ⟨o, ho, hq⟩

/-- **Input on a declared place after the passes** (AC1, AC3): with MOD-031 and the input rule
of [CORE-060] for the context without a correspondence, `inputs` on a place the transition's
input arcs named before the passes answers the values the firing consumed from the place the
passes sent it to. -/
theorem mod031ctx_inputs_after_passes {value : T → V} {O : CorrOps N A} {R : CorrCtx N T V}
    (h : MOD_031 O) (h6 : MOD_031_ctx value O R) (h60 : CORE_060 value (R none)) (d : CDef N A)
    (ss : List ((N → N) × (String → String))) (hd : d.corr = none) (x : N)
    (hx : x ∈ discIn d.toTransDef) (δ : Delivered N T) (hδ : δ.inputs (corrChain ss x) ≠ []) :
    (R (corrPasses O ss d).corr).inputs (corrPasses O ss d).toTransDef.toTrans δ x =
      some ((δ.inputs (corrChain ss x)).map value) := by
  have hn : x ∈ d.namedPlaces := by
    show x ∈ d.toTransDef.namedPlaces
    unfold discIn at hx
    simp only [TransDef.namedPlaces, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
  rw [(mod031ctx_after_passes h h6 d ss hd x hn (corrPasses O ss d).toTransDef.toTrans δ [] []).1]
  apply h60.1 _ _ _ _ hδ
  have hq : corrChain ss x ∈ discIn (corrPasses O ss d).toTransDef :=
    ((mod031_disc_passes h.2.1 ss d).1 _).2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  exact hq

end CtxLemmas

/-- ✓ The reference contexts satisfy MOD-031 line 6 at every place type. -/
@[evidence holds MOD_031_ctx]
theorem MOD_031_ctx_reference {N A T V : Type} [DecidableEq N] (value : T → V) :
    MOD_031_ctx value (refCorrOps (N := N) (A := A)) (refResCtx value) :=
  mod031ctx_of_via value refCorrOps (refCtx value) (fun _ => rfl)

/-! ### Wrong contexts -/

section WrongCtx

variable {N T V : Type} [DecidableEq N]

/-- **The name first** (a wrong binding adapter, the behaviour RD-30 recorded): a call on a place
that is itself a place of the transition of the call's kind answers for that place; any other
place is resolved through `look` first. -/
def litFirstCtx (look : Option (List (N × N)) → N → N) (C : Ctx N T V) : CorrCtx N T V :=
  fun c =>
  { inputs := fun t δ p => if p ∈ inPlaces t then C.inputs t δ p else C.inputs t δ (look c p)
    input := fun t δ p => if p ∈ inPlaces t then C.input t δ p else C.input t δ (look c p)
    inputToken := fun t δ p =>
      if p ∈ inPlaces t then C.inputToken t δ p else C.inputToken t δ (look c p)
    read := fun t δ p => if ReadArc t p then C.read t δ p else C.read t δ (look c p)
    output := fun t e p vs =>
      if OutputArc t p then C.output t e p vs else C.output t e (look c p) vs }

/-- The name-first adapter over the reference context. -/
def nameFirstResCtx (value : T → V) : CorrCtx N T V := litFirstCtx corrResolve (refCtx value)

/-- Without a correspondence the name-first context is the context it calls. -/
theorem litFirstCtx_none (look : Option (List (N × N)) → N → N) (C : Ctx N T V)
    (h3 : ∀ q, look none q = q) : litFirstCtx look C none = C := by
  cases C
  simp only [litFirstCtx, h3, ite_self]

/-- A context that resolves the place for the declared-place check only, and then reads or
writes the token store at the place it was given, for `inputs` and `output`. -/
def checkOnlyCtx (value : T → V) : CorrCtx N T V := fun c =>
  { refResCtx value c with
    inputs := fun t δ p =>
      if corrResolve c p ∈ inPlaces t then some ((δ.inputs p).map value) else none
    output := fun t e p vs =>
      if OutputArc t (corrResolve c p) then some (e ++ vs.map fun v => (p, v)) else none }

/-- A context that resolves every call but the output call. -/
def noOutputCtx (value : T → V) : CorrCtx N T V := fun c =>
  { refResCtx value c with output := (refCtx value).output }

/-- A context that resolves every call but `read`. -/
def noReadCtx (value : T → V) : CorrCtx N T V := fun c =>
  { refResCtx value c with read := (refCtx value).read }

/-- A context that resolves `inputs`, `read` and `output`, but not `input` and `inputToken`. -/
def inputsOnlyCtx (value : T → V) : CorrCtx N T V := fun c =>
  { refResCtx value c with input := (refCtx value).input, inputToken := (refCtx value).inputToken }

/-- A context whose `input` resolves the place twice, as an `input` that resolves and then hands
the resolved place to a call that resolves again. -/
def resolveTwiceCtx (value : T → V) : CorrCtx N T V := fun c =>
  { refResCtx value c with
    input := fun t δ p => (refCtx value).input t δ (corrResolve c (corrResolve c p)) }

/-- A context that resolves through the entry only: on a transition that carries a
correspondence, a place without an entry reports an error (Java's `placeAlias.get(place)` where
the code writes `placeAlias.getOrDefault(place, place)`). -/
def noDefaultCtx (value : T → V) : CorrCtx N T V := fun c =>
  match c with
  | none => refCtx value
  | some al =>
    { inputs := fun t δ p => (corrLookup al p).bind fun q => (refCtx value).inputs t δ q
      input := fun t δ p => (corrLookup al p).bind fun q => (refCtx value).input t δ q
      inputToken := fun t δ p => (corrLookup al p).bind fun q => (refCtx value).inputToken t δ q
      read := fun t δ p => (corrLookup al p).bind fun q => (refCtx value).read t δ q
      output := fun t e p vs => (corrLookup al p).bind fun q => (refCtx value).output t e q vs }

/-- A context that runs the declared-place check on the place the action gave and reads or
writes the token store at the resolved place (TypeScript's `this.requireInput(place)` where the
code writes `this.requireInput(actual)`). -/
def checkGivenCtx (value : T → V) : CorrCtx N T V := fun c =>
  { inputs := fun t δ p =>
      if p ∈ inPlaces t then some ((δ.inputs (corrResolve c p)).map value) else none
    input := fun t δ p =>
      if p ∈ inPlaces t then
        (match δ.inputs (corrResolve c p) with | [x] => some (value x) | _ => none)
      else none
    inputToken := fun t δ p =>
      if p ∈ inPlaces t then (δ.inputs (corrResolve c p)).head? else none
    read := fun t δ p =>
      if ReadArc t p then ((δ.reads (corrResolve c p)).head?).map value else none
    output := fun t e p vs =>
      if OutputArc t p then some (e ++ vs.map fun v => (corrResolve c p, v)) else none }

/-- Without a correspondence the check-on-the-given-place context is the reference context. -/
theorem checkGivenCtx_none (value : T → V) : checkGivenCtx (N := N) value none = refCtx value :=
  rfl

end WrongCtx

/-! ### Mutant readings of line 6 -/

section CtxMutants

variable {N A T V : Type}

/-- Mutant reading, the name first: line 6 only for a place that is not itself a place of the
transition of the call's kind. -/
def MOD_031_ctx_mutant_literalFirst (_value : T → V) (O : CorrOps N A) (R : CorrCtx N T V) :
    Prop :=
  ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N)
    (vs : List V),
    (p ∉ inPlaces t →
      (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
      (R c).input t δ p = (R none).input t δ (O.look c p) ∧
      (R c).inputToken t δ p = (R none).inputToken t δ (O.look c p)) ∧
    (¬ ReadArc t p → (R c).read t δ p = (R none).read t δ (O.look c p)) ∧
    (¬ OutputArc t p → (R c).output t e p vs = (R none).output t e (O.look c p) vs)

/-- Mutant reading, resolution for the check only: a call reports an error exactly when the call
without a correspondence reports one for the resolved place. -/
def MOD_031_ctx_mutant_checkOnly (_value : T → V) (O : CorrOps N A) (R : CorrCtx N T V) : Prop :=
  ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N)
    (vs : List V),
    ((R c).inputs t δ p).isSome = ((R none).inputs t δ (O.look c p)).isSome ∧
    ((R c).input t δ p).isSome = ((R none).input t δ (O.look c p)).isSome ∧
    ((R c).inputToken t δ p).isSome = ((R none).inputToken t δ (O.look c p)).isSome ∧
    ((R c).read t δ p).isSome = ((R none).read t δ (O.look c p)).isSome ∧
    ((R c).output t e p vs).isSome = ((R none).output t e (O.look c p) vs).isSome

/-- Mutant reading without the output call. -/
def MOD_031_ctx_mutant_noOutput (_value : T → V) (O : CorrOps N A) (R : CorrCtx N T V) : Prop :=
  ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (p : N),
    (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
    (R c).input t δ p = (R none).input t δ (O.look c p) ∧
    (R c).inputToken t δ p = (R none).inputToken t δ (O.look c p) ∧
    (R c).read t δ p = (R none).read t δ (O.look c p)

/-- Mutant reading without `read`. -/
def MOD_031_ctx_mutant_noRead (_value : T → V) (O : CorrOps N A) (R : CorrCtx N T V) : Prop :=
  ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N)
    (vs : List V),
    (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
    (R c).input t δ p = (R none).input t δ (O.look c p) ∧
    (R c).inputToken t δ p = (R none).inputToken t δ (O.look c p) ∧
    (R c).output t e p vs = (R none).output t e (O.look c p) vs

/-- Mutant reading with `inputs` as the only input accessor. -/
def MOD_031_ctx_mutant_inputsOnly (_value : T → V) (O : CorrOps N A) (R : CorrCtx N T V) :
    Prop :=
  ∀ (c : Option (List (N × N))) (t : Trans N) (δ : Delivered N T) (e : List (N × V)) (p : N)
    (vs : List V),
    (R c).inputs t δ p = (R none).inputs t δ (O.look c p) ∧
    (R c).read t δ p = (R none).read t δ (O.look c p) ∧
    (R c).output t e p vs = (R none).output t e (O.look c p) vs

end CtxMutants

/-! ### Examples -/

/-- The AC8 example after its three passes: the declared input `x` now on `b/x`, the declared
output `y` on `b/a/y`. -/
def mod031_acDone : CDef String Unit := corrPasses refCorrOps mod031_ac8 mod031_ex

/-- A firing of the AC8 example that consumed the token `7` from `b/x`. -/
def mod031_δx : Delivered String Nat := ⟨fun p => if p = "b/x" then [7] else [], fun _ => []⟩

/-- A transition over the declared input places `a` and `b`. -/
def mod031_col : CDef String Unit :=
  { core := ⟨"t", [⟨"a", .one⟩, ⟨"b", .one⟩], [], [], []⟩, out := none, timing := .immediate,
    priority := 0, action := .passthrough }

/-- The port binding of the collision: the port `a` bound to a caller place named `b`, the port
`b` to a caller place `c`. -/
def mod031_colBind (p : String) : String := if p = "a" then "b" else if p = "b" then "c" else p

/-- The collision example after its binding: input arcs on `b` and `c`. -/
def mod031_colDone : CDef String Unit := refCorrOps.pass mod031_colBind id mod031_col

/-- A firing of the collision example that consumed `1` from `b` and `2` from `c`. -/
def mod031_δcol : Delivered String Nat :=
  ⟨fun p => if p = "b" then [1] else if p = "c" then [2] else [], fun _ => []⟩

/-- ✓ The reference resolves before it checks and before it reads or writes. A subnet
transition consumes from its declared place `x` and produces on its declared place `y`. After
instantiating it under `a`, binding its port to a caller place named `x` and instantiating the
result under `b`, its arcs name `b/x` and `b/a/y`. The firing consumed `7` from `b/x`: the action's
`input(x)` answers `7`, and `output(y, 5)` writes `5` on `b/a/y`. Without the correspondence both
calls would fail their declared-place check. -/
@[evidence nonvacuous MOD_031_ctx]
theorem MOD_031_ctx_nonvacuous :
    (refResCtx id mod031_acDone.corr).input mod031_acDone.toTransDef.toTrans mod031_δx "x" =
      some 7 ∧
    (refResCtx id mod031_acDone.corr).output mod031_acDone.toTransDef.toTrans [] "y" [5] =
      some [("b/a/y", 5)] ∧
    (refResCtx (T := Nat) id none).input mod031_acDone.toTransDef.toTrans mod031_δx "x" = none ∧
    (refResCtx (T := Nat) id none).output mod031_acDone.toTransDef.toTrans [] "y" [5] = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **No order serves both action styles on a collision.** A transition declares the input
places `a` and `b`; its port `a` is bound to a caller place named `b` and its port `b` to a caller
place `c`, so discovery returns `b` and `c`. The firing consumed `1` from `b` and `2` from `c`. An
action written against the declared places gets `1` for `a` and `2` for `b`. A port-agnostic
action that discovered `b` and asks for it gets `2` too, because `b` is also a declared place that
the correspondence moved to `c`. An adapter that tries the name first (the behaviour RD-30
recorded) gives that action `1` and the declared-place action `1` for `b`. -/
theorem mod031ctx_collision :
    discIn mod031_colDone.toTransDef = ["b", "c"] ∧
    (refResCtx id mod031_colDone.corr).inputs mod031_colDone.toTransDef.toTrans mod031_δcol "a" =
      some [1] ∧
    (refResCtx id mod031_colDone.corr).inputs mod031_colDone.toTransDef.toTrans mod031_δcol "b" =
      some [2] ∧
    (nameFirstResCtx id mod031_colDone.corr).inputs mod031_colDone.toTransDef.toTrans
      mod031_δcol "b" =
      some [1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ✗ A context that does not resolve violates line 6: on the AC8 example, `inputs(x)` reports
an error, where the reference answers the token consumed from `b/x`. -/
@[evidence forbids MOD_031_ctx]
theorem MOD_031_ctx_forbids_noResolve :
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit))
      (fun _ => refCtx id) := by
  intro h
  have := (h mod031_acDone.corr mod031_acDone.toTransDef.toTrans mod031_δx [] "x" []).1
  revert this
  decide

/-- ✗ Resolving twice violates line 6. On the AC8 example it cannot be told apart: `input(x)`
answers `7` as the reference does, because `b/x` is not itself a declared place. On the collision
example the port `a` was bound to the caller place `b` and the port `b` to `c`. An `input(a)` that
resolves twice goes from `a` to `b` and on to `c`, and answers `2`, where line 6 asks for `1`, the
token consumed from `b`. -/
@[evidence forbids MOD_031_ctx]
theorem MOD_031_ctx_forbids_resolveTwice :
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (resolveTwiceCtx id) := by
  intro h
  have := (h mod031_colDone.corr mod031_colDone.toTransDef.toTrans mod031_δcol [] "a" []).2.1
  revert this
  decide

/-- ✗ A lookup without a default violates line 6. Every declared-place call of the AC8 example
passes: `input(x)` answers `7` and `output(y, 5)` writes `5` on `b/a/y`. On the collision example
a port-agnostic action that discovered the place `c` and asks `inputs(c)` gets an error, because
`c` has no entry in the correspondence; line 6 asks for `[2]`, the answer for `c` itself. -/
@[evidence forbids MOD_031_ctx]
theorem MOD_031_ctx_forbids_noDefault :
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (noDefaultCtx id) := by
  intro h
  have := (h mod031_colDone.corr mod031_colDone.toTransDef.toTrans mod031_δcol [] "c" []).1
  revert this
  decide

/-- ✗ Checking the place the action gave violates line 6. Without a correspondence this context is
the reference one. On the AC8 example `input(x)` fails its declared-place check, because the
transition's input arc is on `b/x`, not on `x`, although the store holds `7` on `b/x`; line 6 asks
for `7`. -/
@[evidence forbids MOD_031_ctx]
theorem MOD_031_ctx_forbids_checkGiven :
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (checkGivenCtx id) := by
  intro h
  have := (h mod031_acDone.corr mod031_acDone.toTransDef.toTrans mod031_δx [] "x" []).2.1
  revert this
  decide

/-- The wrong contexts above on the two examples. Resolving twice answers `input(x)` with `7` on the
AC8 example, as the reference does, and `input(a)` with `2` on the collision example. The lookup
without a default answers every declared-place call of the AC8 example as the reference does and
reports an error for `inputs(c)` on the collision example. Checking the given place fails
`input(x)` on the AC8 example. -/
theorem mod031ctx_wrong_examples :
    (resolveTwiceCtx id mod031_acDone.corr).input mod031_acDone.toTransDef.toTrans mod031_δx "x" =
      some 7 ∧
    (resolveTwiceCtx id mod031_colDone.corr).input mod031_colDone.toTransDef.toTrans mod031_δcol
      "a" = some 2 ∧
    (noDefaultCtx id mod031_acDone.corr).input mod031_acDone.toTransDef.toTrans mod031_δx "x" =
      some 7 ∧
    (noDefaultCtx (T := Nat) id mod031_acDone.corr).output mod031_acDone.toTransDef.toTrans [] "y"
      [5] = some [("b/a/y", 5)] ∧
    (noDefaultCtx id mod031_colDone.corr).inputs mod031_colDone.toTransDef.toTrans mod031_δcol "c" =
      none ∧
    (checkGivenCtx id mod031_acDone.corr).input mod031_acDone.toTransDef.toTrans mod031_δx "x" =
      none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The timeout example: a transition whose output specification is `xor(b, timeout(a))`. -/
def mod031_to : CDef String Unit :=
  { core := ⟨"t", [⟨"i", .one⟩], [], [], []⟩,
    out := some (.xor (.place "b") (.timeout (.place "a"))), timing := .immediate, priority := 0,
    action := .passthrough }

/-- The timeout example after the collision's binding: `xor(c, timeout(b))`. -/
def mod031_toDone : CDef String Unit := refCorrOps.pass mod031_colBind id mod031_to

/-- **A resolving call on a place that is already actual resolves it again.** A transition
produces `xor(b, timeout(a))`; its port `a` is bound to a caller place named `b` and its port `b`
to `c`, so the output specification becomes `xor(c, timeout(b))`. An executor that deposits the
timeout token through a resolving output call on the place the timeout branch names, `b`, writes it
on `c`, the other branch, because `b` is also a declared place that the correspondence moved to
`c` (the behaviour RD-31 recorded). The call without a correspondence, which Java and TypeScript
make, writes it on `b`. -/
theorem mod031ctx_timeout_resolveTwice :
    mod031_toDone.toTransDef.out.map outPlaces = some ["c", "b"] ∧
    (refResCtx (T := Nat) id mod031_toDone.corr).output mod031_toDone.toTransDef.toTrans [] "b" [0] =
      some [("c", 0)] ∧
    (refResCtx (T := Nat) id none).output mod031_toDone.toTransDef.toTrans [] "b" [0] =
      some [("b", 0)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The name-first context kills the mutant reading that resolves only a place that is not
itself a place of the call's kind. On the collision example, `inputs(b)` answers `1`, the tokens
of the actual `b`, where the declared `b` resolves to `c` and must answer `2`. -/
@[evidence mutant MOD_031_ctx]
theorem MOD_031_ctx_mutant_literalFirst_killed :
    MOD_031_ctx_mutant_literalFirst (id : Nat → Nat) (refCorrOps (N := String) (A := Unit))
      (nameFirstResCtx id) ∧
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (nameFirstResCtx id) := by
  refine ⟨fun c t δ e p vs => ?_, fun h => ?_⟩
  · have hn : nameFirstResCtx (N := String) (T := Nat) id none = refCtx id :=
      litFirstCtx_none corrResolve (refCtx id) (fun _ => rfl)
    rw [hn]
    refine ⟨fun hp => ?_, fun hr => ?_, fun ho => ?_⟩
    · simp only [nameFirstResCtx, litFirstCtx, hp, if_false]
      exact ⟨rfl, rfl, rfl⟩
    · simp only [nameFirstResCtx, litFirstCtx, hr, if_false]
      rfl
    · simp only [nameFirstResCtx, litFirstCtx, ho, if_false]
      rfl
  · have := (h mod031_colDone.corr mod031_colDone.toTransDef.toTrans mod031_δcol [] "b" []).1
    revert this
    decide

/-- The check-only context kills the mutant reading that resolves for the declared-place check
alone. On the AC8 example, `inputs(x)` passes its check on `b/x` and then reads the store at `x`,
which holds nothing, where the reference reads `7` from `b/x`. -/
@[evidence mutant MOD_031_ctx]
theorem MOD_031_ctx_mutant_checkOnly_killed :
    MOD_031_ctx_mutant_checkOnly (id : Nat → Nat) (refCorrOps (N := String) (A := Unit))
      (checkOnlyCtx id) ∧
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (checkOnlyCtx id) := by
  refine ⟨fun c t δ e p vs => ?_, fun h => ?_⟩
  · refine ⟨?_, rfl, rfl, rfl, ?_⟩
    · show (if corrResolve c p ∈ inPlaces t then some ((δ.inputs p).map id) else none).isSome =
        ((refCtx id).inputs t δ (corrResolve c p)).isSome
      by_cases hq : corrResolve c p ∈ inPlaces t <;> simp [refCtx, hq]
    · show (if OutputArc t (corrResolve c p) then some (e ++ vs.map fun v => (p, v))
          else none).isSome = ((refCtx id).output t e (corrResolve c p) vs).isSome
      by_cases hq : OutputArc t (corrResolve c p) <;> simp [refCtx, hq]
  · have := (h mod031_acDone.corr mod031_acDone.toTransDef.toTrans mod031_δx [] "x" []).1
    revert this
    decide

/-- The context that does not resolve the output call kills the reading without it. On the AC8
example, `output(y, 5)` reports an error, where the reference writes `5` on `b/a/y`. -/
@[evidence mutant MOD_031_ctx]
theorem MOD_031_ctx_mutant_noOutput_killed :
    MOD_031_ctx_mutant_noOutput (id : Nat → Nat) (refCorrOps (N := String) (A := Unit))
      (noOutputCtx id) ∧
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (noOutputCtx id) := by
  refine ⟨fun c t δ p => ⟨rfl, rfl, rfl, rfl⟩, fun h => ?_⟩
  have := (h mod031_acDone.corr mod031_acDone.toTransDef.toTrans mod031_δx [] "y" [5]).2.2.2.2
  revert this
  decide

/-- The read example after a pass that adds 10: the read arc on `11`. -/
def mod031_readDone : CDef Nat Unit := refCorrOps.pass (· + 10) id mod031_readEx

/-- A firing of the read example that read the token `3` on `11`. -/
def mod031_δread : Delivered Nat Nat := ⟨fun _ => [], fun p => if p = 11 then [3] else []⟩

/-- The context that does not resolve `read` kills the reading without it. A transition reads
its declared place `1`, which a pass moved to `11`; `read(1)` reports an error, where the
reference answers the token `3` read on `11`. -/
@[evidence mutant MOD_031_ctx]
theorem MOD_031_ctx_mutant_noRead_killed :
    MOD_031_ctx_mutant_noRead (id : Nat → Nat) (refCorrOps (N := Nat) (A := Unit))
      (noReadCtx id) ∧
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := Nat) (A := Unit)) (noReadCtx id) := by
  refine ⟨fun c t δ e p vs => ⟨rfl, rfl, rfl, rfl⟩, fun h => ?_⟩
  have := (h mod031_readDone.corr mod031_readDone.toTransDef.toTrans mod031_δread [] 1 []).2.2.2.1
  revert this
  decide

/-- The context that resolves `inputs` but not `input` and `inputToken` kills the reading with
`inputs` as the only input accessor. On the AC8 example, `input(x)` reports an error, where the
reference answers `7`. -/
@[evidence mutant MOD_031_ctx]
theorem MOD_031_ctx_mutant_inputsOnly_killed :
    MOD_031_ctx_mutant_inputsOnly (id : Nat → Nat) (refCorrOps (N := String) (A := Unit))
      (inputsOnlyCtx id) ∧
    ¬ MOD_031_ctx (id : Nat → Nat) (refCorrOps (N := String) (A := Unit)) (inputsOnlyCtx id) := by
  refine ⟨fun c t δ e p vs => ⟨rfl, rfl, rfl⟩, fun h => ?_⟩
  have := (h mod031_acDone.corr mod031_acDone.toTransDef.toTrans mod031_δx [] "x" []).2.1
  revert this
  decide

/-- **MOD-031 and its context line with the context rules of the reference.** The reference
correspondence operations and the reference contexts of composed transitions satisfy MOD-031,
its line 6, and, without a correspondence, CORE-060 and CORE-062. -/
theorem mod031ctx_joint_ref {N A T V : Type} [DecidableEq N] (value : T → V) :
    MOD_031 (refCorrOps (N := N) (A := A)) ∧
    MOD_031_ctx value (refCorrOps (N := N) (A := A)) (refResCtx value) ∧
    CORE_060 value (refResCtx (N := N) value none) ∧ CORE_062 value (refResCtx (N := N) value none) :=
  ⟨MOD_031_reference, MOD_031_ctx_reference value, CORE_060_reference value,
    CORE_062_reference value⟩

end Libpetri.Spec
