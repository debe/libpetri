import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild

set_option linter.missingDocs true

/-!
# CORE-042: Action binding separation (`spec/01-core-model.md`)

CORE-042 is a pure-function requirement (kind F) over two abstract binding functions on built
nets (`BuiltNet`, `Reference/Build.lean`): the resolver form `Bind b r`, where the resolver `r`
answers a transition name with an action or defers it (`none`), and the map form `BindMap b m`,
where the map `m` maps some transition names to actions. An action is read as its identity tag
(`Act`: the built-in passthrough or another action named by an opaque id). Binding never rejects:
both forms are functions, so a partially bound net is a value like any other.

The statement says that binding changes only the action of each transition: the places, the
terminal places and the transitions, in order, with their names, arcs, output specifications,
timings and priorities, are kept (line 1). In the resolver form an answered name gets its action
and a deferred one keeps it (lines 2 and 3). In the map form a mapped name gets its action
(line 4); the transitions the map omits all carry passthrough, or all carry the action they
carried (line 5), the part of the map form all runtimes share. Which of the two is the spec's
documented divergence: Java and TypeScript substitute passthrough, Rust keeps the action
(`CORE_042_mapForms_undecided`).

The witness is the reference binding `refBind` with the map read either way: `mapKeep` (Rust,
`CORE_042_reference_keep`) and `mapClobber` (Java, TypeScript, `CORE_042_reference_clobber`).
Wrong bindings are killed: one that drops read arcs, one that ignores the resolver, one whose map
form ignores the map, and one per line that meets a plausible wrong reading of that line.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-042: Action Binding Separation -/

requirement CORE_042
  id "CORE-042"
  title "Action Binding Separation"
  kind F
  scope "Java, TypeScript, Rust (net-level bindActions, both forms); Python rides on the Rust binding and exposes no net-level binding"
  source verbatim "spec/01-core-model.md"
  quote "The net's static structure (places, transitions, arcs, timing, priority) MUST be separable from the runtime behavior (actions)."
        "A `bindActions()` operation takes a structure and a mapping of transition names to actions, producing a new net with actions bound."
        "*When* actions are bound to a net, in either form, the new net *shall* have the name, the places and the terminal places of the original net and, for each transition of the original net, in the same order, a transition with the same name, arcs, output specification, timing and priority."
        "*When* actions are bound with a resolver that returns an action for a transition's name, the transition *shall* carry that action in the new net."
        "*When* actions are bound with a resolver that returns no action (`null`/`None`) for a transition's name, the transition *shall* carry in the new net the action it carried before."
        "*When* actions are bound with a mapping that maps a transition's name to an action, the transition *shall* carry that action in the new net."
        "*When* actions are bound with a mapping whose values are actions and that does not map a transition's name, the transition *shall* carry in the new net either the passthrough action or the action it carried before, and an implementation makes the same one of these two choices for every transition, every net and every mapping, so a transition that carried passthrough still carries passthrough."
        "Binding actions to a net *shall* return a new net for every net and every resolver or mapping, and *shall* leave the original net unchanged."
        "Binding is lazy and total: it never rejects, so a partially bound net is a legitimate intermediate value and an action MAY be bound after instantiation ([MOD-031] AC7); the declared structure is reconciled against the bound behaviour at compile time ([CORE-043])."
        "**Divergence:** the map form substitutes passthrough for every transition the map omits in Java and TypeScript (so a second call clobbers the first's bindings) but leaves them untouched in Rust; only the resolver form, where a `null`/`None` result defers a transition, binds in stages identically across implementations."
        "In Java a mapping may hold a name with a `null` value, and the map form then defers that transition as the resolver form does; TypeScript substitutes passthrough for a `null` or `undefined` value."
  reading "For every resolver-form binding Bind and map-form binding BindMap:"
          "for every built net b and every resolver r, the net Bind b r and the net BindMap b r each have b's places and b's terminal places, and their transition lists match b's position by position (same length, same order), each transition with b's name and arcs (core), output specification, timing and priority;"
          "for every b and r, the transition at each position of Bind b r carries the action a whenever r answers that position's name in b with a;"
          "for every b and r, the transition at each position of Bind b r carries the action b's transition there carried whenever r answers that name with none (defers it);"
          "for every b and every map m, the transition at each position of BindMap b m carries the action a whenever m maps that position's name in b to a;"
          "either, for every b and m, the transition at each position of BindMap b m carries passthrough whenever m does not map that name, or, for every b and m, it carries the action b's transition there carried whenever m does not map that name."
  assumes "A binding is a function from a built net (BuiltNet: places, transition definitions in declaration order, terminal places; Reference/Build.lean) and a resolver or map to a built net. A resolver and a map are both read as a function from names to an optional action: the resolver's null/None and a name the map does not hold are none. An action is read as its identity tag (Act: the built-in passthrough or another action named by an opaque id); what an action does is CORE-050's and the action model's (W3)."
          "The lines range over mappings whose values are actions (the body's 'a mapping of transition names to actions', and the quoted line 5 sentence's 'a mapping whose values are actions'). A mapping that holds a name with a null value, which Java's map allows, is outside them and outside every quoted shall sentence: the quoted Java sentence records what the runtimes do with it (Java defers that transition, since getOrDefault returns the held null and the resolver form keeps a transition whose resolver gives null, java/src/main/java/org/libpetri/core/PetriNet.java:202 and :219; TypeScript substitutes passthrough, typescript/src/core/petri-net.ts:80-82; a Rust map holds only actions). Read as none, such a mapping would make Java's map form keep some omitted transitions and clobber others within one call, which line 5 forbids; the line 5 sentence names mappings whose values are actions so that it does not."
          "The sentence that binding returns a new net for every net and every resolver or mapping and leaves the original net unchanged is not a line: it holds of every binding in the model, where a binding is a function on immutable values, so it returns a net for every net and every resolver or map and cannot change its argument b; in the runtimes it is tested directly. 'Total, it never rejects' is its first half: it includes a resolver or map that leaves some transitions with passthrough or answers a name that is no transition (that name is never asked for, so it is ignored). 'Lazy' is read as: binding checks nothing, neither comparing a bound action with the transition's output specification nor requiring every transition to be bound, so a partially bound net is a legitimate value, and reconciling it with the declared output specifications is the compile-time check of CORE-043. Binding after instantiation (MOD-031 AC7) and per-instance binding, including an override key that names no transition (ruling D87), are MOD-030's and MOD-031's (W8)."
          "The lines are stated per position, not per name, so they do not need the shared unique-names assumption (NetNamesDistinct, rulings D10 and D23): with two transitions of one name every runtime asks the resolver once per transition and binds both (java/src/main/java/org/libpetri/core/PetriNet.java:215-229, typescript/src/core/petri-net.ts:92-105, rust/libpetri-core/src/petri_net.rs:187-202), and so does the statement. Under that assumption binding by position is binding by name."
          "Line 1 is the body's first sentence: binding changes no field of the static structure. It names the terminal places (EXEC-042) and the output specification, which the body's list '(places, transitions, arcs, timing, priority)' does not: both are static structure and all three runtimes keep them (java/src/main/java/org/libpetri/core/PetriNet.java:228, typescript/src/core/petri-net.ts:104-105, rust/libpetri-core/src/petri_net.rs:165-174). The quoted sentence asks for a transition with the same fields, not the same transition: all three runtimes rebuild a rebound transition through the transition builder (Java and TypeScript rebuildWithAction; Rust rebuild_with_action, rust/libpetri-core/src/petri_net.rs:195-200 and rust/libpetri-core/src/transition.rs:614-643, with a fresh TransitionId), so the identity of a rebound transition (CORE-021) is not kept, and the line compares the fields position by position. The net's name, which the quoted sentence also names, is not a field of BuiltNet; every runtime keeps it (the same three places) and a test checks it outside the model. The subnet membership metadata is kept as MOD-026 says (the mapping survives a re-bind unchanged) and the declared-to-actual place correspondence as MOD-031 says (the rebuild that swaps the action carries it forward); neither is modelled here. A binding that rebuilds a transition and drops its read arcs (CORE_042_forbids_dropReads) violates line 1, and so does one that keeps only what firing reads and resets the priority (CORE_042_mutant_firingView_killed)."
          "The sentence 'When actions are bound to a net, in either form, a transition that has a match specification ([NU-020]) shall have the same match specification in the new net.' is not quoted by this block and no line here states it; its coverage is deferred to the NU-020 block (W9), which quotes it once a line over the ν-net definition states it. It is outside this model: the match specification (NU-020) is not a field of TransDef but of the ν-net model's definition that extends it (CORE-020's assumes, W9), so no binding on BuiltNet can drop it, and a rebuild that binds the action and drops the match specification has exactly refBind as its shadow on BuiltNet and meets every line here. All three runtimes carry the match specification forward and warn that dropping it would turn a join correlated by name into a plain join (java/src/main/java/org/libpetri/core/PetriNet.java:261-266, typescript/src/core/petri-net.ts:1020-1026, rust/libpetri-core/src/transition.rs:632-634). The sentence is a line over the ν-net definition and is handed to the NU-020 block (W9)."
          "Lines 2 and 3 are the resolver form, which all three runtimes share: an answered name gets the action, a null/None result defers the transition, which keeps its action. A binding that ignores the resolver (CORE_042_forbids_ignoreResolver) violates line 2, and so does one that binds only transitions still carrying passthrough (CORE_042_mutant_onlyUnbound_killed). A resolver form that replaces a deferred action by passthrough (the map form's Java reading applied to the resolver) violates line 3 (CORE_042_mutant_deferPassthrough_killed)."
          "Lines 4 and 5 are the map form's common part (ruling D20 (a) on clash core-b#4: the common part, and the divergence recorded). Rust keeps an omitted transition's action (mapKeep, rust/libpetri-core/src/petri_net.rs:177-183) and Java and TypeScript substitute passthrough (mapClobber, java/src/main/java/org/libpetri/core/PetriNet.java:202, typescript/src/core/petri-net.ts:80-82); both readings satisfy the block (CORE_042_reference_keep, CORE_042_reference_clobber) and they differ on a net whose omitted transition carries another action (CORE_042_mapForms_undecided). Line 5 asks for one reading per map form, as each runtime has: every omitted transition of every net carries passthrough, or every one keeps its action. A map form that keeps some omitted transitions and clobbers others meets the per-transition reading and violates line 5 (CORE_042_mutant_perTransition_killed). A map form that ignores the map (CORE_042_forbids_ignoreMap) violates line 4, and so does one whose map binds only transitions still carrying passthrough (CORE_042_mutant_mapOnlyUnbound_killed). Line 5 is stronger than AC4 alone: a map form that resets an omitted transition's action to a fixed other action meets AC4 and violates line 5 (CORE_042_mutant_ac4Only_killed)."
          "AC1 (a net can be created with no actions, all transitions using passthrough) is the builder default: a transition built without an action carries passthrough (TransIn.resolve, resolve_action_none in Reference/Build.lean), which is CORE-051's line (W3) and is not restated here; CORE_042_nonvacuous starts from such a net."
          "AC2 (bindActions(mapping) produces a new net with actions bound by transition name) is line 4 with line 1."
          "AC3 (the original net is not modified) is the second half of the quoted sentence that binding leaves the original net unchanged, which holds of every binding in the model (above) and is not a line."
          "AC4 (unbound transitions retain the passthrough action) is line 5 on a transition that carried passthrough, and line 3 for the resolver form. The test derivation (bind 2 of 3 transitions, the third still has passthrough) is CORE_042_nonvacuous, for the resolver form and both map readings."
          "The paragraph on SubnetDef.bindActions (the same argument forms, keyed by unprefixed names, a new definition) is the operation on a subnet definition, MOD-051's paragraph 'Binding actions on a definition' with its AC8, and is quoted there (W11). The Python binding exposes binding on instances and subnet definitions only (rust/libpetri-py/src/model.rs:667, :893), not on a net; it rides on the Rust binding."
  signoff "pending"
  statement : ∀ {N A : Type}, (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
      (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) → Prop :=
    fun Bind BindMap =>
      (∀ b r, ∀ f ∈ [Bind, BindMap],
        (f b r).places = b.places ∧ (f b r).terminals = b.terminals ∧
        List.Forall₂ (fun d' d => d'.core = d.core ∧ d'.out = d.out ∧ d'.timing = d.timing ∧
          d'.priority = d.priority) (f b r).trans b.trans) ∧
      (∀ b r, List.Forall₂ (fun d' d => ∀ x, r d.core.name = some x → d'.action = x)
        (Bind b r).trans b.trans) ∧
      (∀ b r, List.Forall₂ (fun d' d => r d.core.name = none → d'.action = d.action)
        (Bind b r).trans b.trans) ∧
      (∀ b m, List.Forall₂ (fun d' d => ∀ x, m d.core.name = some x → d'.action = x)
        (BindMap b m).trans b.trans) ∧
      ((∀ b m, List.Forall₂ (fun d' d => m d.core.name = none → d'.action = .passthrough)
          (BindMap b m).trans b.trans) ∨
        (∀ b m, List.Forall₂ (fun d' d => m d.core.name = none → d'.action = d.action)
          (BindMap b m).trans b.trans))

/- The pinned readable form of CORE-042: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_042 : {N A : Type} →
  (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) →
    (BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) → Prop :=
fun {N A} Bind BindMap =>
  (∀ (b : BuiltNet N A) (r : String → Option (Act A)),
      ∀ f ∈ [Bind, BindMap],
        (f b r).places = b.places ∧
          (f b r).terminals = b.terminals ∧
            List.Forall₂
              (fun d' d => d'.core = d.core ∧ d'.out = d.out ∧ d'.timing = d.timing ∧ d'.priority = d.priority)
              (f b r).trans b.trans) ∧
    (∀ (b : BuiltNet N A) (r : String → Option (Act A)),
        List.Forall₂ (fun d' d => ∀ (x : Act A), r d.core.name = some x → d'.action = x) (Bind b r).trans b.trans) ∧
      (∀ (b : BuiltNet N A) (r : String → Option (Act A)),
          List.Forall₂ (fun d' d => r d.core.name = none → d'.action = d.action) (Bind b r).trans b.trans) ∧
        (∀ (b : BuiltNet N A) (m : String → Option (Act A)),
            List.Forall₂ (fun d' d => ∀ (x : Act A), m d.core.name = some x → d'.action = x) (BindMap b m).trans
              b.trans) ∧
          ((∀ (b : BuiltNet N A) (m : String → Option (Act A)),
              List.Forall₂ (fun d' d => m d.core.name = none → d'.action = Act.passthrough) (BindMap b m).trans
                b.trans) ∨
            ∀ (b : BuiltNet N A) (m : String → Option (Act A)),
              List.Forall₂ (fun d' d => m d.core.name = none → d'.action = d.action) (BindMap b m).trans b.trans)
-/
#guard_msgs in #print CORE_042

/-! ### The five lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of CORE-042: both forms keep the static structure. -/
def core042_line1 (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) :
    Prop :=
  ∀ b r, ∀ f ∈ [Bind, BindMap],
    (f b r).places = b.places ∧ (f b r).terminals = b.terminals ∧
    List.Forall₂ (fun d' d => d'.core = d.core ∧ d'.out = d.out ∧ d'.timing = d.timing ∧
      d'.priority = d.priority) (f b r).trans b.trans

/-- Line 2 of CORE-042: the resolver form gives an answered name its action. -/
def core042_line2 (Bind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  ∀ b r, List.Forall₂ (fun d' d => ∀ x, r d.core.name = some x → d'.action = x)
    (Bind b r).trans b.trans

/-- Line 3 of CORE-042: the resolver form keeps a deferred transition's action. -/
def core042_line3 (Bind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  ∀ b r, List.Forall₂ (fun d' d => r d.core.name = none → d'.action = d.action)
    (Bind b r).trans b.trans

/-- Line 4 of CORE-042: the map form gives a mapped name its action. -/
def core042_line4 (BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  ∀ b m, List.Forall₂ (fun d' d => ∀ x, m d.core.name = some x → d'.action = x)
    (BindMap b m).trans b.trans

/-- Line 5 of CORE-042: the map form gives every omitted transition passthrough, or keeps the
action of every omitted transition. -/
def core042_line5 (BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  (∀ b m, List.Forall₂ (fun d' d => m d.core.name = none → d'.action = .passthrough)
      (BindMap b m).trans b.trans) ∨
    (∀ b m, List.Forall₂ (fun d' d => m d.core.name = none → d'.action = d.action)
      (BindMap b m).trans b.trans)

/-- CORE-042 is its five lines. -/
theorem core042_iff (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) :
    CORE_042 Bind BindMap ↔ core042_line1 Bind BindMap ∧ core042_line2 Bind ∧ core042_line3 Bind ∧
      core042_line4 BindMap ∧ core042_line5 BindMap :=
  Iff.rfl

end Lines

/-! ### A per-transition binding and its lines -/

section PerTransition

variable {N A : Type}

/-- A binding that rewrites each transition definition on its own, by a function of the
resolver: the shape of every binding in this file. -/
def core042_mapBind (g : (String → Option (Act A)) → TransDef N A → TransDef N A) :
    BuiltNet N A → (String → Option (Act A)) → BuiltNet N A :=
  fun b r => { b with trans := b.trans.map (g r) }

/-- A per-transition binding's transition list matches the original position by position. -/
theorem core042_forall₂_map {R : TransDef N A → TransDef N A → Prop}
    {f : TransDef N A → TransDef N A} {l : List (TransDef N A)} (h : ∀ d ∈ l, R (f d) d) :
    List.Forall₂ R (l.map f) l :=
  List.forall₂_map_left_iff.2 (List.forall₂_same.2 h)

/-- Line 1 holds of two per-transition bindings that keep every non-action field. -/
theorem core042_line1_of (g g' : (String → Option (Act A)) → TransDef N A → TransDef N A)
    (hg : ∀ r d, (g r d).core = d.core ∧ (g r d).out = d.out ∧ (g r d).timing = d.timing ∧
      (g r d).priority = d.priority)
    (hg' : ∀ r d, (g' r d).core = d.core ∧ (g' r d).out = d.out ∧ (g' r d).timing = d.timing ∧
      (g' r d).priority = d.priority) :
    core042_line1 (core042_mapBind g) (core042_mapBind g') := by
  intro b r f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨rfl, rfl, core042_forall₂_map fun d _ => hg r d⟩
  · exact ⟨rfl, rfl, core042_forall₂_map fun d _ => hg' r d⟩

/-- The reference binding is the per-transition binding by `bindWith`. -/
theorem core042_refBind_eq :
    (refBind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) =
      core042_mapBind (fun r d => d.bindWith r) := rfl

/-- The reference binding meets line 1 together with any per-transition map form that keeps
every non-action field. -/
theorem core042_ref_fields (r : String → Option (Act A)) (d : TransDef N A) :
    (d.bindWith r).core = d.core ∧ (d.bindWith r).out = d.out ∧ (d.bindWith r).timing = d.timing ∧
      (d.bindWith r).priority = d.priority :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Lines 2 and 3 hold of the reference binding. -/
theorem core042_ref_line23 :
    core042_line2 (refBind : BuiltNet N A → _ → _) ∧ core042_line3 (refBind : BuiltNet N A → _ → _) :=
  ⟨fun b r => core042_forall₂_map fun _ _ _ h => bindWith_answered h,
    fun b r => core042_forall₂_map fun _ _ h => by rw [bindWith_deferred h]⟩

end PerTransition

/-! ### The reference, with the map read either way -/

section Reference

variable {N A : Type}

/-- The map form as Rust reads it: the reference binding with the map as resolver (a name the map
omits is deferred, `rust/libpetri-core/src/petri_net.rs:177-183`). -/
def refBindMapKeep (b : BuiltNet N A) (m : String → Option (Act A)) : BuiltNet N A :=
  refBind b (mapKeep m)

/-- The map form as Java and TypeScript read it: the reference binding with a name the map omits
answered by passthrough (`java/src/main/java/org/libpetri/core/PetriNet.java:202`,
`typescript/src/core/petri-net.ts:80-82`). -/
def refBindMapClobber (b : BuiltNet N A) (m : String → Option (Act A)) : BuiltNet N A :=
  refBind b (mapClobber m)

/- The two readings of the map form are the witness models of CORE-042's map-form argument. -/
#spec_witness refBindMapKeep
#spec_witness refBindMapClobber

/-- ✓ The reference binding satisfies CORE-042 with the map read as Rust reads it: an omitted
name keeps its action. -/
@[evidence holds CORE_042]
theorem CORE_042_reference_keep : CORE_042 (refBind (N := N) (A := A)) refBindMapKeep := by
  refine ⟨core042_line1_of (fun r d => d.bindWith r) (fun m d => d.bindWith (mapKeep m))
      core042_ref_fields (fun m d => core042_ref_fields (mapKeep m) d),
    core042_ref_line23.1, core042_ref_line23.2, fun b m => ?_, ?_⟩
  · exact core042_forall₂_map fun _ _ _ h => bindWith_answered (r := mapKeep m) h
  · exact Or.inr fun b m => core042_forall₂_map fun _ _ h => by
      rw [bindWith_deferred (r := mapKeep m) h]

/-- ✓ The reference binding satisfies CORE-042 with the map read as Java and TypeScript read
it: an omitted name gets passthrough. -/
@[evidence holds CORE_042]
theorem CORE_042_reference_clobber : CORE_042 (refBind (N := N) (A := A)) refBindMapClobber := by
  refine ⟨core042_line1_of (fun r d => d.bindWith r) (fun m d => d.bindWith (mapClobber m))
      core042_ref_fields (fun m d => core042_ref_fields (mapClobber m) d),
    core042_ref_line23.1, core042_ref_line23.2, fun b m => ?_, ?_⟩
  · exact core042_forall₂_map fun _ _ _ h =>
      bindWith_answered (r := mapClobber m) (by simp [mapClobber, h])
  · exact Or.inl fun b m => core042_forall₂_map fun _ _ h =>
      bindWith_answered (r := mapClobber m) (by simp [mapClobber, h])

end Reference

/-! ### Examples -/

/-- The example net: places 0 to 3 and three transitions `a` (0 to 1, a read arc on 3, priority
5), `b` (1 to 2) and `c` (2 to 3), built without actions, so each carries passthrough. -/
def core042_ex : BuiltNet Nat Nat :=
  ⟨[0, 1, 2, 3],
    [({ core := ⟨"a", [⟨0, .one⟩], [], [3], []⟩, out := some (.place 1), priority := some 5 } :
        TransIn Nat Nat).resolve,
     ({ core := ⟨"b", [⟨1, .one⟩], [], [], []⟩, out := some (.place 2) } : TransIn Nat Nat).resolve,
     ({ core := ⟨"c", [⟨2, .one⟩], [], [], []⟩, out := some (.place 3) } : TransIn Nat Nat).resolve],
    []⟩

/-- The example mapping: `a` to action 1, `b` to action 2, `c` not mapped. -/
def core042_map : String → Option (Act Nat) :=
  fun n => if n = "a" then some (.other 1) else if n = "b" then some (.other 2) else none

/-- A resolver that answers `a` with action 2 and defers every other name. -/
def core042_rebindA : String → Option (Act Nat) :=
  fun n => if n = "a" then some (.other 2) else none

/-- ✓ Every line of CORE-042 is exercised by the reference (the test derivation): the example
net is built without actions, so all three transitions carry passthrough (AC1); binding `a` and
`b` and leaving `c` out gives `a` and `b` their actions and leaves `c` with passthrough, in the
resolver form and in both map readings (lines 2, 4, 5, AC2, AC4), and keeps the places and the
non-action fields (line 1); rebinding `a` with the other names deferred keeps `b`'s action
(line 3); and the two map readings differ on `b` when the second map omits it. -/
@[evidence nonvacuous CORE_042]
theorem CORE_042_nonvacuous :
    core042_ex.trans.map (·.action) = [.passthrough, .passthrough, .passthrough] ∧
    (refBind core042_ex core042_map).trans.map (·.action) = [.other 1, .other 2, .passthrough] ∧
    (refBindMapKeep core042_ex core042_map).trans.map (·.action) =
      [.other 1, .other 2, .passthrough] ∧
    (refBindMapClobber core042_ex core042_map).trans.map (·.action) =
      [.other 1, .other 2, .passthrough] ∧
    (refBind core042_ex core042_map).places = [0, 1, 2, 3] ∧
    (refBind core042_ex core042_map).trans.map (·.priority) = [5, 0, 0] ∧
    (refBind (refBind core042_ex core042_map) core042_rebindA).trans.map (·.action) =
      [.other 2, .other 2, .passthrough] ∧
    (refBindMapKeep (refBind core042_ex core042_map) core042_rebindA).trans.map (·.action) =
      [.other 2, .other 2, .passthrough] ∧
    (refBindMapClobber (refBind core042_ex core042_map) core042_rebindA).trans.map (·.action) =
      [.other 2, .passthrough, .passthrough] := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩ <;> decide

/-- ? The map form's two readings both satisfy CORE-042 and give different nets: binding the
example's bound net with a map that holds only `a` keeps `b`'s action 2 under Rust's reading and
replaces it by passthrough under Java's and TypeScript's (the spec's documented divergence,
clash core-b#4). Which one an implementation follows is not settled by the block. -/
@[evidence undecided CORE_042]
theorem CORE_042_mapForms_undecided :
    CORE_042 (refBind (N := Nat) (A := Nat)) refBindMapKeep ∧
    CORE_042 (refBind (N := Nat) (A := Nat)) refBindMapClobber ∧
    (refBindMapKeep (refBind core042_ex core042_map) core042_rebindA).trans.map (·.action) ≠
      (refBindMapClobber (refBind core042_ex core042_map) core042_rebindA).trans.map
        (·.action) :=
  ⟨CORE_042_reference_keep, CORE_042_reference_clobber, by decide⟩

/-! ### Wrong bindings -/

section Wrong

variable {N A : Type}

/-- A binding that rebuilds every transition without its read arcs, and is the reference
otherwise. -/
def core042_dropReadsBind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A :=
  core042_mapBind fun r d => { d.bindWith r with core := { d.core with reads := [] } }

/-- A binding that ignores the resolver: the net comes back unchanged. -/
def core042_ignoreBind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A :=
  fun b _ => b

end Wrong

/-- The first transition of the example's bound net under a binding of the example. -/
theorem core042_head {R : TransDef Nat Nat → TransDef Nat Nat → Prop} {l : List (TransDef Nat Nat)}
    {d : TransDef Nat Nat} {l' : List (TransDef Nat Nat)} (h : List.Forall₂ R l (d :: l')) :
    ∃ d₀ l₀, l = d₀ :: l₀ ∧ R d₀ d := by
  cases h with
  | cons hr _ => exact ⟨_, _, rfl, hr⟩

/-- The second transition of the example's bound net under a binding of the example. -/
theorem core042_second {R : TransDef Nat Nat → TransDef Nat Nat → Prop}
    {l : List (TransDef Nat Nat)} {d d' : TransDef Nat Nat} {l' : List (TransDef Nat Nat)}
    (h : List.Forall₂ R l (d :: d' :: l')) : ∃ d₀ d₁ l₀, l = d₀ :: d₁ :: l₀ ∧ R d₁ d' := by
  cases h with
  | cons _ h' => cases h' with
    | cons hr _ => exact ⟨_, _, _, rfl, hr⟩

/-- ✗ A binding that drops the read arcs when it rebuilds a transition violates CORE-042
(line 1): the example's transition `a` loses its read arc on place 3. -/
@[evidence forbids CORE_042]
theorem CORE_042_forbids_dropReads :
    ¬ CORE_042 (core042_dropReadsBind (N := Nat) (A := Nat)) refBindMapKeep := by
  intro h
  obtain ⟨-, -, hf⟩ := h.1 core042_ex core042_map _ (List.mem_cons_self ..)
  obtain ⟨d₀, l₀, he, hr⟩ := core042_head hf
  have h1 := congrArg (·.head?.map (·.core.reads)) he
  simp only [core042_dropReadsBind, core042_mapBind, core042_ex, List.map_cons,
    List.head?_cons, Option.map_some] at h1
  rw [hr.1] at h1
  exact absurd h1 (by decide)

/-- ✗ A binding that ignores the resolver violates CORE-042 (line 2): the example's `a` keeps
passthrough although the mapping answers it with action 1. -/
@[evidence forbids CORE_042]
theorem CORE_042_forbids_ignoreResolver :
    ¬ CORE_042 (core042_ignoreBind (N := Nat) (A := Nat)) refBindMapKeep := by
  intro h
  obtain ⟨d₀, l₀, he, hr⟩ := core042_head (h.2.1 core042_ex core042_map)
  have h1 := hr (.other 1) (by decide)
  have h2 := congrArg (·.head?.map (·.action)) he
  simp only [core042_ignoreBind, core042_ex, List.head?_cons, Option.map_some] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- ✗ A map form that ignores the map violates CORE-042 (line 4): the example's `a` keeps
passthrough although the map maps it to action 1. -/
@[evidence forbids CORE_042]
theorem CORE_042_forbids_ignoreMap :
    ¬ CORE_042 (refBind (N := Nat) (A := Nat)) core042_ignoreBind := by
  intro h
  obtain ⟨d₀, l₀, he, hr⟩ := core042_head (h.2.2.2.1 core042_ex core042_map)
  have h1 := hr (.other 1) (by decide)
  have h2 := congrArg (·.head?.map (·.action)) he
  simp only [core042_ignoreBind, core042_ex, List.head?_cons, Option.map_some] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Mutant: line 1 read as what firing reads -/

section MutantFiringView

variable {N A : Type}

/-- Mutant reading of line 1: binding keeps the places, the terminal places and, position by
position, what firing reads of each transition (`TransDef.toTrans`: name and arcs, output
specification, and whether the timing has a deadline). Lines 2 to 5 are as in CORE-042. -/
def CORE_042_mutant_firingView
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  (∀ b r, ∀ f ∈ [Bind, BindMap],
    (f b r).places = b.places ∧ (f b r).terminals = b.terminals ∧
    List.Forall₂ (fun d' d => d'.toTrans = d.toTrans) (f b r).trans b.trans) ∧
  core042_line2 Bind ∧ core042_line3 Bind ∧ core042_line4 BindMap ∧ core042_line5 BindMap

/-- A binding that rebuilds every transition with priority 0 (a rebuild that forgets the
priority), and is the reference otherwise. -/
def core042_resetPrioBind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A :=
  core042_mapBind fun r d => { d.bindWith r with priority := 0 }

end MutantFiringView

/-- The priority-resetting binding kills the mutant: it changes nothing firing reads, so it meets
the firing-view reading, but the example's `a` comes back with priority 0, not 5 (line 1). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_firingView_killed :
    CORE_042_mutant_firingView (core042_resetPrioBind (N := Nat) (A := Nat)) refBindMapKeep ∧
      ¬ CORE_042 (core042_resetPrioBind (N := Nat) (A := Nat)) refBindMapKeep := by
  obtain ⟨-, -, -, h4, h5⟩ := CORE_042_reference_keep (N := Nat) (A := Nat)
  refine ⟨⟨fun b r f hf => ?_, fun b r => ?_, fun b r => ?_, h4, h5⟩, fun h => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨rfl, rfl, core042_forall₂_map fun _ _ => rfl⟩
    · exact ⟨rfl, rfl, core042_forall₂_map fun _ _ => rfl⟩
  · exact core042_forall₂_map fun _ _ _ h => bindWith_answered (r := r) h
  · exact core042_forall₂_map fun d _ h => by
      show (d.bindWith r).action = _
      rw [bindWith_deferred h]
  · obtain ⟨-, -, hf⟩ := h.1 core042_ex core042_map _ (List.mem_cons_self ..)
    obtain ⟨d₀, l₀, he, hr⟩ := core042_head hf
    have h1 := congrArg (·.head?.map (·.priority)) he
    simp only [core042_resetPrioBind, core042_mapBind, core042_ex, List.map_cons,
      List.head?_cons, Option.map_some] at h1
    rw [hr.2.2.2] at h1
    exact absurd h1 (by decide)

/-! ### Mutant: line 2 read as binding only unbound transitions -/

section MutantOnlyUnbound

variable {N A : Type}

/-- Mutant reading of line 2: the resolver form gives an answered name its action when the
transition still carries passthrough (binding fills unbound transitions only). Lines 1 and 3 to 5
are as in CORE-042. -/
def CORE_042_mutant_onlyUnbound
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  core042_line1 Bind BindMap ∧
  (∀ b r, List.Forall₂ (fun d' d => d.action = .passthrough → ∀ x, r d.core.name = some x →
    d'.action = x) (Bind b r).trans b.trans) ∧
  core042_line3 Bind ∧ core042_line4 BindMap ∧ core042_line5 BindMap

/-- The definition after binding only if it still carries passthrough. -/
def core042_bindUnbound (r : String → Option (Act A)) (d : TransDef N A) : TransDef N A :=
  match d.action with
  | .passthrough => d.bindWith r
  | .other _ => d

/-- A binding that binds only transitions still carrying passthrough. -/
def core042_onlyUnboundBind : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A :=
  core042_mapBind core042_bindUnbound

/-- Binding only unbound transitions keeps every non-action field. -/
theorem core042_bindUnbound_fields (r : String → Option (Act A)) (d : TransDef N A) :
    (core042_bindUnbound r d).core = d.core ∧ (core042_bindUnbound r d).out = d.out ∧
      (core042_bindUnbound r d).timing = d.timing ∧
      (core042_bindUnbound r d).priority = d.priority := by
  unfold core042_bindUnbound
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Binding only unbound transitions keeps a deferred transition's action. -/
theorem core042_bindUnbound_deferred {r : String → Option (Act A)} {d : TransDef N A}
    (h : r d.core.name = none) : (core042_bindUnbound r d).action = d.action := by
  unfold core042_bindUnbound
  split
  · rw [bindWith_deferred h]
  · rfl

/-- Binding only unbound transitions gives an answered unbound transition its action. -/
theorem core042_bindUnbound_answered {r : String → Option (Act A)} {d : TransDef N A} {x : Act A}
    (hp : d.action = .passthrough) (h : r d.core.name = some x) :
    (core042_bindUnbound r d).action = x := by
  unfold core042_bindUnbound
  rw [hp]
  exact bindWith_answered h

end MutantOnlyUnbound

/-- The only-unbound binding kills the mutant: it binds every unbound transition, so it meets the
fill-only reading, but rebinding the example's bound `a` (action 1) with action 2 leaves it with
action 1 (line 2). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_onlyUnbound_killed :
    CORE_042_mutant_onlyUnbound (core042_onlyUnboundBind (N := Nat) (A := Nat)) refBindMapKeep ∧
      ¬ CORE_042 (core042_onlyUnboundBind (N := Nat) (A := Nat)) refBindMapKeep := by
  obtain ⟨-, -, -, h4, h5⟩ := CORE_042_reference_keep (N := Nat) (A := Nat)
  refine ⟨⟨core042_line1_of core042_bindUnbound (fun m d => d.bindWith (mapKeep m))
      core042_bindUnbound_fields (fun m d => core042_ref_fields (mapKeep m) d),
    fun b r => core042_forall₂_map fun _ _ hp _ h => core042_bindUnbound_answered hp h,
    fun b r => core042_forall₂_map fun _ _ h => core042_bindUnbound_deferred h, h4, h5⟩,
    fun h => ?_⟩
  obtain ⟨d₀, l₀, he, hr⟩ := core042_head (h.2.1 (refBind core042_ex core042_map) core042_rebindA)
  have h1 := hr (.other 2) (by decide)
  have h2 := congrArg (·.head?.map (·.action)) he
  simp only [core042_onlyUnboundBind, core042_mapBind, refBind, core042_ex, List.map_cons,
    List.head?_cons, Option.map_some] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Mutant: line 3 read as AC4 -/

section MutantDeferPassthrough

variable {N A : Type}

/-- Mutant reading of line 3 (AC4 applied to the resolver form): a deferred transition that
carried passthrough still carries passthrough. Lines 1, 2, 4 and 5 are as in CORE-042. -/
def CORE_042_mutant_deferPassthrough
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  core042_line1 Bind BindMap ∧ core042_line2 Bind ∧
  (∀ b r, List.Forall₂ (fun d' d => r d.core.name = none → d.action = .passthrough →
    d'.action = .passthrough) (Bind b r).trans b.trans) ∧
  core042_line4 BindMap ∧ core042_line5 BindMap

end MutantDeferPassthrough

/-- The resolver form read as Java's map form (a deferred name gets passthrough) kills the
mutant: an unbound deferred transition stays passthrough, so it meets the AC4 reading, but
deferring the example's bound `a` (action 1) replaces its action by passthrough (line 3). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_deferPassthrough_killed :
    CORE_042_mutant_deferPassthrough (refBindMapClobber (N := Nat) (A := Nat)) refBindMapKeep ∧
      ¬ CORE_042 (refBindMapClobber (N := Nat) (A := Nat)) refBindMapKeep := by
  obtain ⟨-, -, -, h4, h5⟩ := CORE_042_reference_keep (N := Nat) (A := Nat)
  obtain ⟨-, -, -, h4c, -⟩ := CORE_042_reference_clobber (N := Nat) (A := Nat)
  refine ⟨⟨core042_line1_of (fun m d => d.bindWith (mapClobber m))
      (fun m d => d.bindWith (mapKeep m))
      (fun m d => core042_ref_fields (mapClobber m) d)
      (fun m d => core042_ref_fields (mapKeep m) d),
    h4c, fun b r => core042_forall₂_map fun _ _ h _ =>
      bindWith_answered (r := mapClobber r) (by simp [mapClobber, h]), h4, h5⟩, fun h => ?_⟩
  obtain ⟨d₀, l₀, he, hr⟩ :=
    core042_head (h.2.2.1 (refBind core042_ex core042_map) (fun _ => none))
  have h1 := hr rfl
  have h2 := congrArg (·.head?.map (·.action)) he
  simp only [refBindMapClobber, refBind, core042_ex, List.map_cons,
    List.head?_cons, Option.map_some] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Mutant: line 4 read as binding only unbound transitions -/

section MutantMapOnlyUnbound

variable {N A : Type}

/-- Mutant reading of line 4: the map form gives a mapped name its action when the transition
still carries passthrough. Lines 1 to 3 and 5 are as in CORE-042. -/
def CORE_042_mutant_mapOnlyUnbound
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  core042_line1 Bind BindMap ∧ core042_line2 Bind ∧ core042_line3 Bind ∧
  (∀ b m, List.Forall₂ (fun d' d => d.action = .passthrough → ∀ x, m d.core.name = some x →
    d'.action = x) (BindMap b m).trans b.trans) ∧
  core042_line5 BindMap

end MutantMapOnlyUnbound

/-- The only-unbound binding used as the map form kills the mutant: it binds every unbound
mapped transition and keeps every omitted one, so it meets the fill-only reading and line 5, but
mapping the example's bound `a` (action 1) to action 2 leaves it with action 1 (line 4). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_mapOnlyUnbound_killed :
    CORE_042_mutant_mapOnlyUnbound (refBind (N := Nat) (A := Nat)) core042_onlyUnboundBind ∧
      ¬ CORE_042 (refBind (N := Nat) (A := Nat)) core042_onlyUnboundBind := by
  refine ⟨⟨core042_line1_of (fun r d => d.bindWith r) core042_bindUnbound
      core042_ref_fields core042_bindUnbound_fields,
    core042_ref_line23.1, core042_ref_line23.2,
    fun b m => core042_forall₂_map fun _ _ hp _ h => core042_bindUnbound_answered hp h,
    Or.inr fun b m => core042_forall₂_map fun _ _ h => core042_bindUnbound_deferred h⟩,
    fun h => ?_⟩
  obtain ⟨d₀, l₀, he, hr⟩ :=
    core042_head (h.2.2.2.1 (refBind core042_ex core042_map) core042_rebindA)
  have h1 := hr (.other 2) (by decide)
  have h2 := congrArg (·.head?.map (·.action)) he
  simp only [core042_onlyUnboundBind, core042_mapBind, refBind, core042_ex, List.map_cons,
    List.head?_cons, Option.map_some] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Mutant: line 5 read as AC4 alone -/

section MutantAc4Only

variable {N A : Type}

/-- Mutant reading of line 5 (AC4 alone): an omitted transition that carried passthrough still
carries passthrough, whatever happens to an omitted transition that carried another action.
Lines 1 to 4 are as in CORE-042. -/
def CORE_042_mutant_ac4Only
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  core042_line1 Bind BindMap ∧ core042_line2 Bind ∧ core042_line3 Bind ∧ core042_line4 BindMap ∧
  (∀ b m, List.Forall₂ (fun d' d => m d.core.name = none → d.action = .passthrough →
    d'.action = .passthrough) (BindMap b m).trans b.trans)

/-- The definition after a map form that binds a mapped name and resets an omitted transition
that carried another action to the fixed action 0. -/
def core042_resetOther (m : String → Option (Act Nat)) (d : TransDef N Nat) : TransDef N Nat :=
  match m d.core.name, d.action with
  | some x, _ => { d with action := x }
  | none, .passthrough => d
  | none, .other _ => { d with action := .other 0 }

/-- A map form that resets an omitted transition's action to the fixed action 0. -/
def core042_resetOtherBind : BuiltNet N Nat → (String → Option (Act Nat)) → BuiltNet N Nat :=
  core042_mapBind core042_resetOther

/-- The resetting map form keeps every non-action field. -/
theorem core042_resetOther_fields (m : String → Option (Act Nat)) (d : TransDef N Nat) :
    (core042_resetOther m d).core = d.core ∧ (core042_resetOther m d).out = d.out ∧
      (core042_resetOther m d).timing = d.timing ∧
      (core042_resetOther m d).priority = d.priority := by
  unfold core042_resetOther
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

end MutantAc4Only

/-- The resetting map form kills the mutant: it binds every mapped name and leaves an omitted
passthrough transition with passthrough, so it meets AC4, but mapping nothing on the example's
bound net turns `a`'s action 1 into action 0, which is neither passthrough nor action 1
(line 5). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_ac4Only_killed :
    CORE_042_mutant_ac4Only (refBind (N := Nat) (A := Nat)) core042_resetOtherBind ∧
      ¬ CORE_042 (refBind (N := Nat) (A := Nat)) core042_resetOtherBind := by
  refine ⟨⟨core042_line1_of (fun r d => d.bindWith r) core042_resetOther
      core042_ref_fields core042_resetOther_fields,
    core042_ref_line23.1, core042_ref_line23.2,
    fun b m => core042_forall₂_map fun d _ x h => ?_,
    fun b m => core042_forall₂_map fun d _ h hp => ?_⟩, fun h => ?_⟩
  · show (core042_resetOther m d).action = x
    unfold core042_resetOther
    rw [h]
  · show (core042_resetOther m d).action = _
    unfold core042_resetOther
    rw [h, hp]
    exact hp
  · rcases h.2.2.2.2 with h5 | h5
    · obtain ⟨d₀, l₀, he, hr⟩ :=
        core042_head (h5 (refBind core042_ex core042_map) (fun _ => none))
      have h2 := congrArg (·.head?.map (·.action)) he
      simp only [core042_resetOtherBind, core042_mapBind, refBind, core042_ex, List.map_cons,
        List.head?_cons, Option.map_some] at h2
      rw [hr rfl] at h2
      exact absurd h2 (by decide)
    · obtain ⟨d₀, l₀, he, hr⟩ :=
        core042_head (h5 (refBind core042_ex core042_map) (fun _ => none))
      have h2 := congrArg (·.head?.map (·.action)) he
      simp only [core042_resetOtherBind, core042_mapBind, refBind, core042_ex, List.map_cons,
        List.head?_cons, Option.map_some] at h2
      rw [hr rfl] at h2
      exact absurd h2 (by decide)

/-! ### Mutant: line 5 read per transition -/

section MutantPerTransition

variable {N A : Type}

/-- Mutant reading of line 5 (per transition): each omitted transition carries passthrough or
the action it carried, and the choice may differ from one transition, net or mapping to the
next. Lines 1 to 4 are as in CORE-042. -/
def CORE_042_mutant_perTransition
    (Bind BindMap : BuiltNet N A → (String → Option (Act A)) → BuiltNet N A) : Prop :=
  core042_line1 Bind BindMap ∧ core042_line2 Bind ∧ core042_line3 Bind ∧ core042_line4 BindMap ∧
  (∀ b m, List.Forall₂ (fun d' d => m d.core.name = none →
    d'.action = .passthrough ∨ d'.action = d.action) (BindMap b m).trans b.trans)

/-- The definition after a map form that binds a mapped name, keeps an omitted transition that
carries action 2 and gives every other omitted transition passthrough. -/
def core042_mixed (m : String → Option (Act Nat)) (d : TransDef N Nat) : TransDef N Nat :=
  match m d.core.name with
  | some x => { d with action := x }
  | none => if d.action = .other 2 then d else { d with action := .passthrough }

/-- A map form that keeps some omitted transitions and clobbers others. -/
def core042_mixedBind : BuiltNet N Nat → (String → Option (Act Nat)) → BuiltNet N Nat :=
  core042_mapBind core042_mixed

/-- The mixed map form keeps every non-action field. -/
theorem core042_mixed_fields (m : String → Option (Act Nat)) (d : TransDef N Nat) :
    (core042_mixed m d).core = d.core ∧ (core042_mixed m d).out = d.out ∧
      (core042_mixed m d).timing = d.timing ∧ (core042_mixed m d).priority = d.priority := by
  unfold core042_mixed
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

end MutantPerTransition

/-- The mixed map form kills the mutant: it binds every mapped name and gives every omitted
transition passthrough or its action, so it meets the per-transition reading, but mapping
nothing on the example's bound net clobbers `a` (action 1 becomes passthrough) and keeps `b`
(action 2), so neither uniform reading holds (line 5). -/
@[evidence mutant CORE_042]
theorem CORE_042_mutant_perTransition_killed :
    CORE_042_mutant_perTransition (refBind (N := Nat) (A := Nat)) core042_mixedBind ∧
      ¬ CORE_042 (refBind (N := Nat) (A := Nat)) core042_mixedBind := by
  refine ⟨⟨core042_line1_of (fun r d => d.bindWith r) core042_mixed
      core042_ref_fields core042_mixed_fields,
    core042_ref_line23.1, core042_ref_line23.2,
    fun b m => core042_forall₂_map fun d _ x h => ?_,
    fun b m => core042_forall₂_map fun d _ h => ?_⟩, fun h => ?_⟩
  · show (core042_mixed m d).action = x
    unfold core042_mixed
    rw [h]
  · show (core042_mixed m d).action = _ ∨ (core042_mixed m d).action = _
    by_cases hd : d.action = .other 2
    · exact Or.inr (by simp [core042_mixed, h, hd])
    · exact Or.inl (by simp [core042_mixed, h, hd])
  · rcases h.2.2.2.2 with h5 | h5
    · obtain ⟨d₀, d₁, l₀, he, hr⟩ :=
        core042_second (h5 (refBind core042_ex core042_map) (fun _ => none))
      have h2 := congrArg (fun l : List (TransDef Nat Nat) => (l.drop 1).head?.map (·.action)) he
      simp only [core042_mixedBind, core042_mapBind, refBind, core042_ex, List.map_cons,
        List.drop_succ_cons, List.drop_zero, List.head?_cons, Option.map_some] at h2
      rw [hr rfl] at h2
      exact absurd h2 (by decide)
    · obtain ⟨d₀, l₀, he, hr⟩ :=
        core042_head (h5 (refBind core042_ex core042_map) (fun _ => none))
      have h2 := congrArg (·.head?.map (·.action)) he
      simp only [core042_mixedBind, core042_mapBind, refBind, core042_ex, List.map_cons,
        List.head?_cons, Option.map_some] at h2
      rw [hr rfl] at h2
      exact absurd h2 (by decide)

end Libpetri.Spec
