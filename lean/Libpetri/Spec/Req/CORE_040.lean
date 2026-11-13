import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Text.CORE_040

set_option linter.missingDocs true

/-!
# CORE-040: Net builder (`spec/01-core-model.md`)

CORE-040 is a pure-function requirement (kind F) over an abstract net builder
`NB : NetBuilder B` (`Reference/Build.lean`): from what the host added (`NetIn B`: declared
places, the instances of transition builder `B` it added in the order added, and the declared
terminal places of [EXEC-042]) the builder returns a built net (`BuiltNet`) or a rejection. The
statement says which transitions and which places the built net holds, and when building
succeeds. It says nothing about what the handle shows after later calls (CORE-041), about binding
(CORE-042) or about the compile check (CORE-043).

The witness is the reference net builder `refNetBuild`. Wrong builders are killed, one per
load-bearing line: one that reverses the transitions (line 1), one that collects only input and
output places, as before ruling D32 (line 2), one that drops a declared place no arc names
(line 2), one that misreads a ForwardInput or a Timeout in the output specification (line 2), one
that sorts the transitions by priority (line 1), one that keeps a place twice (line 3), one that
adds a place nobody declared or named (line 3), and one that rejects an empty net (line 4). The
net's terminal places, and which nets with terminal places build, are EXEC-042's build block
(`EXEC_042_build`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-040: Net Builder -/

requirement CORE_040
  id "CORE-040"
  title "Net Builder"
  kind F
  scope "all net builders used without composition or fusion sets"
  source verbatim "spec/01-core-model.md"
  covers CORE_040.s1, CORE_040.s2, CORE_040.s3, CORE_040.s4, CORE_040.s5, CORE_040.s6
  reading "For every transition builder B and every net builder NB over B's instances:"
          "if NB returns the net b for the input inp and the added transitions of inp have pairwise distinct names, the transitions of b are the definitions of the added transitions, in the order added;"
          "if NB returns b for inp, every declared place of inp, every declared terminal place of inp and every place an added transition has an arc on (an arc place: input, read, inhibitor or reset) or holds in the allPlaces set of its output specification (an output arc, IO-017) is a place of b;"
          "if NB returns b for inp, every place of b is a declared place, a declared terminal place or a place an added transition has an arc on or holds in the allPlaces set of its output specification, and no place of b appears twice;"
          "for every input inp that declares no terminal place, NB returns a net."
  assumes "A net builder (NetBuilder B) is the build call of one implementation's net builder, read as a function from what the host added (NetIn B: the declared places in the order declared, the added transitions in the order added, as instances of the transition builder B, and the declared terminal places) to a built net (BuiltNet: its places, its transitions' definitions, its terminal places) or a rejection with a message (a panic or an exception, read as `.error msg`). A net holds only what a transition builder returned (BuiltNet.FromBuilder; the W2 tracer decision), so the added transitions are instances of B, not bare definitions. Places are the abstract place type N, identity = equality on N; how a host place object maps to N (by name in TypeScript, Rust and Python, by name and token type in Java) is CORE-002's (PlaceKeyed)."
          "Scope. The block concerns a builder used without composition (MOD-020 instance composition, MOD-025 direct composition, and MOD-027's rejection of an arc on a port place that instance composition bound) and without fusion sets (MOD-060, MOD-061), as its first quoted sentence says. Fusion rewrites the arcs of every transition (rewriter::apply_fusion, called from build_with_fusion in rust/libpetri-core/src/petri_net.rs), which breaks line 1, and removes non-canonical members from the place set (build_with_fusion, its step 4), which breaks line 2; build panics or throws on fusion overlap (build_with_fusion) and on an arc naming a port place that instance composition bound (MOD-027, reject_bound_port_references) with no terminal place declared, which breaks line 4 (Java: java/src/main/java/org/libpetri/core/PetriNet.java, Builder.build, which throws from buildWithFusion and rejectRetired). What a composed or fused net holds is the composition model's (W8), stated over the same net builder extended. Rust's second public constructor PetriNet::map_transitions (rust/libpetri-core/src/petri_net.rs) is not a net builder: its documented, unchecked precondition is that the mapping introduces no place the net does not already declare, so a net it returns meets line 2 only when the caller keeps that precondition."
          "Line 1 is the declaration order of ruling D32 (a): the order the transitions were added is the net's transition order, which EXEC-002 (FIFO among equal priorities) and CORE-037 (the order of the dead-arc report) read. Its premise is the shared unique-names assumption of rulings D10 and D23 (a) (spec/03-timing.md, TIME-010: the transitions of one net have pairwise distinct names), on the added transitions, read over the list of additions (the quoted 'each added once'), so one transition instance added twice has its name twice and is outside the premise; no builder checks it. Outside it the runtimes differ: given one transition instance twice, Java and TypeScript hold it once (a set) and Rust twice (a Vec, a clone keeps its identity) (clash core-b#5, the transitions field of PetriNet in rust/libpetri-core/src/petri_net.rs, the derived Clone of Transition in rust/libpetri-core/src/transition.rs). A builder that reverses the transitions (core040_reverseNB) violates line 1 and meets the order-free reading (CORE_040_mutant_orderFree)."
          "Line 2 is AC3 made a MUST by ruling D32 (a): the places of every arc of all five kinds are collected, the arc places of the glossary (input, read, inhibitor, reset; ArcPlace in Spec/GlossaryTime.lean) and every place of the output specification (OutputArc; IO-017's AllPlaces, so the target of a ForwardInput and every place of a Timeout child count). All three runtimes do so (PetriNetBuilder::transition in rust/libpetri-core/src/petri_net.rs, PetriNet.Builder.transition in java/src/main/java/org/libpetri/core/PetriNet.java, PetriNetBuilder.transition in typescript/src/core/petri-net.ts). A declared terminal place is declared as a place too in all three (PetriNetBuilder::terminal in rust/libpetri-core/src/petri_net.rs, PetriNet.Builder.terminal in java/src/main/java/org/libpetri/core/PetriNet.java, PetriNetBuilder.terminal in typescript/src/core/petri-net.ts). A builder that collects only input and output places (core040_inOutOnlyNB, the pre-D32 reading, CORE_040_mutant_inOutOnly) or drops a declared place no arc names (core040_dropDeclaredNB, CORE_040_mutant_arcPlacesOnly) violates line 2, and so does one that collects the source of a ForwardInput instead of its target and nothing from a Timeout child (core040_outSlipNB, CORE_040_forbids_outSlip: place 5 of the example is the target of a ForwardInput inside a Timeout). The quoted sentence collects the allPlaces set of IO-017, which holds a ForwardInput's target only; its source is collected all the same, as an input place: the transition builder rejects a forward from a place that is not an input of the transition (IO-014 AC3, Spec/Glossary.lean WellFormedOut), and the added transitions are its outputs. Line 2 is what discharges the hypothesis hDecl (Novel.Seam.ArcsDeclared) of the postfix soundness theorems for every builder that meets CORE-040 (core040_arcsDeclared), not only for the reference (refNetBuild_arcsDeclared_toNNetB)."
          "Line 3: the net holds no place other than those of line 2 and no place twice, both on N. Ruling D66 (a) keeps 'no place twice' a MUST, and every runtime meets it under its own identity (CORE-002): Rust and Java keep the places in a set under their place equality, and TypeScript, where place(name) returns a fresh object each call (typescript/src/core/place.ts), keeps the builder's places in a Map from name to place, so two place objects named 'A' give PetriNet.places one entry, the first object added (PetriNetBuilder._places and addPlace, typescript/src/core/petri-net.ts), as the compiled net keys places by name (typescript/src/runtime/compiled-net.ts). A builder that keeps two place objects of one name, as a place set keyed by object reference does (the behaviour RD-03 in spec/runtime-defects.md recorded of TypeScript's builder), holds a place twice under name identity (N := String) and violates line 3. A builder that keeps a place twice (core040_noDedupNB, CORE_040_mutant_dupsAllowed) or adds a place nobody declared or named (core040_extraNB, CORE_040_mutant_extraAllowed) violates line 3. The order of the places is not stated: ruling D32 orders transitions only, and the reference keeps the last occurrence of a place where the runtimes keep the first."
          "Line 4: the net builder rejects nothing of its own. Its one rejection in scope is EXEC-042 AC5 (a declared terminal place that an added transition consumes from or reads, NetIn.TerminalClash); on an input with no terminal place it cannot arise. Over an input with terminal places, EXEC-042's build block (EXEC_042_build, kind F, over every abstract net builder, not over the reference only) says both directions: its line 1 rejects a clash, its line 2 builds every input without one, so a builder that also rejects a terminal place on an inhibitor or reset arc violates EXEC_042_build line 2 on exec042_netInh (as EXEC_042_build_mutant_rejectAll_killed shows for the builder that rejects every terminal place). EXEC_042_build's own scope note reads its line 2, with no terminal place declared, as this line 4. A transition definition the transition builder rejects never reaches the net builder: the added transitions are instances, and CORE-020 says which inputs build. Without line 4 a builder that rejects everything meets lines 1 to 3 vacuously; one that rejects an empty net (core040_rejectEmptyNB, CORE_040_mutant_noAccept) violates it. Only success and failure are stated, not a message."
          "Terminal places of the built net (BuiltNet.terminals). None of CORE-040's four lines reads them; a declared terminal place enters the net as a place by line 2. That the built net's terminal places are exactly the declared ones is EXEC_042_build line 3, over every abstract net builder; a builder that drops them (exec042_dropTerminalsNB, the TypeScript EMPTY_TERMINALS choice in PetriNetBuilder.build (typescript/src/core/petri-net.ts) made unconditionally) violates it (EXEC_042_build_forbids_dropTerminals). How often a terminal place is listed is stated nowhere: EXEC_042_build line 3 reads the terminal places as a set, all three runtimes keep each once (PetriNetBuilder::terminal in rust/libpetri-core/src/petri_net.rs, Java's LinkedHashSet, TypeScript's Map by name) and the reference keeps them once each in declaration order (refNetBuild_terminals); no requirement reads the multiplicity."
          "AC1 (the builder can add places and transitions) is lines 1, 2 and 4 together: a declared place and an added transition are in the net, and building succeeds (CORE_040_nonvacuous). The builder pattern as an API shape is a Q-kind test (ruling D99 (a))."
          "AC2 (build produces an immutable net) is CORE-041's subject: here a built net is a value (BuiltNet), and that a handle on it shows the same net after later builder calls is CORE-041's line over BuilderApi, whose builder trace (copyBuilder_trace) shows refNetBuild's net. A builder that hands out its live sets (aliasBuilder, the behaviour RD-02 recorded of TypeScript's builder) violates CORE-041's line (ruling D66 (a)); no runtime's built net shares its place or transition set with the builder."
          "AC3 (places referenced by transitions are auto-collected) is line 2; its parenthesis ('implementations that auto-collect from arcs SHOULD do so') is replaced by the MUST of ruling D32 (a). The test derivation (build a net with transitions and verify all places from arcs are present) is line 2 on CORE_040_nonvacuous's example, whose transitions have arcs of all five kinds, with an output specification of every node kind but Xor: Place, And, Timeout and a ForwardInput inside the Timeout (a bare ForwardInput does not build, IO-014). The example's second transition has priority 5 and the first priority 0, so the order added (line 1) is not the priority order: a builder that sorts the transitions by priority (core040_prioSortNB, CORE_040_forbids_prioSort) violates line 1 on it."
  signoff "2026-11-13 306502b72cef9ade ai"
  statement : ∀ {N A : Type} [DecidableEq N] (B : TBuilder N A), NetBuilder B → Prop :=
    fun B NB =>
      (∀ inp b, NB inp = .ok b → (inp.trans.map fun x => (B.defOf x).core.name).Nodup →
        b.trans = inp.trans.map B.defOf) ∧
      (∀ inp b, NB inp = .ok b → ∀ p,
        (p ∈ inp.places ∨ p ∈ inp.terminals ∨
          ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p) →
        p ∈ b.places) ∧
      (∀ inp b, NB inp = .ok b →
        (∀ p ∈ b.places, p ∈ inp.places ∨ p ∈ inp.terminals ∨
          ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p) ∧
        b.places.Nodup) ∧
      (∀ inp : NetIn B, inp.terminals = [] → ∃ b, NB inp = .ok b)

/- The pinned readable form of CORE-040: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_040 : {N A : Type} → [DecidableEq N] → (B : TBuilder N A) → NetBuilder B → Prop :=
fun {N A} [DecidableEq N] B NB =>
  (∀ (inp : NetIn B) (b : BuiltNet N A),
      NB inp = Except.ok b →
        (List.map (fun x => (B.defOf x).core.name) inp.trans).Nodup → b.trans = List.map B.defOf inp.trans) ∧
    (∀ (inp : NetIn B) (b : BuiltNet N A),
        NB inp = Except.ok b →
          ∀ (p : N),
            (p ∈ inp.places ∨
                p ∈ inp.terminals ∨ ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p) →
              p ∈ b.places) ∧
      (∀ (inp : NetIn B) (b : BuiltNet N A),
          NB inp = Except.ok b →
            (∀ p ∈ b.places,
                p ∈ inp.places ∨
                  p ∈ inp.terminals ∨
                    ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p) ∧
              b.places.Nodup) ∧
        ∀ (inp : NetIn B), inp.terminals = [] → ∃ b, NB inp = Except.ok b
-/
#guard_msgs in #print CORE_040

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type} [DecidableEq N]

/-- A place the net builder must collect from an input: a declared place, a declared terminal
place, or a place an added transition has an arc on or names in its output specification. -/
def core040Coll (B : TBuilder N A) (inp : NetIn B) (p : N) : Prop :=
  p ∈ inp.places ∨ p ∈ inp.terminals ∨
    ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p

/-- Line 1 of CORE-040. -/
def core040_line1 (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  ∀ inp b, NB inp = .ok b → (inp.trans.map fun x => (B.defOf x).core.name).Nodup →
    b.trans = inp.trans.map B.defOf

/-- Line 2 of CORE-040. -/
def core040_line2 (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  ∀ inp b, NB inp = .ok b → ∀ p, core040Coll B inp p → p ∈ b.places

/-- Line 3 of CORE-040. -/
def core040_line3 (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  ∀ inp b, NB inp = .ok b → (∀ p ∈ b.places, core040Coll B inp p) ∧ b.places.Nodup

/-- Line 4 of CORE-040. -/
def core040_line4 (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  ∀ inp : NetIn B, inp.terminals = [] → ∃ b, NB inp = .ok b

/-- CORE-040 is its four lines. -/
theorem core040_iff (B : TBuilder N A) (NB : NetBuilder B) :
    CORE_040 B NB ↔
      core040_line1 B NB ∧ core040_line2 B NB ∧ core040_line3 B NB ∧ core040_line4 B NB :=
  Iff.rfl

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N] {B : TBuilder N A}

omit [DecidableEq N] in
/-- The places a definition names are its arc places (the glossary's Arc place: input, read,
inhibitor, reset) and the places of its output specification (Output arc). -/
theorem core040_named_iff {d : TransDef N A} {p : N} :
    p ∈ d.namedPlaces ↔ ArcPlace d.toTrans p ∨ OutputArc d.toTrans p := by
  rw [mem_namedPlaces]
  unfold ArcPlace
  constructor
  · rintro (h | h | h | h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inr (.inl h)))
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr (.inr h)))
    · exact .inr h
  · rintro ((h | h | h | h) | h)
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))

/-- The places the reference collects are exactly the places CORE-040 says a net must collect. -/
theorem core040_coll_iff {inp : NetIn B} {p : N} :
    core040Coll B inp p ↔ p ∈ inp.collect.places := by
  rw [mem_collect_places]
  unfold core040Coll
  simp only [core040_named_iff]

omit [DecidableEq N] in
/-- With no terminal place declared no terminal place clashes. -/
theorem core040_noClash {inp : NetIn B} (h : inp.terminals = []) : ¬ inp.TerminalClash :=
  fun ⟨p, hp, _⟩ => by rw [h] at hp; cases hp

/-- ✓ The reference net builder satisfies CORE-040, over every transition builder: it keeps the
added transitions' definitions in the order added (with or without distinct names), collects
exactly the declared places, the terminal places and the places the added transitions name, drops
duplicates, and rejects only a terminal place that an added transition consumes from or reads,
which needs a terminal place. -/
@[evidence holds CORE_040]
theorem CORE_040_reference {N A : Type} [DecidableEq N] (B : TBuilder N A) :
    CORE_040 B refNetBuild := by
  refine ⟨fun inp b h _ => refNetBuild_trans h, fun inp b h p hp => ?_,
    fun inp b h => ⟨fun p hp => ?_, refNetBuild_places_nodup h⟩,
    fun inp ht => ⟨_, refNetBuild_of_terminals_nil ht⟩⟩
  · rw [(refNetBuild_eq_ok_iff.1 h).2]
    exact core040_coll_iff.1 hp
  · rw [(refNetBuild_eq_ok_iff.1 h).2] at hp
    exact core040_coll_iff.2 hp

end Reference

/-! ### A consequence: every builder meeting CORE-040 declares its arcs -/

/-- Under the unique-names premise of line 1, every net a builder meeting CORE-040 returns declares
every arc in its branch-expanded view: the hypothesis `hDecl` (`ArcsDeclared`) of
`postfix_proven_sound`, `postfix_deadlock_sound` and `phase_postfix_deadlock_sound` holds of it.
This is `refNetBuild_arcsDeclared_toNNetB` stated from the requirement, not from the reference. -/
theorem core040_arcsDeclared {N A : Type} [DecidableEq N] {B : TBuilder N A} {NB : NetBuilder B}
    (h : CORE_040 B NB) {inp : NetIn B} {b : BuiltNet N A} (hb : NB inp = .ok b)
    (hn : (inp.trans.map fun x => (B.defOf x).core.name).Nodup) : ArcsDeclared b.toNNetB := by
  intro ft hft n hn'
  have ht := h.1 inp b hb hn
  simp only [BuiltNet.toNNetB, List.mem_flatMap] at hft
  obtain ⟨d, hd, hft⟩ := hft
  rw [ht, List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  show n ∈ b.places
  refine h.2.1 inp b hb n (.inr (.inr ⟨x, hx, core040_named_iff.1 ?_⟩))
  unfold TransDef.namedPlaces
  cases ho : (B.defOf x).out with
  | none =>
    rw [ho] at hft
    rw [List.mem_singleton.1 hft] at hn'
    unfold arcNames at hn'
    simpa using hn'
  | some o =>
    rw [ho] at hft
    obtain ⟨br, hbr, rfl⟩ := List.mem_map.1 hft
    unfold arcNames at hn'
    simp only [List.mem_append] at hn' ⊢
    rcases hn' with (((h1 | h1) | h1) | h1) | h1
    · exact .inl (.inl (.inl (.inl h1)))
    · exact .inl (.inl (.inl (.inr h1)))
    · exact .inl (.inl (.inr h1))
    · exact .inl (.inr h1)
    · exact .inr (by simpa using outPlaces_of_branch o br hbr n h1)

/-! ### Example -/

/-- The first example input: an input arc on place 0, an inhibitor arc on place 1, output
`Place 2`. -/
def core040_in1 : TransIn Nat Unit :=
  { core := { name := "t1", inputs := [⟨0, .one⟩], inhibitors := [1], reads := [], resets := [] },
    out := some (.place 2) }

/-- The second example input: an input arc on place 2, a read arc on place 3, a reset arc on
place 4, output `And(Place 0, Timeout(ForwardInput(2 → 5)))`, priority 5 (higher than t1's
default 0). -/
def core040_in2 : TransIn Nat Unit :=
  { core := { name := "t2", inputs := [⟨2, .one⟩], inhibitors := [], reads := [3], resets := [4] },
    out := some (.and (.place 0) (.timeout (.forward 2 5))), priority := some 5 }

/-- The reference transition builder's first instance: call 0 on the first input. -/
def core040_x1 : (refTransBuild (N := Nat) (A := Unit)).I :=
  ⟨(0, core040_in1.resolve), 0, core040_in1,
    refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide),
      ⟨fun _ h => by simp [core040_in1] at h, rfl⟩⟩⟩

/-- The reference transition builder's second instance: call 1 on the second input. -/
def core040_x2 : (refTransBuild (N := Nat) (A := Unit)).I :=
  ⟨(1, core040_in2.resolve), 1, core040_in2,
    refTransBuildRaw_ok.2 ⟨(refBuild_eq_none_iff _).1 (by decide),
      ⟨fun _ h => by simp [core040_in2] at h, rfl⟩⟩⟩

/-- The example net input: declared places 9 (no arc names it) and 0 (also an arc place), the two
transitions in the order t1, t2, no terminal place. -/
def core040_ex : NetIn (refTransBuild (N := Nat) (A := Unit)) :=
  ⟨[9, 0], [core040_x1, core040_x2], []⟩

/-- The example's transitions have distinct names (line 1's premise). -/
theorem core040_ex_names :
    (core040_ex.trans.map fun x => ((refTransBuild (N := Nat) (A := Unit)).defOf x).core.name).Nodup := by
  decide

/-- ✓ Every line of CORE-040 is exercised by the reference: the example builds (line 4), its net
holds t1 then t2, the order added and not the priority order (priorities 0 then 5; line 1), the
declared place 9 that no arc names, the input places 0 and 2, the inhibitor place 1, the read
place 3, the reset place 4 and the place 5 that only a ForwardInput inside a Timeout names (line
2, all five arc kinds, AC3 and the test derivation), nothing else and place 0, declared and
arc-named, once (line 3). -/
@[evidence nonvacuous CORE_040]
theorem CORE_040_nonvacuous :
    ∃ b, refNetBuild core040_ex = .ok b ∧
      b.trans.map (·.core.name) = ["t1", "t2"] ∧ b.trans.map (·.priority) = [0, 5] ∧
      b.places.Perm [9, 0, 1, 2, 3, 4, 5] ∧ b.places.Nodup := by
  refine ⟨_, refNetBuild_of_terminals_nil rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Wrong builders -/

section Wrong

variable {N A : Type} [DecidableEq N] {B : TBuilder N A}

/-- A net builder that runs the reference and then changes the net it returns with `f`. -/
def core040_post (f : NetIn B → BuiltNet N A → BuiltNet N A) : NetBuilder B :=
  fun inp => (refNetBuild inp).map (f inp)

/-- A post-processing builder returns `b` exactly when no terminal place clashes and `b` is `f`
of the collected net. -/
theorem core040_post_ok {f : NetIn B → BuiltNet N A → BuiltNet N A} {inp : NetIn B}
    {b : BuiltNet N A} :
    core040_post f inp = .ok b ↔ ¬ inp.TerminalClash ∧ b = f inp inp.collect := by
  unfold core040_post
  by_cases hc : inp.TerminalClash
  · obtain ⟨e, he⟩ := refNetBuild_error_iff.2 hc
    rw [he]
    exact ⟨(fun c => by simp [Except.map] at c), fun ⟨hn, _⟩ => absurd hc hn⟩
  · rw [refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩]
    exact ⟨fun c => ⟨hc, (Except.ok.inj c).symm⟩, fun ⟨_, e⟩ => e ▸ rfl⟩

/-- A post-processing builder accepts every input with no terminal place. -/
theorem core040_post_line4 (f : NetIn B → BuiltNet N A → BuiltNet N A) :
    core040_line4 B (core040_post f) :=
  fun _ ht => ⟨_, core040_post_ok.2 ⟨core040_noClash ht, rfl⟩⟩

/-- A builder that holds the added transitions in reverse order. -/
def core040_reverseNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun _ b => { b with trans := b.trans.reverse }

/-- A builder that collects only the declared places, the terminal places and the input and
output places of the added transitions (no inhibitor, read or reset place): auto-collection
before ruling D32. -/
def core040_inOutOnlyNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun inp b => { b with places :=
    (inp.places ++ inp.terminals ++ (inp.trans.map B.defOf).flatMap fun d =>
      inPlaces d.toTrans ++ (d.out.map outPlaces).getD []).dedup }

/-- A builder that drops a declared place no arc names: it collects only the terminal places and
the places the added transitions name. -/
def core040_dropDeclaredNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun inp b => { b with places :=
    (inp.terminals ++ (inp.trans.map B.defOf).flatMap TransDef.namedPlaces).dedup }

/-- A builder that keeps the places it collects as a list with duplicates: a place declared and
also named by an arc is held twice (under name identity, a place set keyed by object reference, the
behaviour RD-03 recorded of TypeScript's `PetriNet.places`; ruling D66 (a)). -/
def core040_noDedupNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun inp b => { b with places :=
    inp.places ++ inp.terminals ++ (inp.trans.map B.defOf).flatMap TransDef.namedPlaces }

/-- A builder that adds the place `q` to every net (an implicit start or sink place), once. -/
def core040_extraNB (B : TBuilder N A) (q : N) : NetBuilder B :=
  core040_post fun _ b => { b with places := if q ∈ b.places then b.places else b.places ++ [q] }

/-- Stable sort by priority, highest first (the precompiled executors' priority partition, applied
at build). -/
def core040_sortByPrio : List (TransDef N A) → List (TransDef N A)
  | [] => []
  | d :: ds => core040_insPrio d (core040_sortByPrio ds)
where
  /-- Insert `d` ahead of the sorted tail, first among equal priorities. -/
  core040_insPrio (d : TransDef N A) : List (TransDef N A) → List (TransDef N A)
    | [] => [d]
    | e :: es => if d.priority < e.priority then e :: core040_insPrio d es else d :: e :: es

/-- A builder that holds the added transitions sorted by priority, highest first. -/
def core040_prioSortNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun _ b => { b with trans := core040_sortByPrio b.trans }

/-- An output collector with two slips: a `ForwardInput` gives its source, not its target, and a
`Timeout` gives nothing. -/
def core040_slipOutPlaces : Out N → List N
  | .place p => [p]
  | .forward src _ => [src]
  | .and l r => core040_slipOutPlaces l ++ core040_slipOutPlaces r
  | .xor l r => core040_slipOutPlaces l ++ core040_slipOutPlaces r
  | .timeout _ => []

/-- A builder that collects the output places with the slipped collector (the arc places and the
declared places correctly). -/
def core040_outSlipNB (B : TBuilder N A) : NetBuilder B :=
  core040_post fun inp b => { b with places :=
    (inp.places ++ inp.terminals ++ (inp.trans.map B.defOf).flatMap fun d =>
      d.core.inputs.map (·.place) ++ d.core.inhibitors ++ d.core.reads ++ d.core.resets ++
        (d.out.map core040_slipOutPlaces).getD []).dedup }

/-- A builder that rejects a net with no transition, and is the reference otherwise. -/
def core040_rejectEmptyNB (B : TBuilder N A) : NetBuilder B :=
  fun inp => if inp.trans.isEmpty then .error "empty net" else refNetBuild inp

end Wrong

/-! ### Mutant readings -/

section Mutants

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 1: the net holds the added transitions, in any order. Lines 2 to 4 are
as in CORE-040. -/
def CORE_040_mutant_orderFree (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  (∀ inp b, NB inp = .ok b → (inp.trans.map fun x => (B.defOf x).core.name).Nodup →
    b.trans.Perm (inp.trans.map B.defOf)) ∧
  core040_line2 B NB ∧ core040_line3 B NB ∧ core040_line4 B NB

/-- Mutant reading of line 2, auto-collection before ruling D32: every declared place, terminal
place, input place and output place is a place of the net. Lines 1, 3 and 4 are as in CORE-040. -/
def CORE_040_mutant_inOutOnly (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  core040_line1 B NB ∧
  (∀ inp b, NB inp = .ok b → ∀ p,
    (p ∈ inp.places ∨ p ∈ inp.terminals ∨
      ∃ x ∈ inp.trans, p ∈ inPlaces (B.defOf x).toTrans ∨ OutputArc (B.defOf x).toTrans p) →
    p ∈ b.places) ∧
  core040_line3 B NB ∧ core040_line4 B NB

/-- Mutant reading of line 2, auto-collection only: every terminal place and every place an
added transition names is a place of the net, a declared place need not be. Lines 1, 3 and 4 are
as in CORE-040. -/
def CORE_040_mutant_arcPlacesOnly (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  core040_line1 B NB ∧
  (∀ inp b, NB inp = .ok b → ∀ p,
    (p ∈ inp.terminals ∨
      ∃ x ∈ inp.trans, ArcPlace (B.defOf x).toTrans p ∨ OutputArc (B.defOf x).toTrans p) →
    p ∈ b.places) ∧
  core040_line3 B NB ∧ core040_line4 B NB

/-- Mutant reading of line 3 without "no place twice": the net holds no other place. Lines 1, 2
and 4 are as in CORE-040. -/
def CORE_040_mutant_dupsAllowed (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  core040_line1 B NB ∧ core040_line2 B NB ∧
  (∀ inp b, NB inp = .ok b → ∀ p ∈ b.places, core040Coll B inp p) ∧ core040_line4 B NB

/-- Mutant reading of line 3 without "no other place": the net holds no place twice. Lines 1, 2
and 4 are as in CORE-040. -/
def CORE_040_mutant_extraAllowed (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  core040_line1 B NB ∧ core040_line2 B NB ∧
  (∀ inp b, NB inp = .ok b → b.places.Nodup) ∧ core040_line4 B NB

/-- Mutant reading without line 4: what a net holds when the builder accepts, with no line on
when it accepts. -/
def CORE_040_mutant_noAccept (B : TBuilder N A) (NB : NetBuilder B) : Prop :=
  core040_line1 B NB ∧ core040_line2 B NB ∧ core040_line3 B NB

end Mutants

/-- The reference transition builder at the example's types. -/
abbrev core040_B : TBuilder Nat Unit := refTransBuild (N := Nat) (A := Unit)

/-- A place collected from the example by the reference is a place CORE-040 says the net must
collect. -/
theorem core040_ex_coll {p : Nat} (h : p ∈ core040_ex.collect.places) :
    core040Coll core040_B core040_ex p :=
  core040_coll_iff.2 h

/-- The reversing builder kills the order-free mutant: it holds the added transitions, so it
meets the order-free reading, but the example's t1, t2 come back as t2, t1 (line 1). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_orderFree_killed :
    CORE_040_mutant_orderFree core040_B (core040_reverseNB core040_B) ∧
      ¬ CORE_040 core040_B (core040_reverseNB core040_B) := by
  obtain ⟨-, h2, h3, -⟩ := CORE_040_reference core040_B
  refine ⟨⟨fun inp b hb _ => ?_, fun inp b hb => ?_, fun inp b hb => ?_,
    core040_post_line4 _⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    exact List.reverse_perm _
  · obtain ⟨hc, rfl⟩ := core040_post_ok.1 hb
    exact h2 inp inp.collect (refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩)
  · obtain ⟨hc, rfl⟩ := core040_post_ok.1 hb
    exact h3 inp inp.collect (refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩)
  · have := congrArg (List.map (·.core.name))
      (h.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩) core040_ex_names)
    exact absurd this (by decide)

/-- ✗ A builder that holds the added transitions in reverse order violates CORE-040 (line 1). -/
@[evidence forbids CORE_040]
theorem CORE_040_forbids_reverse : ¬ CORE_040 core040_B (core040_reverseNB core040_B) :=
  CORE_040_mutant_orderFree_killed.2

/-- ✗ A builder that sorts the transitions by priority violates CORE-040 (line 1): the example's
t1 (priority 0), t2 (priority 5) come back as t2, t1. -/
@[evidence forbids CORE_040]
theorem CORE_040_forbids_prioSort : ¬ CORE_040 core040_B (core040_prioSortNB core040_B) := by
  intro h
  have := congrArg (List.map (·.core.name))
    (h.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩) core040_ex_names)
  exact absurd this (by decide)

/-- The input-and-output-only builder kills the pre-D32 mutant: it collects the declared,
terminal, input and output places, so it meets that reading, but the example's inhibitor place 1
is not a place of its net (line 2). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_inOutOnly_killed :
    CORE_040_mutant_inOutOnly core040_B (core040_inOutOnlyNB core040_B) ∧
      ¬ CORE_040 core040_B (core040_inOutOnlyNB core040_B) := by
  refine ⟨⟨fun inp b hb _ => ?_, fun inp b hb p hp => ?_, fun inp b hb => ?_,
    core040_post_line4 _⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb; rfl
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]
    rcases hp with h1 | h1 | ⟨x, hx, h1 | ⟨o, ho, h1⟩⟩
    · exact .inl (.inl h1)
    · exact .inl (.inr h1)
    · exact .inr ⟨_, ⟨x, hx, rfl⟩, .inl h1⟩
    · have ho' : (core040_B.defOf x).out = some o := ho
      exact .inr ⟨_, ⟨x, hx, rfl⟩, .inr (by rw [ho']; exact h1)⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    refine ⟨fun p hp => ?_, List.nodup_dedup _⟩
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map] at hp
    rcases hp with (h1 | h1) | ⟨_, ⟨x, hx, rfl⟩, h1 | h1⟩
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr ⟨x, hx, .inl (.inl h1)⟩)
    · refine .inr (.inr ⟨x, hx, .inr ?_⟩)
      cases ho : (core040_B.defOf x).out with
      | none => rw [ho] at h1; cases h1
      | some o => rw [ho] at h1; exact ⟨o, ho, h1⟩
  · have := h.2.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩) 1
      (core040_ex_coll (by decide))
    exact absurd this (by decide)

/-- ✗ A builder that collects only input and output places violates CORE-040 (line 2): the
inhibitor place 1 is missing. -/
@[evidence forbids CORE_040]
theorem CORE_040_forbids_inOutOnly : ¬ CORE_040 core040_B (core040_inOutOnlyNB core040_B) :=
  CORE_040_mutant_inOutOnly_killed.2

/-- The declared-place-dropping builder kills the arc-places-only mutant: it collects every
terminal place and every place an added transition names, so it meets that reading, but the
example's declared place 9, which no arc names, is not a place of its net (line 2). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_arcPlacesOnly_killed :
    CORE_040_mutant_arcPlacesOnly core040_B (core040_dropDeclaredNB core040_B) ∧
      ¬ CORE_040 core040_B (core040_dropDeclaredNB core040_B) := by
  refine ⟨⟨fun inp b hb _ => ?_, fun inp b hb p hp => ?_, fun inp b hb => ?_,
    core040_post_line4 _⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb; rfl
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]
    rcases hp with h1 | ⟨x, hx, h1⟩
    · exact .inl h1
    · exact .inr ⟨_, ⟨x, hx, rfl⟩, core040_named_iff.2 h1⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    refine ⟨fun p hp => ?_, List.nodup_dedup _⟩
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map] at hp
    rcases hp with h1 | ⟨_, ⟨x, hx, rfl⟩, h1⟩
    · exact .inr (.inl h1)
    · exact .inr (.inr ⟨x, hx, core040_named_iff.1 h1⟩)
  · have := h.2.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩) 9
      (.inl (by decide))
    exact absurd this (by decide)

/-- ✗ A builder that drops a declared place no arc names violates CORE-040 (line 2): the
declared place 9 is missing. -/
@[evidence forbids CORE_040]
theorem CORE_040_forbids_dropDeclared :
    ¬ CORE_040 core040_B (core040_dropDeclaredNB core040_B) :=
  CORE_040_mutant_arcPlacesOnly_killed.2

/-- ✗ A builder whose output collector gives a ForwardInput's source and nothing of a Timeout
violates CORE-040 (line 2, IO-017): the example's place 5, the target of the ForwardInput inside
t2's Timeout, is missing. -/
@[evidence forbids CORE_040]
theorem CORE_040_forbids_outSlip : ¬ CORE_040 core040_B (core040_outSlipNB core040_B) := by
  intro h
  have := h.2.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩) 5
    (core040_ex_coll (by decide))
  exact absurd this (by decide)

/-- The duplicating builder kills the duplicates-allowed mutant: it holds every place it must and
no other, so it meets that reading, but the example's place 0, declared and named by an arc, is
held twice (line 3). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_dupsAllowed_killed :
    CORE_040_mutant_dupsAllowed core040_B (core040_noDedupNB core040_B) ∧
      ¬ CORE_040 core040_B (core040_noDedupNB core040_B) := by
  refine ⟨⟨fun inp b hb _ => ?_, fun inp b hb p hp => ?_, fun inp b hb p hp => ?_,
    core040_post_line4 _⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb; rfl
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    have := core040_coll_iff.1 hp
    simpa [NetIn.collect] using this
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    exact core040_coll_iff.2 (by simpa [NetIn.collect] using hp)
  · have := (h.2.2.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩)).2
    exact absurd this (by decide)

/-- The place-adding builder kills the extra-allowed mutant: it holds every place it must and
none twice, so it meets that reading, but the example's net holds place 99, which nobody declared
or named (line 3). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_extraAllowed_killed :
    CORE_040_mutant_extraAllowed core040_B (core040_extraNB core040_B 99) ∧
      ¬ CORE_040 core040_B (core040_extraNB core040_B 99) := by
  refine ⟨⟨fun inp b hb _ => ?_, fun inp b hb p hp => ?_, fun inp b hb => ?_,
    core040_post_line4 _⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb; rfl
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    have := core040_coll_iff.1 hp
    show p ∈ (if 99 ∈ inp.collect.places then inp.collect.places
      else inp.collect.places ++ [99])
    split
    · exact this
    · exact List.mem_append_left _ this
  · obtain ⟨-, rfl⟩ := core040_post_ok.1 hb
    show List.Nodup (if 99 ∈ inp.collect.places then inp.collect.places
      else inp.collect.places ++ [99])
    split
    · exact collect_places_nodup inp
    · rename_i hq
      exact List.nodup_append.2 ⟨collect_places_nodup inp, List.nodup_singleton _,
        fun a ha b hb' e => hq (by rw [List.mem_singleton.1 hb'] at e; exact e ▸ ha)⟩
  · have h99 := (h.2.2.1 core040_ex _ (core040_post_ok.2 ⟨core040_noClash rfl, rfl⟩)).1 99
      (by decide)
    exact absurd (core040_coll_iff.1 h99) (by decide)

/-- The empty-net-rejecting builder kills the mutant without line 4: whenever it accepts it is
the reference, so it meets lines 1 to 3, but it rejects the empty net with no terminal place
(line 4). -/
@[evidence mutant CORE_040]
theorem CORE_040_mutant_noAccept_killed :
    CORE_040_mutant_noAccept core040_B (core040_rejectEmptyNB core040_B) ∧
      ¬ CORE_040 core040_B (core040_rejectEmptyNB core040_B) := by
  obtain ⟨h1, h2, h3, -⟩ := CORE_040_reference core040_B
  have hr : ∀ inp b, core040_rejectEmptyNB core040_B inp = .ok b → refNetBuild inp = .ok b := by
    intro inp b hb
    unfold core040_rejectEmptyNB at hb
    split at hb
    · cases hb
    · exact hb
  refine ⟨⟨fun inp b hb => h1 inp b (hr inp b hb), fun inp b hb => h2 inp b (hr inp b hb),
    fun inp b hb => h3 inp b (hr inp b hb)⟩, fun h => ?_⟩
  obtain ⟨b, hb⟩ := h.2.2.2 NetIn.empty rfl
  exact nomatch hb

end Libpetri.Spec
