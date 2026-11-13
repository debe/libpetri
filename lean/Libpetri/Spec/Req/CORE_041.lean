import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryBuild
import Libpetri.Spec.Text.CORE_041

set_option linter.missingDocs true

/-!
# CORE-041: Net immutability (`spec/01-core-model.md`)

CORE-041 is a behaviour requirement (kind B) over a net builder seen as a state machine
(`BuilderApi B`, `Reference/Build.lean`): calls that declare a place, add a transition or declare a
terminal place, `build`, which returns a handle on the built net, and `view`, what a handle shows
in a state. A history of uses (`BUse`) mixes calls and builds, in the order made.

The statement has two lines, against a net builder `NB` (the function CORE-040 is stated over):

* **line 0** (the builder trace): right after a build, the handle shows `NB` applied to every call
  made on the builder before that build;
* **line 1** (stability): what the handle shows right after the build is what it shows after any
  later uses of the same builder, calls and builds alike.

Line 1 alone is the immutability sentence, and a builder whose handle always shows the empty net
satisfies it (design note S6). Line 0 pins what the handle shows relative to `NB`: that builder is
killed against every `NB` that puts a declared place into the net, as CORE-040 requires, and meets
CORE-041 against the net builder that always returns the empty net.

The witness is the reference builder `copyBuilder` with the reference net builder `refNetBuild`
(Java and TypeScript copy their collections in `build`, Rust consumes the builder, the Python
binding clones it). Wrong builders are killed: `aliasBuilder`, whose built net shares the builder's
live place and transition sets (the behaviour RD-02 recorded of TypeScript's builder; ruling
D66 (a), line 1); a blind
builder whose handle always shows the empty net (line 0); a builder that empties itself at build,
so a second build forgets the calls made before the first (line 0 over histories with a build);
and a builder that keeps only the last built net, so a later build changes an earlier handle
(line 1, its builds half).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## Uses of a builder -/

section Uses

variable {N A : Type}

/-- One use of a net builder: a call before `build` (`BOp`: declare a place, add a transition,
declare a terminal place) or a `build` call. -/
inductive BUse (B : TBuilder N A) where
  /-- A call that declares a place, adds a transition or declares a terminal place. -/
  | call (op : BOp B)
  /-- A `build` call (its handle is dropped). -/
  | build

/-- The calls of a history of uses, in the order made (the builds dropped). -/
def callsOf {B : TBuilder N A} : List (BUse B) → List (BOp B)
  | [] => []
  | .call op :: us => op :: callsOf us
  | .build :: us => callsOf us

/-- The state of a builder after one use. -/
def useStep {B : TBuilder N A} (BA : BuilderApi B) (s : BA.S) : BUse B → BA.S
  | .call op => BA.step s op
  | .build => (BA.build s).1

/-- The state of a builder after a history of uses. -/
def runUses {B : TBuilder N A} (BA : BuilderApi B) (s : BA.S) (us : List (BUse B)) : BA.S :=
  us.foldl (useStep BA) s

end Uses

/-! ## CORE-041: Net Immutability -/

requirement CORE_041
  id "CORE-041"
  title "Net Immutability"
  kind B
  scope "all net builders used without composition or fusion sets"
  source verbatim "spec/01-core-model.md"
  covers CORE_041.s1, CORE_041.s2, CORE_041.s3, CORE_041.s4
  reading "For every transition builder B, every net builder NB over B's instances and every builder state machine BA:"
          "for every history of uses of a new builder (calls and builds, in the order made), the handle the next build returns shows, right after that build, NB's result (a built net or a rejection) on every call of the history, in the order made (NetIn.ofOps of the calls; a build adds nothing and resets nothing);"
          "for every history of uses of a new builder and every later history of uses, the handle the build after the first history returns shows after the later history what it showed right after that build."
  assumes "A builder state machine (BuilderApi in Reference/Build.lean) is the net builder of one implementation: its calls declare a place, add a built transition or declare a terminal place (BOp), build returns a handle on the built net, and view is what a handle shows (a built net, or the rejection the build reported: a Java exception or a Rust panic is read as a handle that shows the rejection). The net builder NB is the function CORE-040 is stated over. On its own, line 0 pins the handle relative to NB only: the blind builder, whose handle always shows the empty net, meets CORE-041 against the net builder that always returns the empty net (core041_blind_constEmpty). Read together with CORE-040 over the same NB, line 0 says that the handle shows CORE-040's built net (the builder trace, design note 3.8): every NB that meets CORE-040 lines 2 and 4 puts a declared place into the net, and then the blind builder violates line 0 (core041_blind_killed_declared). The joint statement over one shared NB is the integrator's (Spec/ConsistencyStructure.lean)."
          "Line 0 is the first quoted shall sentence. Without it the block is satisfied by a builder whose handle always shows the empty net (design note S6: core041_blindBuilder satisfies line 1, CORE_041_mutant_stableOnly_killed). Line 0 equates the handle with NB's whole result, so the build rejects exactly when NB rejects; in scope that is the rejection of EXEC-042 AC5 (CORE-040 line 4: the net builder rejects nothing of its own). A history may hold earlier builds; a build adds nothing to what the builder holds and resets nothing, so a second build shows every call made so far, including those made before the first build, as Java, TypeScript and the Python binding do (the Python NetBuilder clones the accumulated builder, PyPetriNetBuilder build in rust/libpetri-py/src/model.rs). A builder that empties itself at build meets line 0 on histories without an earlier build and line 1, and violates line 0 at its second build (core041_resetBuilder, CORE_041_mutant_firstBuild_killed). Rust consumes the builder (PetriNetBuilder::build in rust/libpetri-core/src/petri_net.rs), so in Rust no use follows a build and both lines speak of the first build only."
          "Line 1 is the second quoted shall sentence and the body's two sentences ('After construction, a Petri net definition is immutable.' and 'The set of places, transitions, and their connections cannot be modified.'): a net's connections are the arcs of its transitions, which the built net carries in its transition definitions (TransDef), so a built net that keeps its places, transitions and terminal places keeps its connections. Later uses are calls and builds alike: a builder that keeps only the last built net, so that a later build changes the net an earlier handle shows, violates it (core041_slotBuilder, CORE_041_mutant_callsOnly_killed, the reading that allows later calls only)."
          "Ruling D66 (a): the MUST stands, and every runtime's built net keeps its own place and transition sets. Java copies the sets into unmodifiable ones (the private PetriNet constructor, java/src/main/java/org/libpetri/core/PetriNet.java), and TypeScript's build gives the net copies of the builder's place map and transition set (typescript/src/core/petri-net.ts build, new Set(this._places.values()) and new Set(this._transitions)), so a place or transition added after build, or a channel composition that removes a caller transition, does not reach a net already built. A builder whose build passes its own live sets to the net (aliasBuilder, the behaviour RD-02 in spec/runtime-defects.md recorded of TypeScript's builder) shows a transition added after build in the built net and violates line 1 (CORE_041_forbids_alias, and CORE_041_mutant_traceOnly_killed: it meets line 0)."
          "Scope: a net built without fusion sets, instance composition or retired ports, as in CORE-040, which both quoted shall sentences name ('a net builder used as [CORE-040] describes'); those rewrite arcs and drop places, and belong to the composition model (W8). Nets derived from a built net (binding actions, CORE-042; composition) are new nets built through a builder, not changes to the built net, and are outside this block. What a handle shows is the net's places, transitions with their definitions and terminal places; the net's name and subnet membership are not modelled."
          "AC1 (no mutation methods exist on the constructed net) and AC2 (collections returned by the net are unmodifiable or copies) are API shape, tested and not proven (kind Q): the model has no method that changes a built net, and a host that changed a returned collection would be changing the net, which line 1 forbids for the builder's own uses only. In TypeScript the returned sets are read-only by type only. The test derivation ('build a net; verify no mutation API exists') is AC1. As in CORE-040 (ruling D99 (a)), these API-shape criteria stay in the markdown unmarked."
  signoff "2026-11-13 9626d777196eacc9 ai"
  statement : ∀ {N A : Type} [DecidableEq N] (B : TBuilder N A), NetBuilder B → BuilderApi B → Prop :=
    fun B NB BA =>
      (∀ pre : List (BUse B),
        BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2 =
          NB (NetIn.ofOps (callsOf pre))) ∧
      (∀ pre post : List (BUse B),
        BA.view (runUses BA (BA.build (runUses BA BA.init pre)).1 post)
            (BA.build (runUses BA BA.init pre)).2 =
          BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2)

/- The pinned readable form of CORE-041: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_041 : {N A : Type} → [DecidableEq N] → (B : TBuilder N A) → NetBuilder B → BuilderApi B → Prop :=
fun {N A} [DecidableEq N] B NB BA =>
  (∀ (pre : List (BUse B)),
      BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2 =
        NB (NetIn.ofOps (callsOf pre))) ∧
    ∀ (pre post : List (BUse B)),
      BA.view (runUses BA (BA.build (runUses BA BA.init pre)).1 post) (BA.build (runUses BA BA.init pre)).2 =
        BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2
-/
#guard_msgs in #print CORE_041

/-! ### The two lines, named (for the mutants) -/

section Lines

variable {N A : Type} [DecidableEq N]

/-- Line 0 of CORE-041: the builder trace. -/
def core041_line0 (B : TBuilder N A) (NB : NetBuilder B) (BA : BuilderApi B) : Prop :=
  ∀ pre : List (BUse B),
    BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2 =
      NB (NetIn.ofOps (callsOf pre))

/-- Line 1 of CORE-041: stability under every later use. -/
def core041_line1 (B : TBuilder N A) (BA : BuilderApi B) : Prop :=
  ∀ pre post : List (BUse B),
    BA.view (runUses BA (BA.build (runUses BA BA.init pre)).1 post)
        (BA.build (runUses BA BA.init pre)).2 =
      BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2

/-- CORE-041 is its two lines. -/
theorem core041_iff (B : TBuilder N A) (NB : NetBuilder B) (BA : BuilderApi B) :
    CORE_041 B NB BA ↔ core041_line0 B NB BA ∧ core041_line1 B BA :=
  Iff.rfl

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N] {B : TBuilder N A}

/-- What the reference builder holds after a history of uses: its calls appended to what it held,
in the order made. -/
theorem copyBuilder_runUses_fst (s : (copyBuilder B).S) (us : List (BUse B)) :
    (runUses (copyBuilder B) s us).1 = (callsOf us).foldl NetIn.addOp s.1 := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    cases u with
    | call op => exact ih ((copyBuilder B).step s op)
    | build => exact ih ((copyBuilder B).build s).1

/-- The reference builder only appends to its built nets. -/
theorem copyBuilder_runUses_snd (s : (copyBuilder B).S) (us : List (BUse B)) :
    ∃ extra, (runUses (copyBuilder B) s us).2 = s.2 ++ extra := by
  induction us generalizing s with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons u us ih =>
    cases u with
    | call op => exact ih ((copyBuilder B).step s op)
    | build =>
      obtain ⟨e, he⟩ := ih ((copyBuilder B).build s).1
      refine ⟨[refNetBuild s.1] ++ e, ?_⟩
      show (runUses (copyBuilder B) ((copyBuilder B).build s).1 us).2 = _
      rw [he]
      exact List.append_assoc _ _ _

/-- A handle of the reference builder that names a kept net shows it after any later uses. -/
theorem copyBuilder_view_runUses (s : (copyBuilder B).S) (us : List (BUse B)) {h : Nat}
    (hh : h < s.2.length) :
    (copyBuilder B).view (runUses (copyBuilder B) s us) h = (copyBuilder B).view s h := by
  obtain ⟨e, he⟩ := copyBuilder_runUses_snd s us
  show (runUses (copyBuilder B) s us).2[h]?.getD _ = s.2[h]?.getD _
  rw [he, List.getElem?_append_left hh]

/-- ✓ The reference builder state machine with the reference net builder satisfies CORE-041:
`build` keeps `refNetBuild` of what was added (line 0, with `copyBuilder_view_built`) and later
uses never change a kept net (line 1). -/
@[evidence holds CORE_041]
theorem CORE_041_reference (B : TBuilder N A) :
    CORE_041 B (refNetBuild (B := B)) (copyBuilder B) := by
  refine ⟨fun pre => ?_, fun pre post => ?_⟩
  · rw [copyBuilder_view_built, copyBuilder_runUses_fst]
    rfl
  · exact copyBuilder_view_runUses _ post (by simp [copyBuilder])

end Reference

/-! ### Example -/

/-- The example transition builder: the reference one over `Nat` places. -/
abbrev core041B : TBuilder Nat Unit := refTransBuild

/-- The example history after the first build: declare place 1, then build again. -/
def core041_later : List (BUse core041B) := [.call (.place 1), .build]

/-- ✓ Both lines of CORE-041 are exercised by the reference: a new builder that declares place 0
and builds shows the net with place 0 (line 0), and still shows it after place 1 is declared and
the builder builds again, while that second build shows places 0 and 1 (line 1, and line 0 on a
history with an earlier build). -/
@[evidence nonvacuous CORE_041]
theorem CORE_041_nonvacuous :
    (copyBuilder core041B).view
        ((copyBuilder core041B).build (runUses (copyBuilder core041B) (copyBuilder core041B).init
          [.call (.place 0)])).1
        ((copyBuilder core041B).build (runUses (copyBuilder core041B) (copyBuilder core041B).init
          [.call (.place 0)])).2 = .ok ⟨[0], [], []⟩ ∧
    (copyBuilder core041B).view
        (runUses (copyBuilder core041B)
          ((copyBuilder core041B).build (runUses (copyBuilder core041B) (copyBuilder core041B).init
            [.call (.place 0)])).1 core041_later)
        ((copyBuilder core041B).build (runUses (copyBuilder core041B) (copyBuilder core041B).init
          [.call (.place 0)])).2 = .ok ⟨[0], [], []⟩ ∧
    refNetBuild (NetIn.ofOps (callsOf ([.call (.place 0), .build] ++ core041_later))) =
      (.ok ⟨[0, 1], [], []⟩ : Except String (BuiltNet Nat Unit)) :=
  ⟨rfl, rfl, rfl⟩

/-- The places a handle shows (none for a rejection): a decidable view of a built net. -/
def core041_places {N A : Type} : Except String (BuiltNet N A) → List N
  | .ok b => b.places
  | .error _ => []

/-! ### Violation: a builder that shares its live sets (ruling D66 (a)) -/

/-- ✗ The aliasing builder (the behaviour RD-02 recorded of TypeScript's builder) violates
CORE-041 (line 1): build a new
builder, then declare place 0, and the handle the build returned shows place 0. -/
@[evidence forbids CORE_041]
theorem CORE_041_forbids_alias :
    ¬ CORE_041 core041B (refNetBuild (B := core041B)) (aliasBuilder core041B) := by
  intro h
  exact aliasBuilder_unstable_empty (B := core041B) 0 (h.2 [] [.call (.place 0)])

/-! ### Mutant: line 0 alone (the trace without stability) -/

section MutantTrace

variable {N A : Type} [DecidableEq N]

/-- Mutant reading: only the builder trace (line 0), no stability. -/
def CORE_041_mutant_traceOnly (B : TBuilder N A) (NB : NetBuilder B) (BA : BuilderApi B) : Prop :=
  core041_line0 B NB BA

/-- The aliasing builder holds every call made so far. -/
theorem aliasBuilder_runUses {B : TBuilder N A} (s : (aliasBuilder B).S) (us : List (BUse B)) :
    runUses (aliasBuilder B) s us = (callsOf us).foldl NetIn.addOp s := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    cases u with
    | call op => exact ih (s.addOp op)
    | build => exact ih s

end MutantTrace

/-- The aliasing builder kills the trace-only reading: right after a build its handle shows the
reference net builder's result on every call made (line 0), but a later call changes it. -/
@[evidence mutant CORE_041]
theorem CORE_041_mutant_traceOnly_killed :
    CORE_041_mutant_traceOnly core041B (refNetBuild (B := core041B)) (aliasBuilder core041B) ∧
      ¬ CORE_041 core041B (refNetBuild (B := core041B)) (aliasBuilder core041B) := by
  refine ⟨fun pre => ?_, CORE_041_forbids_alias⟩
  show refNetBuild (runUses (aliasBuilder core041B) NetIn.empty pre) = _
  rw [aliasBuilder_runUses]
  rfl

/-! ### Mutant: line 1 alone (immutability without the trace, design note S6) -/

section MutantStable

variable {N A : Type} [DecidableEq N]

/-- Mutant reading: only stability (line 1), the spike's `Immutable`. -/
def CORE_041_mutant_stableOnly (B : TBuilder N A) (_ : NetBuilder B) (BA : BuilderApi B) : Prop :=
  core041_line1 B BA

/-- A blind builder: its handle always shows the empty net, whatever was added. -/
def core041_blindBuilder (B : TBuilder N A) : BuilderApi B where
  S := Unit
  H := Unit
  init := ()
  step _ _ := ()
  build _ := ((), ())
  view _ _ := .ok ⟨[], [], []⟩

end MutantStable

/-- The blind builder kills the stability-only reading: its handle never changes (line 1), but a
new builder that declares place 0 and builds shows the empty net (line 0). The kill is relative to
the net builder: here `NB` is the reference `refNetBuild`; `core041_blind_killed_declared` gives
it for every `NB` that keeps a declared place, and `core041_blind_constEmpty` shows that it fails
for the net builder that always returns the empty net. -/
@[evidence mutant CORE_041]
theorem CORE_041_mutant_stableOnly_killed :
    CORE_041_mutant_stableOnly core041B (refNetBuild (B := core041B)) (core041_blindBuilder core041B) ∧
      ¬ CORE_041 core041B (refNetBuild (B := core041B)) (core041_blindBuilder core041B) := by
  refine ⟨fun _ _ => rfl, fun h => ?_⟩
  have := congrArg core041_places (h.1 [.call (.place 0)])
  exact absurd this (by decide)

/-- Line 0 pins the handle relative to `NB` only: the blind builder meets CORE-041 against the net
builder that always returns the empty net. That net builder violates CORE-040 (a declared place is
not in its net), so the joint reading over one `NB` excludes the pair. -/
theorem core041_blind_constEmpty :
    CORE_041 core041B (fun _ => .ok ⟨[], [], []⟩) (core041_blindBuilder core041B) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- The blind builder violates CORE-041 against every net builder that, given only the declaration
of place `p`, returns a net holding `p`. Every net builder that meets CORE-040 does: line 4 makes
it accept that input (no terminal place) and line 2 puts the declared place `p` into the net. -/
theorem core041_blind_killed_declared {N A : Type} [DecidableEq N] {B : TBuilder N A}
    (NB : NetBuilder B) (p : N)
    (hNB : ∃ b, NB (NetIn.ofOps [.place p]) = .ok b ∧ p ∈ b.places) :
    ¬ CORE_041 B NB (core041_blindBuilder B) := by
  intro h
  obtain ⟨b, hb, hp⟩ := hNB
  have h0 := h.1 [.call (.place p)]
  have h1 : (Except.ok ⟨[], [], []⟩ : Except String (BuiltNet N A)) = .ok b := h0.trans hb
  cases h1
  exact absurd hp (List.not_mem_nil)

/-! ### Mutant: line 0 over histories without an earlier build (builds that reset) -/

section MutantFirstBuild

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 0: the builder trace only for histories of calls, with no earlier
build. Line 1 is as in CORE-041. -/
def CORE_041_mutant_firstBuild (B : TBuilder N A) (NB : NetBuilder B) (BA : BuilderApi B) : Prop :=
  (∀ ops : List (BOp B),
    BA.view (BA.build (runUses BA BA.init (ops.map BUse.call))).1
        (BA.build (runUses BA BA.init (ops.map BUse.call))).2 =
      NB (NetIn.ofOps ops)) ∧
  core041_line1 B BA

/-- A builder that keeps its built nets as the reference does, but empties what was added at
every build: a second build forgets the calls made before the first. -/
def core041_resetBuilder (B : TBuilder N A) : BuilderApi B where
  S := NetIn B × List (Except String (BuiltNet N A))
  H := Nat
  init := (NetIn.empty, [])
  step s op := (s.1.addOp op, s.2)
  build s := ((NetIn.empty, s.2 ++ [refNetBuild s.1]), s.2.length)
  view s h := s.2[h]?.getD (.error "no such net")

/-- Calls on the reset builder append to what was added and keep the built nets. -/
theorem core041_resetBuilder_runUses_calls {B : TBuilder N A} (s : (core041_resetBuilder B).S)
    (ops : List (BOp B)) :
    runUses (core041_resetBuilder B) s (ops.map BUse.call) = (ops.foldl NetIn.addOp s.1, s.2) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih ((core041_resetBuilder B).step s op)

/-- The reset builder only appends to its built nets. -/
theorem core041_resetBuilder_runUses_snd {B : TBuilder N A} (s : (core041_resetBuilder B).S)
    (us : List (BUse B)) :
    ∃ extra, (runUses (core041_resetBuilder B) s us).2 = s.2 ++ extra := by
  induction us generalizing s with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons u us ih =>
    cases u with
    | call op => exact ih ((core041_resetBuilder B).step s op)
    | build =>
      obtain ⟨e, he⟩ := ih ((core041_resetBuilder B).build s).1
      refine ⟨[refNetBuild s.1] ++ e, ?_⟩
      show (runUses (core041_resetBuilder B) ((core041_resetBuilder B).build s).1 us).2 = _
      rw [he]
      exact List.append_assoc _ _ _

end MutantFirstBuild

/-- The reset builder kills the first-build reading: right after a build from a history of calls
it shows the reference net builder's result, and later uses never change a handle (line 1), but a
new builder that declares place 0, builds and builds again shows the empty net at the second
build, where line 0 asks for the net with place 0. -/
@[evidence mutant CORE_041]
theorem CORE_041_mutant_firstBuild_killed :
    CORE_041_mutant_firstBuild core041B (refNetBuild (B := core041B))
        (core041_resetBuilder core041B) ∧
      ¬ CORE_041 core041B (refNetBuild (B := core041B)) (core041_resetBuilder core041B) := by
  refine ⟨⟨fun ops => ?_, fun pre post => ?_⟩, fun h => ?_⟩
  · show ((runUses (core041_resetBuilder core041B) (NetIn.empty, [])
        (ops.map BUse.call)).2 ++ [refNetBuild (runUses (core041_resetBuilder core041B)
          (NetIn.empty, []) (ops.map BUse.call)).1])[(runUses (core041_resetBuilder core041B)
            (NetIn.empty, []) (ops.map BUse.call)).2.length]?.getD _ = _
    rw [core041_resetBuilder_runUses_calls]
    simp [NetIn.ofOps]
  · obtain ⟨e, he⟩ := core041_resetBuilder_runUses_snd
      ((core041_resetBuilder core041B).build
        (runUses (core041_resetBuilder core041B) (core041_resetBuilder core041B).init pre)).1 post
    show (runUses (core041_resetBuilder core041B) _ post).2[_]?.getD _ = _
    rw [he, List.getElem?_append_left (by simp [core041_resetBuilder])]
    rfl
  · have := congrArg core041_places (h.1 [.call (.place 0), .build])
    exact absurd this (by decide)

/-! ### Mutant: line 1 under later calls only (no later builds) -/

section MutantCalls

variable {N A : Type} [DecidableEq N]

/-- Mutant reading of line 1: the handle is stable under later calls (`BOp`), with no later
build. Line 0 is as in CORE-041. -/
def CORE_041_mutant_callsOnly (B : TBuilder N A) (NB : NetBuilder B) (BA : BuilderApi B) : Prop :=
  core041_line0 B NB BA ∧
  ∀ (pre : List (BUse B)) (post : List (BOp B)),
    BA.view (BA.run (BA.build (runUses BA BA.init pre)).1 post)
        (BA.build (runUses BA BA.init pre)).2 =
      BA.view (BA.build (runUses BA BA.init pre)).1 (BA.build (runUses BA BA.init pre)).2

/-- A builder that keeps only the last built net in one slot, and every handle shows the slot:
a later build replaces the net an earlier handle shows. -/
def core041_slotBuilder (B : TBuilder N A) : BuilderApi B where
  S := NetIn B × Except String (BuiltNet N A)
  H := Unit
  init := (NetIn.empty, .error "not built")
  step s op := (s.1.addOp op, s.2)
  build s := ((s.1, refNetBuild s.1), ())
  view s _ := s.2

/-- The slot builder holds every call made so far. -/
theorem core041_slotBuilder_runUses_fst {B : TBuilder N A} (s : (core041_slotBuilder B).S)
    (us : List (BUse B)) :
    (runUses (core041_slotBuilder B) s us).1 = (callsOf us).foldl NetIn.addOp s.1 := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    cases u with
    | call op => exact ih ((core041_slotBuilder B).step s op)
    | build => exact ih ((core041_slotBuilder B).build s).1

/-- Later calls never change the slot builder's slot. -/
theorem core041_slotBuilder_run_snd {B : TBuilder N A} (s : (core041_slotBuilder B).S)
    (ops : List (BOp B)) : ((core041_slotBuilder B).run s ops).2 = s.2 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih ((core041_slotBuilder B).step s op)

end MutantCalls

/-- The slot builder kills the calls-only reading: it shows the reference net builder's result
right after a build (line 0) and later calls never change it, but building a new builder,
declaring place 0 and building again changes what the first handle shows (line 1). -/
@[evidence mutant CORE_041]
theorem CORE_041_mutant_callsOnly_killed :
    CORE_041_mutant_callsOnly core041B (refNetBuild (B := core041B))
        (core041_slotBuilder core041B) ∧
      ¬ CORE_041 core041B (refNetBuild (B := core041B)) (core041_slotBuilder core041B) := by
  refine ⟨⟨fun pre => ?_, fun pre post => core041_slotBuilder_run_snd _ post⟩, fun h => ?_⟩
  · show refNetBuild (runUses (core041_slotBuilder core041B) _ pre).1 = _
    rw [core041_slotBuilder_runUses_fst]
    rfl
  · have := congrArg core041_places (h.2 [] [.call (.place 0), .build])
    exact absurd this (by decide)

end Libpetri.Spec
