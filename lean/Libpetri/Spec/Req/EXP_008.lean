import Libpetri.Spec.Registry
import Libpetri.Spec.Glossary
import Libpetri.Export.Styles
import Libpetri.Spec.Text.EXP_008

set_option linter.missingDocs true

/-!
# EXP-008: Styling, the place categories (`spec/09-export.md`)

The category an export gives a place: the row of the node table (`spec/petri-net-styles.json`,
generated as `Libpetri.Export.NodeCat`) its node is drawn with. The requirement is a predicate
over an abstract place classifier `C : PlaceClassifier N`, which gets the net, its environment
places, its terminal places and a place, and returns a node row. It reads only the arcs of the
net (no marking, no graph), so no export model is needed: the join "every place node is drawn
with the row `C` gives" is the third clause of the glossary agreement `ExportAgrees`, which the
export consistency theorem carries, and `EXP_002_draws_EXP_008` shows the reference exporter
drawing those rows.

Ruling D51 (a): the precedence is the one all three runtimes share, terminal, then environment,
then start, then end; and the block states the common form of "end place", true of both runtime
shapes. Java and TypeScript count a read arc as keeping a place from being an end place, Rust
counts only input arcs; the two differ on exactly one kind of place, one that an output spec
names and that only read arcs touch on the consuming side. The block leaves that place open
(`EXP_008_readOnly_open`). The end state of D51 is the Java and TypeScript reading, so that
shape is the reference (`refPlaceCategory`), and the Rust shape is an allowed classifier
(`EXP_008_allows_inputsOnly`) until its mapper is changed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

variable {N : Type}

/-! ## Vocabulary: the arcs a category reads -/

/-- Some transition of `X` has an output arc on `p` (glossary: Output arc): some output spec
names `p`, a `ForwardInput`'s target included. -/
def HasOutputArc [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (OutputArc t p)

/-- Some transition of `X` has an input arc on `p` (glossary: Input arc). -/
def HasInputArc [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (p ∈ inPlaces t)

/-- Some transition of `X` has a read arc on `p` (glossary: Read arc). -/
def HasReadArc [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (ReadArc t p)

/-- **A place classifier**: given a net, its environment places (ENV-001), its terminal places
(EXEC-042) and a place, the node row the export draws the place with. -/
abbrev PlaceClassifier (N : Type) :=
  Reference.Net N → (N → Bool) → (N → Bool) → N → NodeCat

/-! ## The witness: the classifier of the Java and TypeScript mappers -/

/-- **The reference place classifier** (witness model): terminal first, then environment, then
start (no output arc), then end (no input arc and no read arc), else the regular `place` row.
It is the shape of `PlaceAnalysis.category` in Java and `placeCategory` over `analyzePlaces` in
TypeScript, which count a read arc as an outgoing arc, and it is the end state of ruling D51. It
agrees with those functions on every place some arc touches; on a place no arc touches they
answer `place` (an unknown name) and draw no node for it (EXP-001, ruling D60), while this
classifier answers start, as the Rust mapper does for the node it draws. -/
def refPlaceCategory [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else if HasInputArc X p = false ∧ HasReadArc X p = false then .«end»
  else .place

#spec_witness refPlaceCategory

/-! ## EXP-008: Styling -/

requirement EXP_008
  id "EXP-008"
  title "Styling"
  kind F
  scope "every exporter's mapper, on the place nodes of a net (before a documentation generator restyles interface ports)"
  source verbatim "spec/09-export.md"
  covers EXP_008.s1, EXP_008.s2, EXP_008.s3, EXP_008.s4, EXP_008.s5, EXP_008.s6, EXP_008.s7,
        EXP_008.s8
  reading "For the place classifier C, every net X with environment places env and terminal places term, and every place p:"
          "a terminal place is terminal;"
          "an environment place that is not terminal is environment;"
          "for a place that is neither (an ordinary place): it is start exactly when no transition has an output arc on it;"
          "it is end when some transition has an output arc on it and none has an input arc or a read arc on it;"
          "it is not end when some transition has an input arc on it;"
          "it is start, end or the regular place row;"
          "and if some transition has an output arc on it, some has a read arc on it and none has an input arc on it, then every ordinary place p' of every net X' (with any env' and term') of which the same holds gets the same row as p."
  assumes "The model is a place classifier C : PlaceClassifier N: the node row (glossary of the style table, Libpetri.Export.NodeCat) the export's mapper gives place p of net X, given the environment places env (ENV-001) and the terminal places term (EXEC-042) as predicates. C reads only the arcs of X, as every runtime's analysis does (analyze_places in the Rust crate libpetri-export, PlaceAnalysis.java, analyzePlaces in petri-net-mapper.ts); the marking, the timing and the configuration play no part. Lines 1 to 6 fix C from the arc kinds on p in every case but one, and line 7 makes that one case, too, the same answer for every place and every net, so C reads no more of X than whether p has an output arc, an input arc and a read arc. That the exporter draws each place node with the row C gives is the third clause of the glossary agreement ExportAgrees (each place node has the category C gives its place, with the configuration's environment places and the net's terminal places), which the export consistency theorem carries; that a place row is not the transition row is EXP-002's line 1 and EXP-003's line 3; EXP_002_draws_EXP_008 shows the reference exporter drawing each place node with the row of the reference classifier. This block itself does not see the graph."
          "C is the mapper's classification, the one the production export pipeline gives. The three documentation generators (SubnetDotExport.java, subnet-dot-export.ts, and the Rust subnet_dot_export module; compile-time diagrams, EXP-011) afterwards rewrite the DOT of a subnet body and redraw its interface-port places with the interface-port row; that rewrite is a later step on the DOT text, not C's answer, and is out of scope. The markdown says so in the sentence after the bullets. A mapper that gives an ordinary place the interface-port row itself violates line 6 (EXP_008_forbids_otherRow)."
          "Which places get a node at all is EXP-001's subject (ruling D60): Rust draws every declared place, Java and TypeScript only places some arc touches. Line 3 gives a place that no arc touches the start category, which is what Rust draws; Java and TypeScript draw no node for it, so their answer for it is never seen (PlaceAnalysis.category answers place for an unknown name). The reference classifier answers start, as Rust does."
          "The words 'incoming' and 'outgoing' of the body bullets ('no incoming arcs', 'no outgoing arcs') are read as the markdown's sentence after the bullets defines them, which is how all three runtimes count: an incoming arc of a place is an output arc of some transition on it (glossary: Output arc, the target of a ForwardInput included), and an input arc on it is an outgoing arc. Whether a read arc is an outgoing arc is the open case of ruling D51 (next assumption). Inhibitor arcs and reset arcs count as neither, although the glossary draws them from the place to the transition and the reset edge of EXP-004 and EXP-013 is drawn from the transition to the place (clash exp-a#5 and exp-a#9): a classifier that counts them as outgoing violates line 4 (EXP_008_forbids_glossaryDirections), one that counts a reset arc as incoming violates line 3 (EXP_008_forbids_resetIncoming)."
          "Ruling D51 (a): the common form of 'end place'. A place that an output spec names, on which no transition has an input arc and some transition has a read arc, is regular in Java and TypeScript (a read arc counts as outgoing) and end in Rust (only input arcs count). Lines 4 and 5 hold of both shapes and leave that place open (EXP_008_readOnly_open); the Rust shape is an allowed classifier (EXP_008_allows_inputsOnly). The case is open per classifier, not per place: line 7 says a classifier answers it the same way for every such place of every net, so a mix of the two shapes is rejected, whether the answer hangs on whether the reader writes elsewhere (EXP_008_forbids_readByWriter) or on whether the reader is the place's own writer (EXP_008_forbids_selfReadSkipped). The end state of D51, that a read arc keeps a place from being an end place, is the reference classifier's answer; the later line that makes line 4 an 'exactly when' with read arcs counted waits for the Rust mapper to change and is not encoded. The markdown records the open case and the intended answer in a sentence without shall."
          "The precedence terminal, environment, start, end is all three runtimes' (ruling D51) and is lines 1 to 3 and 6: a terminal environment place is terminal (EXP_008_forbids_envFirst), an environment place no output spec names is environment, not start (EXP_008_forbids_startFirst), and a place with no arcs at all is start, not end (EXP_008_forbids_endFirst). EXEC-042 builds reject a terminal place with an input or read arc, which the precedence does not need."
          "AC1 (start places are visually distinct from other places) and AC2 (end places are visually distinct from other places) are read on the style table: the start row and the end row each differ from every other place row and from the transition row (EXP_008_rows_distinct, decided on the generated table), and lines 1 to 7 decide which places get the start and the end row. The drawn style is tied to C by the third clause of ExportAgrees, so AC1 and AC2 are EXP_008_rows_distinct together with that clause, carried by the export consistency theorem, and EXP_002_draws_EXP_008 (EXP_002.lean, tagged as citing EXP-008 AC1 and AC2), which proves on the reference exporter, for every cluster stage, that each place node has the reference classifier's row and a style different from every place or transition node of another row. The colours of the body bullets ('e.g., green', 'e.g., blue', 'e.g., yellow') are examples; the values are the table's and are checked by the runtimes' tests, not here. The bullet on transitions (a distinct colour) is the transition row's difference from the place rows in EXP_008_rows_distinct; that transitions are drawn with the transition row is EXP-003's subject."
          "The test derivation (a net with start and end places, export, styling applied) is EXP_008_nonvacuous on the reference classifier: a net with a start, a regular, an end, an environment, a terminal and an inhibitor-only place."
          "Out of scope: the rows of composition (interface-port, sync-channel), which only the documentation generators' rewrite of a subnet diagram uses (see the second assumption; MOD-040 and EXP-016 add grouping only), and the rows of junctions (EXP-012), which are synthetic nodes, not place nodes; ν correlation (NU-020, EXP-018) changes no place category. Places are compared by identity (DecidableEq N); export IDs and sanitising are EXP-014's (ruling D46)."
  signoff "2026-11-13 1e4bf950dfb9a657 ai"
  statement : ∀ {N : Type} [DecidableEq N], PlaceClassifier N → Prop :=
    fun C => ∀ X env term p,
      (term p = true → C X env term p = .terminal) ∧
      (term p = false → env p = true → C X env term p = .environment) ∧
      (term p = false → env p = false →
        (C X env term p = .start ↔ HasOutputArc X p = false) ∧
        (HasOutputArc X p = true → HasInputArc X p = false → HasReadArc X p = false →
          C X env term p = .«end») ∧
        (HasInputArc X p = true → C X env term p ≠ .«end») ∧
        (C X env term p = .start ∨ C X env term p = .«end» ∨ C X env term p = .place) ∧
        (HasOutputArc X p = true → HasInputArc X p = false → HasReadArc X p = true →
          ∀ X' env' term' p', term' p' = false → env' p' = false →
            HasOutputArc X' p' = true → HasInputArc X' p' = false → HasReadArc X' p' = true →
            C X' env' term' p' = C X env term p))

/- The pinned readable form of EXP-008: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_008 : {N : Type} → [DecidableEq N] → PlaceClassifier N → Prop :=
fun {N} [DecidableEq N] C =>
  ∀ (X : Reference.Net N) (env term : N → Bool) (p : N),
    (term p = true → C X env term p = NodeCat.terminal) ∧
      (term p = false → env p = true → C X env term p = NodeCat.environment) ∧
        (term p = false →
          env p = false →
            (C X env term p = NodeCat.start ↔ HasOutputArc X p = false) ∧
              (HasOutputArc X p = true →
                  HasInputArc X p = false → HasReadArc X p = false → C X env term p = NodeCat.end) ∧
                (HasInputArc X p = true → C X env term p ≠ NodeCat.end) ∧
                  (C X env term p = NodeCat.start ∨ C X env term p = NodeCat.end ∨ C X env term p = NodeCat.place) ∧
                    (HasOutputArc X p = true →
                      HasInputArc X p = false →
                        HasReadArc X p = true →
                          ∀ (X' : Reference.Net N) (env' term' : N → Bool) (p' : N),
                            term' p' = false →
                              env' p' = false →
                                HasOutputArc X' p' = true →
                                  HasInputArc X' p' = false →
                                    HasReadArc X' p' = true → C X' env' term' p' = C X env term p))
-/
#guard_msgs in #print EXP_008

/-! ### The reference -/

/-- The reference classifier satisfies EXP-008 at every place type. -/
@[evidence holds EXP_008]
theorem EXP_008_reference {N : Type} [DecidableEq N] : EXP_008 (refPlaceCategory (N := N)) := by
  intro X env term p
  unfold refPlaceCategory
  cases term p <;> cases env p <;> cases HasOutputArc X p <;> cases HasInputArc X p <;>
    cases HasReadArc X p <;> simp +contextual

/-! ### The Rust shape and the open case -/

/-- The classifier of the Rust mapper (`analyze_places` and `place_category` in the crate
`libpetri-export`): only an input arc counts as outgoing. -/
def exp008_inputsOnly [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else if HasInputArc X p = false then .«end»
  else .place

/-- ✓ The Rust shape satisfies EXP-008 as ruling D51 (a) states it now: the common form. -/
@[evidence allows EXP_008]
theorem EXP_008_allows_inputsOnly : EXP_008 (exp008_inputsOnly (N := Nat)) := by
  intro X env term p
  unfold exp008_inputsOnly
  cases term p <;> cases env p <;> cases HasOutputArc X p <;> cases HasInputArc X p <;>
    cases HasReadArc X p <;> simp +contextual

/-- `w` outputs to place `0`; `r` reads place `0` and consumes nothing. -/
def exp008_readOnlyNet : Reference.Net Nat :=
  { places := [0]
    transitions :=
      [{ core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
         out := some (.place 0) },
       { core := { name := "r", inputs := [], inhibitors := [], reads := [0], resets := [] },
         out := none }] }

/-- The case the common form leaves open: a place that an output spec names and that only a read
arc touches on the consuming side is regular in the reference (Java, TypeScript, the end state
of D51) and end in the Rust shape, and both classifiers satisfy the block. -/
theorem EXP_008_readOnly_open :
    refPlaceCategory exp008_readOnlyNet (fun _ => false) (fun _ => false) 0 = .place ∧
    exp008_inputsOnly exp008_readOnlyNet (fun _ => false) (fun _ => false) 0 = .«end» := by
  decide

/-! ### Examples: wrong classifiers, one per line -/

/-- A classifier that tests environment before terminal. -/
def exp008_envFirst [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if env p then .environment else refPlaceCategory X env term p

/-- ✗ Letting environment beat terminal violates EXP-008 (line 1): a terminal environment place
is terminal. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_envFirst : ¬ EXP_008 (exp008_envFirst (N := Nat)) := by
  intro h
  have := (h { places := [0], transitions := [] } (fun _ => true) (fun _ => true) 0).1 rfl
  revert this
  decide

/-- A classifier that tests "no output arc" first, before terminal and environment. -/
def exp008_startFirst [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if HasOutputArc X p = false then .start else refPlaceCategory X env term p

/-- ✗ Letting start beat environment violates EXP-008 (line 2): an environment place that no
output spec names is environment. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_startFirst : ¬ EXP_008 (exp008_startFirst (N := Nat)) := by
  intro h
  have := (h { places := [0], transitions := [] } (fun _ => true) (fun _ => false) 0).2.1 rfl rfl
  revert this
  decide

/-- A classifier that tests end before start: a place with no arcs becomes end. -/
def exp008_endFirst [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasInputArc X p = false ∧ HasReadArc X p = false then .«end»
  else if HasOutputArc X p = false then .start
  else .place

/-- ✗ Testing end before start violates EXP-008 (line 3): a place with no arcs is start. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_endFirst : ¬ EXP_008 (exp008_endFirst (N := Nat)) := by
  intro h
  have := ((h { places := [0], transitions := [] } (fun _ => false) (fun _ => false) 0).2.2
    rfl rfl).1.2 (by decide)
  revert this
  decide

/-- Some transition of `X` has a reset arc on `p`. -/
def exp008_hasReset [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (ResetArc t p)

/-- A classifier that counts a reset arc as incoming, as the reset edge is drawn from the
transition to the place. -/
def exp008_resetIncoming [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false ∧ exp008_hasReset X p = false then .start
  else if HasInputArc X p = false ∧ HasReadArc X p = false then .«end»
  else .place

/-- `z` resets place `0`; nothing outputs to it. -/
def exp008_resetOnlyNet : Reference.Net Nat :=
  { places := [0]
    transitions :=
      [{ core := { name := "z", inputs := [], inhibitors := [], reads := [], resets := [0] },
         out := none }] }

/-- ✗ Counting a reset arc as incoming violates EXP-008 (line 3): a place that is only reset is
start. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_resetIncoming : ¬ EXP_008 (exp008_resetIncoming (N := Nat)) := by
  intro h
  have := ((h exp008_resetOnlyNet (fun _ => false) (fun _ => false) 0).2.2 rfl rfl).1.2
    (by decide)
  revert this
  decide

/-- Some transition of `X` has an inhibitor arc on `p`. -/
def exp008_hasInhibitor [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (InhibitorArc t p)

/-- A classifier that reads the glossary's arc directions: inhibitor and reset arcs go from the
place to the transition, so they count as outgoing. -/
def exp008_glossaryDirections [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else if HasInputArc X p = false ∧ HasReadArc X p = false ∧ exp008_hasInhibitor X p = false ∧
      exp008_hasReset X p = false then .«end»
  else .place

/-- `w` outputs to place `0`; `g` is inhibited by place `0`. -/
def exp008_inhibitedNet : Reference.Net Nat :=
  { places := [0]
    transitions :=
      [{ core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
         out := some (.place 0) },
       { core := { name := "g", inputs := [], inhibitors := [0], reads := [], resets := [] },
         out := none }] }

/-- ✗ Counting an inhibitor arc as outgoing violates EXP-008 (line 4): a place that is written
and only inhibits is end. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_glossaryDirections :
    ¬ EXP_008 (exp008_glossaryDirections (N := Nat)) := by
  intro h
  have := ((h exp008_inhibitedNet (fun _ => false) (fun _ => false) 0).2.2 rfl rfl).2.1
    (by decide) (by decide) (by decide)
  revert this
  decide

/-- A classifier that reads "end" as "has an incoming arc": every place an output spec names
is end. -/
def exp008_everyWrittenEnd [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else .«end»

/-- `a` consumes place `0` and outputs to place `1`; `b` consumes place `1`. -/
def exp008_chainNet : Reference.Net Nat :=
  { places := [0, 1]
    transitions :=
      [{ core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
         out := some (.place 1) },
       { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
         out := none }] }

/-- ✗ Drawing a written and consumed place as end violates EXP-008 (line 5). -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_everyWrittenEnd : ¬ EXP_008 (exp008_everyWrittenEnd (N := Nat)) := by
  intro h
  have := ((h exp008_chainNet (fun _ => false) (fun _ => false) 1).2.2 rfl rfl).2.2.1
    (by decide)
  revert this
  decide

/-- A classifier that draws a regular place with another row of the node table, the
interface-port row: the documentation generators' restyling of a subnet's port places moved
into the mapper and applied to every regular place. -/
def exp008_otherRow [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  match refPlaceCategory X env term p with
  | .place => .interfacePort
  | c => c

/-- ✗ Drawing an ordinary place with a row other than start, end and place violates EXP-008
(line 6). -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_otherRow : ¬ EXP_008 (exp008_otherRow (N := Nat)) := by
  intro h
  have := ((h exp008_chainNet (fun _ => false) (fun _ => false) 1).2.2 rfl rfl).2.2.2.1
  revert this
  decide

/-- Some transition of `X` that has an output spec reads `p`. -/
def exp008_readByWriter [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => t.out.isSome && decide (ReadArc t p)

/-- A classifier whose read loop sits inside the output-spec block, so a read arc counts as
outgoing only when the reading transition has an output spec: the Rust shape when the reader
writes nothing, the Java and TypeScript shape when it writes elsewhere. -/
def exp008_readByWriterOnly [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else if HasInputArc X p = false ∧ exp008_readByWriter X p = false then .«end»
  else .place

/-- `w` outputs to place `0`; `r` reads place `0` and outputs to place `1`. -/
def exp008_readerWritesNet : Reference.Net Nat :=
  { places := [0, 1]
    transitions :=
      [{ core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
         out := some (.place 0) },
       { core := { name := "r", inputs := [], inhibitors := [], reads := [0], resets := [] },
         out := some (.place 1) }] }

/-- ✗ Mixing the two shapes by whether the reader writes elsewhere violates EXP-008 (line 7):
place `0` has an output arc, a read arc and no input arc in both `exp008_readOnlyNet` and
`exp008_readerWritesNet`, and the classifier answers end in the first and place in the
second. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_readByWriter : ¬ EXP_008 (exp008_readByWriterOnly (N := Nat)) := by
  intro h
  have := ((h exp008_readOnlyNet (fun _ => false) (fun _ => false) 0).2.2 rfl rfl).2.2.2.2
    (by decide) (by decide) (by decide) exp008_readerWritesNet (fun _ => false) (fun _ => false) 0
    rfl rfl (by decide) (by decide) (by decide)
  revert this
  decide

/-- Some transition of `X` reads `p` and has no output arc on `p`. -/
def exp008_foreignRead [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t => decide (ReadArc t p) && !decide (OutputArc t p)

/-- A classifier that skips a read self-loop (a transition that reads and writes the place)
when it marks a place outgoing. -/
def exp008_selfReadSkipped [DecidableEq N] : PlaceClassifier N := fun X env term p =>
  if term p then .terminal
  else if env p then .environment
  else if HasOutputArc X p = false then .start
  else if HasInputArc X p = false ∧ exp008_foreignRead X p = false then .«end»
  else .place

/-- `w` reads place `0` and outputs to place `0`: a read self-loop and nothing else. -/
def exp008_selfReadNet : Reference.Net Nat :=
  { places := [0]
    transitions :=
      [{ core := { name := "w", inputs := [], inhibitors := [], reads := [0], resets := [] },
         out := some (.place 0) }] }

/-- ✗ Mixing the two shapes by whether the reader is the place's own writer violates EXP-008
(line 7): place `0` has an output arc, a read arc and no input arc in both `exp008_selfReadNet`
and `exp008_readOnlyNet`, and the classifier answers end in the first and place in the
second. -/
@[evidence forbids EXP_008]
theorem EXP_008_forbids_selfReadSkipped : ¬ EXP_008 (exp008_selfReadSkipped (N := Nat)) := by
  intro h
  have := ((h exp008_selfReadNet (fun _ => false) (fun _ => false) 0).2.2 rfl rfl).2.2.2.2
    (by decide) (by decide) (by decide) exp008_readOnlyNet (fun _ => false) (fun _ => false) 0
    rfl rfl (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### The style table: AC1 and AC2 -/

/-- AC1, AC2 and the transition bullet, on the generated style table: the start row and the end
row differ from every other place row, and every place row differs from the transition row.
Any two of the six rows differ. -/
theorem EXP_008_rows_distinct :
    [NodeCat.terminal, .environment, .start, .«end», .place, .transition].Pairwise
      (fun a b => nodeStyle a ≠ nodeStyle b) := by
  decide

/-! ### Non-vacuity -/

/-- The example net of the test derivation: `a` consumes place `0` and outputs to place `1`;
`b` consumes `1`, is inhibited by `5` and outputs to `2` and `4`; `c` consumes the environment
place `3`. Place `4` is terminal. -/
def exp008_exampleNet : Reference.Net Nat :=
  { places := [0, 1, 2, 3, 4, 5]
    transitions :=
      [{ core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
         out := some (.place 1) },
       { core := { name := "b", inputs := [⟨1, .one⟩], inhibitors := [5], reads := [], resets := [] },
         out := some (.and (.place 2) (.place 4)) },
       { core := { name := "c", inputs := [⟨3, .one⟩], inhibitors := [], reads := [], resets := [] },
         out := none }] }

/-- The test derivation on the reference classifier: the net has a start place (`0`), a regular
place (`1`), an end place (`2`), an environment place (`3`), a terminal place (`4`) and a place
that only an inhibitor arc touches, which is start (`5`); and the start and end rows it draws
differ from the regular place row. -/
@[evidence nonvacuous EXP_008]
theorem EXP_008_nonvacuous :
    let C := refPlaceCategory exp008_exampleNet (fun p => p == 3) (fun p => p == 4)
    C 0 = .start ∧ C 1 = .place ∧ C 2 = .«end» ∧ C 3 = .environment ∧ C 4 = .terminal ∧
      C 5 = .start ∧ nodeStyle (C 0) ≠ nodeStyle (C 1) ∧ nodeStyle (C 2) ≠ nodeStyle (C 1) := by
  decide

end Libpetri.Spec
