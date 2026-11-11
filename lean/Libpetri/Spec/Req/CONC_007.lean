import Libpetri.Spec.Registry
import Libpetri.Reference.Compiled

set_option linter.missingDocs true

/-!
# CONC-007: Compiled net representation (`spec/05-concurrency.md`)

CONC-007 is a pure-function requirement (kind F) over an abstract compile function
`Cmp : (Trans N → Bool) → Net N → CompiledNet N` (`Reference/Compiled.lean`): what the
integer-indexed form of a net holds, given the net and the match predicate `hm` (which of its
transitions carry a match specification). Seven lines, one per part of the compiled net: the
place IDs are a bijection between the places of the net and `0 … P-1`; the transition IDs are
declaration positions; the needs-mask and the inhibitor-mask are exact, with no bit at or above
`P`; the consumption places are exactly the input and reset places; the reverse index is exactly
the arc-place relation; a transition without a cardinality check needs no count beyond presence,
and a cardinality check lists exactly input places with their required counts and covers every
input that needs more than one token; and the match flag of a transition is set exactly when the
transition carries a match specification.

The witness is the reference compiler `refCompileWith`. Wrong compilers are killed by mutants: an
ID range with one ID too many, transitions numbered in reverse, a needs-mask that also holds the
reset places, an inhibitor-mask that also holds the read places, a needs bit one past the last
place ID, consumption places without the reset places, a reverse index without the inhibitor
places, a reverse index that also holds the output places, a cardinality check with every count
1, a compiler that sets every match flag, and one that sets none. Further wrong compilers are
forbidden outright: two places with one ID, a place index without the output places, a
needs-mask without the read places, consumption places with the read places, and no cardinality
check at all. The presence check on the compiled masks answers what CONC-004's presence check
answers (`conc007_presence_iff`), for every compiler that satisfies the block.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The seven lines, named -/

section Lines

variable {N : Type}

/-- Line 1 of CONC-007: the place IDs. A place has ID `i` exactly when `i` is below `P` and `i`
names the place; every number below `P` names a place; a name has an ID exactly when it is a
place of the net. -/
def conc007_line1 (n : Reference.Net N) (c : CompiledNet N) : Prop :=
  (∀ p i, c.placeId p = some i ↔ i < c.placeCount ∧ c.placeAt i = some p) ∧
  (∀ i, (c.placeAt i).isSome ↔ i < c.placeCount) ∧
  (∀ p, (c.placeId p).isSome ↔ p ∈ netPlaceList n)

/-- Line 2 of CONC-007: the transition with ID `j` is the `j`-th declared transition. -/
def conc007_line2 (n : Reference.Net N) (c : CompiledNet N) : Prop :=
  c.trans = n.transitions

/-- Line 3 of CONC-007 at the place IDs: the needs-mask and the inhibitor-mask are exact there. -/
def conc007_line3_atIds (c : CompiledNet N) : Prop :=
  ∀ j t i p, c.trans[j]? = some t → c.placeAt i = some p →
    (c.needs j i = true ↔ NeedsMask t p) ∧ (c.inhibitor j i = true ↔ InhibitorMask t p)

/-- Line 3 of CONC-007 beyond the place IDs: no mask of a transition ID has a bit at or above
`P`. -/
def conc007_line3_outside (c : CompiledNet N) : Prop :=
  ∀ j i, j < c.transCount → c.placeCount ≤ i → c.needs j i = false ∧ c.inhibitor j i = false

/-- Line 3 of CONC-007: the needs-mask and the inhibitor-mask are exact, at every number. -/
def conc007_line3 (c : CompiledNet N) : Prop :=
  conc007_line3_atIds c ∧ conc007_line3_outside c

/-- Line 4 of CONC-007: the consumption places are exactly the input and reset places. -/
def conc007_line4 (c : CompiledNet N) : Prop :=
  ∀ j t i, c.trans[j]? = some t →
    (i ∈ c.consumption j ↔ ∃ p, c.placeAt i = some p ∧ (p ∈ inPlaces t ∨ ResetArc t p))

/-- Line 5 of CONC-007: the reverse index is exactly the arc-place relation. -/
def conc007_line5 (c : CompiledNet N) : Prop :=
  ∀ i p j, c.placeAt i = some p →
    (j ∈ c.affected i ↔ ∃ t, c.trans[j]? = some t ∧ ArcPlace t p)

/-- Line 6 of CONC-007: the cardinality check. Without one, every input needs at most one token;
with one, every entry is an input place's ID with that input's required count, and every input
that needs more than one token has its entry. -/
def conc007_line6 (c : CompiledNet N) : Prop :=
  ∀ j t, c.trans[j]? = some t →
    (c.card j = none → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1) ∧
    (∀ l, c.card j = some l →
      (∀ e ∈ l, ∃ s ∈ t.core.inputs, c.placeId s.place = some e.1 ∧ e.2 = requiredCount s.card) ∧
      (∀ s ∈ t.core.inputs, 1 < requiredCount s.card →
        ∃ i, c.placeId s.place = some i ∧ (i, requiredCount s.card) ∈ l))

/-- Line 7 of CONC-007: the match flag of the transition `t` with ID `j` is set exactly when `t`
carries a match specification, `hm t`. -/
def conc007_line7 (hm : Trans N → Bool) (c : CompiledNet N) : Prop :=
  ∀ j t, c.trans[j]? = some t → c.hasMatch j = hm t

end Lines

/-! ## CONC-007: Compiled Net Representation -/

requirement CONC_007
  id "CONC-007"
  title "Compiled Net Representation"
  kind F
  scope "all compilers of the bitmap executor's compiled net (Rust CompiledNet::compile, Java CompiledNet.compile, TypeScript CompiledNet.compile), on every net, read as its arcs and output specifications together with which of its transitions carry a match specification"
  source verbatim "spec/05-concurrency.md"
  quote "The compiled net *shall* number the places of the net from 0 to P-1, where P is the number of places of the net, so that each place has exactly one ID and each ID names exactly one place."
        "The compiled net *shall* give each transition its declaration position as its ID, numbering the transitions from 0 in the order the net declares them."
        "The needs-mask of a transition *shall* hold exactly the IDs of its input and read places, and its inhibitor-mask exactly the IDs of its inhibitor places."
        "The consumption places of a transition *shall* be exactly the IDs of its input and reset places."
        "The reverse index *shall* map the ID of each place to exactly the IDs of the transitions that have an input, read, inhibitor or reset arc on that place."
        "*If* a transition has no cardinality check, *then* each of its inputs *shall* require at most one token."
        "Each entry of a cardinality check *shall* be the ID of an input place of the transition with the required count of that input, and each input that requires more than one token *shall* have an entry."
        "The compiled net *shall* set the match presence flag of a transition exactly when the transition carries a match specification ([NU-020])."
  reading "For every compile function Cmp, every match predicate hm (hm t: the transition t carries a match specification) and every net n, with c the compiled net Cmp hm n:"
          "(line 1) a place p has ID i exactly when i < P and i names p; every i < P names a place; a name has an ID exactly when it is a place of n (netPlaceList n: its declared places and every place an arc or the output specification of a transition names);"
          "(line 2) the transitions of c, indexed by ID, are the transitions of n in declaration order;"
          "(line 3) for the transition t with ID j and the place p with ID i, bit i of j's needs-mask is set exactly when p is an input or read place of t (NeedsMask), and bit i of j's inhibitor-mask exactly when p is an inhibitor place of t (InhibitorMask); for every transition ID j and every i at or above P, neither mask of j has bit i set;"
          "(line 4) for the transition t with ID j, i is among j's consumption places exactly when i names an input or reset place of t;"
          "(line 5) for the place p with ID i, j is in i's reverse index exactly when j is the ID of a transition t that has p as an arc place (ArcPlace: an input, read, inhibitor or reset arc);"
          "(line 6) for the transition t with ID j: if j has no cardinality check, every input of t requires at most one token; if it has one, every entry is (ID of an input place of t, required count of that input), and every input that requires more than one token has its entry;"
          "(line 7) for the transition t with ID j, j's match flag is hm t."
  assumes "A compile function is read as a function from a match predicate and a net to a CompiledNet (Reference/Compiled.lean): place count P, ID lookup placeId, ID-to-place map placeAt, transitions by ID, needs and inhibitor masks as bit functions over (transition ID, place ID), consumption places and reverse index as lists, a cardinality check as an optional list of (place ID, required count), and a match flag. Only membership of the lists is stated: their order and repetitions are not normative (all three collect a transition once per arc and then de-duplicate the reverse index: Rust through a hash set, whose iteration order is not fixed, rust/libpetri-runtime/src/compiled_net.rs:110; Java with distinct(), java/src/main/java/org/libpetri/runtime/CompiledNet.java:237-245; TypeScript through a Set, typescript/src/runtime/compiled-net.ts:203-207)."
          "The masks are stated at every number for every transition ID: at a place ID by NeedsMask and InhibitorMask, and at a number at or above P they hold no bit, which is what 'exactly the IDs' says. The runtimes test the masks word by word over all ceil(P/ws) words (rust/libpetri-runtime/src/bitmap.rs contains_all; Java and TypeScript compare whole long and Uint32 words), so a stray needs bit at or above P would leave its transition never enabled. A compiler whose needs-masks also set bit P meets line 3 at the place IDs and is killed (CONC_007_mutant_padBit_killed). Bits under a number that is no transition ID belong to no mask and are not stated."
          "A net with match specifications is read as its Reference.Net, which holds every arc and output specification of its transitions, together with the match predicate hm: hm t holds exactly when t carries a match specification. The compiled net holds nothing of a match specification but its flag, so lines 1 to 6 state the compiled net of every net, with or without match specifications, and line 7 states both halves of the match-flag sentence. The predicate is over transition values, so two transitions that are equal as values (same name, same arcs) get one flag; a net in which only one of two such transitions carries a match specification is out of scope. That the ν-net model gives hm as the presence of its match specification is NU-020's line (W9), which instantiates this block at that predicate. Rust (rust/libpetri-runtime/src/compiled_net.rs:52 and :120), TypeScript (typescript/src/runtime/compiled-net.ts:65 and :138) and Java's PrecompiledNet (java/src/main/java/org/libpetri/runtime/PrecompiledNet.java:96 and :253) store the flag; Java's bitmap CompiledNet stores none and its executor reads the flag as compiled.transition(j).matchSpec() != null (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java:428 and :1381), a value of the compiled net's transition at ID j, which meets line 7 because line 2 fixes that transition. Whether the flag is computed at compile time or read on demand is AC2's question (kind Q) and is not stated. A compiler that sets every flag is killed on a net without match specifications (CONC_007_mutant_noMatchLine_killed), and a compiler that sets no flag, which meets the half 'no flag without a match specification', is killed on a net whose transitions carry one (CONC_007_mutant_noFlagSet_killed)."
          "'The places of the net' are read as netPlaceList n. The runtimes compile nets whose declared places include every arc place and every place of an output specification: every net builder output does (CORE-040 line 2). Rust's PetriNet::map_transitions can return a net that breaks this, against its documented unchecked precondition (rust/libpetri-core/src/petri_net.rs:157-174); Rust numbers places from net.places() alone (rust/libpetri-runtime/src/compiled_net.rs:68-75) and panics at compile on an arc place it did not number (:124), so such a net is out of scope. On a net built by the reference net builder these are exactly the built net's places (netPlaceList_built, refCompileWith_placeCount_built in Reference/Compiled.lean), the places the builder collected from the declared places, the arcs and the output specifications. A compiler that leaves out the output specifications gives no ID to a place that is only deposited into and is forbidden (CONC_007_forbids_noOutputPlaces)."
          "'Stable' is read as ruling D55 (a): the IDs are fixed for the life of the compiled net. In Lean this holds by type: a compiled net is an immutable value and its IDs are fields of it. The order in which places are numbered is not stated (line 1 fixes a bijection onto 0 to P-1, not which one): Rust sorts the place names, Java and TypeScript number places by first use, and the reference keeps the order List.dedup leaves. Transition numbering is fixed: the ID is the declaration position (line 2), as the EXEC-002 block numbers transitions. A compiler that numbers the transitions in another order, here in reverse, meets every other line and is killed (CONC_007_mutant_permTrans_killed)."
          "The reset-mask of the original body is replaced by the consumption places (ruling D55 (a)): Rust and TypeScript keep no reset-mask, and the one Java builds is read by no executor (java/src/main/java/org/libpetri/runtime/CompiledNet.java resetMask). The consumption places are what the three compilers keep (rust/libpetri-runtime/src/compiled_net.rs consumption_place_ids, typescript/src/runtime/compiled-net.ts _consumptionPlaceIds, java CompiledNet consumptionPlaceIds). A needs-mask that also holds the reset places (the reset-mask folded into needs) is killed (CONC_007_mutant_resetNeeds_killed): a reset never gates its transition (CORE-034). An inhibitor-mask that also holds the read places is killed (CONC_007_mutant_readInhibitor_killed), and a needs-mask without the read places and consumption places that hold the read places are forbidden (CONC_007_forbids_noReadNeeds, CONC_007_forbids_readConsumption): a read arc gates its transition and never consumes."
          "Line 5 is CONC-005's 'affected transitions': a transition that only deposits into a place is not in its reverse index, and an inhibitor arc puts its transition in the index (all three runtimes add it, so that a token landing on an inhibitor place re-checks the transition). The reading without the inhibitor places is killed (CONC_007_mutant_noInhibitorAffected_killed), and so is the reading that also lists a transition under the places it deposits into (CONC_007_mutant_outputAffected_killed)."
          "Line 6 is the weak form both runtime choices meet: Rust and TypeScript give a cardinality check to a transition with any input that is not One, and list every input; Java gives one only for a required count above 1, All or AtLeast, and lists every input. Both satisfy the block (CONC_007_reference, CONC_007_allows_javaCard). The cardinality bullet ('needed for a transition with an input that requires more than one token') is read with the presence bit: it already shows one token, so an input of required count at most 1 (One, All, Exactly 0 or 1, AtLeast 0 or 1) needs no count check. That phase 2 then answers what the cardinality check of the glossary answers is CONC-008's line, not restated here. A check whose entries carry count 1 meets the first half of line 6 and is killed by the second (CONC_007_mutant_unitCounts_killed); a compiler that builds no cardinality check at all is killed by the first (CONC_007_forbids_noCard)."
          "The presence check on the compiled masks, over the presence bitmap indexed by place ID, answers what CONC-004's presence check (MaskCheck) answers on the bitmap by name, for every compiler that satisfies the block (conc007_presence_iff). The body's 'This enables array-based access instead of hash map lookups' is the reason for the representation, a quality property, and is not encoded."
          "AC1 (places and transitions have stable numeric IDs) is lines 1 and 2, with 'stable' read as above. A compiler that gives two places one ID violates line 1 (CONC_007_forbids_mergedIds), and so does one whose ID range has an ID too many (CONC_007_mutant_noRange_killed)."
          "AC2 (all masks are precomputed at compilation time, not at each enablement check) is a quality property of when the masks are computed and is not encoded: the block states what the compiled net holds, a function of the net alone. The test derivation (compile a net and verify that the masks match the expected bit patterns) is CONC_007_nonvacuous on a seven-place, two-transition net."
  signoff "pending"
  statement : ∀ {N : Type}, ((Trans N → Bool) → Reference.Net N → CompiledNet N) → Prop :=
    fun Cmp => ∀ hm n,
      ((∀ p i, (Cmp hm n).placeId p = some i ↔
          i < (Cmp hm n).placeCount ∧ (Cmp hm n).placeAt i = some p) ∧
        (∀ i, ((Cmp hm n).placeAt i).isSome ↔ i < (Cmp hm n).placeCount) ∧
        (∀ p, ((Cmp hm n).placeId p).isSome ↔ p ∈ netPlaceList n)) ∧
      (Cmp hm n).trans = n.transitions ∧
      ((∀ j t i p, (Cmp hm n).trans[j]? = some t → (Cmp hm n).placeAt i = some p →
          ((Cmp hm n).needs j i = true ↔ NeedsMask t p) ∧
          ((Cmp hm n).inhibitor j i = true ↔ InhibitorMask t p)) ∧
        (∀ j i, j < (Cmp hm n).transCount → (Cmp hm n).placeCount ≤ i →
          (Cmp hm n).needs j i = false ∧ (Cmp hm n).inhibitor j i = false)) ∧
      (∀ j t i, (Cmp hm n).trans[j]? = some t →
        (i ∈ (Cmp hm n).consumption j ↔
          ∃ p, (Cmp hm n).placeAt i = some p ∧ (p ∈ inPlaces t ∨ ResetArc t p))) ∧
      (∀ i p j, (Cmp hm n).placeAt i = some p →
        (j ∈ (Cmp hm n).affected i ↔ ∃ t, (Cmp hm n).trans[j]? = some t ∧ ArcPlace t p)) ∧
      (∀ j t, (Cmp hm n).trans[j]? = some t →
        ((Cmp hm n).card j = none → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1) ∧
        (∀ l, (Cmp hm n).card j = some l →
          (∀ e ∈ l, ∃ s ∈ t.core.inputs,
            (Cmp hm n).placeId s.place = some e.1 ∧ e.2 = requiredCount s.card) ∧
          (∀ s ∈ t.core.inputs, 1 < requiredCount s.card →
            ∃ i, (Cmp hm n).placeId s.place = some i ∧ (i, requiredCount s.card) ∈ l))) ∧
      (∀ j t, (Cmp hm n).trans[j]? = some t → (Cmp hm n).hasMatch j = hm t)

/- The pinned readable form of CONC-007: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_007 : {N : Type} → ((Reference.Trans N → Bool) → Reference.Net N → CompiledNet N) → Prop :=
fun {N} Cmp =>
  ∀ (hm : Reference.Trans N → Bool) (n : Reference.Net N),
    ((∀ (p : N) (i : ℕ), (Cmp hm n).placeId p = some i ↔ i < (Cmp hm n).placeCount ∧ (Cmp hm n).placeAt i = some p) ∧
        (∀ (i : ℕ), ((Cmp hm n).placeAt i).isSome = true ↔ i < (Cmp hm n).placeCount) ∧
          ∀ (p : N), ((Cmp hm n).placeId p).isSome = true ↔ p ∈ netPlaceList n) ∧
      (Cmp hm n).trans = n.transitions ∧
        ((∀ (j : ℕ) (t : Reference.Trans N) (i : ℕ) (p : N),
              (Cmp hm n).trans[j]? = some t →
                (Cmp hm n).placeAt i = some p →
                  ((Cmp hm n).needs j i = true ↔ NeedsMask t p) ∧
                    ((Cmp hm n).inhibitor j i = true ↔ InhibitorMask t p)) ∧
            ∀ (j i : ℕ),
              j < (Cmp hm n).transCount →
                (Cmp hm n).placeCount ≤ i → (Cmp hm n).needs j i = false ∧ (Cmp hm n).inhibitor j i = false) ∧
          (∀ (j : ℕ) (t : Reference.Trans N) (i : ℕ),
              (Cmp hm n).trans[j]? = some t →
                (i ∈ (Cmp hm n).consumption j ↔ ∃ p, (Cmp hm n).placeAt i = some p ∧ (p ∈ inPlaces t ∨ ResetArc t p))) ∧
            (∀ (i : ℕ) (p : N) (j : ℕ),
                (Cmp hm n).placeAt i = some p →
                  (j ∈ (Cmp hm n).affected i ↔ ∃ t, (Cmp hm n).trans[j]? = some t ∧ ArcPlace t p)) ∧
              (∀ (j : ℕ) (t : Reference.Trans N),
                  (Cmp hm n).trans[j]? = some t →
                    ((Cmp hm n).card j = none → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1) ∧
                      ∀ (l : List (ℕ × ℕ)),
                        (Cmp hm n).card j = some l →
                          (∀ e ∈ l,
                              ∃ s ∈ t.core.inputs, (Cmp hm n).placeId s.place = some e.1 ∧ e.2 = requiredCount s.card) ∧
                            ∀ s ∈ t.core.inputs,
                              1 < requiredCount s.card →
                                ∃ i, (Cmp hm n).placeId s.place = some i ∧ (i, requiredCount s.card) ∈ l) ∧
                ∀ (j : ℕ) (t : Reference.Trans N), (Cmp hm n).trans[j]? = some t → (Cmp hm n).hasMatch j = hm t
-/
#guard_msgs in #print CONC_007

/-- CONC-007 is its seven lines, for every match predicate and every net. -/
theorem conc007_iff {N : Type} (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    CONC_007 Cmp ↔ ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧
      conc007_line3 (Cmp hm n) ∧ conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧
      conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n) :=
  Iff.rfl

/-! ### The reference -/

section Reference

variable {N : Type} [DecidableEq N]

/-- Line 1 holds of the reference compiler, with any match flag. -/
theorem conc007_refWith_line1 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line1 n (refCompileWith hm n) :=
  ⟨fun _ _ => refCompileWith_placeId_iff, fun _ => refCompileWith_placeAt_isSome,
    fun _ => refCompileWith_placeId_isSome⟩

/-- Line 3 holds of the reference compiler, with any match flag. -/
theorem conc007_refWith_line3 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line3 (refCompileWith hm n) :=
  ⟨fun _ _ _ _ ht hp => ⟨refCompileWith_needs_at ht hp, refCompileWith_inhibitor_at ht hp⟩,
    fun _ _ _ hi => refCompileWith_needs_outside (.inr hi)⟩

/-- Line 4 holds of the reference compiler, with any match flag. -/
theorem conc007_refWith_line4 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line4 (refCompileWith hm n) := by
  intro j t i ht
  have ht : n.transitions[j]? = some t := ht
  rw [refCompileWith_mem_consumption]
  constructor
  · rintro ⟨t', p, ht', hp, h⟩
    rw [ht] at ht'; cases ht'
    exact ⟨p, hp, h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨t, p, ht, hp, h⟩

/-- Line 5 holds of the reference compiler, with any match flag. -/
theorem conc007_refWith_line5 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line5 (refCompileWith hm n) := by
  intro i p j hp
  rw [refCompileWith_mem_affected]
  constructor
  · rintro ⟨t, p', ht, hp', h⟩
    rw [hp] at hp'; cases hp'
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, p, ht, hp, h⟩

/-- Line 6 holds of the reference compiler, with any match flag. -/
theorem conc007_refWith_line6 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line6 (refCompileWith hm n) := by
  intro j t ht
  have ht : n.transitions[j]? = some t := ht
  refine ⟨fun h s hs => ?_, fun l hl => ⟨fun e he => refCompileWith_card_entry ht hl he,
    fun s hs _ => ?_⟩⟩
  · rw [(refCompileWith_card_none_iff ht).1 h s hs]
    decide
  · rw [refCompileWith_card ht] at hl
    split at hl
    · cases hl
    · cases hl
      have hm' : s.place ∈ netPlaceList n :=
        mem_netPlaceList_of_arc (List.mem_of_getElem? ht) (.inl (List.mem_map_of_mem hs))
      exact ⟨_, refCompileWith_placeId_of_mem hm',
        List.mem_map_of_mem (f := fun (s : NInSpec N) =>
          ((refPlaceIndex n).idx s.place, requiredCount s.card)) hs⟩

/-- Line 7 holds of the reference compiler: its match flag is the flag function it is given. -/
theorem conc007_refWith_line7 (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line7 hm (refCompileWith hm n) :=
  fun _ _ ht => refCompileWith_hasMatch ht

/-- Lines 1 to 6 hold of the reference compiler, with any match flag. -/
theorem conc007_refWith_lines (hm : Trans N → Bool) (n : Reference.Net N) :
    conc007_line1 n (refCompileWith hm n) ∧ conc007_line2 n (refCompileWith hm n) ∧
      conc007_line3 (refCompileWith hm n) ∧ conc007_line4 (refCompileWith hm n) ∧
      conc007_line5 (refCompileWith hm n) ∧ conc007_line6 (refCompileWith hm n) :=
  ⟨conc007_refWith_line1 hm n, rfl, conc007_refWith_line3 hm n, conc007_refWith_line4 hm n,
    conc007_refWith_line5 hm n, conc007_refWith_line6 hm n⟩

/-- ✓ The reference compiler satisfies CONC-007: its place index is `flatIndex` over the places
of the net, its transitions are the net's in declaration order, its masks, consumption places,
reverse index and cardinality checks are those of `Reference/Compiled.lean`, its masks hold no
bit at or above `P`, and its match flag is the match predicate it is given. -/
@[evidence holds CONC_007]
theorem CONC_007_reference : CONC_007 (refCompileWith (N := N)) := fun hm n =>
  let h := conc007_refWith_lines hm n
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, conc007_refWith_line7 hm n⟩

end Reference

/-! ### The link to CONC-004 -/

/-- **The presence check on the compiled masks is CONC-004's presence check.** For every compiler
that satisfies CONC-007 and the transition `t` with ID `j`, the presence check on `j`'s compiled
masks over the presence bitmap indexed by place ID passes exactly when the presence check of `t`
passes on the bitmap by name. -/
@[evidence cites "CONC-004" "the presence check on the compiled masks, over the bitmap indexed by place ID, passes exactly when every needs-mask bit is set and no inhibitor-mask bit is set"]
theorem conc007_presence_iff {N : Type} {Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N}
    (h : CONC_007 Cmp) (hm : Trans N → Bool) (n : Reference.Net N) {j : Nat} {t : Trans N}
    (ht : (Cmp hm n).trans[j]? = some t) (bits : N → Bool) :
    (Cmp hm n).presence j ((Cmp hm n).indexBits bits) = true ↔ MaskCheck t bits := by
  obtain ⟨⟨h1a, h1b, h1c⟩, h2, ⟨h3, -⟩, -⟩ := h hm n
  have htm : t ∈ n.transitions := by rw [← h2]; exact List.mem_of_getElem? ht
  have hid : ∀ p, p ∈ netPlaceList n →
      ∃ i, i < (Cmp hm n).placeCount ∧ (Cmp hm n).placeAt i = some p := fun p hp => by
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((h1c p).2 hp)
    exact ⟨i, (h1a p i).1 hi⟩
  simp only [CompiledNet.presence, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro hall
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨i, hi, hpa⟩ := hid p
        (mem_netPlaceList_of_arc htm (hp.elim (fun h => .inl h) (fun h => .inr (.inl h))))
      have hb := (hall i hi).1
      rw [((h3 j t i p ht hpa).1).2 hp] at hb
      simpa [CompiledNet.indexBits, hpa] using hb
    · obtain ⟨i, hi, hpa⟩ := hid p (mem_netPlaceList_of_arc htm (.inr (.inr (.inl hp))))
      have hb := (hall i hi).2
      rw [((h3 j t i p ht hpa).2).2 hp] at hb
      simpa [CompiledNet.indexBits, hpa] using hb
  · rintro ⟨hn, hh⟩ i hi
    obtain ⟨p, hpa⟩ := Option.isSome_iff_exists.1 ((h1b i).2 hi)
    have hib : (Cmp hm n).indexBits bits i = bits p := by simp [CompiledNet.indexBits, hpa]
    rw [hib]
    constructor
    · by_cases hq : NeedsMask t p
      · exact .inr (hn p hq)
      · left
        cases hc : (Cmp hm n).needs j i
        · rfl
        · exact absurd (((h3 j t i p ht hpa).1).1 hc) hq
    · by_cases hq : InhibitorMask t p
      · exact .inr (hh p hq)
      · left
        cases hc : (Cmp hm n).inhibitor j i
        · rfl
        · exact absurd (((h3 j t i p ht hpa).2).1 hc) hq

/-! ### Examples -/

/-- The first transition of the example net: a `One` input on `0`, an `Exactly(2)` input on `1`,
a read arc on `2`, an inhibitor arc on `3`, a reset arc on `4`, and output `Place 5`. -/
def conc007_t1 : Trans Nat :=
  { core := { name := "t1", inputs := [⟨0, .one⟩, ⟨1, .exactly 2⟩], inhibitors := [3],
              reads := [2], resets := [4] },
    out := some (.place 5) }

/-- The second transition of the example net: a `One` input on `5`, and output `Place 6`. -/
def conc007_t2 : Trans Nat :=
  { core := { name := "t2", inputs := [⟨5, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 6) }

/-- The example net: places `0` to `6`, transitions `t1` and `t2`. -/
def conc007_net : Reference.Net Nat := ⟨[0, 1, 2, 3, 4, 5, 6], [conc007_t1, conc007_t2]⟩

/-- The match predicate under which only `t2` carries a match specification. -/
def conc007_hmT2 (t : Trans Nat) : Bool := t.core.name == "t2"

/-- The ID the reference compiler gives a place of the example net. -/
def conc007_id (p : Nat) : Nat := ((refCompileNet conc007_net).placeId p).getD 0

/-- Every place of the example net is the place with its ID. -/
theorem conc007_placeAt_id :
    ∀ p ∈ [0, 1, 2, 3, 4, 5, 6], (refCompileNet conc007_net).placeAt (conc007_id p) = some p := by
  decide

/-- ✓ Every line of CONC-007 is exercised by the reference on the example net (the test
derivation): seven place IDs; the transitions in declaration order; `t1`'s needs-mask holds its
input places `0`, `1` and its read place `2` but not its reset place `4`, its inhibitor-mask holds
`3`, and neither mask has bit `7 = P`; `t1`'s consumption places are `0`, `1` and the reset place
`4`, not the read place `2`; the reverse index of `3` (an inhibitor place) is `t1`, of `5`
(deposited by `t1`, consumed by `t2`) is `t2` alone, of `6` (only deposited) is empty; `t1`'s
cardinality check lists both inputs with their counts 1 and 2, `t2` has none; no match flag
without match specifications, and with `t2` carrying one exactly `t2`'s flag; and the presence
check on the compiled masks passes with `0`, `1`, `2` marked and fails once the inhibitor place
`3` is marked too. -/
@[evidence nonvacuous CONC_007]
theorem CONC_007_nonvacuous :
    (refCompileNet conc007_net).placeCount = 7 ∧
    ((refCompileNet conc007_net).trans.map (·.core.name)) = ["t1", "t2"] ∧
    ((refCompileNet conc007_net).needs 0 (conc007_id 0) = true ∧
      (refCompileNet conc007_net).needs 0 (conc007_id 1) = true ∧
      (refCompileNet conc007_net).needs 0 (conc007_id 2) = true ∧
      (refCompileNet conc007_net).needs 0 (conc007_id 4) = false ∧
      (refCompileNet conc007_net).needs 0 (conc007_id 3) = false ∧
      (refCompileNet conc007_net).inhibitor 0 (conc007_id 3) = true ∧
      (refCompileNet conc007_net).needs 0 7 = false ∧
      (refCompileNet conc007_net).inhibitor 0 7 = false) ∧
    (conc007_id 4 ∈ (refCompileNet conc007_net).consumption 0 ∧
      conc007_id 1 ∈ (refCompileNet conc007_net).consumption 0 ∧
      conc007_id 2 ∉ (refCompileNet conc007_net).consumption 0) ∧
    ((refCompileNet conc007_net).affected (conc007_id 3) = [0] ∧
      (refCompileNet conc007_net).affected (conc007_id 5) = [1] ∧
      (refCompileNet conc007_net).affected (conc007_id 6) = []) ∧
    ((refCompileNet conc007_net).card 0 = some [(conc007_id 0, 1), (conc007_id 1, 2)] ∧
      (refCompileNet conc007_net).card 1 = none) ∧
    ((refCompileNet conc007_net).hasMatch 0 = false ∧
      (refCompileNet conc007_net).hasMatch 1 = false ∧
      (refCompileWith conc007_hmT2 conc007_net).hasMatch 0 = false ∧
      (refCompileWith conc007_hmT2 conc007_net).hasMatch 1 = true) ∧
    ((refCompileNet conc007_net).presence 0
        ((refCompileNet conc007_net).indexBits fun p => decide (p < 3)) = true ∧
      (refCompileNet conc007_net).presence 0
        ((refCompileNet conc007_net).indexBits fun p => decide (p < 4)) = false) := by
  decide

/-! ### Violation: two places with one ID -/

/-- A compiler that gives every name the ID `0`, and is the reference otherwise. -/
def conc007_mergedCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with placeId := fun _ => some 0 }

/-- ✗ A compiler that gives two places one ID violates CONC-007 (line 1, AC1): places `0` and `1`
of the example net would both be the place with ID `0`. -/
@[evidence forbids CONC_007]
theorem CONC_007_forbids_mergedIds : ¬ CONC_007 (conc007_mergedCompile (N := Nat)) := fun h => by
  have a := ((h (fun _ => false) conc007_net).1.1 0 0).1 rfl
  have b := ((h (fun _ => false) conc007_net).1.1 1 0).1 rfl
  rw [a.2] at b
  exact absurd (Option.some.inj b.2) (by decide)

/-! ### Violation: a place index without the output places -/

/-- The net with every output specification removed. -/
def conc007_stripOut {N : Type} (n : Reference.Net N) : Reference.Net N :=
  ⟨n.places, n.transitions.map fun t => { t with out := none }⟩

/-- A compiler that collects the places from the declared places and the arcs only, leaving out
the output specifications (the Java or TypeScript compiler without its `allPlaces` of the output
specification), and is the reference otherwise. -/
def conc007_noOutCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm (conc007_stripOut n) with trans := n.transitions }

/-- A net that does not declare the place `1` its transition deposits into. -/
def conc007_outNet : Reference.Net Nat :=
  ⟨[0], [{ core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                      resets := [] },
            out := some (.place 1) }]⟩

/-- ✗ A compiler whose place index leaves out the output places violates CONC-007 (line 1): the
undeclared output place `1` is a place of the net and gets no ID, so the executor could not store
the token the transition produces. -/
@[evidence forbids CONC_007]
theorem CONC_007_forbids_noOutputPlaces : ¬ CONC_007 (conc007_noOutCompile (N := Nat)) :=
  fun h => by
    have := ((h (fun _ => false) conc007_outNet).1.2.2 1).2 (by decide)
    revert this
    decide

/-! ### Mutant: line 1 without the range `0 … P-1` -/

section MutantRange

variable {N : Type}

/-- Mutant reading of line 1: the ID lookup and the ID-to-place map are inverse and a name has an
ID exactly when it is a place of the net, but `P` need not be the number of places (an ID below
`P` may name no place). Lines 2 to 7 are as in CONC-007. -/
def CONC_007_mutant_noRange (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) : Prop :=
  ∀ hm n, ((∀ p i, (Cmp hm n).placeId p = some i ↔
        i < (Cmp hm n).placeCount ∧ (Cmp hm n).placeAt i = some p) ∧
      (∀ p, ((Cmp hm n).placeId p).isSome ↔ p ∈ netPlaceList n)) ∧
    conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧ conc007_line4 (Cmp hm n) ∧
    conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

end MutantRange

/-- A compiler whose place count is one more than the number of places, and is the reference
otherwise. -/
def conc007_padCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool) (n : Reference.Net N) :
    CompiledNet N :=
  { refCompileWith hm n with placeCount := (refCompileWith hm n).placeCount + 1 }

/-- The padding compiler kills the mutant: its ID lookup and ID-to-place map are the reference's,
so it meets the mutant reading, but on the empty net the ID `0` is below `P = 1` and names no
place (line 1). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_noRange_killed :
    CONC_007_mutant_noRange (conc007_padCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_padCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨⟨fun p i => ?_, h1.2.2⟩, h2,
      ⟨h3.1, fun j i hj hi => h3.2 j i hj (Nat.le_of_succ_le hi)⟩, h4, h5, h6, h7⟩
    show (refCompileWith hm n).placeId p = some i ↔
      i < (refCompileWith hm n).placeCount + 1 ∧ (refCompileWith hm n).placeAt i = some p
    rw [h1.1 p i]
    constructor
    · rintro ⟨hi, hp⟩; exact ⟨Nat.lt_succ_of_lt hi, hp⟩
    · rintro ⟨-, hp⟩
      exact ⟨(h1.2.1 i).1 (by rw [hp]; rfl), hp⟩
  · have := ((h (fun _ => false) ⟨[], []⟩).1.2.1 0).2 (by decide)
    revert this
    decide

/-! ### Mutant: transitions numbered in another order -/

section MutantPerm

variable {N : Type}

/-- Mutant reading of line 2: the transitions by ID are the net's transitions in some order.
Lines 1 and 3 to 7 are as in CONC-007. -/
def CONC_007_mutant_permTrans (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) : Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ (Cmp hm n).trans.Perm n.transitions ∧
    conc007_line3 (Cmp hm n) ∧ conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧
    conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

/-- A net with its transitions in reverse order. -/
def conc007_revNet (n : Reference.Net N) : Reference.Net N := ⟨n.places, n.transitions.reverse⟩

/-- Reversing the transitions keeps the places of the net. -/
theorem conc007_mem_revNet {n : Reference.Net N} {p : N} :
    p ∈ netPlaceList (conc007_revNet n) ↔ p ∈ netPlaceList n := by
  simp [mem_netPlaceList, conc007_revNet]

end MutantPerm

/-- A compiler that numbers the transitions in reverse declaration order: the reference compiler
on the reversed net. -/
def conc007_revCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool) (n : Reference.Net N) :
    CompiledNet N :=
  refCompileWith hm (conc007_revNet n)

/-- The reversing compiler kills the mutant: every part of it is consistent with its own
numbering, so it meets the mutant reading, but on the example net the transition with ID `0` is
`t2`, not `t1` (line 2). This numbering breaks EXEC-002's tie-break by declaration order. -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_permTrans_killed :
    CONC_007_mutant_permTrans (conc007_revCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_revCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm (conc007_revNet n)
    exact ⟨⟨h1.1, h1.2.1, fun p => (h1.2.2 p).trans conc007_mem_revNet⟩,
      List.reverse_perm _, h3, h4, h5, h6, h7⟩
  · have := congrArg (List.map (·.core.name)) (h (fun _ => false) conc007_net).2.1
    revert this
    decide

/-! ### Mutant: a needs-mask that also holds the reset places -/

section MutantReset

variable {N : Type}

/-- Mutant reading of line 3 (the body's reset-mask folded into the needs-mask): bit `i` of the
needs-mask is set exactly when `i` names an input, read or reset place. Lines 1, 2 and 4 to 7, and
line 3 beyond the place IDs, are as in CONC-007. -/
def CONC_007_mutant_resetNeeds (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧
    ((∀ j t i p, (Cmp hm n).trans[j]? = some t → (Cmp hm n).placeAt i = some p →
      ((Cmp hm n).needs j i = true ↔ NeedsMask t p ∨ ResetArc t p) ∧
      ((Cmp hm n).inhibitor j i = true ↔ InhibitorMask t p)) ∧
      conc007_line3_outside (Cmp hm n)) ∧
    conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n) ∧
    conc007_line7 hm (Cmp hm n)

end MutantReset

/-- A needs-mask that also holds the reset places. -/
def conc007_resetNeeds {N : Type} [DecidableEq N] (n : Reference.Net N) (j i : Nat) : Bool :=
  match n.transitions[j]?, (refPlaceIndex n).name? i with
  | some t, some p => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads ∨ p ∈ t.core.resets)
  | _, _ => false

/-- A compiler whose needs-mask also holds the reset places, and is the reference otherwise. -/
def conc007_resetNeedsCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with needs := conc007_resetNeeds n }

/-- The reset-needs compiler kills the mutant: it meets the mutant reading, but `t1`'s reset
place `4` is in its needs-mask, although a reset never gates its transition (line 3). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_resetNeeds_killed :
    CONC_007_mutant_resetNeeds (conc007_resetNeedsCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_resetNeedsCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, ⟨fun j t i p ht hp => ⟨?_, (h3.1 j t i p ht hp).2⟩,
      fun j i hj hi => ⟨?_, (h3.2 j i hj hi).2⟩⟩, h4, h5, h6, h7⟩
    · have ht : n.transitions[j]? = some t := ht
      have hp : (refPlaceIndex n).name? i = some p := hp
      show conc007_resetNeeds n j i = true ↔ _
      simp [conc007_resetNeeds, ht, hp, NeedsMask, ReadArc, ResetArc, or_assoc]
    · have hn : (refPlaceIndex n).name? i = none := (refPlaceIndex n).name?_eq_none_iff.2 hi
      show conc007_resetNeeds n j i = false
      unfold conc007_resetNeeds
      rw [hn]
      cases n.transitions[j]? <;> rfl
  · have hp4 : (conc007_resetNeedsCompile (fun _ => false) conc007_net).placeAt (conc007_id 4) =
        some 4 :=
      conc007_placeAt_id 4 (by decide)
    have := ((h (fun _ => false) conc007_net).2.2.1.1 0 conc007_t1 (conc007_id 4) 4 rfl hp4).1.1
      (by decide)
    simp [NeedsMask, inPlaces, ReadArc, conc007_t1] at this

/-! ### Mutant: an inhibitor-mask that also holds the read places -/

section MutantReadInh

variable {N : Type}

/-- Mutant reading of line 3 (read arcs and inhibitor arcs both test without consuming, and land
in one mask): bit `i` of the inhibitor-mask is set exactly when `i` names an inhibitor or read
place. Lines 1, 2 and 4 to 7, the needs half of line 3 and line 3 beyond the place IDs are as in
CONC-007. -/
def CONC_007_mutant_readInhibitor (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧
    ((∀ j t i p, (Cmp hm n).trans[j]? = some t → (Cmp hm n).placeAt i = some p →
      ((Cmp hm n).needs j i = true ↔ NeedsMask t p) ∧
      ((Cmp hm n).inhibitor j i = true ↔ InhibitorMask t p ∨ ReadArc t p)) ∧
      conc007_line3_outside (Cmp hm n)) ∧
    conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n) ∧
    conc007_line7 hm (Cmp hm n)

end MutantReadInh

/-- An inhibitor-mask that also holds the read places. -/
def conc007_readInh {N : Type} [DecidableEq N] (n : Reference.Net N) (j i : Nat) : Bool :=
  match n.transitions[j]?, (refPlaceIndex n).name? i with
  | some t, some p => decide (p ∈ t.core.inhibitors ∨ p ∈ t.core.reads)
  | _, _ => false

/-- A compiler whose inhibitor-mask also holds the read places, and is the reference
otherwise. -/
def conc007_readInhCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with inhibitor := conc007_readInh n }

/-- The read-inhibitor compiler kills the mutant: it meets the mutant reading, but `t1`'s read
place `2` is in its inhibitor-mask, so `t1` would be blocked by the very token its read arc needs
(line 3). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_readInhibitor_killed :
    CONC_007_mutant_readInhibitor (conc007_readInhCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_readInhCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, ⟨fun j t i p ht hp => ⟨(h3.1 j t i p ht hp).1, ?_⟩,
      fun j i hj hi => ⟨(h3.2 j i hj hi).1, ?_⟩⟩, h4, h5, h6, h7⟩
    · have ht : n.transitions[j]? = some t := ht
      have hp : (refPlaceIndex n).name? i = some p := hp
      show conc007_readInh n j i = true ↔ _
      simp [conc007_readInh, ht, hp, InhibitorMask, InhibitorArc, ReadArc]
    · have hn : (refPlaceIndex n).name? i = none := (refPlaceIndex n).name?_eq_none_iff.2 hi
      show conc007_readInh n j i = false
      unfold conc007_readInh
      rw [hn]
      cases n.transitions[j]? <;> rfl
  · have hp2 : (conc007_readInhCompile (fun _ => false) conc007_net).placeAt (conc007_id 2) =
        some 2 :=
      conc007_placeAt_id 2 (by decide)
    have := ((h (fun _ => false) conc007_net).2.2.1.1 0 conc007_t1 (conc007_id 2) 2 rfl hp2).2.1
      (by decide)
    simp [InhibitorMask, InhibitorArc, conc007_t1] at this

/-! ### Mutant: a needs bit one past the last place ID -/

section MutantPad

variable {N : Type}

/-- Mutant reading of line 3: the masks are exact at the place IDs, and nothing is stated at a
number at or above `P`. Lines 1, 2 and 4 to 7 are as in CONC-007. -/
def CONC_007_mutant_padBit (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) : Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧
    conc007_line3_atIds (Cmp hm n) ∧ conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧
    conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

end MutantPad

/-- The needs-mask with the stray bit `P` set for every transition ID (a `0..=place_count` loop,
or padding bits of the last word that were never cleared). -/
def conc007_padNeeds {N : Type} [DecidableEq N] (hm : Trans N → Bool) (n : Reference.Net N)
    (j i : Nat) : Bool :=
  (refCompileWith hm n).needs j i ||
    (decide (i = (refCompileWith hm n).placeCount) && decide (j < n.transitions.length))

/-- A compiler whose needs-masks also set bit `P`, and is the reference otherwise. -/
def conc007_padBitCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with needs := conc007_padNeeds hm n }

/-- The padding-bit compiler kills the mutant: every bit at a place ID is the reference's, so it
meets the mutant reading, but `t1`'s needs-mask has bit `7 = P` set (line 3). A word-wise check
then never passes, since no marking sets a bit at or above `P`. -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_padBit_killed :
    CONC_007_mutant_padBit (conc007_padBitCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_padBitCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, fun j t i p ht hp => ?_, h4, h5, h6, h7⟩
    have hp' : (refCompileWith hm n).placeAt i = some p := hp
    have hlt : i < (refCompileWith hm n).placeCount := (h1.2.1 i).1 (by rw [hp']; rfl)
    have hne : i ≠ (refCompileWith hm n).placeCount := Nat.ne_of_lt hlt
    refine ⟨?_, (h3.1 j t i p ht hp).2⟩
    show conc007_padNeeds hm n j i = true ↔ _
    simp only [conc007_padNeeds, hne, decide_false, Bool.false_and, Bool.or_false]
    exact (h3.1 j t i p ht hp).1
  · have := ((h (fun _ => false) conc007_net).2.2.1.2 0 7 (by decide) (by decide)).1
    revert this
    decide

/-! ### Violation: a needs-mask without the read places -/

/-- A needs-mask that holds only the input places. -/
def conc007_inputNeeds {N : Type} [DecidableEq N] (n : Reference.Net N) (j i : Nat) : Bool :=
  match n.transitions[j]?, (refPlaceIndex n).name? i with
  | some t, some p => decide (p ∈ inPlaces t)
  | _, _ => false

/-- A compiler whose needs-mask leaves out the read places, and is the reference otherwise. -/
def conc007_inputNeedsCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with needs := conc007_inputNeeds n }

/-- ✗ A compiler whose needs-mask leaves out the read places violates CONC-007 (line 3): `t1`'s
read place `2` is not in its needs-mask, so `t1` would pass the presence check with `2` empty. -/
@[evidence forbids CONC_007]
theorem CONC_007_forbids_noReadNeeds : ¬ CONC_007 (conc007_inputNeedsCompile (N := Nat)) :=
  fun h => by
    have hp2 : (conc007_inputNeedsCompile (fun _ => false) conc007_net).placeAt (conc007_id 2) =
        some 2 :=
      conc007_placeAt_id 2 (by decide)
    have := ((h (fun _ => false) conc007_net).2.2.1.1 0 conc007_t1 (conc007_id 2) 2 rfl hp2).1.2
      (.inr (show (2 : Nat) ∈ conc007_t1.core.reads by decide))
    revert this
    decide

/-! ### Mutant: consumption places without the reset places -/

section MutantConsumption

variable {N : Type}

/-- Mutant reading of line 4: the consumption places are exactly the input places (a drain is
not a consumption). Lines 1 to 3 and 5 to 7 are as in CONC-007. -/
def CONC_007_mutant_inputsOnly (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    (∀ j t i, (Cmp hm n).trans[j]? = some t →
      (i ∈ (Cmp hm n).consumption j ↔ ∃ p, (Cmp hm n).placeAt i = some p ∧ p ∈ inPlaces t)) ∧
    conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

end MutantConsumption

/-- Consumption places without the reset places. -/
def conc007_inputsOnly {N : Type} [DecidableEq N] (n : Reference.Net N) (j : Nat) : List Nat :=
  match n.transitions[j]? with
  | some t => (inPlaces t).map (refPlaceIndex n).idx
  | none => []

/-- A compiler whose consumption places are the input places only, and is the reference
otherwise. -/
def conc007_inputsOnlyCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with consumption := conc007_inputsOnly n }

/-- The inputs-only compiler kills the mutant: it meets the mutant reading, but `t1`'s reset
place `4` is not among its consumption places (line 4). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_inputsOnly_killed :
    CONC_007_mutant_inputsOnly (conc007_inputsOnlyCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_inputsOnlyCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, h3, fun j t i ht => ?_, h5, h6, h7⟩
    have ht : n.transitions[j]? = some t := ht
    have htm : t ∈ n.transitions := List.mem_of_getElem? ht
    show i ∈ conc007_inputsOnly n j ↔
      ∃ p, (refCompileWith hm n).placeAt i = some p ∧ p ∈ inPlaces t
    simp only [conc007_inputsOnly, ht]
    rw [List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, refCompileWith_placeAt_idx (mem_netPlaceList_of_arc htm (.inl hp)), hp⟩
    · rintro ⟨p, hpa, hp⟩
      obtain ⟨-, rfl⟩ := refCompileWith_placeAt_iff.1 hpa
      exact ⟨p, hp, rfl⟩
  · have hp4 : (conc007_inputsOnlyCompile (fun _ => false) conc007_net).placeAt (conc007_id 4) =
        some 4 :=
      conc007_placeAt_id 4 (by decide)
    have := ((h (fun _ => false) conc007_net).2.2.2.1 0 conc007_t1 (conc007_id 4) rfl).2
      ⟨4, hp4, .inr (show (4 : Nat) ∈ conc007_t1.core.resets by decide)⟩
    revert this
    decide

/-! ### Violation: consumption places that hold the read places -/

/-- Consumption places that also hold the read places. -/
def conc007_readConsumption {N : Type} [DecidableEq N] (n : Reference.Net N) (j : Nat) :
    List Nat :=
  match n.transitions[j]? with
  | some t => (inPlaces t ++ t.core.reads ++ t.core.resets).map (refPlaceIndex n).idx
  | none => []

/-- A compiler whose consumption places also hold the read places, and is the reference
otherwise. -/
def conc007_readConsumptionCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with consumption := conc007_readConsumption n }

/-- ✗ A compiler whose consumption places hold the read places violates CONC-007 (line 4): `t1`
would consume from its read place `2`, which a read arc never does. -/
@[evidence forbids CONC_007]
theorem CONC_007_forbids_readConsumption :
    ¬ CONC_007 (conc007_readConsumptionCompile (N := Nat)) := fun h => by
  obtain ⟨p, hp, hpin⟩ := ((h (fun _ => false) conc007_net).2.2.2.1 0 conc007_t1 (conc007_id 2)
    rfl).1 (by decide)
  have hp' : (refCompileNet conc007_net).placeAt (conc007_id 2) = some p := hp
  rw [conc007_placeAt_id 2 (by decide)] at hp'
  cases Option.some.inj hp'
  simp [inPlaces, ResetArc, conc007_t1] at hpin

/-! ### Mutant: a reverse index without the inhibitor places -/

section MutantAffected

variable {N : Type}

/-- Mutant reading of line 5: the reverse index of a place holds the transitions with an input,
read or reset arc on it (an inhibitor arc does not count). Lines 1 to 4, 6 and 7 are as in
CONC-007. -/
def CONC_007_mutant_noInhibitorAffected
    (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) : Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    conc007_line4 (Cmp hm n) ∧
    (∀ i p j, (Cmp hm n).placeAt i = some p →
      (j ∈ (Cmp hm n).affected i ↔
        ∃ t, (Cmp hm n).trans[j]? = some t ∧ (p ∈ inPlaces t ∨ ReadArc t p ∨ ResetArc t p))) ∧
    conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

end MutantAffected

/-- A transition touches a place through an input, read or reset arc. -/
def conc007_touchNoInh {N : Type} [DecidableEq N] (n : Reference.Net N) (p : N) (j : Nat) : Bool :=
  match n.transitions[j]? with
  | some t => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads ∨ p ∈ t.core.resets)
  | none => false

/-- A reverse index without the inhibitor places. -/
def conc007_noInh {N : Type} [DecidableEq N] (n : Reference.Net N) (i : Nat) : List Nat :=
  match (refPlaceIndex n).name? i with
  | some p => (List.range n.transitions.length).filter (conc007_touchNoInh n p)
  | none => []

/-- A compiler whose reverse index leaves out the inhibitor places, and is the reference
otherwise. -/
def conc007_noInhCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with affected := conc007_noInh n }

/-- The compiler without inhibitor places kills the mutant: it meets the mutant reading, but the
reverse index of `t1`'s inhibitor place `3` is empty (line 5), so a token landing on `3` would not
re-check `t1` ([CONC-005]). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_noInhibitorAffected_killed :
    CONC_007_mutant_noInhibitorAffected (conc007_noInhCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_noInhCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, h3, h4, fun i p j hp => ?_, h6, h7⟩
    have hp : (refPlaceIndex n).name? i = some p := hp
    show j ∈ conc007_noInh n i ↔
      ∃ t, n.transitions[j]? = some t ∧ (p ∈ inPlaces t ∨ ReadArc t p ∨ ResetArc t p)
    simp only [conc007_noInh, hp]
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨-, hj⟩
      cases ht : n.transitions[j]? with
      | none => simp [conc007_touchNoInh, ht] at hj
      | some t =>
        simp only [conc007_touchNoInh, ht] at hj
        exact ⟨t, rfl, of_decide_eq_true hj⟩
    · rintro ⟨t, ht, h⟩
      refine ⟨(List.getElem?_eq_some_iff.1 ht).1, ?_⟩
      simp only [conc007_touchNoInh, ht]; exact decide_eq_true h
  · have hp3 : (conc007_noInhCompile (fun _ => false) conc007_net).placeAt (conc007_id 3) =
        some 3 :=
      conc007_placeAt_id 3 (by decide)
    have := ((h (fun _ => false) conc007_net).2.2.2.2.1 (conc007_id 3) 3 0 hp3).2
      ⟨conc007_t1, rfl, .inr (.inr (.inl (show (3 : Nat) ∈ conc007_t1.core.inhibitors by decide)))⟩
    revert this
    decide

/-! ### Mutant: a reverse index that also holds the output places -/

section MutantOutAffected

variable {N : Type}

/-- Mutant reading of line 5: the reverse index of a place holds the transitions with an arc on
it or that deposit into it. Lines 1 to 4, 6 and 7 are as in CONC-007. -/
def CONC_007_mutant_outputAffected
    (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) : Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    conc007_line4 (Cmp hm n) ∧
    (∀ i p j, (Cmp hm n).placeAt i = some p →
      (j ∈ (Cmp hm n).affected i ↔
        ∃ t, (Cmp hm n).trans[j]? = some t ∧
          (p ∈ inPlaces t ∨ ReadArc t p ∨ InhibitorArc t p ∨ ResetArc t p ∨
            p ∈ (t.out.map outPlaces).getD []))) ∧
    conc007_line6 (Cmp hm n) ∧ conc007_line7 hm (Cmp hm n)

end MutantOutAffected

/-- A transition touches a place through an arc or through its output specification. -/
def conc007_touchOut {N : Type} [DecidableEq N] (n : Reference.Net N) (p : N) (j : Nat) : Bool :=
  match n.transitions[j]? with
  | some t => decide (p ∈ inPlaces t ∨ p ∈ t.core.reads ∨ p ∈ t.core.inhibitors ∨
      p ∈ t.core.resets ∨ p ∈ (t.out.map outPlaces).getD [])
  | none => false

/-- A reverse index that also holds the output places. -/
def conc007_outAffected {N : Type} [DecidableEq N] (n : Reference.Net N) (i : Nat) : List Nat :=
  match (refPlaceIndex n).name? i with
  | some p => (List.range n.transitions.length).filter (conc007_touchOut n p)
  | none => []

/-- A compiler whose reverse index also lists a transition under every place it deposits into
(one extra add per output place in the Java or TypeScript loop), and is the reference
otherwise. -/
def conc007_outAffectedCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  { refCompileWith hm n with affected := conc007_outAffected n }

/-- The output-affected compiler kills the mutant: it meets the mutant reading, but the reverse
index of the place `6`, into which `t2` only deposits, holds `t2` (line 5), so every deposit of
`t2` would re-check `t2` against [CONC-005]'s affected transitions. -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_outputAffected_killed :
    CONC_007_mutant_outputAffected (conc007_outAffectedCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_outAffectedCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, h3, h4, fun i p j hp => ?_, h6, h7⟩
    have hp : (refPlaceIndex n).name? i = some p := hp
    show j ∈ conc007_outAffected n i ↔
      ∃ t, n.transitions[j]? = some t ∧
        (p ∈ inPlaces t ∨ ReadArc t p ∨ InhibitorArc t p ∨ ResetArc t p ∨
          p ∈ (t.out.map outPlaces).getD [])
    simp only [conc007_outAffected, hp]
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨-, hj⟩
      cases ht : n.transitions[j]? with
      | none => simp [conc007_touchOut, ht] at hj
      | some t =>
        simp only [conc007_touchOut, ht] at hj
        exact ⟨t, rfl, of_decide_eq_true hj⟩
    · rintro ⟨t, ht, h⟩
      refine ⟨(List.getElem?_eq_some_iff.1 ht).1, ?_⟩
      simp only [conc007_touchOut, ht]; exact decide_eq_true h
  · have hp6 : (conc007_outAffectedCompile (fun _ => false) conc007_net).placeAt (conc007_id 6) =
        some 6 :=
      conc007_placeAt_id 6 (by decide)
    obtain ⟨t, ht, ha⟩ := ((h (fun _ => false) conc007_net).2.2.2.2.1 (conc007_id 6) 6 1 hp6).1
      (by decide)
    have ht' : conc007_net.transitions[1]? = some t := ht
    have : t = conc007_t2 := by
      simp [conc007_net] at ht'
      exact ht'.symm
    subst this
    simp [ArcPlace, conc007_t2, inPlaces, ReadArc, InhibitorArc, ResetArc] at ha

/-! ### Line 6: the cardinality check -/

section Card

variable {N : Type} [DecidableEq N]

/-- Cardinality checks built unless `skip` holds of the transition, listing every input's place ID
with its required count. -/
def conc007_cardWith (skip : Trans N → Bool) (n : Reference.Net N) (j : Nat) :
    Option (List (Nat × Nat)) :=
  match n.transitions[j]? with
  | some t => if skip t then none
      else some (t.core.inputs.map fun (s : NInSpec N) =>
        ((refPlaceIndex n).idx s.place, requiredCount s.card))
  | none => none

/-- The compiler with `conc007_cardWith skip` as its cardinality checks, the reference
otherwise. -/
def conc007_cardCompile (skip : Trans N → Bool) (hm : Trans N → Bool) (n : Reference.Net N) :
    CompiledNet N :=
  { refCompileWith hm n with card := conc007_cardWith skip n }

/-- A compiler that skips the cardinality check only for transitions all of whose inputs require
at most one token satisfies CONC-007. -/
theorem conc007_cardCompile_ok (skip : Trans N → Bool)
    (hskip : ∀ t, skip t = true → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1) :
    CONC_007 (conc007_cardCompile skip) := by
  intro hm n
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := CONC_007_reference (N := N) hm n
  refine ⟨h1, h2, h3, h4, h5, fun j t ht => ?_, h7⟩
  have ht : n.transitions[j]? = some t := ht
  have hc : (conc007_cardCompile skip hm n).card j = if skip t then none
      else some (t.core.inputs.map fun (s : NInSpec N) =>
        ((refPlaceIndex n).idx s.place, requiredCount s.card)) := by
    show conc007_cardWith skip n j = _
    simp only [conc007_cardWith, ht]
  have hmem : ∀ s ∈ t.core.inputs, s.place ∈ netPlaceList n := fun s hs =>
    mem_netPlaceList_of_arc (List.mem_of_getElem? ht) (.inl (List.mem_map_of_mem hs))
  rw [hc]
  refine ⟨fun h => ?_, fun l hl => ?_⟩
  · cases hs : skip t
    · rw [hs] at h; cases h
    · exact hskip t hs
  · cases hs : skip t
    · rw [hs] at hl
      cases hl
      refine ⟨fun e he => ?_, fun s hs _ => ?_⟩
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
        exact ⟨s, hs, refCompileWith_placeId_of_mem (hm := hm) (hmem s hs), rfl⟩
      · exact ⟨_, refCompileWith_placeId_of_mem (hm := hm) (hmem s hs),
          List.mem_map_of_mem (f := fun (s : NInSpec N) =>
            ((refPlaceIndex n).idx s.place, requiredCount s.card)) hs⟩
    · rw [hs] at hl; cases hl

end Card

/-- Java's test for "needs a cardinality check": some input requires more than one token, or is
`All` or `AtLeast` (java/src/main/java/org/libpetri/runtime/CompiledNet.java). The compiler skips
the check when the test fails. -/
def conc007_javaSkip {N : Type} (t : Trans N) : Bool :=
  t.core.inputs.all fun s => match s.card with
    | .one => true
    | .exactly k => decide (k ≤ 1)
    | _ => false

/-- ✓ Java's choice of which transitions get a cardinality check is allowed: it also skips an
`Exactly(1)` input, which requires one token. -/
@[evidence allows CONC_007]
theorem CONC_007_allows_javaCard : CONC_007 (conc007_cardCompile (conc007_javaSkip (N := Nat))) := by
  refine conc007_cardCompile_ok _ fun t ht s hs => ?_
  have := List.all_eq_true.1 ht s hs
  revert this
  cases s.card <;> simp [requiredCount, Card.required]

/-- ✗ A compiler that builds no cardinality check violates CONC-007 (line 6): `t1`'s `Exactly(2)`
input requires two tokens. -/
@[evidence forbids CONC_007]
theorem CONC_007_forbids_noCard :
    ¬ CONC_007 (conc007_cardCompile (N := Nat) fun _ => true) := fun h => by
  have := ((h (fun _ => false) conc007_net).2.2.2.2.2.1 0 conc007_t1 rfl).1 rfl ⟨1, .exactly 2⟩
    (by simp [conc007_t1])
  revert this
  decide

section MutantUnit

variable {N : Type}

/-- Mutant reading of line 6: only its first half (a transition without a cardinality check needs
no count beyond presence), so the entries of a check are not constrained. Lines 1 to 5 and 7 are
as in CONC-007. -/
def CONC_007_mutant_unitCounts (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧
    (∀ j t, (Cmp hm n).trans[j]? = some t →
      (Cmp hm n).card j = none → ∀ s ∈ t.core.inputs, requiredCount s.card ≤ 1) ∧
    conc007_line7 hm (Cmp hm n)

end MutantUnit

/-- Cardinality checks built where the reference builds them, giving every input the count 1. -/
def conc007_unitCard {N : Type} [DecidableEq N] (n : Reference.Net N) (j : Nat) :
    Option (List (Nat × Nat)) :=
  match n.transitions[j]? with
  | some t => if onlyOneInputs t then none
      else some (t.core.inputs.map fun (s : NInSpec N) => ((refPlaceIndex n).idx s.place, 1))
  | none => none

/-- A compiler whose cardinality checks give every input the count 1, and is the reference
otherwise. -/
def conc007_unitCompile {N : Type} [DecidableEq N] (hm : Trans N → Bool) (n : Reference.Net N) :
    CompiledNet N :=
  { refCompileWith hm n with card := conc007_unitCard n }

/-- The unit-count compiler kills the mutant: it builds a check exactly where the reference does,
so it meets the mutant reading, but `t1`'s check gives its `Exactly(2)` input the count 1
(line 6). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_unitCounts_killed :
    CONC_007_mutant_unitCounts (conc007_unitCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_unitCompile (N := Nat)) := by
  refine ⟨fun hm n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := CONC_007_reference (N := Nat) hm n
    refine ⟨h1, h2, h3, h4, h5, fun j t ht hn s hs => ?_, h7⟩
    have ht : n.transitions[j]? = some t := ht
    have hn : conc007_unitCard n j = none := hn
    simp only [conc007_unitCard, ht] at hn
    cases ho : onlyOneInputs t
    · rw [ho] at hn; cases hn
    · rw [(onlyOneInputs_iff t).1 ho s hs]
      decide
  · have hc : (conc007_unitCompile (fun _ => false) conc007_net).card 0 =
        some [(conc007_id 0, 1), (conc007_id 1, 1)] := by decide
    obtain ⟨i, -, hi⟩ :=
      (((h (fun _ => false) conc007_net).2.2.2.2.2.1 0 conc007_t1 rfl).2 _ hc).2
        ⟨1, .exactly 2⟩ (by simp [conc007_t1]) (by decide)
    simp [requiredCount, Card.required] at hi

/-! ### Mutants: the match flag -/

section MutantMatch

variable {N : Type}

/-- Mutant reading without line 7: the match flag is not constrained. Lines 1 to 6 are as in
CONC-007. -/
def CONC_007_mutant_noMatchLine (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n)

/-- Mutant reading with only one half of line 7: a transition without a match specification has
no flag, and the flag of a transition with one is not constrained. Lines 1 to 6 are as in
CONC-007. -/
def CONC_007_mutant_noFlagSet (Cmp : (Trans N → Bool) → Reference.Net N → CompiledNet N) :
    Prop :=
  ∀ hm n, conc007_line1 n (Cmp hm n) ∧ conc007_line2 n (Cmp hm n) ∧ conc007_line3 (Cmp hm n) ∧
    conc007_line4 (Cmp hm n) ∧ conc007_line5 (Cmp hm n) ∧ conc007_line6 (Cmp hm n) ∧
    (∀ j t, (Cmp hm n).trans[j]? = some t → hm t = false → (Cmp hm n).hasMatch j = false)

end MutantMatch

/-- A compiler that sets every match flag, whatever the match predicate. -/
def conc007_allFlagsCompile {N : Type} [DecidableEq N] (_hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  refCompileWith (fun _ => true) n

/-- A compiler that sets no match flag, whatever the match predicate. -/
def conc007_noFlagsCompile {N : Type} [DecidableEq N] (_hm : Trans N → Bool)
    (n : Reference.Net N) : CompiledNet N :=
  refCompileNet n

/-- The compiler that sets every match flag kills the first mutant: it is the reference compiler
with a flag function that always answers yes, so it meets lines 1 to 6, but on the example net
without match specifications `t1` has its flag set (line 7). -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_noMatchLine_killed :
    CONC_007_mutant_noMatchLine (conc007_allFlagsCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_allFlagsCompile (N := Nat)) := by
  refine ⟨fun _ n => conc007_refWith_lines _ n, fun h => ?_⟩
  have := (h (fun _ => false) conc007_net).2.2.2.2.2.2 0 conc007_t1 rfl
  revert this
  decide

/-- The compiler that sets no match flag kills the second mutant: it sets no flag for a
transition without a match specification, so it meets the mutant reading, but when `t2` carries a
match specification its flag stays clear (line 7). This is the half that a block over nets without
match specifications could not state. -/
@[evidence mutant CONC_007]
theorem CONC_007_mutant_noFlagSet_killed :
    CONC_007_mutant_noFlagSet (conc007_noFlagsCompile (N := Nat)) ∧
      ¬ CONC_007 (conc007_noFlagsCompile (N := Nat)) := by
  refine ⟨fun _ n => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := conc007_refWith_lines (fun _ => false) n
    exact ⟨h1, h2, h3, h4, h5, h6, fun j _ _ _ => refCompileNet_hasMatch j⟩
  · have := (h conc007_hmT2 conc007_net).2.2.2.2.2.2 1 conc007_t2 rfl
    revert this
    decide

end Libpetri.Spec
