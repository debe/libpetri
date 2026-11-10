import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryEnable

set_option linter.missingDocs true

/-!
# PERF-042: Sparse enablement masks (`spec/10-performance.md`)

PERF-042 is a pure-function requirement (kind F) at the word level of the presence check. An
executor keeps each transition's needs-mask and inhibitor-mask as full-width bitmaps (one word per
run of place indices, [CONC-004]) and compiles each into a sparse form: the empty sentinel, a single
word with its index, or the list of its non-zero words with their indices. The requirement is a
predicate over an abstract sparse check `C : SparseCheck` (a compile step from a mask to a sparse
form, and a presence check on the sparse forms and a presence bitmap) at a word size `w`. Three
lines pin the sparse forms (the representation part of AC1 to AC3); the fourth says the presence
check on the sparse forms answers what the full-width presence check answers (AC4).

The block is checked against the reference sparse check `refSparse`, against four wrong checks
(the two shipped TypeScript regressions, the word index in a signed 8-bit slot and the single-word
compare on signed 32-bit values, and two plausible slips, a multi-word check that reads its first
non-zero word only and an empty inhibitor mask read as "blocked"), and against three compile steps
whose results are right but whose forms are not (a "sparse" form that keeps every word, and one
that always emits the list form) and one with no single-word form, which only line 2 rejects. A control, `truncSparse`, shows that a check reading its words
at its own word size, as the runtimes do, meets the line.

The word layer is local to this block: no model or glossary module has words (the glossary's
presence check, `MaskCheck` in `GlossaryEnable.lean`, reads one bit per place). The join lemma
`denseEnable_maskCheck` ties the two levels: under any injective placement of places at bits of
words, the full-width word check passes exactly when the glossary presence check passes, so
"full-width bitmap check" carries no second meaning beside [CONC-004]'s formula.

What the three cases cost (no computation for an empty mask, one AND and one compare for a single
word, a loop over the non-zero words only) is not a property of a pure function and is not encoded.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## The word layer -/

/-- **Glossary: Word** (no other Lean term). "A machine word of a bitmap: it holds the bits of a
run of consecutive place indices. A bitmap is a sequence of words, and a word past the end of a
bitmap reads as zero [CONC-004], [PERF-042]."

A bitmap as a list of words, each a natural number; `FitsIn` bounds them by a word size. -/
abbrev Words := List Nat

/-- Word `i` of a bitmap, `0` past the end (glossary: Word). -/
def wordAt (s : Words) (i : Nat) : Nat := s.getD i 0

/-- Every word of the bitmap is below `2 ^ w`: the bitmap is made of `w`-bit words (`w = 64` in
Rust and Java, `w = 32` in TypeScript). -/
def FitsIn (w : Nat) (s : Words) : Prop := ∀ x ∈ s, x < 2 ^ w

instance (w : Nat) (s : Words) : Decidable (FitsIn w s) :=
  inferInstanceAs (Decidable (∀ x ∈ s, x < 2 ^ w))

/-- The full-width containment check: for every word index of the mask, the snapshot's word holds
every bit of the mask's word (`(marking & mask) == mask`, word by word). -/
def denseContainsAll (snap mask : Words) : Bool :=
  (List.range mask.length).all fun i => wordAt snap i &&& wordAt mask i == wordAt mask i

/-- The full-width intersection check: for some word index of the mask, the snapshot's word and
the mask's word share a bit (`(marking & mask) != 0`, word by word). -/
def denseIntersects (snap mask : Words) : Bool :=
  (List.range mask.length).any fun i => wordAt snap i &&& wordAt mask i != 0

/-- **The full-width presence check** of [CONC-004] on words: every word of the needs-mask is
contained in the presence bitmap and no word of the inhibitor-mask meets it,
`(marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0` (glossary: Presence
check), computed over every word of both masks. -/
def denseEnable (needs inhib snap : Words) : Bool :=
  denseContainsAll snap needs && !denseIntersects snap inhib

/-! ## Sparse forms and sparse checks -/

/-- The three sparse forms of a mask of PERF-042. -/
inductive SparseMask where
  /-- The empty sentinel: no non-zero word, the check is skipped. -/
  | empty
  /-- One non-zero word: its index and its value. -/
  | single (i m : Nat)
  /-- A list of words with their indices (in the reference, two or more non-zero words in index
  order). -/
  | multi (es : List (Nat × Nat))
  deriving DecidableEq, Repr

/-- A sparse enablement check: how it compiles a full-width mask into a sparse form, and the
presence check it runs on the sparse form of a needs-mask, the sparse form of an inhibitor-mask
and a presence bitmap. A runtime's own encoding of the three cases (sentinel values, index and
value arrays) is read through `SparseMask`. -/
structure SparseCheck where
  /-- Compile a full-width mask into its sparse form. -/
  compile : Words → SparseMask
  /-- The presence check on the sparse needs form, the sparse inhibitor form and a bitmap. -/
  check : SparseMask → SparseMask → Words → Bool

/-- The non-zero words of a mask `f` at the indices `l`, with their indices. -/
def nonZeroWords (f : Nat → Nat) (l : List Nat) : List (Nat × Nat) :=
  l.filterMap fun i => if f i = 0 then none else some (i, f i)

/-- The non-zero words of a mask with their indices, in index order (`mem_nonZeroOf`: the
entries are exactly the pairs of an index and the non-zero word the mask holds there). -/
def nonZeroOf (mask : Words) : List (Nat × Nat) :=
  nonZeroWords (wordAt mask) (List.range mask.length)

/-! ## The reference sparse check -/

/-- Compile a full-width mask into its sparse form (Rust `compile_sparse`,
`precompiled_net.rs`; Java and TypeScript compile the same three cases). -/
def compileSparse (mask : Words) : SparseMask :=
  match nonZeroOf mask with
  | [] => .empty
  | [(i, m)] => .single i m
  | es => .multi es

/-- Sparse containment: every listed word of the mask is contained in the snapshot. -/
def SparseMask.containsAll : SparseMask → Words → Bool
  | .empty, _ => true
  | .single i m, s => wordAt s i &&& m == m
  | .multi es, s => es.all fun p => wordAt s p.1 &&& p.2 == p.2

/-- Sparse intersection: some listed word of the mask meets the snapshot. -/
def SparseMask.intersects : SparseMask → Words → Bool
  | .empty, _ => false
  | .single i m, s => wordAt s i &&& m != 0
  | .multi es, s => es.any fun p => wordAt s p.1 &&& p.2 != 0

/-- The presence check on sparse forms: the needs form is contained and the inhibitor form meets
nothing. -/
def sparsePresence (needs inhib : SparseMask) (snap : Words) : Bool :=
  needs.containsAll snap && !inhib.intersects snap

/-- **The reference sparse check**: compile each mask with `compileSparse`, then the needs check
(contains all) and the inhibitor check (meets none) on the sparse forms. -/
def refSparse : SparseCheck := ⟨compileSparse, sparsePresence⟩

/- The reference sparse check is the witness model of PERF-042's `holds` theorem. -/
#spec_witness refSparse

/-! ## PERF-042: Sparse Enablement Masks -/

requirement PERF_042
  id "PERF-042"
  title "Sparse Enablement Masks"
  kind F
  scope "executors that use sparse enablement masks (the precompiled executors)"
  source verbatim "spec/10-performance.md"
  quote "*Where* an executor uses sparse enablement masks, it *shall* compile a needs-mask or an inhibitor-mask to the empty sentinel exactly when all its words are zero and a mask with exactly one non-zero word to the single-word form holding that word's index and value, and it *shall* put only non-zero words of the mask, each with its index, into a multi-word form."
        "*Where* an executor uses sparse enablement masks, its presence check on the sparse forms compiled from a transition's needs-mask and inhibitor-mask *shall* return, for every presence bitmap, the result of the presence check of [CONC-004] computed over every word of both masks."
        "These two sentences hold for masks and presence bitmaps of the same number of words, each word within the executor's word size."
        "Enablement results are identical to full-width bitmap checks."
  reading "At word size w, for every mask m whose words are below 2^w:"
          "C compiles m to the empty sentinel exactly when m has no non-zero word;"
          "when m has exactly one non-zero word, x at index i, C compiles m to the single-word form (i, x);"
          "when C compiles m to a multi-word form, every entry (i, x) of it has x non-zero and x the word of m at index i."
          "For every needs-mask, inhibitor-mask and presence bitmap of the same number of words, each below 2^w, C's presence check on the compiled forms of the two masks returns what the full-width presence check returns: every word of the needs-mask is contained in the bitmap's word of the same index, and no word of the inhibitor-mask shares a bit with it."
  assumes "A bitmap is a list of words, each a natural number, and a word past the end of a bitmap reads as zero (glossary: Word). Every line is stated at a word size w for masks whose words are below 2^w (FitsIn), and line 4 for a needs-mask, an inhibitor-mask and a presence bitmap of the same number of words, as the runtimes build them (W words of 64 bits in Rust and Java, of 32 bits in TypeScript). So a check that reads its words at its own word size meets the line at that size (PERF_042_accepts_trunc); the reference reads unbounded naturals and meets it at every size."
          "The model is a sparse check (SparseCheck): a compile step from a full-width mask to one of the body's three forms (SparseMask: the empty sentinel, one word with its index, a list of words with their indices) and a presence check on the sparse forms of the needs-mask and the inhibitor-mask. The runtimes compile the forms when the precompiled net is built (Rust from_arc and compile_sparse in precompiled_net.rs, Java PrecompiledNet, TypeScript precompiled-net.ts); a runtime's own encoding of the three cases is read through SparseMask. Line 4 constrains compile and check together, since the check only ever sees compiled forms; a compile slip (the signed 8-bit word index) breaks it as much as a check slip."
          "Which place sits at which bit of which word is the compiled net's business ([CONC-007]); the join lemma denseEnable_maskCheck shows that, for any injective placement, the full-width check passes exactly when the glossary presence check (MaskCheck, [CONC-004]) passes, so the block needs no placement. [CONC-020] (a dependency) puts the sparse masks into the precompiled net's flat arrays; it bears on the scope only (the precompiled executors), so no line refers to it."
          "The priority SHOULD is about whether an executor uses a sparse representation at all; the lines bind an executor that does (the Where clause of both sentences, and the spec sentence that says so in words), so for such an executor they are mandatory."
          "The body sentence 'Enablement masks SHOULD use a sparse representation to avoid scanning zero words in large nets.', the cost halves of its three cases ('skip the check entirely', 'one AND + one compare operation', 'iterate only non-zero entries') and 'This avoids scanning W words when most are zero (common in large, sparse nets).' are about how the check is computed and what it costs, which a pure function cannot show; they are quality properties (kind Q) and are not encoded. The representation halves of the three cases ('Empty (sentinel value)', 'store word index + mask value', 'store only non-zero word indices and their mask values') are lines 1 to 3."
          "AC1 (empty masks are detected and skipped with no computation) is line 1 for 'detected' (the sentinel stands for exactly the masks with no non-zero word; PERF_042_mutant_listOnly kills a compile step that never emits it) and line 4 for its result (an empty needs form passes and an empty inhibitor form blocks nothing; PERF_042_forbids_emptyBlocks kills a check that reads an empty inhibitor form as blocked). 'Skipped with no computation' is cost (kind Q), not encoded."
          "AC2 (a single-word mask uses one AND and one compare, no loop) is line 2 for the form (a mask with one non-zero word compiles to its index and value; PERF_042_mutant_noSingle kills, through line 2 alone, a compile step that keeps the sentinel and puts such a mask in a one-entry list). 'One AND and one compare, no loop' is cost (kind Q), not encoded; PERF_042_forbids_signed kills the shipped slip in that compare."
          "AC3 (a multi-word sparse mask iterates only non-zero words) is line 3 for the form (the multi-word form lists non-zero words of the mask only; PERF_042_mutant_allWords kills a compile step that keeps the zero words) and line 4 for its result (every non-zero word is checked; PERF_042_forbids_firstWord kills a check that reads the first only). That the check's loop walks the listed entries and nothing else is cost (kind Q), not encoded: a check that scans every word of the bitmap on correct forms meets the line."
          "AC4 (enablement results identical to full-width bitmap checks) is line 4. The test derivation's net with 200 places whose transitions touch 2 or 3 places is line 4 on one net, exercised by the reference in PERF_042_twoHundredPlaces; its 'is faster' is a cost criterion (kind Q)."
          "The check is the presence phase only. The cardinality check and the ν-match check ([CONC-008]) are later phases and are not part of it; reset arcs and output arcs play no part (glossary: Presence check)."
  signoff "pending"
  statement : Nat → SparseCheck → Prop :=
    fun w C =>
      (∀ m, FitsIn w m → (C.compile m = .empty ↔ nonZeroOf m = [])) ∧
      (∀ m i x, FitsIn w m → nonZeroOf m = [(i, x)] → C.compile m = .single i x) ∧
      (∀ m es, FitsIn w m → C.compile m = .multi es →
        ∀ p ∈ es, p.2 ≠ 0 ∧ wordAt m p.1 = p.2) ∧
      (∀ needs inhib snap, FitsIn w needs → FitsIn w inhib → FitsIn w snap →
        needs.length = snap.length → inhib.length = snap.length →
        C.check (C.compile needs) (C.compile inhib) snap = denseEnable needs inhib snap)

/- The pinned readable form of PERF-042: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.PERF_042 : ℕ → SparseCheck → Prop :=
fun w C =>
  (∀ (m : Words), FitsIn w m → (C.compile m = SparseMask.empty ↔ nonZeroOf m = [])) ∧
    (∀ (m : Words) (i x : ℕ), FitsIn w m → nonZeroOf m = [(i, x)] → C.compile m = SparseMask.single i x) ∧
      (∀ (m : Words) (es : List (ℕ × ℕ)),
          FitsIn w m → C.compile m = SparseMask.multi es → ∀ p ∈ es, p.2 ≠ 0 ∧ wordAt m p.1 = p.2) ∧
        ∀ (needs inhib snap : Words),
          FitsIn w needs →
            FitsIn w inhib →
              FitsIn w snap →
                List.length needs = List.length snap →
                  List.length inhib = List.length snap →
                    C.check (C.compile needs) (C.compile inhib) snap = denseEnable needs inhib snap
-/
#guard_msgs in #print PERF_042

/-! ### The reference -/

/-- Filtering the zero words out leaves the containment check unchanged. -/
theorem nonZeroWords_all (f : Nat → Nat) (s : Words) (l : List Nat) :
    ((nonZeroWords f l).all fun p => wordAt s p.1 &&& p.2 == p.2) =
      l.all fun i => wordAt s i &&& f i == f i := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' : ((List.filterMap (fun i => if f i = 0 then none else some (i, f i)) l).all
        fun p => wordAt s p.1 &&& p.2 == p.2) = l.all fun i => wordAt s i &&& f i == f i := ih
    by_cases h : f a = 0
    · simp only [nonZeroWords, List.filterMap_cons, h, if_true, List.all_cons, ih']
      simp
    · simp only [nonZeroWords, List.filterMap_cons, h, if_false, List.all_cons, ih']

/-- Filtering the zero words out leaves the intersection check unchanged. -/
theorem nonZeroWords_any (f : Nat → Nat) (s : Words) (l : List Nat) :
    ((nonZeroWords f l).any fun p => wordAt s p.1 &&& p.2 != 0) =
      l.any fun i => wordAt s i &&& f i != 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' : ((List.filterMap (fun i => if f i = 0 then none else some (i, f i)) l).any
        fun p => wordAt s p.1 &&& p.2 != 0) = l.any fun i => wordAt s i &&& f i != 0 := ih
    by_cases h : f a = 0
    · simp only [nonZeroWords, List.filterMap_cons, h, if_true, List.any_cons, ih']
      simp
    · simp only [nonZeroWords, List.filterMap_cons, h, if_false, List.any_cons, ih']

/-- A word past the end of a bitmap is zero. -/
theorem wordAt_ge (s : Words) (i : Nat) (h : s.length ≤ i) : wordAt s i = 0 := by
  simp [wordAt, List.getD, List.getElem?_eq_none h]

/-- The entries of `nonZeroOf m` are exactly the pairs of an index and the non-zero word `m`
holds there. -/
theorem mem_nonZeroOf (m : Words) (p : Nat × Nat) :
    p ∈ nonZeroOf m ↔ p.2 ≠ 0 ∧ wordAt m p.1 = p.2 := by
  obtain ⟨i, x⟩ := p
  simp only [nonZeroOf, nonZeroWords, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨a, -, h⟩
    by_cases h0 : wordAt m a = 0
    · simp [h0] at h
    · simp only [h0, if_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h0, rfl⟩
  · rintro ⟨hx, hw⟩
    have hi : i < m.length := by
      apply Classical.byContradiction
      intro hi
      rw [wordAt_ge m i (Nat.le_of_not_lt hi)] at hw
      exact hx hw.symm
    refine ⟨i, hi, ?_⟩
    simp [hw, hx]

/-- The sparse containment check of a compiled mask is the full-width one. -/
theorem compileSparse_containsAll (mask snap : Words) :
    (compileSparse mask).containsAll snap = denseContainsAll snap mask := by
  unfold denseContainsAll
  rw [← nonZeroWords_all]
  unfold compileSparse nonZeroOf
  split <;> rename_i h <;> simp [SparseMask.containsAll, h]

/-- The sparse intersection check of a compiled mask is the full-width one. -/
theorem compileSparse_intersects (mask snap : Words) :
    (compileSparse mask).intersects snap = denseIntersects snap mask := by
  unfold denseIntersects
  rw [← nonZeroWords_any]
  unfold compileSparse nonZeroOf
  split <;> rename_i h <;> simp [SparseMask.intersects, h]

/-- The reference compiles a mask to the empty sentinel exactly when it has no non-zero word. -/
theorem compileSparse_empty (m : Words) : compileSparse m = .empty ↔ nonZeroOf m = [] := by
  unfold compileSparse
  split <;> simp_all

/-- The reference's multi-word form is the list of the mask's non-zero words. -/
theorem compileSparse_multi {m : Words} {es : List (Nat × Nat)}
    (h : compileSparse m = .multi es) : es = nonZeroOf m := by
  unfold compileSparse at h
  split at h <;> simp_all

/-- The reference sparse check satisfies PERF-042 at every word size: it compiles to the empty
sentinel exactly the masks with no non-zero word and a one-word mask to that word, its multi-word
form is the list of non-zero words, and dropping zero words leaves the check unchanged, since a
zero word is contained in every snapshot word and meets none (`compileSparse_containsAll`,
`compileSparse_intersects`). -/
@[evidence holds PERF_042]
theorem PERF_042_reference (w : Nat) : PERF_042 w refSparse := by
  refine ⟨fun m _ => compileSparse_empty m, fun m i x _ h => ?_, fun m es _ h p hp => ?_,
    fun needs inhib snap _ _ _ _ _ => ?_⟩
  · show compileSparse m = _
    unfold compileSparse
    rw [h]
  · rw [compileSparse_multi h] at hp
    exact (mem_nonZeroOf m p).1 hp
  · simp [refSparse, sparsePresence, denseEnable, compileSparse_containsAll,
      compileSparse_intersects]

/-! ### A check at its own word size -/

/-- Read every word modulo `2 ^ w`, as a runtime with `w`-bit words does (TypeScript `>>> 0` at
`w = 32`). -/
def truncWords (w : Nat) (s : Words) : Words := s.map (· % 2 ^ w)

/-- Reading a bitmap of `w`-bit words modulo `2 ^ w` changes nothing. -/
theorem truncWords_of_fits {w : Nat} {s : Words} (h : FitsIn w s) : truncWords w s = s := by
  unfold truncWords
  conv => rhs; rw [← List.map_id s]
  exact List.map_congr_left fun x hx => Nat.mod_eq_of_lt (h x hx)

/-- The reference sparse check with every word read at word size `w`: a model of a runtime check
faithful to its word width. -/
def truncSparse (w : Nat) : SparseCheck :=
  ⟨fun m => compileSparse (truncWords w m), fun n i s => sparsePresence n i (truncWords w s)⟩

/-- A check that reads its words at its own word size meets PERF-042 at that size: the line asks
nothing of words a `w`-bit runtime cannot hold. (Not `holds` evidence: `truncSparse` is a control,
not the reference.) -/
theorem PERF_042_accepts_trunc (w : Nat) : PERF_042 w (truncSparse w) := by
  obtain ⟨h1, h2, h3, h4⟩ := PERF_042_reference w
  refine ⟨fun m hm => ?_, fun m i x hm h => ?_, fun m es hm h => ?_,
    fun needs inhib snap hn hi hs hl1 hl2 => ?_⟩
  · show compileSparse (truncWords w m) = _ ↔ _
    rw [truncWords_of_fits hm]
    exact h1 m hm
  · show compileSparse (truncWords w m) = _
    rw [truncWords_of_fits hm]
    exact h2 m i x hm h
  · change compileSparse (truncWords w m) = _ at h
    rw [truncWords_of_fits hm] at h
    exact h3 m es hm h
  · show sparsePresence (compileSparse (truncWords w needs)) (compileSparse (truncWords w inhib))
      (truncWords w snap) = _
    rw [truncWords_of_fits hn, truncWords_of_fits hi, truncWords_of_fits hs]
    exact h4 needs inhib snap hn hi hs hl1 hl2

/-! ### The full-width check is the glossary presence check -/

/-- A word contains another exactly when it holds every bit of it. -/
theorem word_and_eq_iff_bits (s m : Nat) :
    s &&& m = m ↔ ∀ b, m.testBit b = true → s.testBit b = true := by
  constructor
  · intro h b hb
    have := congrArg (fun x => x.testBit b) h
    simp [Nat.testBit_and, hb] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_and]
    cases hm : m.testBit b with
    | false => simp
    | true => simp [h b hm]

/-- Two words meet exactly when they share a bit. -/
theorem word_and_ne_zero_iff_bits (s m : Nat) :
    s &&& m ≠ 0 ↔ ∃ b, m.testBit b = true ∧ s.testBit b = true := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hm : m.testBit b with
    | false => simp
    | true =>
      cases hs : s.testBit b with
      | false => simp
      | true => exact absurd ⟨b, hm, hs⟩ hne
  · rintro ⟨b, hm, hs⟩ h0
    have := congrArg (fun x => x.testBit b) h0
    simp [Nat.testBit_and, hm, hs] at this

/-- The full-width containment check is containment of bit sets: every bit of every word of the
mask is set in the snapshot's word of the same index. -/
theorem denseContainsAll_iff (snap mask : Words) :
    denseContainsAll snap mask = true ↔
      ∀ i b, (wordAt mask i).testBit b = true → (wordAt snap i).testBit b = true := by
  unfold denseContainsAll
  rw [List.all_eq_true]
  constructor
  · intro h i b hb
    by_cases hi : i < mask.length
    · have := h i (List.mem_range.mpr hi)
      exact (word_and_eq_iff_bits _ _).mp (by simpa using this) b hb
    · rw [wordAt_ge mask i (Nat.le_of_not_lt hi)] at hb
      simp at hb
  · intro h i _
    simpa using (word_and_eq_iff_bits _ _).mpr (h i)

/-- The full-width intersection check is intersection of bit sets: some bit of some word of the
mask is set in the snapshot's word of the same index. -/
theorem denseIntersects_iff (snap mask : Words) :
    denseIntersects snap mask = true ↔
      ∃ i b, (wordAt mask i).testBit b = true ∧ (wordAt snap i).testBit b = true := by
  unfold denseIntersects
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, -, h⟩
    have h' : wordAt snap i &&& wordAt mask i ≠ 0 := by simpa using h
    obtain ⟨b, hm, hs⟩ := (word_and_ne_zero_iff_bits _ _).mp h'
    exact ⟨i, b, hm, hs⟩
  · rintro ⟨i, b, hm, hs⟩
    have hi : i < mask.length := by
      apply Classical.byContradiction
      intro hi
      rw [wordAt_ge mask i (Nat.le_of_not_lt hi)] at hm
      simp at hm
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simpa using (word_and_ne_zero_iff_bits _ _).mpr ⟨b, hm, hs⟩

/-- The full-width presence check on bit sets: every bit of the needs-mask is set in the
bitmap and no bit of the inhibitor-mask is. -/
theorem denseEnable_iff_bits (needs inhib snap : Words) :
    denseEnable needs inhib snap = true ↔
      (∀ i b, (wordAt needs i).testBit b = true → (wordAt snap i).testBit b = true) ∧
        (∀ i b, (wordAt inhib i).testBit b = true → (wordAt snap i).testBit b = false) := by
  unfold denseEnable
  rw [Bool.and_eq_true, denseContainsAll_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    denseIntersects_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h i b hb
    cases hs : (wordAt snap i).testBit b with
    | false => rfl
    | true => exact absurd ⟨i, b, hb, hs⟩ h
  · rintro h ⟨i, b, hb, hs⟩
    rw [h i b hb] at hs
    exact Bool.false_ne_true hs

/-- A bitmap over places `bits` packed into the words `w` by the placement `loc`: `loc p = (i, b)`
puts place `p` at bit `b` of word `i`, and a bit of `w` is set exactly when a place of `bits` sits
there. -/
def PacksTo {N : Type} (loc : N → Nat × Nat) (bits : N → Bool) (w : Words) : Prop :=
  ∀ i b, (wordAt w i).testBit b = true ↔ ∃ p, loc p = (i, b) ∧ bits p = true

/-- Under an injective placement, the full-width check on packed bitmaps reads the places: every
needed place is present and no inhibiting place is. -/
theorem denseEnable_iff_places {N : Type} {loc : N → Nat × Nat}
    (hinj : ∀ p q, loc p = loc q → p = q) {needs inhib snap : N → Bool} {nw iw sw : Words}
    (hn : PacksTo loc needs nw) (hi : PacksTo loc inhib iw) (hs : PacksTo loc snap sw) :
    denseEnable nw iw sw = true ↔
      (∀ p, needs p = true → snap p = true) ∧ (∀ p, inhib p = true → snap p = false) := by
  have hsnap : ∀ p, (wordAt sw (loc p).1).testBit (loc p).2 = true ↔ snap p = true := by
    intro p
    rw [hs]
    constructor
    · rintro ⟨q, hq, h⟩
      rwa [hinj q p hq] at h
    · intro h
      exact ⟨p, rfl, h⟩
  rw [denseEnable_iff_bits]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · exact (hsnap p).1 (h1 _ _ ((hn _ _).2 ⟨p, rfl, hp⟩))
    · have h := h2 _ _ ((hi _ _).2 ⟨p, rfl, hp⟩)
      cases hp' : snap p with
      | false => rfl
      | true => rw [(hsnap p).2 hp'] at h; exact absurd h (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨fun k b hb => ?_, fun k b hb => ?_⟩
    · obtain ⟨p, hp, hnp⟩ := (hn k b).1 hb
      exact (hs k b).2 ⟨p, hp, h1 p hnp⟩
    · obtain ⟨p, hp, hip⟩ := (hi k b).1 hb
      cases hsk : (wordAt sw k).testBit b with
      | false => rfl
      | true =>
        obtain ⟨q, hq, hsq⟩ := (hs k b).1 hsk
        rw [hinj q p (hq.trans hp.symm), h2 p hip] at hsq
        exact absurd hsq Bool.false_ne_true

/-- **The join to [CONC-004].** Pack a transition's needs-mask, its inhibitor-mask (glossary
terms) and a bitmap over places into words by an injective placement: the full-width word check
passes exactly when the glossary presence check `MaskCheck` passes. So the full-width check of
PERF-042 is the presence check of [CONC-004], read word by word. -/
@[evidence cites "CONC-004" "the presence check (marking & needs-mask) == needs-mask AND (marking & inhibitor-mask) == 0, read word by word: on bitmaps packed into words by any injective placement of places at bits, the full-width word check denseEnable of PERF-042 passes exactly when MaskCheck passes"]
theorem denseEnable_maskCheck {N : Type} [DecidableEq N] (t : Trans N) {loc : N → Nat × Nat}
    (hinj : ∀ p q, loc p = loc q → p = q) {bits : N → Bool} {nw iw sw : Words}
    (hn : PacksTo loc (fun p => decide (p ∈ inPlaces t ∨ ReadArc t p)) nw)
    (hi : PacksTo loc (fun p => decide (InhibitorArc t p)) iw) (hs : PacksTo loc bits sw) :
    denseEnable nw iw sw = true ↔ MaskCheck t bits := by
  rw [denseEnable_iff_places hinj hn hi hs]
  simp only [MaskCheck, NeedsMask, InhibitorMask, decide_eq_true_eq]

/-! ### Violation: the word index in a signed 8-bit slot -/

/-- The sparse form with its word index kept in a signed 8-bit slot (TypeScript `Int8Array`,
regression test `typescript/tests/runtime/precompiled-net-word-index.test.ts`). An index `i` is
stored as `i mod 256`, read signed: below 128 it is a single word at that (possibly wrong) index;
`-2` (stored 254) is the empty sentinel; any other negative value reads as the multi-word case
with empty lists. -/
def compileInt8 (mask : Words) : SparseMask :=
  match compileSparse mask with
  | .single i m =>
    if i % 256 < 128 then .single (i % 256) m else if i % 256 = 254 then .empty else .multi []
  | x => x

/-- The sparse check over the signed 8-bit index slot. -/
def int8Sparse : SparseCheck := ⟨compileInt8, sparsePresence⟩

set_option maxRecDepth 100000 in
/-- ✗ The signed 8-bit word index violates PERF-042 at 32-bit words: a transition whose only
input place sits in word 128 (place index 4096 and above) is enabled with that place empty. -/
@[evidence forbids PERF_042]
theorem PERF_042_forbids_int8 : ¬ PERF_042 32 int8Sparse := fun h => by
  have := h.2.2.2 (List.replicate 128 0 ++ [1]) (List.replicate 129 0) (List.replicate 129 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### Violation: the compare on signed 32-bit values -/

/-- The needs check with the compare done on signed 32-bit values (TypeScript without `>>> 0`,
regression test `typescript/tests/runtime/precompiled-net-bit31.test.ts`): `(snapshot & m)` is
negative when bit 31 is set while `m` is read unsigned, so a mask word holding bit 31 never
matches. Each word is checked at its own index, in the single-word and in the multi-word case. -/
def signedContainsAll : SparseMask → Words → Bool
  | .empty, _ => true
  | .single i m, s => (wordAt s i &&& m == m) && !m.testBit 31
  | .multi es, s => es.all fun p => (wordAt s p.1 &&& p.2 == p.2) && !p.2.testBit 31

/-- The sparse check with the signed 32-bit needs compare. -/
def signedSparse : SparseCheck :=
  ⟨compileSparse, fun needs inhib snap => signedContainsAll needs snap && !inhib.intersects snap⟩

/-- ✗ The signed compare violates PERF-042 at 32-bit words: a transition whose input place is
place 31 (bit 31 of word 0) is never enabled, also with the place marked. -/
@[evidence forbids PERF_042]
theorem PERF_042_forbids_signed : ¬ PERF_042 32 signedSparse := fun h => by
  have := h.2.2.2 [2 ^ 31] [0] [2 ^ 31] (by decide) (by decide) (by decide) rfl rfl
  revert this
  decide

/-- The signed compare fails at a word index other than 0 too (place 63 with 32-bit words), and
in the multi-word case: the slip is the compare, not the word it reads. -/
theorem signedSparse_wrong_elsewhere :
    signedSparse.check (compileSparse [0, 2 ^ 31]) (compileSparse [0, 0]) [0, 2 ^ 31] = false ∧
      denseEnable [0, 2 ^ 31] [0, 0] [0, 2 ^ 31] = true ∧
      signedSparse.check (compileSparse [1, 2 ^ 31]) (compileSparse [0, 0]) [1, 2 ^ 31] = false ∧
      denseEnable [1, 2 ^ 31] [0, 0] [1, 2 ^ 31] = true := by
  decide

/-! ### Violation: the first non-zero word only -/

/-- A multi-word needs check that reads its first non-zero word only. -/
def firstWordSparse : SparseCheck :=
  ⟨compileSparse, fun needs inhib snap =>
    (match needs with
      | .multi (p :: _) => wordAt snap p.1 &&& p.2 == p.2
      | x => x.containsAll snap) && !inhib.intersects snap⟩

/-- ✗ Reading the first non-zero word only violates PERF-042 (AC3's 'iterate only non-zero
words' still means every non-zero word): a transition needing places in words 0 and 1 is enabled
with the word-1 place empty. -/
@[evidence forbids PERF_042]
theorem PERF_042_forbids_firstWord : ¬ PERF_042 32 firstWordSparse := fun h => by
  have := h.2.2.2 [1, 1] [0, 0] [1, 0] (by decide) (by decide) (by decide) rfl rfl
  revert this
  decide

/-! ### Violation: an empty inhibitor mask read as blocked -/

/-- An inhibitor check that reads the empty sentinel as "blocked" instead of "skip". -/
def emptyBlocksSparse : SparseCheck :=
  ⟨compileSparse, fun needs inhib snap =>
    needs.containsAll snap &&
      (match inhib with
        | .empty => false
        | x => !x.intersects snap)⟩

/-- ✗ Reading an empty inhibitor mask as blocked violates PERF-042 (AC1's 'skipped'): a
transition without inhibitor arcs whose input place is marked is never enabled. -/
@[evidence forbids PERF_042]
theorem PERF_042_forbids_emptyBlocks : ¬ PERF_042 32 emptyBlocksSparse := fun h => by
  have := h.2.2.2 [1] [0] [1] (by decide) (by decide) (by decide) rfl rfl
  revert this
  decide

/-! ### Mutants: right results, wrong forms -/

/-- Line 4 of PERF-042 alone: the presence check on the compiled forms answers what the
full-width check answers. The mutants below meet it and break lines 1 to 3. -/
def ResultLineOnly (w : Nat) (C : SparseCheck) : Prop :=
  ∀ needs inhib snap, FitsIn w needs → FitsIn w inhib → FitsIn w snap →
    needs.length = snap.length → inhib.length = snap.length →
    C.check (C.compile needs) (C.compile inhib) snap = denseEnable needs inhib snap

/-- A "sparse" form that keeps every word: the multi-word list holds every word index of the
mask, zero words included (the `!= 0` filter forgotten), so every check scans all W words. -/
def compileAllWords (mask : Words) : SparseMask :=
  .multi ((List.range mask.length).map fun i => (i, wordAt mask i))

/-- The presence check over the every-word form. -/
def allWordsSparse : SparseCheck := ⟨compileAllWords, sparsePresence⟩

/-- ✗ Keeping the zero words in the multi-word form meets line 4 (its results are right) and
violates PERF-042 (AC3's 'only non-zero words', line 3): the mask `[0, 1]` is compiled to a list
with the zero word 0 in it. -/
@[evidence mutant PERF_042]
theorem PERF_042_mutant_allWords : ResultLineOnly 32 allWordsSparse ∧ ¬ PERF_042 32 allWordsSparse := by
  refine ⟨fun needs inhib snap _ _ _ _ _ => ?_, fun h => ?_⟩
  · simp [allWordsSparse, compileAllWords, sparsePresence, SparseMask.containsAll,
      SparseMask.intersects, denseEnable, denseContainsAll, denseIntersects, List.all_map,
      List.any_map, Function.comp_def]
  · have := h.2.2.1 [0, 1] _ (by decide) rfl (0, 0) (by decide)
    simp at this

/-- A compile step that always emits the list form: an empty mask becomes an empty list (no
sentinel), a one-word mask a one-entry list (no single-word fast path). -/
def compileListOnly (mask : Words) : SparseMask := .multi (nonZeroOf mask)

/-- The presence check over the list-only form. -/
def listOnlySparse : SparseCheck := ⟨compileListOnly, sparsePresence⟩

/-- ✗ Never emitting the empty sentinel or the single-word form meets line 4 and violates
PERF-042 (AC1's 'detected', line 1, and AC2's form, line 2): the empty mask `[]` is not compiled
to the sentinel, and `[0, 5]` is compiled to a one-entry list instead of the single word 5 at
index 1. -/
@[evidence mutant PERF_042]
theorem PERF_042_mutant_listOnly :
    ResultLineOnly 32 listOnlySparse ∧ ¬ PERF_042 32 listOnlySparse := by
  refine ⟨fun needs inhib snap _ _ _ _ _ => ?_, fun h => ?_⟩
  · simp only [listOnlySparse, compileListOnly, sparsePresence, SparseMask.containsAll,
      SparseMask.intersects, nonZeroOf, nonZeroWords_all, nonZeroWords_any, denseEnable,
      denseContainsAll, denseIntersects]
  · have := (h.1 [] (by decide)).2 rfl
    simp [listOnlySparse, compileListOnly] at this

/-- The list-only form also breaks line 2 on its own: a mask with one non-zero word is not
compiled to the single-word form. -/
theorem listOnlySparse_breaks_single :
    nonZeroOf [0, 5] = [(1, 5)] ∧ listOnlySparse.compile [0, 5] ≠ .single 1 5 := by
  decide

/-- A compile step that keeps the empty sentinel but has no single-word form: a mask with one
non-zero word goes into a one-entry list, as any mask with non-zero words does. -/
def compileNoSingle (mask : Words) : SparseMask :=
  match nonZeroOf mask with
  | [] => .empty
  | es => .multi es

/-- The presence check over the forms without a single-word case. -/
def noSingleSparse : SparseCheck := ⟨compileNoSingle, sparsePresence⟩

/-- `compileNoSingle` is the sentinel on a mask with no non-zero word and the list of its
non-zero words otherwise. -/
theorem compileNoSingle_eq (mask : Words) :
    compileNoSingle mask = if nonZeroOf mask = [] then .empty else .multi (nonZeroOf mask) := by
  unfold compileNoSingle
  split <;> simp_all

/-- PERF-042 without line 2: lines 1, 3 and 4. The model below meets it and breaks line 2. -/
def PERF_042_withoutLine2 (w : Nat) (C : SparseCheck) : Prop :=
  (∀ m, FitsIn w m → (C.compile m = .empty ↔ nonZeroOf m = [])) ∧
  (∀ m es, FitsIn w m → C.compile m = .multi es →
    ∀ p ∈ es, p.2 ≠ 0 ∧ wordAt m p.1 = p.2) ∧
  (∀ needs inhib snap, FitsIn w needs → FitsIn w inhib → FitsIn w snap →
    needs.length = snap.length → inhib.length = snap.length →
    C.check (C.compile needs) (C.compile inhib) snap = denseEnable needs inhib snap)

/-- ✗ A compile step with no single-word form meets lines 1, 3 and 4 (the sentinel is kept, the
list holds only non-zero words, and every result is right) and violates PERF-042 through line 2
alone (AC2's form): the mask `[0, 5]` has the one non-zero word 5 at index 1 and is compiled to
the one-entry list, not to the single-word form. -/
@[evidence mutant PERF_042]
theorem PERF_042_mutant_noSingle :
    PERF_042_withoutLine2 32 noSingleSparse ∧ ¬ PERF_042 32 noSingleSparse := by
  have hc : ∀ m s, (compileNoSingle m).containsAll s =
      (SparseMask.multi (nonZeroOf m)).containsAll s := by
    intro m s
    rw [compileNoSingle_eq]
    split <;> simp_all [SparseMask.containsAll]
  have hi : ∀ m s, (compileNoSingle m).intersects s =
      (SparseMask.multi (nonZeroOf m)).intersects s := by
    intro m s
    rw [compileNoSingle_eq]
    split <;> simp_all [SparseMask.intersects]
  refine ⟨⟨fun m _ => ?_, fun m es _ h p hp => ?_, fun needs inhib snap _ _ _ _ _ => ?_⟩,
    fun h => ?_⟩
  · show compileNoSingle m = .empty ↔ nonZeroOf m = []
    rw [compileNoSingle_eq]
    split <;> simp_all
  · change compileNoSingle m = .multi es at h
    rw [compileNoSingle_eq] at h
    split at h
    · cases h
    · cases h
      exact (mem_nonZeroOf m p).1 hp
  · show sparsePresence (compileNoSingle needs) (compileNoSingle inhib) snap = _
    rw [sparsePresence, hc, hi]
    simp only [SparseMask.containsAll, SparseMask.intersects, nonZeroOf, nonZeroWords_all,
      nonZeroWords_any, denseEnable, denseContainsAll, denseIntersects]
  · have := h.2.1 [0, 5] 1 5 (by decide) (by decide)
    revert this
    decide

/-! ### Every case exercised -/

/-- The line is exercised by the reference in each of the three sparse cases, for the needs-mask
and for the inhibitor-mask, with both answers: the compiled forms are empty (`[]`, and `[0, 0]`
whose words are all zero), single (`[0, 5]`, word 1) and multi (`[1, 0, 2]`, words 0 and 2); an
empty needs-mask and an empty inhibitor-mask pass; a single-word needs-mask passes when its word
is contained and fails when it is not; a multi-word needs-mask fails when its second non-zero
word is missing; a single-word and a multi-word inhibitor-mask block when met and pass when
not. -/
@[evidence nonvacuous PERF_042]
theorem PERF_042_nonvacuous :
    refSparse.compile [] = .empty ∧ refSparse.compile [0, 0] = .empty ∧
    refSparse.compile [0, 5] = .single 1 5 ∧
    refSparse.compile [1, 0, 2] = .multi [(0, 1), (2, 2)] ∧
    refSparse.check (refSparse.compile []) (refSparse.compile []) [] = true ∧
    refSparse.check (refSparse.compile [0, 0]) (refSparse.compile [0, 0]) [0, 0] = true ∧
    refSparse.check (refSparse.compile [0, 5]) (refSparse.compile [0, 0]) [0, 7] = true ∧
    refSparse.check (refSparse.compile [0, 5]) (refSparse.compile [0, 0]) [7, 1] = false ∧
    refSparse.check (refSparse.compile [1, 0, 2]) (refSparse.compile [0, 0, 0]) [1, 0, 2] = true ∧
    refSparse.check (refSparse.compile [1, 0, 2]) (refSparse.compile [0, 0, 0]) [1, 9, 0] = false ∧
    refSparse.check (refSparse.compile [1, 0]) (refSparse.compile [0, 4]) [1, 4] = false ∧
    refSparse.check (refSparse.compile [1, 0]) (refSparse.compile [0, 4]) [1, 0] = true ∧
    refSparse.check (refSparse.compile [1, 0]) (refSparse.compile [2, 4]) [1, 0] = true ∧
    refSparse.check (refSparse.compile [1, 0]) (refSparse.compile [2, 4]) [1, 4] = false := by
  decide

/-- The test derivation's net: 200 places in 32-bit words (W = 7). Transition A needs places 5
and 70 (word 0 bit 5, word 2 bit 6) and is inhibited by place 199 (word 6 bit 7); transition B
needs places 33 and 40 (word 1, bits 1 and 8) and has no inhibitor. Their needs-masks compile to
a multi-word and a single-word form, A's inhibitor-mask to a single word and B's to the empty
sentinel, and the reference answers what the full-width check answers on markings that enable
and that disable each. -/
@[evidence nonvacuous PERF_042]
theorem PERF_042_twoHundredPlaces :
    let aN : Words := [2 ^ 5, 0, 2 ^ 6, 0, 0, 0, 0]
    let aI : Words := [0, 0, 0, 0, 0, 0, 2 ^ 7]
    let bN : Words := [0, 2 ^ 1 + 2 ^ 8, 0, 0, 0, 0, 0]
    let bI : Words := [0, 0, 0, 0, 0, 0, 0]
    let m1 : Words := [2 ^ 5, 2 ^ 1 + 2 ^ 8, 2 ^ 6, 0, 0, 0, 0]
    let m2 : Words := [2 ^ 5, 2 ^ 1, 2 ^ 6, 0, 0, 0, 2 ^ 7]
    let m3 : Words := [2 ^ 5, 2 ^ 1 + 2 ^ 8, 0, 0, 0, 0, 0]
    refSparse.compile aN = .multi [(0, 2 ^ 5), (2, 2 ^ 6)] ∧
    refSparse.compile aI = .single 6 (2 ^ 7) ∧
    refSparse.compile bN = .single 1 (2 ^ 1 + 2 ^ 8) ∧ refSparse.compile bI = .empty ∧
    refSparse.check (refSparse.compile aN) (refSparse.compile aI) m1 = denseEnable aN aI m1 ∧
    refSparse.check (refSparse.compile aN) (refSparse.compile aI) m2 = denseEnable aN aI m2 ∧
    refSparse.check (refSparse.compile aN) (refSparse.compile aI) m3 = denseEnable aN aI m3 ∧
    refSparse.check (refSparse.compile bN) (refSparse.compile bI) m1 = denseEnable bN bI m1 ∧
    refSparse.check (refSparse.compile bN) (refSparse.compile bI) m2 = denseEnable bN bI m2 ∧
    denseEnable aN aI m1 = true ∧ denseEnable aN aI m2 = false ∧ denseEnable aN aI m3 = false ∧
    denseEnable bN bI m1 = true ∧ denseEnable bN bI m2 = false := by
  decide

end Libpetri.Spec
