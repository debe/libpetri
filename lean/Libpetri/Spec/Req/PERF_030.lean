import Libpetri.Spec.Registry
import Libpetri.Reference.Compiled

set_option linter.missingDocs true

/-!
# PERF-030: Bitmap memory efficiency (`spec/10-performance.md`)

PERF-030 is a pure-function requirement (kind F) on the size of a bitmap executor's data,
counted in words (ruling D55 (a), recommendation PERF-R1 (a)). The requirement is a predicate
over an abstract bitmap layout `L : BitmapLayout N` at a word size `ws`: for a net, the number of
words of the presence bitmap, the full-width masks of each transition (each as its list of
words), and the number of words of the dirty set. Five lines bound the three structures: the
presence bitmap takes at most `⌈P / ws⌉` words; there is one mask count `k`, fixed before the net
is chosen, that bounds the masks of every transition of every net; every mask takes at most
`⌈P / ws⌉` words of `ws` bits; the dirty set takes at most `⌈T / ws⌉` words; and no mask is kept
at an ID that is no transition's, so every word the mask structure holds is a word of some
transition's masks. Their sum, the spec's `(1 + k × T) × ⌈P / ws⌉ + ⌈T / ws⌉`, is
`PERF_030_total`; with line 5 it bounds the mask words held at every ID (`PERF_030_held`).

The witness is `refBitmapLayout`: the needs-mask and the inhibitor-mask of the reference compiled
net (`refCompileNet`, `Reference/Compiled.lean`) packed into words by `packBits`, so its masks are
RefCompiled's mask words (`refBitmapLayout_maskWords`) and its word count is RefCompiled's
`layoutWords` (`refBitmapLayout_total`), with `k = refMaskCount = 2`. A layout with five masks
per transition, as Java keeps, also meets the block (`PERF_030_allows_five`): the mask count is
fixed per implementation, not fixed by the requirement.

Wrong layouts are killed, one per line: a presence bitmap with a word per place, masks with one
mask per arc of the transition (so no fixed `k`), masks with a word per place, a dirty set with a
word per transition, and flat mask arrays allocated with `T × P` words whose unread tail lies past
the last transition's slice. A layout that reports a mask of wider numbers as a few words is
killed by the word-size clause of line 3. The AC2 instance (100 places, 50 transitions) is decided
on the reference: 203 words at 64-bit words, 406 at 32-bit words.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## The bitmap layout -/

/-- The bitmap data a bitmap executor keeps for a net: the size of its presence bitmap in words,
the full-width masks of the transition with ID `j` (the `j`-th transition of the net, [CONC-007]),
each as its list of words, and the size of its dirty set in words. The presence bitmap and the
dirty set are run state whose content depends on the marking, so only their size is modelled;
the masks are compiled data, a function of the net. -/
structure BitmapLayout (N : Type) where
  /-- The number of words of the presence bitmap kept for the net. -/
  presence : Reference.Net N → Nat
  /-- The full-width masks kept for the transition with ID `j`, each as its list of words. -/
  masks    : Reference.Net N → Nat → List (List Nat)
  /-- The number of words of the dirty set kept for the net. -/
  dirty    : Reference.Net N → Nat

variable {N : Type}

/-- `P`: the number of places of a net, each counted once: its declared places and every place
an arc or the output specification of a transition names (`netPlaceList`). It is the number of
place IDs of the compiled net (`placeCountOf_eq`). -/
def placeCountOf [DecidableEq N] (n : Reference.Net N) : Nat := (netPlaceList n).dedup.length

/-- The words a layout keeps for a net: the presence bitmap, every mask of every transition, and
the dirty set. -/
def BitmapLayout.total (L : BitmapLayout N) (n : Reference.Net N) : Nat :=
  L.presence n + ((List.range n.transitions.length).map fun j => ((L.masks n j).map List.length).sum).sum +
    L.dirty n

section Ref

variable [DecidableEq N]

/-- `P` is the place count of the reference compiled net. -/
theorem placeCountOf_eq (n : Reference.Net N) : placeCountOf n = (refCompileNet n).placeCount := rfl

/-- A layout whose presence bitmap and dirty set take `⌈P / ws⌉` and `⌈T / ws⌉` words and whose
masks for transition `j` are the bitmaps `bits n j` over place IDs, each packed into `⌈P / ws⌉`
words of `ws` bits (`packBits`); it keeps no mask at an ID that is no transition's. -/
def packedLayout (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool)) : BitmapLayout N where
  presence n := ceilDiv (placeCountOf n) ws
  masks n j :=
    if j < n.transitions.length then (bits n j).map (packBits ws (ceilDiv (placeCountOf n) ws))
    else []
  dirty n := ceilDiv n.transitions.length ws

/-- **The reference bitmap layout** at word size `ws`: per transition, the needs-mask and the
inhibitor-mask of the reference compiled net, packed into words. -/
def refBitmapLayout (ws : Nat) : BitmapLayout N :=
  packedLayout ws fun n j => [(refCompileNet n).needs j, (refCompileNet n).inhibitor j]

/- The reference bitmap layout is the witness model of PERF-030's `holds` theorem. -/
#spec_witness refBitmapLayout

end Ref

/-! ## PERF-030: Bitmap Memory Efficiency -/

requirement PERF_030
  id "PERF-030"
  title "Bitmap Memory Efficiency"
  kind F
  scope "bitmap executors (the BitmapNetExecutor of Java, TypeScript and Rust; Python through Rust)"
  source verbatim "spec/10-performance.md"
  quote "For a net with P places and T transitions, the bitmap executor *shall* keep its presence bitmap in at most ceil(P / word_size) words, each full-width mask of a transition in at most ceil(P / word_size) words of word_size bits, and its dirty set in at most ceil(T / word_size) words."
        "The bitmap executor *shall* keep at most k full-width masks per transition, for one number k that the implementation fixes and that does not depend on the net, and no full-width mask words beside those masks."
        "Together the three structures take at most (1 + k × T) × ceil(P / word_size) + ceil(T / word_size) words."
  reading "At word size ws (ws > 0), for every net n with P places (placeCountOf n) and T transitions:"
          "the presence bitmap kept for n takes at most ceil(P / ws) words;"
          "there is one number k, chosen before the net, such that every transition of every net has at most k full-width masks;"
          "every full-width mask of a transition of n has at most ceil(P / ws) words, each a number below 2^ws;"
          "the dirty set kept for n takes at most ceil(T / ws) words;"
          "no mask is kept at an ID j that is no transition's (j ≥ T), so every word the mask structure holds is a word of a transition's mask."
  assumes "The model is a bitmap layout (BitmapLayout): for a net, the number of words of the presence bitmap, the full-width masks kept at the ID j (the transition with ID j, its declaration position, CONC-007) as lists of words, and the number of words of the dirty set. The presence bitmap and the dirty set are run state whose content depends on the marking, so only their size is modelled; the masks are compiled data and are modelled as their words, so that line 3 can say what a word is. A faithful layout holds every word the mask structure allocates, read or not: a word that lies in no transition's mask (the unread tail of a flat array allocated too large) sits at an ID that is no transition's. P is placeCountOf n, the places of the net each once (declared places and every place an arc or an output specification names), which is the place count of the compiled net (placeCountOf_eq, CONC-007); T is the number of transitions. The word size is 64 in Rust and Java and 32 in TypeScript, as the markdown says."
          "The reference layout refBitmapLayout keeps, per transition, the needs-mask and the inhibitor-mask of the reference compiled net (refCompileNet) packed into words by packBits, and no mask at an ID that is no transition's, so its masks are RefCompiled's mask words (refBitmapLayout_maskWords) and its total is RefCompiled's layoutWords, (1 + 2 × T) × ceil(P / ws) + ceil(T / ws) (refBitmapLayout_total). Its mask count is refMaskCount = 2: under ruling D55 (a) there is no reset-mask, since Rust and TypeScript keep the consumption places as a list and the reset-mask Java builds is read by no executor."
          "Line 2 is the mask count fixed per implementation (ruling D55 (a), PERF-R1 (a)): the number k is chosen before the net, so a layout whose number of masks grows with the net, one mask per arc of the transition (PERF_030_mutant_perArc), has no such k. The block fixes no value of k and sets no absolute memory cap: the markdown gives the values of the current implementations as information, k = 2 in Rust and TypeScript (the reference) and k = 5 in Java (the needs, inhibitor and reset BitSets and long-array copies of the needs-mask and the inhibitor-mask, java/src/main/java/org/libpetri/runtime/CompiledNet.java:59-65), and a layout with five masks per transition meets the block (PERF_030_allows_five). Which masks must be kept (the needs-mask and the inhibitor-mask) is CONC-007's line, not this block's: PERF-030 bounds memory only, so a layout that keeps fewer masks meets it."
          "A word of word_size bits is a number below 2^ws. Line 3 states it for the masks, so a layout that counts a wider number as one word is not a smaller layout (PERF_030_forbids_wideWords: masks of two-place numbers counted as 1-bit words). The presence bitmap and the dirty set are modelled by their size only and carry no such clause."
          "Line 5 is the quoted words no full-width mask words beside those masks: with it every word the mask structure holds is bounded, wherever a layout places it. Without it, flat mask arrays allocated with T × P words while the stride stays ceil(P / ws) (a hypothetical slip: flat mask arrays sized with the place count instead of the word count; Rust sizes its needs_masks and inhibitor_masks with word_count, rust/libpetri-runtime/src/compiled_net.rs:92-93) would meet lines 1 to 4, since every transition reads a slice of ceil(P / ws) words and the unread tail lies past the last slice (PERF_030_mutant_flatTail: on AC2's net 10003 words, perf030_flatTail_ac2). Placing the same tail inside a transition's masks is killed by line 3 or line 2, and spreading it over many IDs past T is killed by line 5, so the verdict no longer depends on where a model puts the words."
          "One wrong layout per line, each meeting the other four: a presence bitmap with one word per place (PERF_030_mutant_presencePerPlace, line 1), one mask per arc (PERF_030_mutant_perArc, line 2), masks with one word per place (PERF_030_mutant_wordPerPlace, line 3: on the AC2 net one word per place-transition pair and mask, 10003 words, perf030_wordPerPlace_ac2), a dirty set with one word per transition (PERF_030_mutant_dirtyPerTransition, line 4) and flat mask arrays with an unread tail past the last transition (PERF_030_mutant_flatTail, line 5)."
          "The third quoted sentence is a consequence of the five lines, not a line of its own: a layout that meets PERF-030 keeps at most (1 + k × T) × ceil(P / ws) + ceil(T / ws) words for every net, with the k of line 2 (PERF_030_total), and by line 5 the bound holds for the mask words at every ID, not only at the transitions' (PERF_030_held)."
          "The block counts words, not bytes: the heap cost of a mask object (a Java BitSet or long array, a TypeScript typed array, a Rust Vec) is not counted, which is why ruling D55 (a) states AC2 in words; a byte number would be false of Java. Further bitmaps an executor keeps beside the three structures (a copy of the presence bitmap or of the dirty set taken for one pass, the sets of enabled, in-flight, restart-pending or timed transitions, such as Java's timedMask, java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java:195-196) are outside the count, as the markdown says. A set of transitions is indexed by transition ID and is not a full-width mask: line 5 constrains only the mask words at transition IDs, which a set of transitions is not."
          "AC1 (the three structures take at most (1 + k × T) × ceil(P / word_size) + ceil(T / word_size) words, which grows with T × ceil(P / word_size), not with P × T) is PERF_030_total and PERF_030_held. A layout with one word per place in each mask grows with P × T and breaks it (PERF_030_mutant_wordPerPlace, perf030_wordPerPlace_ac2), as does a flat mask array of T × P words (PERF_030_mutant_flatTail, perf030_flatTail_ac2)."
          "AC2 (for 100 places and 50 transitions, at most (1 + 50 × k) × 2 + 1 words at 64-bit words, 203 for k = 2 and 503 for k = 5, and at most (1 + 50 × k) × 4 + 2 words at 32-bit words, 406 for k = 2) is PERF_030_ac2 and PERF_030_ac2_32: the reference on perf030Net, a net with 100 places and 50 transitions, keeps 203 words at 64 bits and 406 at 32 bits, and perf030_ac2_bound and perf030_ac2_bound_32 give the bounds for every k. The former wording ('< 1KB') was false of the reference: 203 words of 8 bytes are 1624 bytes (perf030_old_ac2_bytes)."
          "The test derivation (compile a 100-place, 50-transition net, sum the words that the presence bitmap, the mask arrays and the dirty set hold and compare the sum with AC2) is PERF_030_ac2 and PERF_030_ac2_32 on the reference. A runtime test that sums the allocated lengths of those arrays in an implementation is a quality test (kind Q); no test cites PERF-030 today."
          "The block is about the bitmap executor's three structures. The sparse masks of the precompiled executor are PERF-042's; its flat arrays are PERF-040's (kind Q)."
  signoff "2026-11-13 29912da2d6f403c4 ai"
  statement : ∀ {N : Type} [DecidableEq N], Nat → BitmapLayout N → Prop :=
    fun ws L => 0 < ws →
      (∀ n, L.presence n ≤ ceilDiv (placeCountOf n) ws) ∧
      (∃ k, ∀ n j, j < n.transitions.length → (L.masks n j).length ≤ k) ∧
      (∀ n j, j < n.transitions.length → ∀ m ∈ L.masks n j,
        m.length ≤ ceilDiv (placeCountOf n) ws ∧ ∀ x ∈ m, x < 2 ^ ws) ∧
      (∀ n, L.dirty n ≤ ceilDiv n.transitions.length ws) ∧
      (∀ n j, n.transitions.length ≤ j → L.masks n j = [])

/- The pinned readable form of PERF-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.PERF_030 : {N : Type} → [DecidableEq N] → ℕ → BitmapLayout N → Prop :=
fun {N} [DecidableEq N] ws L =>
  0 < ws →
    (∀ (n : Reference.Net N), L.presence n ≤ ceilDiv (placeCountOf n) ws) ∧
      (∃ k, ∀ (n : Reference.Net N), ∀ j < n.transitions.length, (L.masks n j).length ≤ k) ∧
        (∀ (n : Reference.Net N),
            ∀ j < n.transitions.length,
              ∀ m ∈ L.masks n j, m.length ≤ ceilDiv (placeCountOf n) ws ∧ ∀ x ∈ m, x < 2 ^ ws) ∧
          (∀ (n : Reference.Net N), L.dirty n ≤ ceilDiv n.transitions.length ws) ∧
            ∀ (n : Reference.Net N) (j : ℕ), n.transitions.length ≤ j → L.masks n j = []
-/
#guard_msgs in #print PERF_030

/-! ### The four lines, named (for the mutants) -/

section Lines

variable [DecidableEq N]

/-- Line 1 of PERF-030: the presence bitmap. -/
def perf030_line1 (ws : Nat) (L : BitmapLayout N) : Prop :=
  ∀ n, L.presence n ≤ ceilDiv (placeCountOf n) ws

/-- Line 2 of PERF-030: one mask count for every transition of every net. -/
def perf030_line2 (L : BitmapLayout N) : Prop :=
  ∃ k, ∀ n j, j < n.transitions.length → (L.masks n j).length ≤ k

/-- Line 3 of PERF-030: every mask in at most `⌈P / ws⌉` words of `ws` bits. -/
def perf030_line3 (ws : Nat) (L : BitmapLayout N) : Prop :=
  ∀ n j, j < n.transitions.length → ∀ m ∈ L.masks n j,
    m.length ≤ ceilDiv (placeCountOf n) ws ∧ ∀ x ∈ m, x < 2 ^ ws

/-- Line 4 of PERF-030: the dirty set. -/
def perf030_line4 (ws : Nat) (L : BitmapLayout N) : Prop :=
  ∀ n, L.dirty n ≤ ceilDiv n.transitions.length ws

/-- Line 5 of PERF-030: no mask at an ID that is no transition's. -/
def perf030_line5 (L : BitmapLayout N) : Prop :=
  ∀ n j, n.transitions.length ≤ j → L.masks n j = []

/-- PERF-030 is its five lines, at a positive word size. -/
theorem perf030_iff (ws : Nat) (L : BitmapLayout N) :
    PERF_030 ws L ↔
      (0 < ws → perf030_line1 ws L ∧ perf030_line2 L ∧ perf030_line3 ws L ∧ perf030_line4 ws L ∧
        perf030_line5 L) :=
  Iff.rfl

/-- PERF-030 without line 1. -/
def perf030_without1 (ws : Nat) (L : BitmapLayout N) : Prop :=
  0 < ws → perf030_line2 L ∧ perf030_line3 ws L ∧ perf030_line4 ws L ∧ perf030_line5 L

/-- PERF-030 without line 2. -/
def perf030_without2 (ws : Nat) (L : BitmapLayout N) : Prop :=
  0 < ws → perf030_line1 ws L ∧ perf030_line3 ws L ∧ perf030_line4 ws L ∧ perf030_line5 L

/-- PERF-030 without line 3. -/
def perf030_without3 (ws : Nat) (L : BitmapLayout N) : Prop :=
  0 < ws → perf030_line1 ws L ∧ perf030_line2 L ∧ perf030_line4 ws L ∧ perf030_line5 L

/-- PERF-030 without line 4. -/
def perf030_without4 (ws : Nat) (L : BitmapLayout N) : Prop :=
  0 < ws → perf030_line1 ws L ∧ perf030_line2 L ∧ perf030_line3 ws L ∧ perf030_line5 L

/-- PERF-030 without line 5. -/
def perf030_without5 (ws : Nat) (L : BitmapLayout N) : Prop :=
  0 < ws → perf030_line1 ws L ∧ perf030_line2 L ∧ perf030_line3 ws L ∧ perf030_line4 ws L

end Lines

/-! ### Packed layouts and the reference -/

section Packed

variable [DecidableEq N]

/-- A packed layout keeps the presence bitmap in `⌈P / ws⌉` words. -/
theorem packedLayout_line1 (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool)) :
    perf030_line1 ws (packedLayout ws bits) :=
  fun _ => Nat.le_refl _

/-- A packed layout keeps every mask in `⌈P / ws⌉` words of `ws` bits (`packBits_length`,
`packWord_lt`). -/
theorem packedLayout_line3 (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool)) :
    perf030_line3 ws (packedLayout ws bits) := by
  intro n j hj m hm
  simp only [packedLayout, hj, if_true, List.mem_map] at hm
  obtain ⟨b, -, rfl⟩ := hm
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [packBits, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact packWord_lt _ _ _

/-- A packed layout keeps the dirty set in `⌈T / ws⌉` words. -/
theorem packedLayout_line4 (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool)) :
    perf030_line4 ws (packedLayout ws bits) :=
  fun _ => Nat.le_refl _

/-- A packed layout keeps no mask at an ID that is no transition's. -/
theorem packedLayout_line5 (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool)) :
    perf030_line5 (packedLayout ws bits) := fun _ _ hj => by
  simp [packedLayout, Nat.not_lt.2 hj]

/-- A packed layout keeps as many masks per transition as it is given bitmaps. -/
@[simp] theorem packedLayout_masks_length (ws : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool))
    (n : Reference.Net N) {j : Nat} (hj : j < n.transitions.length) :
    ((packedLayout ws bits).masks n j).length = (bits n j).length := by
  simp [packedLayout, hj]

/-- A packed layout with at most `k` bitmaps per transition meets PERF-030. -/
theorem PERF_030_packed (ws k : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool))
    (hk : ∀ n j, j < n.transitions.length → (bits n j).length ≤ k) :
    PERF_030 ws (packedLayout ws bits) := fun _ =>
  ⟨packedLayout_line1 ws bits, ⟨k, fun n j hj => by simpa [hj] using hk n j hj⟩,
    packedLayout_line3 ws bits, packedLayout_line4 ws bits, packedLayout_line5 ws bits⟩

/-- ✓ The reference bitmap layout satisfies PERF-030 at every word size, with `k = 2` (its
needs-mask and its inhibitor-mask), each packed into `⌈P / ws⌉` words of `ws` bits. -/
@[evidence holds PERF_030]
theorem PERF_030_reference (ws : Nat) : PERF_030 ws (refBitmapLayout (N := N) ws) :=
  PERF_030_packed ws refMaskCount _ fun _ _ _ => by simp [refMaskCount]

/-- The reference layout's masks, transition after transition, are RefCompiled's mask words
(`CompiledNet.maskWords`). -/
theorem refBitmapLayout_maskWords (ws : Nat) (n : Reference.Net N) :
    (List.range n.transitions.length).flatMap ((refBitmapLayout ws).masks n) =
      (refCompileNet n).maskWords ws := by
  unfold CompiledNet.maskWords
  refine List.flatMap_congr fun j hj => ?_
  simp only [refBitmapLayout, packedLayout, List.mem_range.1 hj, if_true, List.map_cons,
    List.map_nil]
  rfl

/-- The words a packed layout with `k` bitmaps per transition keeps:
`(1 + k * T) * ⌈P / ws⌉ + ⌈T / ws⌉`. -/
theorem packedLayout_total (ws k : Nat) (bits : Reference.Net N → Nat → List (Nat → Bool))
    (hk : ∀ n j, (bits n j).length = k) (n : Reference.Net N) :
    (packedLayout ws bits).total n =
      (1 + k * n.transitions.length) * ceilDiv (placeCountOf n) ws +
        ceilDiv n.transitions.length ws := by
  simp only [BitmapLayout.total]
  have : ∀ j ∈ List.range n.transitions.length,
      (((packedLayout ws bits).masks n j).map List.length).sum =
        (List.replicate k (ceilDiv (placeCountOf n) ws)).sum := by
    intro j hj
    congr 1
    simp only [packedLayout, List.mem_range.1 hj, if_true, List.map_map]
    rw [List.eq_replicate_iff]
    refine ⟨by simp [hk], fun x hx => ?_⟩
    simp only [List.mem_map, Function.comp_apply, packBits_length] at hx
    obtain ⟨_, -, rfl⟩ := hx
    rfl
  rw [List.map_congr_left this]
  simp only [List.sum_replicate, smul_eq_mul, List.map_const', List.length_range]
  simp only [packedLayout]
  ring

/-- The reference layout keeps exactly RefCompiled's word count `layoutWords`:
`(1 + 2 * T) * ⌈P / ws⌉ + ⌈T / ws⌉`. -/
theorem refBitmapLayout_total (ws : Nat) (n : Reference.Net N) :
    (refBitmapLayout ws).total n = (refCompileNet n).layoutWords ws := by
  rw [refBitmapLayout, packedLayout_total ws 2 _ (fun _ _ => rfl), layoutWords_eq]
  rfl

end Packed

/-! ### The total -/

/-- **The third quoted sentence.** A layout that meets PERF-030 keeps, for every net, at most
`(1 + k * T) * ⌈P / ws⌉ + ⌈T / ws⌉` words, with the mask count `k` of line 2. -/
theorem PERF_030_total [DecidableEq N] {ws : Nat} {L : BitmapLayout N} (h : PERF_030 ws L)
    (hws : 0 < ws) :
    ∃ k, ∀ n, L.total n ≤
      (1 + k * n.transitions.length) * ceilDiv (placeCountOf n) ws +
        ceilDiv n.transitions.length ws := by
  obtain ⟨h1, ⟨k, h2⟩, h3, h4, -⟩ := h hws
  refine ⟨k, fun n => ?_⟩
  set W := ceilDiv (placeCountOf n) ws
  have hmask : ∀ j ∈ List.range n.transitions.length, ((L.masks n j).map List.length).sum ≤ k * W := by
    intro j hj
    have hj' := List.mem_range.1 hj
    have hle : ((L.masks n j).map List.length).sum ≤ ((L.masks n j).map List.length).length • W :=
      List.sum_le_card_nsmul _ _ fun x hx => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
        exact (h3 n j hj' m hm).1
    simp only [List.length_map, smul_eq_mul] at hle
    exact hle.trans (Nat.mul_le_mul_right _ (h2 n j hj'))
  have hsum : ((List.range n.transitions.length).map fun j => ((L.masks n j).map List.length).sum).sum ≤
      n.transitions.length * (k * W) := by
    have := List.sum_le_card_nsmul
      ((List.range n.transitions.length).map fun j => ((L.masks n j).map List.length).sum) (k * W)
      fun x hx => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact hmask j hj
    simpa using this
  have e : (1 + k * n.transitions.length) * W = W + n.transitions.length * (k * W) := by ring
  unfold BitmapLayout.total
  have := h1 n
  have := h4 n
  omega

/-- The words a layout holds for a net when the masks at the IDs `0 … m - 1` are counted, the IDs
of no transition included when `m > T`. -/
def BitmapLayout.held (L : BitmapLayout N) (n : Reference.Net N) (m : Nat) : Nat :=
  L.presence n + ((List.range m).map fun j => ((L.masks n j).map List.length).sum).sum + L.dirty n

/-- The words held at the first `T` IDs are the layout's total. -/
theorem BitmapLayout.held_transitions (L : BitmapLayout N) (n : Reference.Net N) :
    L.held n n.transitions.length = L.total n := rfl

/-- A sum over `range m` of a function that is zero from `T` on is the sum over `range (min m T)`. -/
theorem perf030_sum_range_min (f : Nat → Nat) (T : Nat) (hf : ∀ j, T ≤ j → f j = 0) :
    ∀ m, ((List.range m).map f).sum = ((List.range (min m T)).map f).sum
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, perf030_sum_range_min f T hf m]
    by_cases hm : m < T
    · rw [show min (m + 1) T = min m T + 1 by omega, show min m T = m by omega, List.range_succ,
        List.map_append, List.sum_append]
    · rw [show min (m + 1) T = min m T by omega]
      simp [hf m (by omega)]

/-- **Line 5 closes the count.** A layout that meets PERF-030 keeps the bound of the third quoted
sentence for the mask words at every ID, not only at the IDs of the transitions: no mask word the
mask structure holds escapes it. -/
theorem PERF_030_held [DecidableEq N] {ws : Nat} {L : BitmapLayout N} (h : PERF_030 ws L)
    (hws : 0 < ws) :
    ∃ k, ∀ n m, L.held n m ≤
      (1 + k * n.transitions.length) * ceilDiv (placeCountOf n) ws +
        ceilDiv n.transitions.length ws := by
  obtain ⟨k, hk⟩ := PERF_030_total h hws
  refine ⟨k, fun n m => ?_⟩
  have h5 := (h hws).2.2.2.2 n
  have hle : ((List.range m).map fun j => ((L.masks n j).map List.length).sum).sum ≤
      ((List.range n.transitions.length).map fun j => ((L.masks n j).map List.length).sum).sum := by
    rw [perf030_sum_range_min _ n.transitions.length (fun j hj => by simp [h5 j hj]) m]
    have key : ∀ a d, ((List.range a).map fun j => ((L.masks n j).map List.length).sum).sum ≤
        ((List.range (a + d)).map fun j => ((L.masks n j).map List.length).sum).sum := by
      intro a d
      rw [List.range_add, List.map_append, List.sum_append]
      exact Nat.le_add_right _ _
    have := key (min m n.transitions.length) (n.transitions.length - min m n.transitions.length)
    rwa [show min m n.transitions.length + (n.transitions.length - min m n.transitions.length) =
      n.transitions.length by omega] at this
  have := hk n
  unfold BitmapLayout.held
  unfold BitmapLayout.total at this
  omega

/-! ### Two concrete nets -/

/-- A net with two places, `0` and `1`, and two transitions: `a` takes a token from each place,
`b` takes one from place `0` while place `1` is empty and deposits into `1`. -/
def perf030SmallNet : Reference.Net Nat :=
  ⟨[0, 1], [⟨⟨"a", [⟨0, .one⟩, ⟨1, .one⟩], [], [], []⟩, none, false⟩,
            ⟨⟨"b", [⟨0, .one⟩], [1], [], []⟩, some (.place 1), false⟩]⟩

/-- AC2's net: 100 places and 50 transitions; transition `j` takes a token from place `2 j` and
deposits one into place `2 j + 1`. -/
def perf030Net : Reference.Net Nat :=
  ⟨List.range 100, (List.range 50).map fun j =>
    ⟨⟨"t", [⟨2 * j, .one⟩], [], [], []⟩, some (.place (2 * j + 1)), false⟩⟩

set_option maxRecDepth 100000 in
/-- AC2's net has 100 places. -/
theorem perf030Net_places : placeCountOf perf030Net = 100 := by decide

/-- AC2's net has 50 transitions. -/
theorem perf030Net_transitions : perf030Net.transitions.length = 50 := by simp [perf030Net]

/-! ### Evidence: the reference on the two nets -/

/-- **AC2.** At 64-bit words the reference keeps 203 words for AC2's net, 100 places and 50
transitions: 2 for the presence bitmap, 2 masks of 2 words for each of the 50 transitions, and 1
for the dirty set. That is the bound `(1 + k × T) × ⌈P / 64⌉ + ⌈T / 64⌉` at `k = 2`. -/
@[evidence nonvacuous PERF_030]
theorem PERF_030_ac2 :
    (refBitmapLayout 64).total perf030Net = 203 ∧
      (1 + 2 * perf030Net.transitions.length) * ceilDiv (placeCountOf perf030Net) 64 +
        ceilDiv perf030Net.transitions.length 64 = 203 := by
  have e : (1 + 2 * perf030Net.transitions.length) * ceilDiv (placeCountOf perf030Net) 64 +
      ceilDiv perf030Net.transitions.length 64 = 203 := by
    rw [perf030Net_places, perf030Net_transitions]
    decide
  refine ⟨?_, e⟩
  rw [refBitmapLayout, packedLayout_total 64 2 _ (fun _ _ => rfl), e]

/-- **AC2 at 32-bit words** (TypeScript): the reference keeps 406 words for AC2's net, 4 for the
presence bitmap, 2 masks of 4 words for each of the 50 transitions, and 2 for the dirty set. -/
theorem PERF_030_ac2_32 : (refBitmapLayout 32).total perf030Net = 406 := by
  rw [refBitmapLayout, packedLayout_total 32 2 _ (fun _ _ => rfl), perf030Net_places,
    perf030Net_transitions]
  decide

/-- AC2's bound at every mask count at 32-bit words: `(1 + 50 × k) × 4 + 2` words. -/
theorem perf030_ac2_bound_32 (k : Nat) :
    (1 + k * 50) * ceilDiv 100 32 + ceilDiv 50 32 = (1 + 50 * k) * 4 + 2 := by
  have h1 : ceilDiv 100 32 = 4 := by decide
  have h2 : ceilDiv 50 32 = 2 := by decide
  rw [h1, h2, Nat.mul_comm k 50]

/-- AC2's bound at every mask count: with 64-bit words, 100 places and 50 transitions, the three
structures take at most `(1 + 50 × k) × 2 + 1` words (203 for `k = 2`, 503 for `k = 5`). -/
theorem perf030_ac2_bound (k : Nat) :
    (1 + k * 50) * ceilDiv 100 64 + ceilDiv 50 64 = (1 + 50 * k) * 2 + 1 := by
  have h1 : ceilDiv 100 64 = 2 := by decide
  have h2 : ceilDiv 50 64 = 1 := by decide
  rw [h1, h2, Nat.mul_comm k 50]

/-- The former AC2 ('< 1KB') is false of the reference: its 203 words of 8 bytes are 1624
bytes. -/
theorem perf030_old_ac2_bytes : 8 * (refBitmapLayout 64).total perf030Net = 1624 ∧ ¬ 1624 < 1024 := by
  rw [PERF_030_ac2.1]
  decide

/-- ✓ The reference on the small net at 64-bit words: transition `a` has the needs-mask word `3`
(places 0 and 1) and an empty inhibitor-mask, transition `b` the needs-mask word `1` (place 0) and
the inhibitor-mask word `2` (place 1); with the presence bitmap and the dirty set, one word each,
the layout keeps 6 words, and RefCompiled's mask words are the four masks in transition order. -/
@[evidence nonvacuous PERF_030]
theorem PERF_030_nonvacuous :
    (refBitmapLayout 64).masks perf030SmallNet 0 = [[3], [0]] ∧
      (refBitmapLayout 64).masks perf030SmallNet 1 = [[1], [2]] ∧
      (refBitmapLayout 64).presence perf030SmallNet = 1 ∧
      (refBitmapLayout 64).dirty perf030SmallNet = 1 ∧
      (refBitmapLayout 64).total perf030SmallNet = 6 ∧
      (refCompileNet perf030SmallNet).maskWords 64 = [[3], [0], [1], [2]] := by
  decide

/-! ### Allowed: five masks per transition (Java) -/

/-- The reset-mask of transition `j`: the place IDs of its reset places (Java's `resetMask`,
which no executor reads). -/
def perf030ResetBits [DecidableEq N] (n : Reference.Net N) (j i : Nat) : Bool :=
  match n.transitions[j]?, (refCompileNet n).placeAt i with
  | some t, some p => decide (p ∈ t.core.resets)
  | _, _ => false

/-- Java's layout: per transition, the needs-mask, the inhibitor-mask and the reset-mask as
`BitSet`s and a long-array copy of the needs-mask and of the inhibitor-mask
(`java/src/main/java/org/libpetri/runtime/CompiledNet.java:59-65`), five masks of `⌈P / 64⌉`
words. -/
def perf030JavaLayout [DecidableEq N] (ws : Nat) : BitmapLayout N :=
  packedLayout ws fun n j =>
    [(refCompileNet n).needs j, (refCompileNet n).inhibitor j, perf030ResetBits n j,
      (refCompileNet n).needs j, (refCompileNet n).inhibitor j]

/-- ✓ A layout with five masks per transition, as Java keeps, meets PERF-030 with `k = 5`: the
requirement fixes the mask count per implementation, not at the reference's 2. -/
@[evidence allows PERF_030]
theorem PERF_030_allows_five [DecidableEq N] (ws : Nat) : PERF_030 ws (perf030JavaLayout (N := N) ws) :=
  PERF_030_packed ws 5 _ fun _ _ _ => by simp

/-! ### Mutants, one per line -/

section Mutants

variable [DecidableEq N]

/-- A presence bitmap with one word per place (a boolean array). -/
def perf030PresencePerPlace (ws : Nat) : BitmapLayout N :=
  { refBitmapLayout ws with presence := placeCountOf }

/-- One full-width mask per arc of the transition (a bitmap for each arc place), so the number of
masks grows with the transition. -/
def perf030PerArc (ws : Nat) : BitmapLayout N :=
  packedLayout ws fun n j =>
    match n.transitions[j]? with
    | some t => (arcPlaces t).map fun p i => decide ((refCompileNet n).placeId p = some i)
    | none => []

/-- Masks with one word per place: the reference's two masks, each packed one place per word. -/
def perf030WordPerPlace (ws : Nat) : BitmapLayout N :=
  { refBitmapLayout ws with masks := (refBitmapLayout 1).masks }

/-- A dirty set with one word per transition (a list or array of flags). -/
def perf030DirtyPerTransition (ws : Nat) : BitmapLayout N :=
  { refBitmapLayout ws with dirty := fun n => n.transitions.length }

/-- The unread tail of one flat mask array allocated with `T × P` words where `T × ⌈P / ws⌉` were
meant: the `T × (P - ⌈P / ws⌉)` words past the last transition's slice. -/
def perf030FlatTail (n : Reference.Net N) (ws : Nat) : List Nat :=
  List.replicate (n.transitions.length * (placeCountOf n - ceilDiv (placeCountOf n) ws)) 0

/-- Flat mask arrays allocated with `T × P` words while the stride stays `⌈P / ws⌉` (a hypothetical
slip; Rust sizes its `needs_masks` and `inhibitor_masks` with the word count): every transition
reads the reference's masks, and the unread tails of the two arrays lie past the last transition's
slice, at the ID `T`. -/
def perf030FlatPlaceCount (ws : Nat) : BitmapLayout N :=
  { refBitmapLayout ws with
    masks := fun n j =>
      if j < n.transitions.length then (refBitmapLayout ws).masks n j
      else if j = n.transitions.length then [perf030FlatTail n ws, perf030FlatTail n ws] else [] }

/-- Masks packed into numbers of twice the word size, each reported as one word. -/
def perf030WideWords (ws : Nat) : BitmapLayout N :=
  { refBitmapLayout ws with masks := (refBitmapLayout (2 * ws)).masks }

end Mutants

/-- ✗ A presence bitmap with one word per place meets lines 2 to 4 and violates PERF-030 through
line 1: the small net's two places take 2 words where `⌈2 / 64⌉ = 1`. -/
@[evidence mutant PERF_030]
theorem PERF_030_mutant_presencePerPlace :
    perf030_without1 64 (perf030PresencePerPlace (N := Nat) 64) ∧
      ¬ PERF_030 64 (perf030PresencePerPlace (N := Nat) 64) := by
  refine ⟨fun hws => ?_, fun h => ?_⟩
  · obtain ⟨-, h2, h3, h4, h5⟩ := PERF_030_reference (N := Nat) 64 hws
    exact ⟨h2, h3, h4, h5⟩
  · have := (h (by decide)).1 perf030SmallNet
    revert this
    decide

/-- ✗ One mask per arc meets lines 1, 3 and 4 and violates PERF-030 through line 2: for every
`k`, a transition with `k + 1` input arcs has `k + 1` masks, so no mask count fixed before the
net bounds it. -/
@[evidence mutant PERF_030]
theorem PERF_030_mutant_perArc :
    perf030_without2 64 (perf030PerArc (N := Nat) 64) ∧ ¬ PERF_030 64 (perf030PerArc (N := Nat) 64) := by
  refine ⟨fun _ => ⟨packedLayout_line1 _ _, packedLayout_line3 _ _, packedLayout_line4 _ _,
    packedLayout_line5 _ _⟩, fun h => ?_⟩
  obtain ⟨k, hk⟩ := (h (by decide)).2.1
  let t : Reference.Trans Nat :=
    ⟨⟨"wide", (List.range (k + 1)).map fun i => ⟨i, .one⟩, [], [], []⟩, none, false⟩
  have := hk ⟨[], [t]⟩ 0 (by simp)
  simp [perf030PerArc, packedLayout, t, arcPlaces] at this

/-- ✗ Masks with one word per place meet lines 1, 2 and 4 and violate PERF-030 through line 3:
on the small net each mask takes 2 words where `⌈2 / 64⌉ = 1`. -/
@[evidence mutant PERF_030]
theorem PERF_030_mutant_wordPerPlace :
    perf030_without3 64 (perf030WordPerPlace (N := Nat) 64) ∧
      ¬ PERF_030 64 (perf030WordPerPlace (N := Nat) 64) := by
  refine ⟨fun hws => ?_, fun h => ?_⟩
  · obtain ⟨h1, -, -, h4, -⟩ := PERF_030_reference (N := Nat) 64 hws
    exact ⟨h1, ⟨2, fun n j hj => by simp [perf030WordPerPlace, refBitmapLayout, packedLayout, hj]⟩, h4,
      fun n j hj => by simp [perf030WordPerPlace, refBitmapLayout, packedLayout, Nat.not_lt.2 hj]⟩
  · have := (h (by decide)).2.2.1 perf030SmallNet 0 (by decide)
    revert this
    decide

/-- On AC2's net, masks with one word per place take one word per place, transition and mask:
2 + 50 × 2 × 100 + 1 = 10003 words, against the bound of 203. -/
theorem perf030_wordPerPlace_ac2 : (perf030WordPerPlace 64).total perf030Net = 10003 := by
  have h := packedLayout_total 1 2
    (fun n j => [(refCompileNet n).needs j, (refCompileNet n).inhibitor j])
    (fun _ _ => rfl) perf030Net
  have e : (perf030WordPerPlace 64).total perf030Net =
      ceilDiv (placeCountOf perf030Net) 64 +
        ((refBitmapLayout 1).total perf030Net - ceilDiv (placeCountOf perf030Net) 1 -
          ceilDiv perf030Net.transitions.length 1) +
        ceilDiv perf030Net.transitions.length 64 := by
    simp only [BitmapLayout.total, perf030WordPerPlace, refBitmapLayout, packedLayout]
    omega
  rw [e, refBitmapLayout, h, perf030Net_places, perf030Net_transitions]
  decide

/-- ✗ A dirty set with one word per transition meets lines 1 to 3 and violates PERF-030 through
line 4: the small net's two transitions take 2 words where `⌈2 / 64⌉ = 1`. -/
@[evidence mutant PERF_030]
theorem PERF_030_mutant_dirtyPerTransition :
    perf030_without4 64 (perf030DirtyPerTransition (N := Nat) 64) ∧
      ¬ PERF_030 64 (perf030DirtyPerTransition (N := Nat) 64) := by
  refine ⟨fun hws => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, -, h5⟩ := PERF_030_reference (N := Nat) 64 hws
    exact ⟨h1, h2, h3, h5⟩
  · have := (h (by decide)).2.2.2.1 perf030SmallNet
    revert this
    decide

/-- ✗ Flat mask arrays of `T × P` words with the stride of `⌈P / ws⌉` meet lines 1 to 4 (every
transition reads the reference's masks) and violate PERF-030 through line 5: on the small net the
unread tails of the two arrays, 2 words each, lie at the ID 2, which is no transition's. -/
@[evidence mutant PERF_030]
theorem PERF_030_mutant_flatTail :
    perf030_without5 64 (perf030FlatPlaceCount (N := Nat) 64) ∧
      ¬ PERF_030 64 (perf030FlatPlaceCount (N := Nat) 64) := by
  refine ⟨fun hws => ?_, fun h => ?_⟩
  · obtain ⟨h1, ⟨k, h2⟩, h3, h4, -⟩ := PERF_030_reference (N := Nat) 64 hws
    refine ⟨h1, ⟨k, fun n j hj => ?_⟩, fun n j hj m hm => ?_, h4⟩
    · simpa [perf030FlatPlaceCount, hj] using h2 n j hj
    · simp only [perf030FlatPlaceCount, hj, if_true] at hm
      exact h3 n j hj m hm
  · have := (h (by decide)).2.2.2.2 perf030SmallNet 2 (by decide)
    revert this
    decide

/-- On AC2's net, at 64-bit words, the flat arrays of `T × P` words hold 10003 words when the
words at the ID `T` are counted, against the bound of 203 that the reference meets. -/
theorem perf030_flatTail_ac2 : (perf030FlatPlaceCount 64).held perf030Net 51 = 10003 := by
  have hc : ((List.range perf030Net.transitions.length).map fun j =>
        (((perf030FlatPlaceCount 64).masks perf030Net j).map List.length).sum) =
      ((List.range perf030Net.transitions.length).map fun j =>
        (((refBitmapLayout 64).masks perf030Net j).map List.length).sum) := by
    apply List.map_congr_left
    intro j hj
    simp [perf030FlatPlaceCount, List.mem_range.1 hj]
  have e : (perf030FlatPlaceCount 64).held perf030Net 51 =
      (refBitmapLayout 64).total perf030Net + 2 * (perf030FlatTail perf030Net 64).length := by
    rw [show 51 = perf030Net.transitions.length + 1 by rw [perf030Net_transitions]]
    simp only [BitmapLayout.held, BitmapLayout.total, List.range_succ, List.map_append,
      List.sum_append, hc]
    simp [perf030FlatPlaceCount]
    omega
  rw [e, PERF_030_ac2.1]
  simp only [perf030FlatTail, List.length_replicate, perf030Net_transitions, perf030Net_places]
  decide

/-- ✗ Counting a mask packed into numbers of twice the word size as that many words violates
PERF-030 through the word-size clause of line 3: at 1-bit words, transition `a` of the small net
has the needs-mask packed into the one number `3`, which is no 1-bit word. -/
@[evidence forbids PERF_030]
theorem PERF_030_forbids_wideWords : ¬ PERF_030 1 (perf030WideWords (N := Nat) 1) := fun h => by
  have := (h (by decide)).2.2.1 perf030SmallNet 0 (by decide)
  revert this
  decide

end Libpetri.Spec
