import Libpetri.Spec.Text

requirement_text PERF_042
  id "PERF-042"
  title "Sparse Enablement Masks"
  priority SHOULD
  kind F
  body r#"Enablement masks SHOULD use a sparse representation to avoid scanning zero words in large nets. Three cases:
- **Empty** (sentinel value): skip the check entirely (e.g., transition with no input places or no inhibitors)
- **Single-word** (fast path): store word index + mask value; one AND + one compare operation
- **Multi-word sparse**: store only non-zero word indices and their mask values; iterate only non-zero entries

This avoids scanning W words when most are zero (common in large, sparse nets).

⟦s1|*Where* an executor uses sparse enablement masks, it *shall* compile a needs-mask or an inhibitor-mask to the empty sentinel exactly when all its words are zero and a mask with exactly one non-zero word to the single-word form holding that word's index and value, and it *shall* put only non-zero words of the mask, each with its index, into a multi-word form.⟧

⟦s2|*Where* an executor uses sparse enablement masks, its presence check on the sparse forms compiled from a transition's needs-mask and inhibitor-mask *shall* return, for every presence bitmap, the result of the presence check of [CONC-004] computed over every word of both masks.⟧

⟦s3|These two sentences hold for masks and presence bitmaps of the same number of words, each word within the executor's word size.⟧ The SHOULD above is about whether an executor uses a sparse representation at all; an executor that does is bound by the two sentences above.

**Acceptance Criteria:**
1. Empty masks are detected and skipped with no computation.
2. Single-word masks use one AND + one compare (no loop).
3. Multi-word sparse masks iterate only non-zero words.
4. ⟦s4|Enablement results are identical to full-width bitmap checks.⟧

**Depends on:** [CONC-004], [CONC-020]
**Test derivation:** Net with 200 places where each transition touches 2–3 places; verify sparse check matches full bitmap check and is faster."#
