import Libpetri.Spec.Text

requirement_text PERF_030
  id "PERF-030"
  title "Bitmap Memory Efficiency"
  priority MUST
  kind F
  body r#"The bitmap executor uses compact representations:
- Place presence: 1 bit per place per bitmap word
- Transition masks: k full-width masks per transition, each ceil(P / word_size) words
- Dirty set: 1 bit per transition

The word size is 64 bits in Rust and Java and 32 bits in TypeScript. The mask count k does not depend on the net. In the current implementations k is 2 in Rust and TypeScript (the needs-mask and the inhibitor-mask of [CONC-007]) and 5 in Java (a reset-mask besides the two, and a word-array copy of each of the two).

For a net with P places and T transitions:
- Presence bitmap: ceil(P / word_size) words
- Per-transition masks: k × ceil(P / word_size) words for each transition
- Dirty set: ceil(T / word_size) words

⟦s1|For a net with P places and T transitions, the bitmap executor *shall* keep its presence bitmap in at most ceil(P / word_size) words, each full-width mask of a transition in at most ceil(P / word_size) words of word_size bits, and its dirty set in at most ceil(T / word_size) words.⟧

⟦s2|The bitmap executor *shall* keep at most k full-width masks per transition, for one number k that the implementation fixes and that does not depend on the net, and no full-width mask words beside those masks.⟧

⟦s3|Together the three structures take at most (1 + k × T) × ceil(P / word_size) + ceil(T / word_size) words.⟧ Further bitmaps an executor keeps beside them (a copy of the presence bitmap or of the dirty set taken for one pass, or a set of enabled, in-flight, restart-pending or timed transitions) are outside this count, and so is the heap overhead of the arrays that hold the words.

**Acceptance Criteria:**
1. The three structures take at most (1 + k × T) × ceil(P / word_size) + ceil(T / word_size) words, which grows with T × ceil(P / word_size), not with P × T.
2. A net with 100 places and 50 transitions keeps at most (1 + 50 × k) × 2 + 1 words in the three structures with 64-bit words (203 words for k = 2 and 503 words for k = 5) and at most (1 + 50 × k) × 4 + 2 words with 32-bit words (406 words for k = 2).

**Test derivation:** Compile a 100-place, 50-transition net; sum the words that the presence bitmap, the mask arrays and the dirty set hold, and compare the sum with AC2."#
