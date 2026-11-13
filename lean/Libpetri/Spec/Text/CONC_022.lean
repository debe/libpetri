import Libpetri.Spec.Text

requirement_text CONC_022
  id "CONC-022"
  title "Flat-Array Token Storage"
  priority SHOULD
  kind F
  body r#"Token storage uses ring buffers indexed by place ID for O(1) access. Each place has a dedicated ring buffer that preserves FIFO ordering [CORE-013] and grows dynamically when capacity is exceeded.

⟦s1|The precompiled executor's token storage *shall* hold a dedicated queue for each place of the net it is built for.⟧

⟦s2|*When* a token is added to a place the token storage holds a queue for, the token storage *shall* append it at the tail of the place's queue whatever the capacity of the place's storage, *shall* keep holding a queue for every place it held, and *shall* leave the queue of every other place unchanged.⟧

⟦s3|*When* the first token of a marked place the token storage holds a queue for is removed, the token storage *shall* return the head of the place's queue, keep the rest of that queue in queue order, keep holding a queue for every place it held, and leave the queue of every other place unchanged.⟧

⟦s4|*When* the first token of a place the token storage holds a queue for is read without removing it, the token storage *shall* return the head of the place's queue, or nothing when the place is not marked.⟧

⟦s5|The token storage *shall* report as the token count of a place it holds a queue for the length of the place's queue.⟧

**Acceptance Criteria:**
1. Token access is O(1) by place ID — no hashing or map lookup.
2. FIFO ordering is preserved (oldest token consumed first, except on a correlated input of a match specification, [NU-020]).
3. Ring buffers grow dynamically when capacity is exceeded.
4. Token count per place is available in O(1).

**Depends on:** [CORE-013]
**Test derivation:** Add and consume tokens in various orders; verify FIFO ordering and correct counts."#
