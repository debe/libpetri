import Libpetri.Spec.Text

requirement_text NU_022
  id "NU-022"
  title "Deterministic Match Selection"
  priority MUST
  kind F
  body r#"When more than one correlation name is simultaneously eligible at a matched
transition, the implementation MUST select the name with the smallest
`(oldest correlated-token timestamp, then NameId)` ordering: oldest first, ties
broken by name. The selection is a pure function of the current marking and MUST
be **identical across all conforming implementations** on names whose values hold only Basic
Multilingual Plane characters ([NU-001]): the firing tie-break
(`selectMatchName` / `select_match_name`) is byte-identical on such names, and any incremental
acceleration of it MUST return byte-identical results to the reference function.
A token a `ForwardInput` forwards on a timeout outcome keeps its original `created_at` in
every implementation ([IO-014]), so a name whose oldest correlated token was forwarded
orders the same everywhere.

A name is eligible at a matched transition when the match keys at least one input and every
correlated input holds at least one token of the name and at least the input's required count of
such tokens; a token whose key yields no name counts for no name ([NU-020]). The oldest
correlated-token timestamp of a name is the earliest `createdAt` among all tokens of the name in
the correlated inputs, whether the firing consumes them or not.

⟦s1|*If* some name is eligible at a matched transition, *then* the selection *shall* return a name.⟧

⟦s2|*When* the selection returns a name, that name *shall* be eligible, and no eligible name *shall* precede it in the order by oldest correlated-token timestamp, then by name order.⟧

**Acceptance Criteria:**
1. Given the same eligible *(name → correlated-token timestamps)* state, every
   implementation selects the same `NameId`.
2. An incremental matcher returns the same `NameId` as the reference
   `selectMatchName` for any sequence of add/consume operations.
3. `NameId` ordering is byte-identical for ASCII/BMP names (an executor-minted
   name is one whenever its transition name and any host-pinned scope are — the
   default scope and the counter are ASCII; [NU-011]); supplementary-plane code
   points MAY order differently per
   [NU-001] (UTF-8 byte order vs UTF-16 code-unit order).

**Depends on:** [NU-020], [NU-001]
**Test derivation:** A randomised differential test (`MatchEngineIncrementalTest`,
`incremental_matches_select_byte_for_byte`, `incremental-matcher.test.ts`) asserts
the incremental `best()` equals `selectMatchName` over non-monotonic timestamps."#
