import Libpetri.Spec.Text

requirement_text CONC_008
  id "CONC-008"
  title "Multi-Phase Enablement"
  priority MUST
  kind F
  body r#"Enablement checking is a multi-phase process:
1. **Phase 1 — Bitmap presence check**: O(W) bitwise check against needs-mask and inhibitor-mask. Fast reject for most transitions.
2. **Phase 2 — Cardinality check**: For transitions with Exactly(n)/All/AtLeast(m), verify actual token counts meet thresholds.
3. **Phase 3 — ν-match check**: For transitions carrying a match specification ([NU-020]), scan the correlated inputs for a name of which every correlated input holds at least its required count of tokens of that name. This is the only per-token phase; there is no value-predicate phase (guards were removed, [IO-006]).

Phases 2 and 3 are only reached if Phase 1 passes, minimizing work for most transitions.

⟦s1|*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, and its presence check passes on the presence bitmap of the marking, its cardinality check *shall* pass exactly when every input place holds at least its required count.⟧

⟦s2|*When* a transition that builds has no match specification and has an `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking and the cardinality check passes.⟧

⟦s3|*When* a transition that builds has no match specification and no `Exactly(n)`, `All` or `AtLeast(m)` input, its enablement check *shall* pass exactly when the presence check passes on the presence bitmap of the marking.⟧

⟦s4|*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when the transition is enabled ([CORE-022]).⟧

⟦s5|*When* a transition that builds has a match specification and phases 1 and 2 pass on the token counts of the marking, its ν-match check *shall* pass exactly when the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name ([NU-020]).⟧

⟦s6|*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking and its ν-match check passes.⟧

⟦s7|*When* a transition that builds has no match specification, its enablement check *shall* pass exactly when phases 1 and 2 pass on the token counts of the marking.⟧

⟦s8|*When* a transition that builds has a match specification, its enablement check *shall* pass exactly when the transition without its match specification is enabled on the token counts of the marking ([CORE-022]), the match specification keys at least one place and there is a name of which every correlated input holds at least its required count of tokens of that name.⟧

**Acceptance Criteria:**
1. A transition with only One inputs and no match specification is fully checked in Phase 1.
2. A transition with Exactly(5) input requires Phase 2 to verify token count.
3. A transition with a match specification requires Phase 3 to scan tokens for a name of which every correlated input holds at least its required count of tokens of that name.

**Test derivation:** Mix of simple and complex transitions; verify correct enablement with minimal re-evaluation."#
