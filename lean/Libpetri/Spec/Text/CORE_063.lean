import Libpetri.Spec.Text

requirement_text CORE_063
  id "CORE-063"
  title "Context Structure Enforcement"
  priority MUST
  kind F
  body r#"The transition context enforces that actions can only access places declared in the transition's structure. Attempting to access an undeclared place (input, read, or output) results in an error.

⟦s1|*If* an action calls an input accessor (`inputs(place)`, `input(place)` or, where it exists, `inputToken(place)`) on a place that does not resolve to an input place of its transition ([MOD-031]), *then* the call *shall* report an error.⟧

⟦s2|*If* an action calls `read(place)` on a place that does not resolve to a read place of its transition ([MOD-031]), *then* the call *shall* report an error, also when the place is an input place of the transition.⟧

⟦s3|*If* an action calls `output(place, ...)`, in its single or its bulk form, on a place that does not resolve to an output place of its transition ([MOD-031]), *then* the call *shall* report an error and declare no token, also when it passes no values.⟧

⟦s4|Every executor hands an action consumed tokens only from the input places of its transition ([EXEC-010]) and read tokens only from its read places ([EXEC-012]).⟧

⟦s5|The plural accessors some languages add, such as `reads(place)` and Java's `inputTokens(place)`, are not named by these rules; each implementation guards them with the check of the singular accessor of the same kind.⟧

⟦s6|These rules govern the calls an action makes through its transition context; a token that reaches the executor without passing through the context is the subject of [CORE-072] AC3.⟧

**Acceptance Criteria:**
1. Accessing undeclared input → error.
2. Accessing undeclared read → error.
3. Producing to undeclared output → error.

**Depends on:** [CORE-060], [CORE-061], [CORE-062]
**Test derivation:** Create context with restricted place sets; attempt out-of-bounds access; verify errors."#
