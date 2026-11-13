import Libpetri.Spec.Text

requirement_text CONC_026
  id "CONC-026"
  title "Optional Output Validation Skip"
  priority MAY
  kind N
  body r#"The executor MAY support an opt-in builder option to skip output validation ([IO-015], [EXEC-021]) for known-correct nets. This is a performance optimization for production use where nets have been verified at development time.

⟦s1|*While* the option is enabled, the executor *shall* deposit the tokens an action wrote without validating them against the transition's output spec.⟧ ⟦s2|The skip covers the whole spec, its `Place` and `ForwardInput` leaves included: a transition whose output spec is a single leaf is not checked for a write to that place either.⟧ It also covers the join-relay check of [NU-054] and the multiplicity warning of [IO-016] AC4, both of which run as part of validation.

[IO-010], [IO-011] and [IO-012], the per-firing check of [IO-015] and the last two firing lines of [CORE-036] for a firing that ends with its action are requirements on an executor with output validation enabled, which is the default. ⟦s3|While the option is enabled they do not apply: a firing that ends with its action deposits the action's write whether or not it equals an output branch.⟧

⟦s4|The option skips nothing else.⟧ ⟦s5|A write to a place the transition does not declare as an output still fails ([CORE-063]).⟧ A firing that ends with the timeout outcome deposits what [IO-013] and [IO-014] say. ⟦s6|The build-time checks of [IO-011], [IO-012], [IO-013] and [IO-014] run when the transition is built, before any executor exists, and no executor option reaches them.⟧

**Acceptance Criteria:**
1. The option is opt-in (validation is on by default).
2. ⟦s7|When enabled, output tokens are deposited without validation.⟧
3. When disabled, output validation behaves identically to the bitmap executor.
4. When enabled, a transition with output spec `Place(P)` whose action writes nothing completes
   without a validation error and deposits nothing, and a transition with `And(A, B)` whose
   action writes only `A` deposits the `A` token.
5. When enabled, a token in a relay target that does not carry the matched name is deposited
   without the [NU-054] diagnostic, and a write of two tokens into one claimed place emits no
   [IO-016] AC4 warning.
6. When enabled, a write to an undeclared place still fails ([CORE-063]), and building a
   transition whose output spec [IO-012] rejects still fails.

**Implementation notes:** the option is offered by the production executor of each language:
Java `PrecompiledNetExecutor.Builder.skipOutputValidation`, TypeScript's
`PrecompiledNetExecutor` option `skipOutputValidation`, Rust's `PrecompiledNetExecutor` and
`OwnedPrecompiledNet` builders (`skip_output_validation`), and Python's
`ExecutorOptions(skip_output_validation=...)`, which sets the Rust one. All four skip the leaf
check, the relay check and the warning alike. The reference executors offer no option.

**Depends on:** [IO-015], [EXEC-021], [NU-054]
**Test derivation:** Enable skip; fire transition with XOR output; verify tokens deposited without validation error. With the skip enabled, fire the AC4 and AC5 transitions and verify the deposits and the absence of any violation, relay diagnostic or warning; with it disabled, verify each fails or warns as [IO-010], [IO-011], [NU-054] and [IO-016] say. Build the AC6 transition with the skip enabled and verify it is rejected."#
