import Libpetri.Spec.Text

requirement_text CORE_062
  id "CORE-062"
  title "Context Output Access"
  priority MUST
  kind F
  body r#"The transition context provides a way for actions to declare output tokens for production, in a single-token form and a bulk-token form.

⟦s1|*When* an action calls `output(place, value)` on an output place of its transition, the call *shall* declare one token carrying `value` on that place, after every token the action declared before.⟧

⟦s2|*When* an action calls the bulk form with a sequence of values on an output place of its transition, the call *shall* declare one token per value on that place, in the order of the sequence, after every token the action declared before.⟧

⟦s3|*When* an action calls the bulk form with no values on an output place of its transition, the call *shall* declare no token and return successfully.⟧

⟦s4|*If* an action calls `output(place, value)` or the bulk form on a place that does not resolve to an output place of its transition ([MOD-031]), *then* the call *shall* report an error and declare no token, also when it passes no values ([CORE-063]).⟧

⟦s5|These four sentences do not govern an output call made after the firing has ended with the timeout outcome ([IO-013]); such a call declares no token that the firing deposits.⟧

**Acceptance Criteria:**
1. `output(place, value)` declares a single token to produce on the given output place.
2. A bulk form accepting multiple values for the same output place in one call is available and produces one token per value in iteration order. Language shapes: Java varargs `output(Place<T>, T...)` plus `output(Place<T>, Iterable<? extends T>)`; TypeScript rest parameters `output<T>(place, ...values: T[])`; Rust `output_many<T>(place_name, impl IntoIterator<Item = T>)`; Python `output_many(place_name, values)` over any iterable.
3. The bulk form validates the output place exactly once and reports an error **before** appending any tokens if the place is not declared, so undeclared-place errors do not leave partial output behind.
4. An empty bulk call (zero values) on a declared output place is a no-op and returns successfully.
5. Producing to an undeclared output place results in an error.

**Depends on:** [CORE-035], [IO-013], [IO-017]
**Test derivation:** Action calls `output(place, value)`; verify token appears in place after firing. Bulk form: action calls the bulk overload with three values; verify all three tokens appear in order. Bulk-undeclared: call bulk overload with a foreign place; verify error raised and no tokens appended."#
