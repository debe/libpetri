import Libpetri.Spec.Text

requirement_text MOD_010
  id "MOD-010"
  title "Instance Creation via instantiate(prefix, params)"
  priority MUST
  kind F
  body r#"A subnet definition produces a **module instance** via `instantiate(prefix, params)`. Instantiation:
1. Takes a string `prefix` and a `params` value matching the subnet's parameter type.
2. Produces a renamed copy of the body net where every place name and every transition name is rewritten as `prefix + "/" + originalName`.
3. The renamed body is a structurally valid `PetriNet` per [CORE-040].
4. Arcs in the renamed body reference the renamed places; the arc topology is identical to the body's arc topology modulo the rename.
5. Timing, priority, and action of each transition are preserved (actions are shared by reference; see [MOD-030]).

The separator `"/"` is reserved by this requirement as the prefix separator. Implementations MUST use exactly `"/"`. Nested instantiation produces names of the form `outer/inner/originalName` (see [MOD-013]).

⟦s1|*If* the prefix given to `instantiate` is empty or contains `/`, *then* `instantiate` *shall* fail.⟧

⟦s2|*When* `instantiate` is given a non-empty prefix that contains no `/` and the body of the subnet definition declares no terminal place ([EXEC-042]), `instantiate` *shall* succeed.⟧

⟦s3|*If* the prefix given to `instantiate` is non-empty and contains no `/` and the body of the subnet definition declares a terminal place ([EXEC-042]), *then* `instantiate` *shall* fail with an error that names one of those terminal places.⟧

⟦s4|*When* `instantiate` succeeds with prefix `p`, the renamed body *shall* hold exactly the body's places and, in the body's order, the body's transitions, each renamed from `x` to `p/x`, with every arc and output specification of a transition naming the renamed places and its timing, priority and action unchanged.⟧

**Acceptance Criteria:**
1. `instantiate("buf1", params)` over a body containing place `slots` produces a renamed place with name `buf1/slots`.
2. Calling `instantiate` twice on the same definition with different prefixes produces two renamed bodies whose place and transition name sets are disjoint.
3. The renamed body is immutable.
4. A `params` value of the wrong type is rejected (compile-time in languages with generics; construction-time error otherwise).

**Depends on:** [CORE-001], [CORE-040]
**Test derivation:** Instantiate a subnet with prefix `b1`; verify every place name in the renamed body begins with `b1/`. Instantiate twice with prefixes `b1` and `b2`; verify name sets disjoint."#
