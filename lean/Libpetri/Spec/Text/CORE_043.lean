import Libpetri.Spec.Text

requirement_text CORE_043
  id "CORE-043"
  title "Output-Declaring Transitions Must Produce"
  priority MUST
  kind F
  body r#"A transition that declares an output spec MUST NOT carry the built-in passthrough action
([CORE-051]) in a net submitted for execution: compiling *or verifying* such a net MUST fail.
Compilation is where structure and action are both final and is the point every executor passes
through, so one check there covers the builder default, either `bindActions` form ([CORE-042]),
binding on a subnet definition ([MOD-051]), per-instance binding ([MOD-030]) and channel merge
([MOD-021]) alike.

Such a transition can never fire usefully: passthrough produces no tokens while [IO-015] requires
every declared branch, so each firing consumes its input and the declared output never arrives.
Verification does not compensate: state-class and SMT analysis read production from the `Arc.Out`
spec, never from the bound action. The rule is unconditional: under an opt-out from per-firing
output validation the firing may succeed, but the net stays structurally incoherent.

⟦s1|*If* a net holds a transition that declares an output spec, a `Timeout`-only spec included, and carries the built-in passthrough action ([CORE-051]), whether bound explicitly, carried because a `bindActions` mapping omitted it ([CORE-042]), or left in place as the builder default, *then* compiling the net *shall* fail with an error that names the first such transition in declaration order.⟧

⟦s2|*If* no transition of a net both declares an output spec and carries the built-in passthrough action, *then* compiling the net *shall not* fail under this requirement.⟧

⟦s3|*If* a transition declares no output spec, or carries an action other than the built-in passthrough, a `fork()` action ([CORE-052]) or a hand-written action that produces nothing included, *then* compiling the net *shall not* fail under this requirement naming that transition.⟧

⟦s4|*When* a net is submitted to a verification entry point (state-class graph or SMT), under any property and option the entry point accepts, the entry point *shall* fail under this requirement exactly when compiling the submitted net does, with an error that names the same transition.⟧

**Acceptance Criteria:**
1. Compiling a net errors when a transition with a non-empty output spec carries passthrough (bound explicitly, carried because a `bindActions` mapping omitted it, or left in place as the builder default), including a `Timeout`-only spec, whose executor-produced `ForwardInput` branch ([IO-014]) passthrough can never reach.
2. The error names the offending transition, the first one in declaration order when there are several.
3. Submitting the same net to a verification entry point (state-class graph or SMT) fails the same way, so verification cannot green-light a net that will not compile.
4. A transition that declares no output spec (a sink) may carry passthrough; [CORE-042] is untouched.
5. The built-in is recognised by identity, so a hand-written action that happens to produce nothing is not claimed; that stays [IO-015]'s business at run time.

**Test derivation:** Compile a net whose transition declares `Out.place(P)` and carries the builder default, then with passthrough bound explicitly, then omitted from a `bindActions` mapping, then declaring `Out.timeout(d, Out.forwardInput(P, Q))`; verify each is rejected naming the transition, and that a sink, a `fork()`-bound transition and a hand-written no-op all compile.
Verify the same rejection at the state-class-graph and SMT entry points."#
