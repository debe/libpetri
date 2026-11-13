import Libpetri.Spec.Text

requirement_text CORE_030
  id "CORE-030"
  title "Input Arc"
  priority MUST
  kind B
  body r#"An input arc connects a place to a transition.

⟦s1|*When* a transition fires, it *shall* consume from each of its input places that is not also one of its reset places ([CORE-034]) as many tokens as the input arc's consumption count ([IO-001]–[IO-004], [IO-007]), oldest first.⟧

⟦s2|*When* a transition fires, each of its input places that is neither one of its reset places nor one of its output places *shall* end the firing holding exactly the consumption count of its input arc fewer tokens than it held before the firing.⟧

*If* a transition declares two input arcs on the same place, **building the transition** *shall* fail with a descriptive error that names the transition and the place and suggests a single arc with `exactly(n)` / `atLeast(n)` instead. Duplicate input arcs have no coherent consumption semantics: executors, state-class graphs and the flattener would each read them differently. The transition builder is the one construction path every net, subnet body and verification input passes through, so a check there reaches all of them. "The same place" is the implementation's own `Place` equality ([CORE-002]; name-and-type in Java, name-only in TypeScript and Rust).

The executors' compile-time check stays as a backstop, with the same message. Both composition seams reconcile colliding arcs before they rebuild a transition, per the canonical merge table of [MOD-021] (channel composition at compose, fusion at build per [MOD-061]). The one binding that can still collapse two input arcs onto one place — two ports of one instance bound to the same host place — is rejected at compose with its own message ([MOD-020]).

**Acceptance Criteria:**
1. Transition with input arc consumes tokens from the place on firing.
2. Consumed tokens follow FIFO order.
3. Two input arcs declared on the same place → building the transition fails with a
   descriptive error naming the transition and the place. No net, executor, state-class
   graph or verifier ever sees such a transition. The executor compile step keeps the same
   check, and message, as a backstop.

**Implementation notes:**
- Java: `Transition.Builder.build()`; the backstop is `CompiledNet.compile`.
- TypeScript: `TransitionBuilder.build()`; the backstop is `CompiledNet.compile`.
- Rust: `TransitionBuilder::build()`, which panics like the builder's other structural
  checks; the backstop is `CompiledNet::compile`.
- Python: `TransitionBuilder.build()` raises `StructureError`, the class the compile-time check
  raised before, never a Rust panic.

This is a behaviour change: a net that declared a duplicate input arc but was only ever
verified or exported, never executed, used to build. It now fails at the transition.

**Test derivation:** Create transition with input arc; add tokens; verify tokens consumed in FIFO order. Create transition with two `one()` inputs on the same place; verify that building the transition fails and names both the transition and the place."#
