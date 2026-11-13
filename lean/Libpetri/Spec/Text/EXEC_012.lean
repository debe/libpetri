import Libpetri.Spec.Text

requirement_text EXEC_012
  id "EXEC-012"
  title "Read Arc Peek"
  priority MUST
  kind B
  body r#"⟦s1|When a transition fires, read arc values are provided to the action without consuming the tokens.⟧ ⟦s2|The oldest token in the read place is peeked.⟧

⟦s3|*When* a transition fires, its action *shall* receive, for each of its read places, the oldest token the place holds.⟧

⟦s4|*When* a transition fires, its action *shall* receive read tokens only from the read places of the transition.⟧

⟦s5|*When* a transition fires, each of its read places that is not one of its reset places *shall* end the firing holding the tokens it held before the firing, in the same queue order, followed by the tokens the firing deposits there.⟧

⟦s6|*If* a transition declares an input arc and a read arc on the same place, *then* building the transition *shall* fail with⟧

```
Transition '<t>' declares an input arc and a read arc on place '<p>'. A read of a place the same firing consumes from has no coherent semantics and is rejected (EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the action.
```

⟦s7|The message is the same, byte for byte, in every implementation.⟧ The read would peek the place after the firing's own consumption ([EXEC-013] AC4), which can leave it empty although the transition was enabled, so no reading of the pair is coherent. ⟦s8|"The same place" is the implementation's own `Place` equality, as for [CORE-030] ([CORE-002]; name-and-type in Java, name-only in TypeScript and Rust).⟧

The check runs when the transition is built, on every construction path, as the check of [CORE-030] does: the transitions that channel composition merges ([MOD-021]), that instantiation rewrites onto host places ([MOD-020]) and that fusion rewrites when the net is built ([MOD-061]) all pass through the transition builder. ⟦s9|It runs after every input-arc check ([CORE-030], [IO-002], [IO-004]) and before the timing check ([TIME-001]) and the output-spec checks ([IO-011]–[IO-014]).⟧ ⟦s10|It walks the read arcs in declaration order and names the place of the first read arc whose place is an input place of the transition.⟧

**Acceptance Criteria:**
1. Read place has tokens A, B; action receives A; both A and B remain after firing.
2. A transition `t` with a `one()` input arc on `p` and a read arc on `p` → building `t` fails with the message above, `<t>` = `t` and `<p>` = `p`. With `all()`, `exactly(2)` or `atLeast(1)` in place of `one()` it fails the same way.
3. A transition `t` with input arcs on `a` and `b` and read arcs declared on `b`, then `a` → the message names `b`. A transition with two input arcs on `p` and a read arc on `p` → the [CORE-030] message, not this one.
4. A transition with an input arc on `a` and a read arc on `b`, or a read arc and a reset arc on the same place, builds.

**Depends on:** [CORE-032], [CORE-030]
**Test derivation:** Read place with 2 tokens; fire transition; verify both tokens remain; verify action received first. Build each rejected transition of AC2 and AC3 and verify the exact message; build each transition of AC4 and verify it builds."#
