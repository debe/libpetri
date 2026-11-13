import Libpetri.Spec.Text

requirement_text IO_011
  id "IO-011"
  title "Output And"
  priority MUST
  kind B
  body r#"⟦s1|`And(children)` is a node of an output spec that represents a parallel fork in which all children are active.⟧ ⟦s2|*When* a transition whose output spec is `And(children)` fires and its action completes, every child, with nested `And`s flattened, *shall* have received tokens: the produced set contains a place that the child names.⟧ ⟦s3|The same holds for an `And` nested in the alternative that an inner `Xor` chose: the produced set *shall* equal, on the places the output spec names, one output branch of the output spec.⟧ ⟦s4|That output branch is unique, because the output branches of a spec that builds are pairwise distinct sets ([IO-012]).⟧

⟦s5|This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).⟧

**A place at most once per branch.** Outputs are sets of places ([IO-015]), and every analysis models one token per claimed place ([IO-016]), so `And(P, P)` does not mean "two tokens into `P`". ⟦s6|*If* a single output branch (one choice at every `Xor`, with nested `And`s flattened) names the same place twice, *then* the output spec *shall* be rejected, with⟧

```
output spec of transition '<t>' names place '<P>' twice in one AND branch; outputs are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up transition
```

**Which place the message names.** ⟦s7|*If* the output spec names a place twice in one output branch, *then* `<P>` in the message *shall* be the place that the following walk of the spec reports first, so that every implementation names the same place:⟧

1. ⟦s8|A `Place(P)` node and a `ForwardInput(from, P)` node name `P`.⟧
2. ⟦s9|A `Timeout` node walks its child and names the places its child names.⟧
3. ⟦s10|An `Xor` node walks its children left to right.⟧ ⟦s11|*If* a child reports a place, *then* the `Xor` *shall* report that place.⟧ ⟦s12|Otherwise the `Xor` names the places its children name, each once, in the order the walk first meets them.⟧
4. ⟦s13|An `And` node walks its children left to right.⟧ ⟦s14|*If* a child reports a place, *then* the `And` *shall* report that place.⟧ ⟦s15|Otherwise, *if* a place the child names, taken in the order the walk first met them, is already named by an earlier child, *then* the `And` *shall* report the first such place.⟧ ⟦s16|Otherwise the `And` names the places its children name, each once, in the order the walk first meets them.⟧

⟦s17|The walk reports a place exactly when some output branch names a place twice, because the alternatives of an `Xor` under an `And` are chosen independently of the `And`'s other children.⟧

The rejection happens when the spec is built if the transition's name is known there, and otherwise when the transition is built; it MUST NOT be bypassable by any construction path (builders, composition, channel merge, fusion). The same place in **different** `Xor` alternatives, such as `Xor(And(P, A), And(P, B))`, is not a duplicate. A composition that produces the duplicate by binding two output ports to one place is rejected with the more specific message of [MOD-020].

**Acceptance Criteria:**
1. Requires at least 1 child.
2. After action completes, ALL children must have received tokens.
3. Validation failure if any child received no tokens.
4. `And(P, P)`, `And(P, And(Q, P))` and `Xor(A, And(P, P))` are rejected with the message above, naming the transition and `P`. `Xor(And(P, A), And(P, B))` is accepted.
5. `And(Xor(A, B), Xor(B, A))` is rejected with the message above, naming the transition and `B`.

**Depends on:** [IO-015], [IO-016]
**Test derivation:** And(P1, P2, P3); action produces to all three; verify success. Action produces to only P1, P2 → validation error. Build a transition with `And(P, P)`, with a nested duplicate, and with the duplicate inside one `Xor` alternative; verify each is rejected with the message; build the two-alternative case and verify it is accepted. Build `And(Xor(A, B), Xor(B, A))` and verify the message names `B`, not `A`."#
