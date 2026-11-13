import Libpetri.Spec.Text

requirement_text IO_012
  id "IO-012"
  title "Output Xor"
  priority MUST
  kind B
  body r#"⟦s1|`Xor(children)` is an output spec node with two or more children; it represents a decision point where the action chooses one child.⟧

⟦s2|*When* a transition whose output spec is `Xor(children)` fires and the firing ends with its action, its produced set *shall* equal, on the places the output spec names, one output branch of the output spec.⟧

⟦s3|*When* a transition whose output spec is `Xor(children)` fires and the firing ends with its action, its produced set *shall not* equal, on the places the output spec names, two output branches that take different children at some `Xor` node.⟧

⟦s4|This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).⟧

⟦s5|A firing ends with its action when it does not end with the timeout outcome ([IO-013]).⟧ ⟦s6|Deposits are compared per place ([CORE-036]): a firing whose deposit puts in every place as many tokens as some timeout-outcome deposit of the transition from the same marking may have ended with the timeout outcome, and the two lines above do not constrain it.⟧

**Distinct alternatives.** ⟦s7|An *assignment* of an output spec chooses one child at each `Xor` node it reaches ([IO-015]).⟧ ⟦s8|`Xor` nodes are told apart by their position in the spec, never by what they contain, so `Xor(P, P)` has two assignments.⟧ ⟦s9|Two assignments are *distinct* when they choose different children at some `Xor` node that both reach.⟧ ⟦s10|*If* two distinct assignments of a transition's output spec claim the same set of places, at any depth of the spec, *then* building the transition *shall* fail with⟧

```
output spec of transition '<t>' is ambiguous: output branches <i> and <j> both claim {<places>}; no write can tell them apart (IO-012)
```

Every implementation runs the check the same way, so the message is identical in all of them:

1. ⟦s11|Enumerate the output branches of the spec per [IO-016], numbered from 0 in enumeration order (the numbering of the virtual transitions `<t>_b<i>` of [VER-001]).⟧ ⟦s12|The enumeration lists exactly one branch per assignment, so two branches at different indices come from distinct assignments.⟧
2. ⟦s13|Read each branch as the set of places it names, a `ForwardInput(from, to)` naming `to`.⟧ Two places are the same under the implementation's own `Place` equality, as for [IO-011] ([CORE-002], [MOD-024]).
3. ⟦s14|Visit the branches in index order.⟧ ⟦s15|The first branch `j` whose set equals the set of an earlier branch fails the check, and `i` is the smallest index of such an earlier branch.⟧ ⟦s16|If no branch fails, the check passes.⟧
4. ⟦s17|`<places>` lists the places of branch `i` by name, separated by `, `, in the order the spec as written names them (leaves left to right).⟧

⟦s18|An implementation MAY decide the check without enumerating every branch, provided it reports the same `i`, `j` and `<places>`.⟧ The check runs when the transition is built, on every construction path, as the check of [IO-011] does. A composition that binds two output ports in different alternatives to one host place yields a spec that this check rejects.

⟦s19|A transition that builds therefore has pairwise distinct output branches, so at most one output branch equals any produced set, and the second line above holds of every firing of such a transition.⟧

**Acceptance Criteria:**
1. Requires at least 2 children.
2. After action completes, exactly 1 child must have received tokens.
3. Zero branches satisfied → validation error.
4. Two branches whose claims are the same set never reach a firing: building the transition rejects them (AC5). A branch whose claim is a strict subset of what was produced does not satisfy the spec at all, so overlapping branches like `Xor(And(A, B, C), And(A, B))` resolve without a tie-break ([IO-015]).
5. Building a transition fails with the message above, naming the reported pair and places, for:
   `Xor(P, P)` (branches 0 and 1, `{P}`); `Xor(And(A, B), And(B, A))` (0 and 1, `{A, B}`);
   `Xor(A, Xor(A, B))` (0 and 1, `{A}`); `And(Q, Xor(P, P))` (0 and 1, `{Q, P}`);
   `Xor(And(A, Xor(B, C)), And(A, B))` (0 and 2, `{A, B}`); `Xor(P, Timeout(d, P))` (0 and 1,
   `{P}`); and, with `a` an input place, `Xor(B, Timeout(d, ForwardInput(a, B)))` (0 and 1,
   `{B}`). `Xor(And(A, B, C), And(A, B))`, `Xor(And(P, A), And(P, B))` and
   `Xor(A, Timeout(d, B))` build.

**Depends on:** [IO-015], [IO-016]
**Test derivation:** Xor(P1, P2); action produces only to P1 → success. Action produces to both → error. Action produces to neither → error. Build a transition with each rejected spec of AC5 and verify the exact message; build each accepted spec and verify it builds. Repeat one rejected spec through composition (two output ports in different alternatives bound to one host place) and verify the same message."#
