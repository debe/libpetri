import Libpetri.Spec.Text

requirement_text IO_013
  id "IO-013"
  title "Output Timeout"
  priority MUST
  kind B
  body r#"⟦s1|`Timeout(duration, child)` is a node of an output spec that gives the action of a firing a budget of `duration` to complete.⟧ ⟦s2|*If* the action does not complete within `duration`, the firing *shall* end with the timeout outcome: it is abandoned, and it deposits the tokens of `child`.⟧ ⟦s3|*When* a firing ends with the timeout outcome, it *shall not* deposit any output of the action, so the marking receives the tokens of `child` and nothing else.⟧ A firing of a transition with a match specification whose timeout outcome fails the relay check of [NU-054] does not end with the timeout outcome: it fails ([EVT-008]) and deposits none of the tokens of `child`.

**One budget per action.** ⟦s4|*If* an output spec holds more than one `Timeout` node, whether one is nested in the child of another or they sit apart, *then* building the transition *shall* fail with⟧

```
output spec of transition '<t>' has <n> Timeout nodes; an output spec has at most one, nested or not (IO-013)
```

⟦s5|where `<n>` is the number of `Timeout` nodes in the spec.⟧ ⟦s6|The check runs when the transition is built, on every construction path, as the check of [IO-011] does.⟧ ⟦s7|A transition that builds therefore has at most one timeout outcome, and the `child` of its `Timeout` holds no `Timeout` node.⟧

**One fixed timeout deposit.** ⟦s8|The executor, not the action, makes the deposit of the timeout outcome, so nothing chooses among alternatives inside the `Timeout` child.⟧ ⟦s9|*If* the child of an output spec's `Timeout` node holds an `Xor` node at any depth, *then* building the transition *shall* fail with⟧

```
output spec of transition '<t>' has a Xor node inside the child of its Timeout node; the timeout outcome deposits one fixed set of places (IO-013)
```

⟦s10|The check runs after the `Timeout` count check above, so the spec it sees holds at most one `Timeout` node.⟧ The check runs when the transition is built, on every construction path, as the check of [IO-011] does. ⟦s11|The timeout outcome of a transition that builds therefore deposits in one fixed set of places: every place the `Timeout` child names.⟧

Whether the abandoned action is actually stopped is implementation-defined and MUST NOT be relied upon. An implementation that cannot cancel the work (for example one that does not own the thread an action runs on) leaves it running to completion; its side effects still happen and only its output is excluded. "Cancellation" is therefore a capability, not a guarantee.

**Acceptance Criteria:**
1. Duration must be positive (> 0).
2. Action completes within duration → normal output validation.
3. Action exceeds duration → every place the timeout child names receives tokens: one minted token for a `Place`, the forwarded tokens for a `ForwardInput` ([IO-014]).
4. An ActionTimedOut event is emitted on timeout.
5. Output the action produced *before* the budget expired is discarded together with the firing: the marking receives the tokens of the timeout child's one fixed set of places and nothing else. In particular a partial write under an `Xor` sibling of the `Timeout` MUST NOT be validated as a second satisfied branch ([EXEC-021], [IO-012]).
6. A `TimeoutException` the action itself raises is an ordinary action failure ([EXEC-030]), not the declared timeout branch: the branch is taken only when the executor's own budget timer fires.
7. `Timeout(d, Timeout(e, P))`, `Xor(Timeout(d, A), Timeout(e, B))` and
   `And(Timeout(d, A), Xor(B, Timeout(e, C)))` are rejected when the transition is built, with
   the message above and `<n>` = 2. `Xor(A, Timeout(d, B))` and `Timeout(d, And(A, B))` build.
8. `Timeout(d, Xor(A, B))` and `Xor(C, Timeout(d, And(A, Xor(B, D))))` are rejected when the
   transition is built, with the `Xor` message above. `Xor(A, Timeout(d, B))` and, with `i` an
   input place, `Timeout(d, And(A, ForwardInput(i, B)))` build.

**Depends on:** [EVT-009]
**Test derivation:** Action sleeps 500ms; timeout at 100ms; verify timeout branch activated and event emitted. Build a transition with each rejected spec of AC7 and AC8 and verify the exact message; build each accepted spec and verify it builds."#
