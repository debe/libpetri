import Libpetri.Spec.Text

requirement_text IO_016
  id "IO-016"
  title "Branch Enumeration"
  priority SHOULD
  kind F
  body r#"The output spec supports static enumeration of all its output branches for structural analysis, its *branch enumeration*.

⟦s1|The branch enumeration of a `Place` node *shall* be one output branch, holding that place.⟧

⟦s2|The branch enumeration of a `ForwardInput(from, to)` node *shall* be one output branch, holding `to`.⟧

⟦s3|The branch enumeration of an `And` node *shall* be the Cartesian product of its children's branch enumerations: one output branch for each choice of one output branch per child, holding the union of the chosen output branches, with the first child's choice varying slowest.⟧

⟦s4|The branch enumeration of an `Xor` node *shall* be the union of its children's branch enumerations: one output branch for each output branch of each child, the first child's output branches first.⟧

⟦s5|The branch enumeration of a `Timeout` node *shall* be its child's branch enumeration.⟧

The enumeration lists one output branch per assignment ([IO-015]). On a spec that builds, the
output branches are pairwise distinct sets ([IO-012]), so no two entries of the list name the
same places.

A branch is a **set** of places: it says which places receive a token when the branch is
taken, not how many tokens each receives. Every analysis built on the enumeration — the
state-class graph's virtual transitions ([VER-010]), the flattener's post vectors behind
the SMT encoding ([VER-001]), the ν fragment check ([NU-051]) — deposits **one** token per
place of a branch the action writes. An action that writes `n > 1` tokens to a place its
branch names once conforms to [IO-015] (which reads the produced set) but is outside what
those analyses explore, in the direction that can make a `proven` false. A net meant to be
verified expresses multiplicity in its topology, and the executor makes the gap visible:
see AC4.

The branches describe what an **action** writes. A firing whose `Timeout` fires ([IO-013])
deposits differently: only the timeout child's places (AC5 of [IO-013]), and one token in a
`ForwardInput`'s `to` per token consumed from its `from` ([IO-014]). The analyses therefore
expand a transition into its branches, in the order above, followed by the **timeout
outcome** when it differs, place by place, from every branch ([VER-001]). On a spec whose timeout child has
no sibling in its branch and forwards at most one token, the list is the branches alone.

**Acceptance Criteria:**
1. `And(P1, P2)` → 1 branch: {P1, P2}
2. `Xor(P1, P2)` → 2 branches: {P1}, {P2}
3. `Xor(And(P1, P2), P3)` → 2 branches: {P1, P2}, {P3}
4. When a validated firing deposited more than one token into a place its matched branch
   names, the executor emits an [EVT-013] log-message event with logger `libpetri.runtime`
   (omitted where the log-message event carries no logger field), level `WARN`, the
   transition's name, and the message
   `'<t>': wrote more than one token to a place its output spec names once (<place>: <n>, …); branch-enumerating analyses model one token per named place, so this firing exceeds what they explore (IO-016)`,
   naming every such place with its count in produced order. The tokens are deposited
   regardless. The event is emitted at most once per transition per execution, so an action
   that fans out on every firing does not flood the store.

**Test derivation:** Enumerate branches for nested structures; verify correct sets. An action
that writes two tokens to the one place its spec names, fired three times: both tokens land
on every firing and exactly one warning is emitted; a spec `And(A, B)` with three tokens to
`A` and two to `B`: one warning naming `(A: 3, B: 2)`; one token per named place: no event."#
