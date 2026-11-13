import Libpetri.Spec.Text

requirement_text EXP_005
  id "EXP-005"
  title "XOR Branch Labels"
  priority SHOULD
  kind F
  body r#"⟦s1|XOR output branches should be labeled to indicate the branching structure.⟧ ⟦s2|Each branch of a XOR should be visually identifiable.⟧

⟦s3|The mapper *shall* draw each `Xor` group with two or more children in an output spec as an `Xor` junction node with exactly one edge out of it for each child, in the order of the children.⟧

⟦s4|The mapper *shall* draw the edges below the edge into a child of an `Xor` junction so that following them down reaches the places of that child's leaves, one path into a place for each leaf, and no other place.⟧

⟦s5|The edge into a `Place`, `ForwardInput` or `Timeout` child of an `Xor` junction *shall* carry the label [EXP-012] gives it, and be dashed exactly when [EXP-012] draws it dashed.⟧

⟦s6|*Where* [EXP-013] combines that edge into a reset place, the edge *shall* carry a label that is not empty in place of the one above.⟧

**Acceptance Criteria:**
1. XOR branches have labels or visual grouping.
2. The viewer can identify which outputs belong to which XOR branch.

**Test derivation:** Net with XOR output; export; verify branches are labeled."#
