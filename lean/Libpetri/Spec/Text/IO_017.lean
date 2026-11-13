import Libpetri.Spec.Text

requirement_text IO_017
  id "IO-017"
  title "allPlaces Flattening"
  priority MUST
  kind F
  body r#"The output specification provides a method to collect all leaf places from the entire tree, regardless of And/Xor/Timeout structure.

⟦s1|The `allPlaces` set of a `Place` node *shall* be the set holding only that place.⟧

⟦s2|The `allPlaces` set of a `ForwardInput(from, to)` node *shall* be the set holding only `to`.⟧

⟦s3|The `allPlaces` set of an `And` node *shall* be the union of its children's `allPlaces` sets.⟧

⟦s4|The `allPlaces` set of an `Xor` node *shall* be the union of its children's `allPlaces` sets.⟧

⟦s5|The `allPlaces` set of a `Timeout` node *shall* be its child's `allPlaces` set.⟧

**Acceptance Criteria:**
1. `Xor(And(P1, P2), Timeout(5s, P3))` → {P1, P2, P3}
2. ForwardInput(from, to) contributes `to` to the set.

**Test derivation:** Nested output spec; verify allPlaces returns complete set."#
