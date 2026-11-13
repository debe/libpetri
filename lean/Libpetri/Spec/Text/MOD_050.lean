import Libpetri.Spec.Text

requirement_text MOD_050
  id "MOD-050"
  title "Verification Pass-Through on Composed Flat Net"
  priority MUST
  kind B
  body r#"All verification facilities specified in section 07 (VER) MUST operate on a composed flat net per [MOD-023] without any composition-aware adaptation. Specifically:

1. Property checks per [VER-002] (deadlock freedom, place bounds, mutual exclusion, unreachability).
2. P-invariant computation per [VER-005].
3. Structural analyses per [VER-020], [VER-021].
4. Untimed over-approximation per [VER-004].
5. State class graph analysis per [VER-010] where supported.

The verifier sees the composed net as a normal `PetriNet`. No modular extension to the verifier API is required by this requirement.

⟦s1|*When* a verification facility specified in section 07 (VER) runs on a net that `build()` returned, it *shall* give the result that section 07 specifies for the hand-written net with the same name, the same places in the same order, the same transitions in the same order with the same names, arcs, output specifications, timing, priorities and actions, and the same terminal places in the same order.⟧

⟦s2|The result of a verification facility specified in section 07 (VER) *shall not* depend on which subnet a place or transition belongs to ([MOD-026]) or on the place correspondence of a transition ([MOD-031]).⟧

**Acceptance Criteria:**
1. Run the SMT verifier on a composed pipeline net; verification completes and produces a result of the same shape as for a hand-written net.
2. Verification results on the composed net match results on the hand-written equivalent net (per [MOD-023]) that lists its places in the composed net's order. A result that does not depend on the order of places matches on every hand-written equivalent.
3. P-invariant computation succeeds and produces invariants over the composed (prefixed) place names.

**Depends on:** [MOD-023], [VER-001]
**Test derivation:** Verify deadlock-freedom on a composed producer/buffer/consumer pipeline; verify the same property on the hand-written equivalent; assert identical results."#
