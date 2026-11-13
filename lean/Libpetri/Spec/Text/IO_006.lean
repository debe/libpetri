import Libpetri.Spec.Text

requirement_text IO_006
  id "IO-006"
  title "~~Input Guard Predicate~~ (Removed)"
  status Removed
  body r#"Guard predicates were removed in favor of modeling conditional token selection via multiple conflicting transitions with XOR-on-input semantics. This avoids coupling predicate evaluation to the enablement check and keeps the input specification purely structural.

**Note (ν-matching is not a guard).** The correlated join of [NU-020] is *not* a
reintroduction of guards. A guard evaluates an arbitrary boolean over a single
token's value; a [NU-020] match instead correlates the **name dimension across
places** by equality — the one decidable predicate — which is
composition-structural like cardinality, not a per-token value test. It is
therefore compatible with the structural discipline this requirement preserves."#
