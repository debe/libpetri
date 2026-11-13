import Libpetri.Spec.Text

requirement_text EXP_006
  id "EXP-006"
  title "Cardinality Labels"
  priority SHOULD
  kind F
  body r#"⟦s1|Multi-token arcs (Exactly(n), All, AtLeast(m)) display count notation on the arc label:⟧
- ⟦s2|Exactly(n): label shows "×n"⟧
- ⟦s3|All: label shows "*"⟧
- ⟦s4|AtLeast(m): label shows "≥m"⟧

⟦s5|The export *shall* give an input arc with cardinality `One` no cardinality label.⟧

⟦s6|The export *shall* give an input arc with cardinality `Exactly(n)` the cardinality label `×n`.⟧

⟦s7|The export *shall* give an input arc with cardinality `All` the cardinality label `*`.⟧

⟦s8|The export *shall* give an input arc with cardinality `AtLeast(m)` the cardinality label `≥m`.⟧

The export *shall* draw the cardinality label of an input arc on the edge of the arc.

**Acceptance Criteria:**
1. Non-One cardinality is displayed on the arc.
2. One cardinality has no cardinality label (default).

**Test derivation:** Net with Exactly(3) and AtLeast(5) inputs; export; verify labels show counts."#
