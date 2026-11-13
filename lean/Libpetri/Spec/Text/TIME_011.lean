import Libpetri.Spec.Text

requirement_text TIME_011
  id "TIME-011"
  title "Clock Restarts on Re-enablement"
  priority MUST
  kind T
  body r#"⟦s1|If a transition stops being armed and is later armed again, the clock restarts from zero.⟧ ⟦s2|The previous elapsed time is discarded.⟧

⟦s3|*When* an armed transition stops being enabled, the executor *shall* discard its stamp.⟧

⟦s4|*When* a transition that lost its clock is armed again, its elapsed time *shall* be measured from the moment it was armed again, not from any earlier stamp.⟧

**Acceptance Criteria:**
1. Transition enabled with Delayed(5s); at 3s it becomes disabled; re-enabled later; must wait another 5s.

**Depends on:** [TIME-010]
**Test derivation:** Enable, partially wait, disable, re-enable; verify full delay applies again."#
