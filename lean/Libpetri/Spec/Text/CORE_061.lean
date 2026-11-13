import Libpetri.Spec.Text

requirement_text CORE_061
  id "CORE-061"
  title "Context Read Access"
  priority MUST
  kind F
  body r#"The transition context provides access to read (non-consumed) token values from declared read places.

⟦s1|*When* an action calls `read(place)` on a read place of its transition, the call *shall* return the value of the token the read arc read from that place, the oldest token the place holds ([EXEC-012]).⟧

⟦s2|The call consumes nothing: by [EXEC-012] the firing leaves the read token in the place, unless the transition also has a reset arc there, which drains the place ([EXEC-013]).⟧

⟦s3|*If* an action calls `read(place)` on a place that does not resolve to a read place of its transition ([MOD-031]), *then* the call *shall* report an error, also when the place is an input place of the transition.⟧

**Acceptance Criteria:**
1. `read(place)` returns the read value without consuming it.
2. Accessing an undeclared read place results in an error.

**Depends on:** [CORE-032], [EXEC-012], [EXEC-013]
**Test derivation:** Fire transition with read arc; verify `read()` returns value; verify token still in place."#
