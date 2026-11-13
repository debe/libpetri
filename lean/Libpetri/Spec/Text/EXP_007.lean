import Libpetri.Spec.Text

requirement_text EXP_007
  id "EXP-007"
  title "Export Configuration"
  priority SHOULD
  kind F
  body r#"⟦s1|The export supports configuration options:⟧
- ⟦s2|**Layout direction**: top-to-bottom, left-to-right, etc.⟧
- ⟦s3|**Show/hide timing**: toggle timing interval display on transitions⟧
- ⟦s4|**Show/hide priority**: toggle priority display on transitions⟧

⟦s5|*Where* the configuration hides timing and priority, the export *shall* label a transition node with the transition's name alone.⟧

⟦s6|*Where* the configuration shows timing and hides priority, the export *shall* label a transition node with the transition's name, a space and `[e, l]ms`, where e is `earliest()` and l is `latest()` of the transition's timing, in milliseconds and in decimal, and l is written `∞` when `hasDeadline()` is false ([TIME-001]).⟧

⟦s7|*Where* the configuration shows priority and the transition's priority n is not 0, the export *shall* label the transition's node with the label it would have if the configuration hid priority, followed by a space and `prio=n`, with n in decimal.⟧

⟦s8|*Where* a transition's priority is 0, the export *shall* label its node with the label it would have if the configuration hid priority.⟧

⟦s9|The export *shall* lay out the drawing in the layout direction the configuration names.⟧

⟦s10|The export *shall* draw the same graph, apart from its layout direction and the label drawn inside each transition node, under two configurations that differ only in the layout direction and the show options.⟧

⟦s11|*Where* a configuration carries a show-types option, the export *shall* draw the same graph whichever value the option has.⟧

⟦s12|The default configuration names the top-to-bottom layout direction and shows timing and priority.⟧

**Acceptance Criteria:**
1. Configuration controls what information is displayed.
2. Default configuration shows all information.
3. Minimal configuration hides timing and priority.

**Test derivation:** Export with default config; export with minimal config; verify difference."#
