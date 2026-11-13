import Libpetri.Spec.Text

requirement_text EVT_005
  id "EVT-005"
  title "TransitionClockRestarted Event"
  priority MUST
  kind B
  body r#"Emitted when a transition's timing clock restarts while the transition stays armed: another transition's firing left it disabled in the intermediate marking, and the marking enabled it again before the executor observed the gap (see [TIME-012]).

⟦s1|A transition's clock restart is pending when it is armed, a start of another transition since the last enablement update left it not enabled in that start's intermediate marking ([TIME-012]), and neither the enablement recheck of a firing pass nor a start of its own has disarmed it since.⟧ ⟦s2|An enablement update restarts the clock of a transition when it leaves the transition armed with the update's clock reading as its stamp and its clock restart no longer pending.⟧ As in [EVT-004], the transitions of a net are taken to have pairwise distinct names.

⟦s3|*When* an enablement update restarts the clock of a transition whose clock restart was pending before the update, the executor *shall* emit, at that update, exactly one TransitionClockRestarted event naming the transition.⟧

⟦s4|The executor *shall* emit a TransitionClockRestarted event naming a transition only at an enablement update before which the transition's clock restart was pending and that restarts the transition's clock.⟧

**Acceptance Criteria:**
1. Emitted only when the transition stays armed but its clock restarts.
2. Not emitted on initial enablement, nor on re-enablement after an observed disablement (both are `TransitionEnabled`).

**Depends on:** [TIME-012]
**Test derivation:** Transition T is armed but not yet ready (for example `delayed(d)` before `d` has elapsed); another transition consumes T's input token, and its synchronous action deposits a new one before the executor re-evaluates T; verify TransitionClockRestarted for T. An executor that re-evaluates between consumption and deposit reports TransitionEnabled instead ([TIME-012] AC6), and so does a firing pass that rechecks a ready T after the consumption, since the recheck disarms it."#
