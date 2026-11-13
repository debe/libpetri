import Libpetri.Spec.Text

requirement_text EVT_004
  id "EVT-004"
  title "TransitionEnabled Event"
  priority MUST
  kind B
  body r#"Emitted when a transition becomes armed ([TIME-010]): when it is armed for the first time, or armed again after the executor disarmed it.

⟦s1|Enabled in this requirement means armed: a transition that is armed again after its own firing, after the enablement recheck of a firing pass disarmed it, or after a reap and a later write of one of its arc places is announced again, even when the marking kept it enabled.⟧ ⟦s2|A transition whose clock restarts while it stays armed is announced with `TransitionClockRestarted` instead ([EVT-005]).⟧ As in the timing requirements, the transitions of a net are taken to have pairwise distinct names ([TIME-010]).

⟦s3|*When* a transition is armed after an enablement update and was not armed before it, the executor *shall* emit, at that update, exactly one TransitionEnabled event naming the transition.⟧

⟦s4|The executor *shall* emit a TransitionEnabled event naming a transition only at an enablement update before which the transition was not armed and after which it is armed.⟧

**Acceptance Criteria:**
1. Emitted each time a transition that was not armed before an enablement update is armed after it.
2. Not emitted if the transition was already armed, including when its clock restarts ([EVT-005]).

**Test derivation:** Add token enabling transition T; verify TransitionEnabled event for T."#
