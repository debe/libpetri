import Libpetri.Spec.Text

requirement_text TIME_010
  id "TIME-010"
  title "Clock Starts on Enablement"
  priority MUST
  kind T
  body r#"The timing clock of a transition runs while the transition is **armed**: enabled and holding a clock (see the glossary). ⟦s1|A transition is newly armed when it is enabled in the initial marking, afterwards when it is enabled after a firing or an injected token writes one of its arc places while it is not armed, and when its clock restarts in a firing ([TIME-012]).⟧ ⟦s2|The clock starts at the moment the transition was most recently newly armed, and the elapsed time for timing decisions is measured from that moment on the firing clock ([TIME-015]).⟧

⟦s3|The executor arms transitions in the enablement update of a cycle ([EXEC-001] step 3).⟧ ⟦s4|A transition is newly armed by the first enablement update that finds it enabled while it is not armed, and its stamp is the firing-clock reading that update takes.⟧ ⟦s5|A synchronous action's deposit is first seen by the enablement update of the next cycle, and an asynchronous completion or an injected token by the enablement update of the cycle that takes it in (steps 1 and 2).⟧ ⟦s6|So the stamp is neither the reading of the cycle in which the arming firing started nor the moment an action completed.⟧ ⟦s7|A clock restarted in a firing ([TIME-012]) is stamped the same way, by the next enablement update that finds the transition enabled.⟧

⟦s8|*When* a transition is newly armed, the executor *shall* stamp it with the firing-clock reading taken by the enablement update that newly arms it ([EXEC-001] step 3).⟧

⟦s9|*While* a transition is armed, its elapsed time *shall* be the current reading of the firing clock minus its stamp.⟧

⟦s10|*While* a transition is armed and its elapsed time is less than its earliest bound, the transition *shall not* fire.⟧

⟦s11|*While* a transition is not armed, the transition *shall not* fire.⟧

⟦s12|The executor *shall not* arm a transition or give an armed transition a different stamp in any step other than an enablement update ([EXEC-001] step 3); another step may only take a stamp away ([TIME-012], [TIME-013]).⟧

⟦s13|*When* the executor runs the enablement update of a cycle ([EXEC-001] step 3), it *shall* take the current reading of the firing clock, and the deadline step of that cycle ([EXEC-001] step 4) *shall* judge expiry at that reading or at a later reading it takes itself.⟧

⟦s14|The firing pass and the decision to wait of a cycle *shall* judge elapsed time at the reading of its deadline step, and no other step of the cycle *shall* take a new reading for these judgements.⟧

Armed is not the marking-level Enabled of [CORE-022]. A transition can be enabled without being armed: a reaped transition ([TIME-013]) is enabled until one of its arc places is written, but holds no clock and does not fire.

The timing requirements identify a transition by its name: a stamp, and whether a transition is reaped, are kept per name. They assume that the transitions of one net have pairwise distinct names. Two transition instances that share a name are distinct under [CORE-021], and a net holding both is outside [TIME-010]–[TIME-015].

**Acceptance Criteria:**
1. Transition enabled at T=10; earliest=3s; transition ready at T=13.
2. Transition enabled at T=10; disabled at T=11; re-enabled at T=15; ready at T=18 (clock restarted).

**Test derivation:** Enable transition; track elapsed time; verify firing window is relative to enablement."#
