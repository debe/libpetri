import Libpetri.Spec.Text

requirement_text CORE_022
  id "CORE-022"
  title "Transition Enablement"
  priority MUST
  kind B
  body r#"⟦s1|A transition is **enabled** in a marking when every input place holds at least its required count (see [IO-001]–[IO-004]), every read place is marked and no inhibitor place is marked.⟧
For a transition with a match specification these conditions are the count-level part of enablement: its enablement check also needs a name of which every correlated input holds at least its required count of tokens ([NU-020]).

⟦s2|*While* an input place of a transition holds fewer tokens than its required count, the transition *shall not* fire.⟧

⟦s3|*While* a read place of a transition is unmarked, the transition *shall not* fire.⟧

⟦s4|*While* an inhibitor place of a transition is marked, the transition *shall not* fire.⟧

⟦s5|*While* a transition that has no match specification ([NU-020]) is enabled, the transition *shall* be able to fire.⟧

⟦s6|This requirement concerns transitions that build. A definition that building the transition rejects ([CORE-030], [IO-002], [IO-004], [EXEC-012], [IO-011]–[IO-014]) is not a transition of any net and is never enabled anywhere; in particular an output spec whose alternatives no write can tell apart ([IO-012]) never reaches a marking.⟧

**Acceptance Criteria:**
1. Transition with satisfied inputs, reads present, inhibitors empty → enabled.
2. Missing input tokens → disabled.
3. Missing read tokens → disabled.
4. Inhibitor place has tokens → disabled.

**Depends on:** [IO-001], [CORE-030], [CORE-031], [CORE-032]
**Test derivation:** Systematically toggle each condition and verify enablement changes."#
