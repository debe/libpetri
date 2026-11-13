import Libpetri.Spec.Text

requirement_text CONC_005
  id "CONC-005"
  title "Dirty Set Optimization"
  priority MUST
  kind B
  body r#"When tokens are added or removed from a place, only transitions affected by that place need re-evaluation. A precomputed reverse index maps each place to the set of transitions that reference it.

⟦s1|*When* a firing or an injected token writes one of a transition's arc places, the executor *shall* re-run the transition's enablement check.⟧

⟦s2|The executor *shall* re-run a transition's enablement check only when a firing or an injected token writes one of its arc places, or when the transition itself fires.⟧

⟦s3|*If* the consumption of a firing, the deposit of a firing or an injected token writes none of a transition's arc places, *then* the transition's enablement check *shall* pass after it exactly when it passed before it.⟧

⟦s4|*While* a transition is reaped ([TIME-013]), the executor *shall not* re-run its enablement check, and only a firing or an injected token that writes one of its arc places *shall* end its reaped state.⟧

The dirty set is maintained as a bitmap: when a place changes, the executor sets the bits for all affected transitions. Each cycle, only dirty transitions are re-evaluated.

**Acceptance Criteria:**
1. Adding a token to place P only marks transitions connected to P as dirty.
2. Transitions not connected to P are not re-evaluated.
3. After re-evaluation, dirty bits are cleared.

**Test derivation:** Net with 50 transitions; add token to place connected to 3 transitions; verify only 3 transitions re-evaluated."#
