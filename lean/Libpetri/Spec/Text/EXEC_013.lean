import Libpetri.Spec.Text

requirement_text EXEC_013
  id "EXEC-013"
  title "Reset Arc Execution"
  priority MUST
  kind B
  body r#"⟦s1|When a transition fires, all tokens are removed from each reset place.⟧ ⟦s2|This happens during the firing step, before the action executes.⟧ Like input consumption, the drain lands in the intermediate marking, so it restarts the clocks of transitions it disables there (see [TIME-012]).

⟦s3|*When* a transition fires, it *shall* drain each of its reset places ([CORE-034]) before its action starts.⟧

⟦s4|*When* a transition fires, it *shall* consume from its input places first, then peek its read places, then drain its reset places.⟧

⟦s5|*When* a transition with a read arc and a reset arc on the same place fires, its action *shall* receive as the read token the oldest token the place held before the drain.⟧

⟦s6|*If* a reset place of a firing transition is unmarked, *then* the drain *shall* remove nothing and the firing *shall* proceed.⟧

⟦s7|A token a synchronous action deposited earlier in the same firing pass survives the drain ([EXEC-003] AC5).⟧

⟦s8|*When* a transition starts in a firing pass, it *shall* drain each of its reset places in that same step, so the place keeps exactly the tokens a synchronous action deposited there earlier in the pass.⟧

**Acceptance Criteria:**
1. Reset place with 5 tokens → all removed.
2. Reset place empty → no error.
3. If the reset place is also an input or read place of another enabled transition, that transition's clock restarts ([TIME-012]).
4. Reset draining occurs **after** read-arc peeking within the same firing: a
   transition with a read arc and a reset arc on the same place observes the
   pre-reset front token via `ctx.read()` (see [EXEC-012], [CORE-032]). The
   overall in-firing order is: input consumption, then read peeks, then reset
   draining.

**Depends on:** [CORE-034], [EXEC-012], [CORE-032], [EXEC-003]
**Test derivation:** Transition with reset on place with 3 tokens; verify all removed; verify clock restart for affected transitions."#
