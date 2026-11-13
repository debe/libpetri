import Libpetri.Spec.Text

requirement_text EXEC_003
  id "EXEC-003"
  title "Competitive Conflict Resolution"
  priority MUST
  kind B
  body r#"⟦s1|When multiple transitions compete for the same input tokens, the highest-priority ready transition fires first and consumes the tokens.⟧ ⟦s2|Lower-priority transitions become disabled if their inputs are no longer satisfied.⟧

⟦s3|A firing pass takes the transitions of its ready order ([EXEC-002]) one at a time from the front: it starts the next transition, or it drops it and goes on with the rest.⟧ ⟦s4|The pass-visible marking is the marking a firing pass began with, minus the tokens earlier firings of the same pass consumed or drained; tokens a synchronous action deposited during the pass are not part of it.⟧

⟦s5|*When* a firing pass starts or drops a transition, the transition *shall* be the next one of the pass's ready order, and it *shall* leave that order.⟧

⟦s6|*When* a firing pass starts a transition, the transition *shall* hold a clock and be enabled on the pass-visible marking, with input counts, read arcs and inhibitor arcs all judged on that marking.⟧

⟦s7|*If* the next transition of a firing pass's ready order holds a clock and is enabled on the pass-visible marking, *then* the executor *shall not* drop it.⟧

⟦s8|*When* a firing pass drops a transition, the transition *shall* lose its clock ([TIME-012]), and the marking *shall* stay unchanged.⟧

⟦s9|*While* a firing pass is under way, its ready order *shall* change only when the pass starts or drops a transition.⟧

⟦s10|*When* a firing pass ends, its ready order *shall* be empty, so a transition of the order that does not hold a clock or is not enabled on the pass-visible marking when it is next is dropped, loses its clock and does not start in that pass.⟧

⟦s11|*When* a transition starts in a firing pass, it *shall* consume, drain and hand its action only tokens of the pass-visible marking, so a token a synchronous action deposited earlier in the same pass survives its `all()`, `atLeast(n)` and reset arcs and does not reach its action.⟧

⟦s12|*While* a firing pass is under way, the executor *shall* change the pass-visible marking only by starting a transition, and *shall* keep every token deposited earlier in the pass, so a token a synchronous action deposits in the pass does not become part of the pass-visible marking.⟧

⟦s13|*When* a firing pass begins, the executor *shall* keep the marking, and every token of the marking *shall* be part of the pass-visible marking of the new pass.⟧

**Acceptance Criteria:**
1. Two transitions sharing input place P; T1 (P=10) and T2 (P=5); one token in P; T1 fires; T2 disabled.
2. If T1 is not ready (timing not satisfied), T2 may fire.
3. Whether a loser's inputs are "no longer satisfied" is judged against the marking
   as consumed by earlier firings in the same firing pass, but before any tokens
   their synchronous actions produced: T1 (higher priority) consumes a token T2
   needs and refills the place via its own output in the same pass; T2 remains
   disabled and may fire no earlier than the next cycle, since the enablement
   recheck of the pass does not count a same-pass deposit (see [EXEC-001]).
4. AC3 governs token **counts**, not only presence. A cardinality gate
   (`exactly(n)`, `atLeast(n)`) re-evaluated during the pass MUST NOT count tokens
   a same-pass synchronous action deposited, and a ν-correlated join whose
   correlated input place received such a deposit fires no earlier than the next
   cycle. AC3 governs inhibitor arcs as well: inside a firing pass, the marking a
   transition fires from in the sense of [CORE-022] is the pass-visible marking, so a
   same-pass deposit into an inhibitor place does not block a transition later in
   the same pass. Deposits become visible to the enablement recheck and to
   consumption at the next cycle, never part-way through a pass.
5. Invisibility extends to consumption, not just to the enablement test. A
   draining arc — `all()`, `atLeast(n)`, or a reset arc — that fires later in the
   same pass takes only the tokens that were present when the pass began, as
   consumed by earlier firings; tokens a same-pass action deposited survive it and
   remain for the next cycle. Deposits land at the tail of each place's FIFO
   queue ([EXEC-010]), so this is the prefix of length `available - deposited`.
   Without this, a gate that correctly refused to *count* a same-pass deposit
   would still *swallow* it.

So a pass behaves as if every firing in it started before any of them deposited: a drain later
in the pass sees a place emptier than any one-at-a-time order leaves it. Verification reads a
firing whose output is drained, reset or inhibited as two steps for that reason ([VER-004]).

**Depends on:** [EXEC-001], [EXEC-002], [EXEC-010], [CORE-022]
**Test derivation:** Two competing transitions; verify only highest priority fires when only 1 token available."#
