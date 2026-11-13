import Libpetri.Spec.Text

requirement_text EXEC_042
  id "EXEC-042"
  title "Terminal Places"
  priority SHOULD
  kind B
  body r#"⟦s1|A net MAY declare **terminal places** (`terminal(place)` on the net builder).⟧ ⟦s2|A terminal place
states, in the model, that the run is over once the place holds a token.⟧ ⟦s3|The executor ends the
run at that point.⟧ Nothing outside the net has to watch the marking and stop it.

A net that never quiesces makes this the only in-net way to say "done". Nets with environment
places are the usual example ([ENV-010]): a workflow that ends on a result, or a session that
ends on a cancel signal injected into a terminal environment place.

**Check points, and strictness.** An implementation MUST check terminal places at these points:
- ⟦s4|on the initial marking, before the first cycle;⟧
- ⟦s5|after every token it deposits, from an action's completion, a mid-action publication
  ([IO-015]), an external injection, or a synchronous action's output within the firing pass
  ([EXEC-001]).⟧

⟦s6|Once a deposit marks a terminal place, **no transition starts afterwards**.⟧ ⟦s7|That includes a
transition that was already enabled later in the same firing pass.⟧ ⟦s8|The deposit that marks the
terminal place completes atomically: all the tokens of that completion's outcome, or of that
published batch, are deposited.⟧ Strictness is what makes the runtime equal to the verification
encoding below. A check "at the next cycle boundary" would let transitions fire that the encoding
says cannot.

⟦s9|*While* a terminal place holds a token, the executor *shall not* take any step of its loop other than ending the run with the termination reason `terminal`: it starts no transition and processes no completion, publication or external event.⟧

⟦s10|*When* the executor deposits the outcome of a completion (its returned emission or its timeout outcome) or a published batch ([IO-015]) and one of its tokens marks a terminal place, it *shall* deposit all of that outcome or batch before the run ends.⟧

**What stopping means.** A stop on a terminal place is a hard stop:
- ⟦s11|Actions still in flight are abandoned. Their late results are discarded and never deposited,
  as in [ENV-015].⟧
- ⟦s12|Completions and external events still queued behind the deposit are not admitted. A queued
  external event is refused ([ENV-004]), exactly as after [ENV-013].⟧
- ⟦s13|The run ends with the termination reason `terminal` ([EXEC-041]), a completed reason.⟧
- No diagnostic event is emitted ([EVT-013] AC5): the stop was designed, not caller-requested.
- ⟦s14|The reason `terminal` takes precedence: while a terminal place holds a token, the run does not
  end `quiescent`, `closed` or `stopped` ([EXEC-041]); a caller whose run budget expired earlier
  may still have been told `stopped` ([ENV-016]).⟧
- ⟦s15|A firing whose mid-action publication ([IO-015]) marked the terminal place is still running: it
  is abandoned like any other action in flight.⟧
- ⟦s16|A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight.⟧
  ⟦s17|Answering a snapshot request changes nothing and is not a step of the loop; [ENV-014] states
  the answer.⟧

⟦s18|*If* no terminal place holds a token, *then* the executor *shall not* end the run with the termination reason `terminal`.⟧

⟦s19|*When* a terminal place holds a token, the executor *shall* end the run with the termination reason `terminal` without waiting for the actions still in flight.⟧

⟦s20|*When* the executor ends the run on a terminal place, it *shall* return the marking it holds at that point and *shall not* restore the tokens that abandoned firings consumed.⟧

⟦s21|*When* the executor ends the run on a terminal place, it *shall* keep every firing still in flight as abandoned work in flight and *shall* refuse every external event still queued ([ENV-004]).⟧

**Well-formedness.** ⟦s22|A terminal place MUST NOT be an input or a read-arc place of any
transition: such a transition could never fire, so the net is rejected when it is built.⟧ ⟦s23|A
terminal place MAY be an environment place: injecting into it ends the run.⟧

⟦s24|*When* the executor injects an external event into a terminal place, it *shall* deposit the event's token there, which ends the run.⟧

⟦s25|*If* a declared terminal place is an input place or a read-arc place of a transition of the net, *then* building the net *shall* fail.⟧

⟦s26|*When* a net is built without composition and without fusion sets and no declared terminal place is an input place or a read-arc place of one of its transitions, building it *shall* succeed, and the built net's terminal places *shall* be exactly the declared ones.⟧

**Composition.** Terminals are a property of the whole net. A subnet body ([MOD-001]) that
declares terminal places MUST be rejected by `compose` and `instantiate` with an error that names
the place. Scoped termination (ending one subnet instance) is not defined.

**Verification.** A verifier MUST apply terminal places automatically, with no restatement by
the caller. For each terminal place `P` it verifies the net, after the in-flight split of
[VER-004], in which:
- `P` inhibits every transition;
- `P` is a sink place ([VER-002]);
- `P` is a conditional-sink marker for every place ([VER-014]), i.e. `sinkPlacesWhen(P, all
  places)`.

This matches the runtime above for every transition the split of [VER-004] cuts in two: a
marking with `P` marked is quiescent and excused, and no transition fires once `P` is marked.
For a transition that stays atomic it holds for the properties named below. It is merged into
open-net contracts ([VER-022]) as a designed terminal. A net with no terminal places MUST
produce byte-identical scripts ([VER-013]).

The in-flight split of [VER-004] applies first. A transition that marks `P` is always split,
because `P` inhibits every transition, so the model has the executor's order: other actions
start while it is in flight, and its completion step marks `P` afterwards. `P` also inhibits
every completion step, so an action in flight when `P` is marked deposits nothing and leaves
its in-flight place marked, which `P` excuses. An abandoned action of a transition that stays
atomic is sound for monotone properties (place bounds, mutual exclusion, unreachability): the
abandoned marking lies below one the model reaches, where its outputs were deposited. It is
sound for `DeadlockFree` and `TerminatesAtSink` too, since `P` excuses every place at the
marking it ends in, and for `JoinedOrDeadLettered` and the upper bound of `QuiescentCount`,
which fewer tokens can only help.

A lower bound is the exception. Take `t: one(a) → ok` with a 100 ms action, `f: one(s) → done`
with a 10 ms action, `done` terminal, and `{a, s}` initially. The executor ends with
`a = ok = 0`, so `QuiescentCount([a, ok], 1, 1)` fails, while every atomic order counts one
token there. So when a `QuiescentCount` has `min > 0` and the net has a terminal place the
property does not list in `waivedBy`, every transition that deposits into a counted place or a
waiver place is split as well ([VER-004]). Its completion step is inhibited by `P` like any
other, so the model abandons the action as the executor does.

**Acceptance Criteria:**
1. A net whose initial marking marks a terminal place fires nothing and ends `terminal`.
2. An asynchronous completion that marks a terminal place ends the run `terminal`. With another
   action still in flight, the run does not wait for it, and its result never appears in the
   marking.
3. An injection that marks a terminal environment place ends the run `terminal`. An external
   event queued behind it is refused.
4. No transition starts after the deposit that marks a terminal place. Where synchronous outputs
   are deposited inside the firing pass, a second transition later in the same pass's order does
   not start. Where they are deposited in the completion phase, that transition may already have
   started, but its result is abandoned and never deposited.
5. A transition that consumes or reads a terminal place is rejected when the net is built.
6. `compose` and `instantiate` reject a subnet body that declares a terminal place.
7. Without the declaration, the net of AC2 is a `DeadlockFree` violation (its other in-flight
   work is stranded). With it, the verifier proves `DeadlockFree` without any sink option from
   the caller.
8. A net without terminal places produces byte-identical verification scripts.
9. On the net above (`t` 100 ms, `f` 10 ms, `done` terminal, `{a, s}`), `QuiescentCount([a, ok],
   1, 1)` is `Violated` and both executors end with `a = ok = 0`. With `done` in `waivedBy` it is
   `Proven`.

**Depends on:** [EXEC-001], [EXEC-020], [EXEC-022], [EXEC-040], [EXEC-041], [CONC-001], [IO-015],
[ENV-004], [ENV-013], [ENV-014], [ENV-015], [EVT-013], [VER-002], [VER-014], [VER-022], [MOD-001]
**Test derivation:** One net per AC. For AC4, build a pass with two enabled transitions ordered
by priority: the first is synchronous and marks the terminal place, the second must never fire.
For AC7, use a fork whose one arm marks the terminal place while the other arm's action is still
in flight."#
