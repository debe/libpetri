import Libpetri.Spec.Text

requirement_text EVT_032
  id "EVT-032"
  title "Marking Replay Cache"
  priority SHOULD
  kind F
  body r#"A replay cache reconstructs execution state at an arbitrary event index from a recorded event
stream, for debug-protocol seek / step. `compute_at(events, index)` returns a `ComputedState`
— the marking (token counts per place), enabled transitions, and in-flight transitions — replayed
from the nearest periodically-cached snapshot rather than from the start of the stream.

⟦s1|*While* every snapshot in the replay cache is at an index no greater than the length of `events` and is the replay of `events` up to that index, `compute_at(events, index)` *shall* return the replay of the first `index` events of `events`, or of all of `events` when `index` is beyond its length.⟧

⟦s2|*When* `compute_at(events, index)` returns, every snapshot it leaves in the replay cache *shall* be at an index no greater than the length of `events` and be the replay of `events` up to that index, provided every snapshot in the cache met both conditions before the call.⟧

⟦s3|The replay of an event stream *shall* start from the empty state (no token in any place, no enabled and no in-flight transition) and apply its events in order, each as follows: a `MarkingSnapshot` sets the token count of every place it carries to the count it carries and of every other place to zero; a `TokenAdded` adds one token to its place; a `TokenRemoved` removes one token from its place, and does nothing if the place has none; a `TransitionEnabled` adds its transition to the enabled transitions; a `TransitionStarted` removes its transition from the enabled transitions and adds it to the in-flight transitions; a `TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut` or `ActionTimedOut` removes its transition from the in-flight transitions; any other event (`ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted`, `LogMessage`) leaves the state unchanged.⟧

The enabled transitions are those with a `TransitionEnabled` event and no later `TransitionStarted` event, so they over-approximate the transitions enabled at that point of the run: a transition whose tokens another firing took, or a reaped transition, stays listed. The in-flight transitions are a set of names, so a transition with two firings in flight at once leaves it when its first firing ends. The replayed token counts include the initial marking only for a stream that reports it in a `MarkingSnapshot` right after its `ExecutionStarted` event, as every executor's stream does ([EVT-014]); the replay reads only the counts of a snapshot. The two transition lists of a `ComputedState` are sets: their order is not specified.

⟦s4|The replay of all events a run has emitted before its first step, or up to the end of any of its steps, *shall* count, for every place the net declares, the tokens that place holds at that point, and *shall* list among the enabled transitions every transition that holds a clock at that point, also one whose clock restart is pending ([EVT-005]).⟧ At an index inside the events of one step, for example between the `TokenRemoved` events of a firing that starts, the replayed counts can match no marking the executor held. The count is required only on the places the net declares: a TypeScript snapshot lists only the declared places, so the snapshot before `ExecutionCompleted` sets the replayed count of an undeclared place back to zero.

**Acceptance Criteria:**
1. `compute_at(events, 0)` is the empty state; `compute_at(events, len)` is the replay of the whole
   stream.
2. An index beyond the stream length is clamped to the end (no panic).
3. Repeated calls on a stream that only grows at its end return state equal to a from-scratch
   replay: the same token count per place and the same sets of enabled and in-flight transitions,
   in an unspecified order. A stream that changed otherwise, for example by the eviction of its
   oldest events ([EVT-024]), needs `invalidate()` before the next call. Reusing cached snapshots
   is expected for speed only: it does not change the state returned.
4. The marking in `ComputedState` carries token counts; replayed tokens need not carry value
   payloads (events carry type + structured metadata, not live objects).
5. Before the first step of a run and after each of its steps, the replay of the events emitted
   so far counts on every declared place the tokens it holds, and lists as enabled every
   transition that holds a clock.

**Depends on:** [EVT-021], [EVT-004], [EVT-006], [EVT-007], [EVT-008], [EVT-009], [EVT-010], [EVT-011], [EVT-012], [EVT-014]
**Test derivation:** Record a multi-firing run; `compute_at` at 0, an intermediate index, the end,
and beyond-end; verify clamping and snapshot reuse. Run a net with token 1 in
place 0 and one transition that takes it and puts 9 back; before the first step and after each
step, compare the replayed counts with the executor's marking and check that every transition
that holds a clock is listed as enabled."#
