import Libpetri.Spec.Text

requirement_text EVT_031
  id "EVT-031"
  title "EventStore Live Subscriptions"
  priority SHOULD
  kind B
  body r#"An event store may expose a live subscription that streams events as they are appended, distinct
from the post-hoc snapshot reads of [EVT-020]. A subscription:
- delivers only events matching its server-side filters (by type, transition, and place);
- is forward-only: events appended **before** the subscription was created are not replayed;
- batches delivery by a caller-chosen `batch_size` and `batch_timeout_ms` (a `batch_size = 1`,
  `batch_timeout_ms = 0` "unary" mode delivers one event at a time for low latency);
- is bounded: it uses a finite channel capacity, and an append of a matching event that finds the channel full ends that subscription instead of waiting for room;
- terminates cleanly on explicit close, when the store is dropped, or when its channel overflows.

This differs from [EVT-024] (DebugEventStore live tailing for debug UIs): EVT-031 governs
subscriptions over the ordinary observability store, with server-side filtering and batching.

⟦s1|*Where* an event store provides live subscriptions, the events a subscription has received at any point, taken over all its batches in the order it received them, *shall* be events that match its filters and were appended to the store after the subscription was created and before that point, in append order, each at most once.⟧

⟦s2|Each batch a subscription receives *shall* hold at least one event and at most `batch_size` events, so that with `batch_size = 1` it receives one event per batch.⟧

⟦s3|Each subscription *shall* have a finite channel capacity.⟧

⟦s4|*When* a receive has taken the first event of its batch, it *shall* add further events until the batch holds `batch_size` events, `batch_timeout_ms` have elapsed since it took that first event, or no further event can arrive, and *shall* then return the batch; with `batch_timeout_ms = 0` it *shall* add only the events already in the channel.⟧

⟦s5|*When* an append of an event that matches the filters of a subscription finds its channel full, the store *shall* end that subscription: the subscription *shall* receive no event appended from then on, and, if none of its receives is pending at that append, its receives *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.⟧

⟦s6|Until the store is dropped, an append *shall* be accepted at every point; in particular it *shall not* wait for room in the channel of a subscription.⟧

⟦s7|*When* a subscription is closed while none of its receives is pending, it *shall* receive no further event, and its next receive *shall* report the end of the stream.⟧

⟦s8|*When* the store is dropped, the receives of each of its subscriptions that has no receive pending *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.⟧

What a close or an overflow does to a receive that is already pending is not specified.

**Acceptance Criteria:**
1. A subscriber receives only events matching its filters, in append order.
2. Events appended before the subscription are not delivered (forward-only).
3. Unary mode delivers one event per batch; batched mode delivers up to `batch_size`, flushing
   early after `batch_timeout_ms`.
4. Explicit close with no receive pending ends iteration cleanly; a full channel ends the subscription: it receives no later event, the append does not wait, and with no receive pending its receives report the end after they have taken the events its channel holds.

**Depends on:** [EVT-020], [EVT-021], [EVT-030]
**Status:** Proposed
**Test derivation:** Run an async net feeding environment events; subscribe with a transition
filter; verify batched forward-only delivery and clean close."#
