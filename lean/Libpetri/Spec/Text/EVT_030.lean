import Libpetri.Spec.Text

requirement_text EVT_030
  id "EVT-030"
  title "Event Filtering"
  priority SHOULD
  kind F
  body r#"The event store or helper functions support:
- Filter by event type
- Filter by transition name
- Filter by place name (for token events)
- Pagination (offset / limit) over the filtered result
- Filter for failure events
- Count events, and an event-type histogram (counters)

⟦s1|*Where* an implementation provides a query over the events of an event store, the query without offset and limit *shall* return exactly the events that `events()` returns and that match every filter the query gives, in the order `events()` returns them, for every query whose transition filter does not name the empty name.⟧

⟦s2|A filter by event type *shall* match the events of the given types, a filter by transition name *shall* match the events that carry one of the given transition names, and a filter by place name *shall* match the events that carry one of the given place names.⟧

⟦s3|An event that carries no transition name *shall* match no filter by transition name, and its presence in the store *shall not* change which other events such a filter returns.⟧

⟦s4|*Where* an implementation provides offset and limit on a query, the query *shall* skip the first `offset` matching events and return the first `limit` of the matching events that follow (all of them when no limit is given), so that the page is taken over the filtered result and not over the store.⟧

⟦s5|*Where* an implementation provides `failures()`, it *shall* return exactly the TransitionFailed, TransitionTimedOut and ActionTimedOut events that `events()` returns, in the order `events()` returns them.⟧

⟦s6|*Where* an implementation provides `counters()`, it *shall* name each event type that occurs among the events `events()` returns exactly once, with the number of those events of that type, and *shall* name no other event type.⟧

⟦s7|*Where* an implementation provides a count of events, the count *shall* be the number of events that `events()` returns whose type is one of the given types, or the number of all of them when no type is given.⟧

**Acceptance Criteria:**
1. `eventsOfType(TransitionCompleted)` returns only completed events.
2. `transitionEvents("MyTransition")` returns all events that carry that transition name, also when the store holds events that carry no transition name.
3. Place filtering returns only token events for the named place(s); offset/limit page the result.
4. `failures()` returns TransitionFailed, TransitionTimedOut, and ActionTimedOut events.
5. `counters()` returns a `{eventType: count}` histogram whose values sum to the total event count.

**Test derivation:** Run net with mixed events; verify each filter, pagination, and the counters
histogram return correct subsets / totals."#
