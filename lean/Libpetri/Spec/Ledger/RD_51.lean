import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_030

runtime_defect RD_51
  title "The event stores lack the EVT-030 query helpers"
  requirements r#"EVT-030 (AC3: filter by place name and page with offset and limit; AC5: an
event-type histogram)."#
  runtimes r#"Java, TypeScript, Rust."#
  defect r#"only the Python binding offered a place filter, offset and limit, and `counters()`;
the Rust store also had no filter by event type."#
  evidence r#"none."#
  fix r#"each store gains the helpers with the Python binding's semantics, without an API break.
Java: default methods `EventStore.placeEvents`, `filter(predicate, offset, limit)` and
`counters()`. TypeScript: free functions `queryEvents` (with `EventQuery`), `placeEvents`,
`countEvents`, `counters` and `eventPlaceName`. Rust: `InMemoryEventStore::events_of_type`,
`place_events`, `query(&EventQuery)`, `count_of_types` and `counters`, and
`NetEvent::event_type`. Tests cite EVT-030 in each language."#
  status "fixed, unreleased"
