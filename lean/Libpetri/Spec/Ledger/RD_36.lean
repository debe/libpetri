import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_014
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_36
  title "Java's debug protocol renders maps and sets in a per-JVM order"
  requirements r#"EVT-025 (the reproducibility paragraph: 'an implementation MUST NOT put one
on the path to the archive or the debug protocol', the debug protocol half), EVT-014 (AC5:
rendering the same event stream twice onto the debug protocol yields identical output)."#
  runtimes r#"Java."#
  defect r#"`NetEventConverter.toEventInfo` builds the `details` of `NetEventInfo` with
`Map.of(...)` of two or more entries (`ExecutionStarted`, `ExecutionCompleted`,
`TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut`), and `withInstancePrefix`
returns `Map.copyOf(copy)`, so every event of a composed net whose details then hold two or
more entries is affected too.
`java/src/main/java/org/libpetri/debug/NetEventConverter.java`: those five cases of
`toEventInfo` and the `Map.copyOf` in `withInstancePrefix`, and through `withInstancePrefix` also
the `TransitionStarted`, `ActionTimedOut`, `TokenAdded` and `TokenRemoved` cases.
`DebugSessionRegistry.tagsFor` hands `Map.copyOf(session.tags())` to
`SessionSummary.tags` (`DebugSessionRegistry.java`), and the `SubnetInstanceInfo`
constructor copies its name sets with `Set.copyOf` (`DebugResponse.java`), which drops
the `LinkedHashSet` order `buildSubnetInstances` builds for a stable `Subscribed` response
(recorded on its own as RD-45).
The iteration order of these immutable collections is salted per JVM, `DebugResponse` is a
Jackson type, and Jackson writes a map and a set in iteration order (no
`ORDER_MAP_ENTRIES_BY_KEYS` is set, and a set is written as an array either way), so one event,
session list or subscription renders differently from one JVM to the next. Rust builds the
event details as a `BTreeMap` (`rust/libpetri-debug/src/net_event_converter.rs`), and
TypeScript as object literals and insertion-ordered sets.
Reproduced with JDK 25.0.2: `Map.of` of the three `ExecutionCompleted` keys and
`Set.copyOf(List.of("a", "b", "c", "d"))` print in different orders in successive JVMs."#
  evidence r#"none; the debug protocol has no model. The EVT_025 assumes record it."#
  fix r#"the debug-protocol records normalise their collections where they are built:
`NetEventInfo.details` and `SessionSummary.tags` are sorted by code point, as Rust's `BTreeMap`
is, `DebugSessionRegistry.tagsFor` returns a sorted copy, and `SubnetInstanceInfo` keeps its build
order (RD-45). Java `NetEventConverterTest.detailsRenderInKeyOrder_EVT014_AC5`,
`DebugSessionRegistryTest.tagsForIsSortedByKey_EVT025` and
`DebugProtocolSubnetTest.subnetInstanceNamesKeepBuildOrder_EVT014_AC5`."#
  status "fixed, unreleased"
