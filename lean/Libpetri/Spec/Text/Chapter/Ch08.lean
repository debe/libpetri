import Libpetri.Spec.Text
import Libpetri.Spec.Text.EVT_001
import Libpetri.Spec.Text.EVT_002
import Libpetri.Spec.Text.EVT_003
import Libpetri.Spec.Text.EVT_004
import Libpetri.Spec.Text.EVT_005
import Libpetri.Spec.Text.EVT_006
import Libpetri.Spec.Text.EVT_007
import Libpetri.Spec.Text.EVT_008
import Libpetri.Spec.Text.EVT_009
import Libpetri.Spec.Text.EVT_010
import Libpetri.Spec.Text.EVT_011
import Libpetri.Spec.Text.EVT_012
import Libpetri.Spec.Text.EVT_013
import Libpetri.Spec.Text.EVT_014
import Libpetri.Spec.Text.EVT_020
import Libpetri.Spec.Text.EVT_021
import Libpetri.Spec.Text.EVT_022
import Libpetri.Spec.Text.EVT_023
import Libpetri.Spec.Text.EVT_024
import Libpetri.Spec.Text.EVT_025
import Libpetri.Spec.Text.EVT_030
import Libpetri.Spec.Text.EVT_031
import Libpetri.Spec.Text.EVT_032

spec_chapter "08-events-observability.md"
  md r#"# 08 — Events & Observability

This document specifies the event types emitted during execution, the event store interface, and observability features.

The ordering sentences of this chapter (which event comes before which within a start, a deposit or a run) read the event store with two kinds of event left out where Java appends them from outside the orchestrator: ActionTimedOut events ([EVT-010]), which Java emits from the action's timer, and the log messages Java captures from actions ([EVT-013]). Such an event can fall between the events of one orchestrator step. TypeScript and Rust append every event from the orchestrator, so in their stores no event falls inside a step.

---

## Event Hierarchy"#
  req EVT_001
  md r#"---"#
  req EVT_002
  md r#"---"#
  req EVT_003
  md r#"---"#
  req EVT_004
  md r#"---"#
  req EVT_005
  md r#"---"#
  req EVT_006
  md r#"---"#
  req EVT_007
  md r#"---"#
  req EVT_008
  md r#"---"#
  req EVT_009
  md r#"---"#
  req EVT_010
  md r#"---"#
  req EVT_011
  md r#"---"#
  req EVT_012
  md r#"---"#
  req EVT_013
  md r#"---"#
  req EVT_014
  md r#"---

## Event Store Interface"#
  req EVT_020
  md r#"---"#
  req EVT_021
  md r#"---"#
  req EVT_022
  md r#"---"#
  req EVT_023
  md r#"---"#
  req EVT_024
  md r#"---"#
  req EVT_025
  md r#"---

## Event Query Helpers"#
  req EVT_030
  md r#"---

## Live Streaming & Replay"#
  req EVT_031
  md r#"---"#
  req EVT_032
