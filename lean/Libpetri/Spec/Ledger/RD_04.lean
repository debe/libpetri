import Libpetri.Spec.Ledger
import Libpetri.Spec.GlossaryEvents
import Libpetri.Spec.Text.EVT_001

runtime_defect RD_04
  title "A TypeScript event shares the executor's consumed array"
  requirements r#"EVT-001 (AC2: collections in events are copies; ruling D66 (a))."#
  runtimes r#"TypeScript."#
  defect r#"the `TransitionStarted` event carries the executor's own `consumed` array, which the
executor also hands on, so the event is not a copy. `typescript/src/runtime/bitmap-net-executor.ts`
(`fireTransition`), `TransitionStarted` (`typescript/src/event/net-event.ts`). The precompiled executor
(`typescript/src/runtime/precompiled-net-executor.ts`) does the same."#
  evidence r#"none. EVT-001 has no block: a Lean event is a value, so a shared array cannot
be stated (⟪netEvent_value⟫, GlossaryEvents.lean, cites EVT-001)."#
  fix r#"both executors put a copy of the consumed tokens into the `TransitionStarted` event, made
only when an event store is enabled. TypeScript `executor-shared-semantics.test.ts`, "carries a
copy of the consumed tokens (EVT-001 AC2)", on both executors."#
  status "fixed, unreleased"
