import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.ENV_015
import Libpetri.Spec.Text.ENV_016
import Libpetri.Spec.Text.EVT_031

unbuilt_requirement UB_01
  title "Immediate termination"
  requirements r#"ENV-015."#
  runtimes r#"Rust, TypeScript, Python."#
  missing r#"`terminateNow()`. Java has it on both executors."#
  status "open"

unbuilt_requirement UB_02
  title "awaitTermination"
  requirements r#"ENV-016."#
  runtimes r#"TypeScript, Rust, Python."#
  missing r#"`awaitTermination(timeout)`. Java has it on both executors."#
  status "open"

unbuilt_requirement UB_03
  title "Run-timeout policy"
  requirements r#"ENV-016."#
  runtimes r#"Rust, Python."#
  missing r#"a run with a caller timeout and an *abandon* or *close* policy. Java
(`run(Duration, RunTimeoutPolicy)`) and TypeScript (`run(timeoutMs, onTimeout)`) have it on both
executors; Rust has `run_sync` and `run_async` only."#
  status "open"

unbuilt_requirement UB_04
  title "Live event-store subscriptions"
  requirements r#"EVT-031."#
  runtimes r#"Java, TypeScript, Rust."#
  missing r#"live subscriptions on the event store. The Python binding has them
(`InMemoryEventStore.subscribe` and `subscribe_stream`, built in `rust/libpetri-py`); the Rust
crate's own `InMemoryEventStore` (`libpetri-event`) has none."#
  status "open"
