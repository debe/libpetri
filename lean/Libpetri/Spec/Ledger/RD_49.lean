import Libpetri.Spec.Ledger
import Libpetri.Reference.Events
import Libpetri.Spec.Req.EVT_032_B
import Libpetri.Spec.Text.EVT_014

runtime_defect RD_49
  title "Rust never emits the MarkingSnapshot event"
  requirements r#"EVT-014 (AC1: emitted at least at execution start and before execution
completion)."#
  runtimes r#"Rust, Python."#
  defect r#"Rust declared `NetEvent::MarkingSnapshot` and its consumers read it (debug converter,
marking cache, archive metadata), but no executor emitted it."#
  evidence r#"the Rust and Python emission ⟪polRust⟫ (`lean/Libpetri/Reference/Events.lean`)
emits both snapshots; the Rust stream then meets EVT-032's run companion (⟪EVT_032_B_rust⟫),
which reads only the counts."#
  fix r#"the shared executor core emits `MarkingSnapshot` right after `ExecutionStarted` and right
before `ExecutionCompleted`, on both backends and in `run_sync` and `run_async`, so Python gets it
too. The session archive reader now reads an archived snapshot back instead of turning it into a
`TransitionEnabled` for an unknown transition. A store that records several runs now holds each
run's start snapshot, so a replay resets to that run's marking."#
  status "fixed, unreleased"
