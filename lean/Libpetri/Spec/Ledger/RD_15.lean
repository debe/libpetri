import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.CONC_003
import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Text.CONC_003
import Libpetri.Spec.Text.EXEC_022

runtime_defect RD_15
  title "A flush can publish after the action completed"
  requirements r#"EXEC-022 (line 4: no output the action had not published before the budget
ran out is deposited or published); CONC-003 (line 2: a publication deposits only a batch the
action flushed before it completed)."#
  runtimes r#"Rust, Python."#
  defect r#"the flush closure has no completed or abandoned check and can outlive the action:
a Rust action that moved `ctx.flush_fn()` into a spawned task, or a Python context held past
the action, can still send a batch after the action completed, by a normal return, an error
return or the expiry of its budget (on a timeout the executor drops the action future). Phase
1b then deposits that batch, although the action had completed before it flushed it. The fix
is an abandoned flag on the closure, set in the timeout arm and at completion.
`rust/libpetri-runtime/src/executor_core/executor.rs` (the `set_flush_fn` closure in
`fire_transition_async`), `rust/libpetri-core/src/context.rs` (`flush_fn`),
`rust/libpetri-py/src/action.rs` (`PyActionContext::from_transition_context`)."#
  evidence r#"⟪EXEC_022_forbids_lateFlush⟫ (EXEC_022.lean); ⟪CONC_003_forbids_flushAfterError⟫
(CONC_003.lean), the case after an error return."#
  fix r#"the flush closure and its spawned task share a gate under one lock: the task marks the
firing ended once the action completes, fails or times out, before it sends the completion, and a
later flush returns an error naming EXEC-022 and deposits nothing (Python raises `RuntimeError`).
Rust `backend_suite_tests.rs` `late_flush::exec_022_a_flush_after_the_firing_ended_is_refused` and
`late_flush::exec_022_a_flush_before_the_timeout_is_deposited`; Python
`test_ctx_flush.py::test_a_flush_after_the_timeout_is_refused_exec_022` and
`::test_a_flush_after_the_action_returned_is_refused_exec_022`."#
  status "fixed, unreleased"
