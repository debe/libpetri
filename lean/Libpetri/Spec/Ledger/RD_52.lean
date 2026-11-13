import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EXEC_041

runtime_defect RD_52
  title "TypeScript keeps reporting `stopped` after the loop an expired run budget left running finishes"
  requirements r#"EXEC-041 (a finish makes its own termination reason available to the caller;
`stopped` only after an immediate termination, another caller-requested stop, a host fault or a
run-ending failure of the run's event store; a run budget that expires ends the caller's wait, not
the loop)."#
  runtimes r#"TypeScript."#
  defect r#"after `run(timeoutMs)` expired, both executors set the reason to `stopped` and set it at
the loop's finish only while it still read `running` (`executeLoop` in
`typescript/src/runtime/bitmap-net-executor.ts` and `precompiled-net-executor.ts`). The loop that
the abandon or close policy left running then finished quiescent, terminal or closed, and
`terminationReason()` still answered `stopped`, so the cause of that finish was never reported.
Java sets the reason only at the loop's finish."#
  evidence r#"none."#
  fix r#"`executeLoop` sets the reason from the terminal flag, the close flag and quiescence at
every finish. The reason reads `stopped` from the expiry until the loop finishes; the caller of the
expired run still gets the truncation through the rejected promise. Tests citing EXEC-041 in
`typescript/tests/runtime/terminal-places.test.ts` check both policies on both executors."#
  status "fixed, unreleased"
