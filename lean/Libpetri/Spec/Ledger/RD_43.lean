import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.VER_013
import Libpetri.Spec.Text.VER_013

runtime_defect RD_43
  title "Java does not poll the total budget after an unclamped z3 call"
  requirements r#"VER-013 (the stop sentences, `VER_013_stop` line 4: a solver call that
starts its process polls again after the reply, and a stop that poll is the first to find is
charged to the running step; and through it line 6 and AC9's reason: an `Unknown` reached after
the deadline passed gets `total verification budget of <N> ms exhausted during <phase>`)."#
  runtimes r#"Java."#
  defect r#"after the process, `Z3Solver.run`
(`java/src/main/java/org/libpetri/smt/z3/Z3Solver.java`) checks only
`VerificationDeadline.cancelled()` and `clamped && deadline.expired() && !answered(reply)`. A
total budget that runs out during a call whose own timeout was not clamped is therefore not
recorded. Concrete run: total budget 10 000 ms, per-call timeout 5 000 ms, and the IC3/PDR
query starts with exactly 5 000 ms left, so `left < timeoutMs` is false and the call is not
clamped; `z3` overruns `-t` and is stopped by the `-T` backstop at about 6 s. `SpacerRunner.run`
returns `Unknown` with the hard-timeout reason, the HORN `Unknown` case of `SmtVerifier.pipeline`
(`java/src/main/java/org/libpetri/smt/SmtVerifier.java`) does not poll, and no later
`enter()` follows, so `verify()` returns the solver's reason where Rust and TypeScript give
`total verification budget of 10000 ms exhausted during IC3/PDR query`. Rust and Python poll
after every call (`Z3Solver::run` calls `total_budget::note_if_expired`, which is `cut`), and
TypeScript's `unknown` case of the IC3/PDR query polls with `run.deadline?.check()`
(in `runPipeline`, `typescript/src/verification/smt-verifier.ts`). The fix is a deadline
poll after every call, clamped or not (`deadline.check()` once the reply is in, before it is
returned unanswered), as Rust's `note_if_expired` does."#
  evidence r#"⟪VER_013_stop_forbids_noPostPoll⟫ (`VER_013.lean`): the runner whose solver
calls make no poll after the reply breaks ⟪VER_013_stop⟫ line 4 on the IC3/PDR query under a
100 ms budget spent from poll 2 and a solver that answers `unknown`; its finished `Unknown`
keeps `the solver answered unknown` where the reference gives the budget reason."#
  fix r#"`Z3Solver.run` polls after every reply, clamped or not, and charges a stop to the running
step when the reply is not an answer; an answer that arrives after the deadline is returned and
the next `enter()` stops the call, as Rust's `note_if_expired` does. Java
`StubZ3Test.totalBudget_spentDuringAnUnclampedCallIsChargedToThatStep_VER013`."#
  status "fixed, unreleased"
