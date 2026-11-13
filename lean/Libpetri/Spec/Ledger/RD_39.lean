import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.NU_052_split
import Libpetri.Spec.Req.NU_055_steps
import Libpetri.Spec.Text.NU_052
import Libpetri.Spec.Text.NU_055
import Libpetri.Spec.Text.VER_006

runtime_defect RD_39
  title "The Route B environment decline reads the selected mode, not whether conflict priority applies"
  requirements r#"NU-052 (the second shall sentence: under `CONFLICT` the verifier verifies
every call conflict priority does not apply to as under `NONE`), VER-006 AC8 (Route B declines
for a shared environment input only when "conflict priority prunes on an environment input two
transitions consume"; "Otherwise its verdict stands"), NU-055 (the third rule of step 5 of the
refusal order: a shared environment input is refused only "where conflict priority is in effect
([NU-052])")."#
  runtimes r#"Rust, Java, TypeScript, and Python through Rust."#
  defect r#"the verifier switches the mode it hands on to `NONE` only when the in-flight split
refuses a pruner (Rust `with_in_flight`, Java `applyInFlight` through `conflictOff`, TypeScript
`applyInFlight` through `_effectivePriority`). When conflict priority does not apply because a
transition of the net is read as reapable, the selected `CONFLICT` reaches the Route B
environment check, which declines whenever an environment place under `AlwaysAvailable` or
`Bounded(k)` has two or more consumers ("is a consumed input shared under conflict priority"),
although Route B itself turns the pruning off on that net (`verify_via_name_scg_reaping`,
`NuScgVerifier.verifyReaping`, `verifyViaNameScgReaping`). So on a net with a ν-join, no declared
budget, one `Deadline` or `Window` transition (`assumeNoReaping` not set) and an uncoloured
environment place two transitions consume, `Unreachable` or `PlaceBound` on a non-environment
place answers `Unknown` ("Declined under environment injection") under `CONFLICT` and the Route B
verdict under `NONE`. The same check refuses a name-alignment call: under `CONFLICT`, on a net
with a reapable transition, a `NameAligned(S)` or `QuiescentNameAligned(S)` call under
`AlwaysAvailable` whose uncoloured environment place outside `S` two transitions consume, and
that steps 1 to 4 and the first two rules of step 5 let through, answers `Unknown` ("is a
consumed input shared under conflict priority") where the refusal order of NU-055 reaches its
later rules or builds the graph.
Rust: `SmtVerifier::verify_net` (passes `self.priority_semantics` to
`route_b_env_observation`) and `route_b_env_observation` (the decline), in
`rust/libpetri-verification/src/smt_verifier.rs`.
Java: `SmtVerifier.pipeline` (passes `effectivePriority()`, still `CONFLICT` unless
`conflictOff`) and `routeBEnvObservation` (the decline), in
`java/src/main/java/org/libpetri/smt/SmtVerifier.java`.
TypeScript: `SmtVerifier.runPipeline` (passes `_effectivePriority`) and `routeBEnvObservation`
(the decline), in `typescript/src/verification/smt-verifier.ts`.
The fix is to hand the environment check `CONFLICT` only when conflict priority applies
(`conflict_pruning_applies` and the pruning not turned off by the split), `NONE` otherwise."#
  evidence r#"none; the setup model ⟪NuSetupFn⟫ of ⟪NU_052_split⟫ does not model the
environment decline. The ⟪NU_052_split⟫ assumes record it, and the ⟪NU_055_refusal⟫ assumes
in `NU_055_steps.lean` (the paragraph on step 5 of the refusal order) record that the gate's conflict fact is "conflict priority is in
effect" as NU-052 states it, not the runtimes' reading."#
  fix r#"the Route B environment check gets `CONFLICT` only where conflict pruning applies and
`NONE` otherwise, in all three runtimes; where pruning applies the decline still stands. Rust
`smt_verifier.rs` `nu_052_env_decline_only_where_conflict_priority_applies`; Java
`SmtVerifierTest.envDeclineReadsWhetherConflictPriorityApplies_NU052_VER006_AC8`; TypeScript
`smt-verifier.test.ts`, "NU-052 / VER-006 AC8: the env decline applies only where conflict
priority is in effect"; Python
`test_nu_verification.py::test_nu_052_env_decline_only_where_conflict_priority_applies`."#
  status "fixed, unreleased"
