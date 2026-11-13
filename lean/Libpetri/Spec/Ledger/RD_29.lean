import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_051
import Libpetri.Spec.Text.MOD_051

runtime_defect RD_29
  title "TypeScript hands the selected environment mode to `verify` only when there is an input port"
  requirements r#"MOD-051 (the setup of each per-property verification: the verifier is set up
with the harness environment places and the selected environment mode, and then passed,
together with the synthetic net, through the configure hook)."#
  runtimes r#"TypeScript."#
  defect r#"`SubnetDef.verify` registers the environment places and the selected mode only when
the harness has an environment place (`typescript/src/core/subnet-def.ts`). For a subnet
with no input or in-out port the configure hook receives a verifier on the verifier default
`AlwaysAvailable` (the `_environmentMode` field of `SmtVerifier`,
`typescript/src/verification/smt-verifier.ts`), not on the selected
mode, so a hook that registers an environment place itself runs under the wrong mode. Rust
(`run_per_property`, `rust/libpetri-verification/src/harness.rs`) and Java
(`SubnetDef.verify`, `java/src/main/java/org/libpetri/core/SubnetDef.java`) set the mode on every call, and
Python rides on Rust."#
  evidence r#"⟪MOD_051_forbids_modeOnlyWithEnvs⟫ in `MOD_051.lean`: the forwarder without
its input port, verified under `Ignore` with a hook that registers `sut/IN`; the TypeScript
shape (⟪mod051ModeOnlyWithEnvs⟫) proves `TerminatesAtSink` where line 4 requires `Violated`."#
  fix r#"`SubnetDef.verify` sets the harness environment places and the selected mode on every
per-property verifier, whether or not the harness has an environment place. TypeScript
`subnet-verify-options.test.ts`, "a hook on a subnet with no input port runs under the selected
mode (MOD-051)"."#
  status "fixed, unreleased"
