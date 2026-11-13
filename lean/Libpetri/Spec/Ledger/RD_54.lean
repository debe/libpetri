import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.IO_011
import Libpetri.Spec.Text.IO_012

runtime_defect RD_54
  title "Rust and TypeScript build an Xor of fewer than two children or an empty And written without its constructor"
  requirements r#"IO-012 (line 1, an `Xor` node has two or more children; AC1), IO-011 (AC1, an `And`
node has at least one child)."#
  runtimes r#"Rust, TypeScript."#
  defect r#"the arity checks lived only in the `xor()` and `and()` factories
(`rust/libpetri-core/src/output.rs`, `typescript/src/core/out.ts`). Rust's `Out::Xor` and `Out::And`
variants are public and a TypeScript output spec can be written as an object literal, and neither
`TransitionBuilder::build` (`rust/libpetri-core/src/transition.rs`) nor `TransitionBuilder.build`
(`typescript/src/core/transition.ts`) ran the checks again, although both re-run the IO-002/IO-004
count and TIME-001 timing factory checks for these paths. `Out::Xor(vec![])` built a transition that
consumes on every firing and then fails output validation; a one-child Xor built as its child, and
an empty And as a spec that claims no place. Java checks in the `Arc.Out.Xor` and `Arc.Out.And`
record constructors; Python goes through `xor()` and `and()`."#
  evidence r#"none beyond the IO_012 AC1 assume."#
  fix r#"the transition builders of Rust and TypeScript reject an `Xor` node with fewer than two
children or an `And` node without one, at any depth, the first such node in pre-order reporting
with the factory's message, after the timing check and before the output-spec checks
(`arity_violation` in `output.rs`, `arityViolation` in `out.ts`). Python's `xor_outputs` and
`and_outputs` now raise the factory's message as a `ValueError`. Tests citing IO-012 AC1 and
IO-011 AC1: `io_012_ac1_xor_and_io_011_ac1_and_arity_is_checked_at_build` in `transition.rs`,
'IO-012 AC1, IO-011 AC1: an object literal does not skip the arity check' in
`typescript/tests/core/out-build-checks.test.ts`, and
`test_io_012_ac1_and_io_011_ac1_arity_is_the_factory_check` in
`python/tests/test_output_spec_build_checks.py`."#
  status "fixed, unreleased"
