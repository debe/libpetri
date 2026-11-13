import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.CORE_060
import Libpetri.Spec.Text.CORE_060

runtime_defect RD_09
  title "Java's `input` with several tokens contradicts its own javadoc"
  requirements r#"CORE-060 (the case is open in the spec; ruling D50 (a))."#
  runtimes r#"Java."#
  defect r#"with more than one token delivered from a place, `input` returns the oldest token's
value, while its javadoc says it fails. Rust, TypeScript and Python report an error.
`TransitionContext.input` (`java/src/main/java/org/libpetri/core/TransitionContext.java`) against
its own javadoc.
Java's `fork()` and `transform(Place, fn)` rely on `input` returning the oldest token (the
documented CORE-052 divergence), so the javadoc is what is wrong."#
  evidence r#"⟪CORE_060_batch_undecided⟫ shows the block leaves the case open; the
defect is Java against its own documentation."#
  fix r#"the javadoc says that `input` returns the oldest value and points to `inputs(Place)` for
the whole batch; the behaviour is unchanged. Java
`TransitionContextTest.core060_input_withSeveralTokens_returnsOldestValue` pins it."#
  status "fixed, unreleased"
