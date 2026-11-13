import Libpetri.Spec.Ledger
import Libpetri.Reference.Timed
import Libpetri.Spec.Text.NU_053
import Libpetri.Spec.Text.VER_003

runtime_defect RD_26
  title "Java reports `counterexampleConfirmed` `false` on the name-coloured encoding"
  requirements r#"VER-003 (the initial-violation sentence: the empty firing sequence, with
`counterexampleConfirmed` not `false`; AC8: on the name-coloured encoding no replay applies and
`counterexampleConfirmed` is absent) and NU-053 (the name-coloured fixpoint query)."#
  runtimes r#"Java."#
  defect r#"the check that the initial marking violates the property is gated on a flat
answer (`colouredPlan == null`), but the replay that follows has no such gate. On a
name-coloured `Violated` the flat decoder finds no `Reachable` fact of the flat arity (the
coloured `Reachable` has another shape), the empty decode makes `assessCounterexample` return
`Unconfirmed`, and the result is `Violated` with `counterexampleConfirmed` `false`, also when
the initial marking violates the property. Rust and TypeScript leave the field absent on this
path. The IC3/PDR `Violated` case of `SmtVerifier.pipeline` and `SmtVerifier.assessCounterexample`
(`java/src/main/java/org/libpetri/smt/SmtVerifier.java`); `CounterexampleDecoder.decodeStateSet`
(`java/src/main/java/org/libpetri/smt/z3/CounterexampleDecoder.java`); Rust
`rust/libpetri-verification/src/smt_verifier.rs` (`replay_phase` returns `None` when
coloured). Confirmed by a run: `JoinRelayTest.fig12c(true)` with `R = 2`, budget `R`, the
`FIG12C_CARRIERS` and `PlaceBound(R, 1)` (violated at the initial marking) returns `Violated`
on route `SMT` with the name-coloured encoding, an empty trace and `counterexampleConfirmed`
`false`. A coloured `Reachable` with the flat arity, which would need one colour slot per
coloured place, does not occur on a net the encoding accepts: every ν-join consumes from two
coloured places at once, so the encoding has at least two slots."#
  evidence r#"line 6 of VER-003 (VER_003.lean) asks for `counterexampleConfirmed` not
`false` at an initial violation; a decider that answers `some false` there, the reference
otherwise, fails the block (checked in the wave W10 mutant run, not kept as a theorem). ν-nets
are outside ⟪Reference.TimedNet⟫, so VER_003.lean has no theorem about the coloured path."#
  fix r#"on the name-coloured encoding the `Violated` answer takes the no-replay branch, reports
`Counterexample replay: not applicable (name-coloured encoding, NU-053)` and leaves
`counterexampleConfirmed` absent, as Rust and TypeScript do. Java
`InitialViolationTraceTest.VER003_AC8_aNameColouredInitialViolationLeavesCounterexampleConfirmedAbsent`
and `VER003_AC8_aNameColouredViolationLeavesCounterexampleConfirmedAbsent`."#
  status "fixed, unreleased"
