import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EXEC_041
import Libpetri.Spec.Text.NU_020
import Libpetri.Spec.Text.NU_054

runtime_defect RD_53
  title "A match key that throws ends the run in Java and TypeScript"
  requirements r#"NU-020 (a token whose key yields no name has no name on that input), NU-054 (a
projection that fails yields no name), EXEC-041 (`stopped` only after an immediate termination,
another caller-requested stop, a host-runtime fault or a run-ending failure of the run's event
store)."#
  runtimes r#"Java, TypeScript."#
  defect r#"a match-key projection that threw while the loop decided enablement or consumed the
matched tokens escaped the executor. Java caught only `ClassCastException`
(`MatchSpec.MatchKey.extract`, and the consume predicate of `fireTransition` in
`BitmapNetExecutor.java` and `PrecompiledNetExecutor.java`), so any other `RuntimeException` ended
the run with `STOPPED` and `run()` raised it, or the executor's constructor raised it when it
seeded the match cache. TypeScript caught nothing (`buildNameIndex`, `cacheAddToken` and
`fireTransition`), so `run()` rejected with the projection's error. Python already read a raise as
no name (`make_py_projection` in `rust/libpetri-py/src/model.rs`); a Rust projection cannot fail by
type."#
  evidence r#"none."#
  fix r#"a projection that throws yields no name: Java's `MatchKey.extract` and the consume
predicates catch any `RuntimeException`, and every TypeScript key call goes through `projectName`
in `typescript/src/runtime/match-engine.ts`. The token correlates with nothing and the run goes
on. Tests citing NU-054 and EXEC-041 (`nuJoin_throwingKeyIsNoName_*` in
`AbstractNetExecutorEngineTest.java`, 'a throwing key is no name' in
`typescript/tests/runtime/nu-net.test.ts`) check both executors, on the match cache and on the
rebuild path: the join fires on the name it can match and the run ends quiescent."#
  status "fixed, unreleased"
