import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.ENV_002
import Libpetri.Spec.Text.ENV_002
import Libpetri.Spec.Text.ENV_010

runtime_defect RD_35
  title "Java's executor builders keep the caller's environment-place set"
  requirements r#"ENV-002 (first block, `ENV_002`: the sentence 'The set of registered
environment places is fixed when the executor is built; no step of a run adds or removes one.',
line 1 and line 3), ENV-010 (whether the run waits at quiescence)."#
  runtimes r#"Java (both executors)."#
  defect r#"`Builder.environmentPlaces(Set<EnvironmentPlace<?>>)` stores the caller's set
(`java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java`,
`PrecompiledNetExecutor.java`), `build()` passes it on and the constructor keeps it
without a copy (`this.environmentPlaces = environmentPlaces;` in both constructors). `inject`
tests that live set on every call (`environmentPlaces.contains(place)` in both), so a host that changes its own set after `build()` adds or
removes a registration in the middle of the run. `hasEnvironmentPlaces` is read once in the
constructor, so the quiescence decision of ENV-010 keeps the registration of
the build while `inject` and the dead-arc report follow the changed set. The varargs overload
copies (`Set.of(places)`) and is not affected. TypeScript copies the names into a set of its
own; Rust and Python take the registrations by value.
Reproduced against `java/target/classes`: an executor built with the caller's set `{A}`
answers an injection into `B` with an error; after the caller removes `A` and adds `B`, an
injection into `A` fails and one into `B` is accepted."#
  evidence r#"⟪ENV_002_forbids_shrinks⟫ (ENV_002.lean): an executor whose registrations
are removed during the run breaks line 3. A registration added during the run breaks line 1.
The fix is `Set.copyOf(places)` in the builder or the constructor."#
  fix r#"both executor constructors keep `Set.copyOf(environmentPlaces)` and compute
`hasEnvironmentPlaces` from that copy, so `inject`, the dead-arc report and the quiescence
decision read one fixed set. Java
`AbstractNetExecutorEnvironmentTest.LifecycleTests.environmentPlacesAreFixedAtBuild_ENV002`, on
both executors."#
  status "fixed, unreleased"
