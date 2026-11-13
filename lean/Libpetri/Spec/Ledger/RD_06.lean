import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_051

runtime_defect RD_06
  title "Java and TypeScript accept `action(null)`"
  requirements r#"CORE-051."#
  runtimes r#"Java, TypeScript."#
  defect r#"the builder setter stores `null` (or `undefined`) as the action. The identity check
of CORE-043 passes such a transition, and every firing of it then fails. Python raises
`TypeError`; Rust cannot express it. `Transition.Builder.action`
(`java/src/main/java/org/libpetri/core/Transition.java`), `TransitionBuilder.action`
(`typescript/src/core/transition.ts`)."#
  evidence r#"none; the CORE_051 assumes record it."#
  fix r#"the builder setter rejects a missing action: Java throws `NullPointerException` on
`action(null)` and TypeScript a `TypeError` on `null` or `undefined`; leaving the call out still
gives the passthrough default. Java `TransitionTest.core051_builder_rejectsNullAction`; TypeScript
`transition.test.ts`, "rejects a null or undefined action (CORE-051)"."#
  status "fixed, unreleased"
