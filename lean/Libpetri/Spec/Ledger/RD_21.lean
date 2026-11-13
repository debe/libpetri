import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_030
import Libpetri.Spec.Text.EVT_013
import Libpetri.Spec.Text.EVT_030

runtime_defect RD_21
  title "Java's `transitionEvents` throws on an event with no transition name"
  requirements r#"EVT-030 (every helper is total; ruling D29 (a)), EVT-013 (AC4: a diagnostic
that no transition is responsible for carries an empty or absent name, so a consumer reads it
without failing)."#
  runtimes r#"Java."#
  defect r#"`transitionEvents` calls `equals` on the transition name of every log message and
throws on an engine diagnostic whose name is `null`, which both Java executors emit on an
interrupted run. `java/src/main/java/org/libpetri/event/EventStore.java`."#
  evidence r#"⟪EVT_030_mutant_throwsOnNameless⟫ (EVT_030.lean)."#
  fix r#"`transitionEvents` compares names with `Objects.equals`, so an event with no transition
name is skipped and the helper does not throw. Java
`EventStoreTest.transitionEventsSkipsAnEventWithNoTransitionName_EVT030_AC2` and
`AbstractTerminationReasonTest.interruptedRunEmitsAnEngineWarning_EVT013`, on both executors."#
  status "fixed, unreleased"
