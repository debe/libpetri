import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_042

runtime_defect RD_05
  title "A TypeScript resolver that returns `undefined` binds `undefined`"
  requirements r#"CORE-042 (a resolver that returns no action defers)."#
  runtimes r#"TypeScript."#
  defect r#"`bindActionsWithResolver` treats only `null` as no action, so a plain JavaScript
resolver such as `name => obj[name]` rebinds an unknown transition to `undefined`.
`PetriNet.bindActionsWithResolver` (`typescript/src/core/petri-net.ts`). `SubnetDef.bindActionsWithResolver`
(`typescript/src/core/subnet-def.ts`) makes the same test."#
  evidence r#"none; the CORE_042 assumes cite it (the block reads a resolver's `null`/`None`
as `none`, line 3, and the model has no `undefined`)."#
  fix r#"both resolver forms treat `undefined` as `null`, and their return type is widened to
`TransitionAction | null | undefined`. TypeScript `petri-net.test.ts`, "bindActionsWithResolver
defers a transition when the resolver returns undefined (CORE-042)";
`subnet-verify-options.test.ts`, "the resolver form defers a transition on undefined, as on null
(CORE-042)"."#
  status "fixed, unreleased"
