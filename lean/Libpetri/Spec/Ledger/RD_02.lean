import Libpetri.Spec.Ledger
import Libpetri.Reference.Build
import Libpetri.Spec.Req.CORE_041
import Libpetri.Spec.Text.CORE_041

runtime_defect RD_02
  title "The TypeScript builder hands its live sets to the built net"
  requirements r#"CORE-041 (ruling D66 (a))."#
  runtimes r#"TypeScript."#
  defect r#"`build()` passes the builder's own place and transition sets to the net, so a later
builder call changes a net that was already built. `PetriNetBuilder.build`
(`typescript/src/core/petri-net.ts`).
A channel `compose` after `build()` even deletes the caller transition from the built net. Only
the build without fusion shares the sets."#
  evidence r#"⟪CORE_041_forbids_alias⟫ (CORE_041.lean), ⟪aliasBuilder_unstable⟫
(Reference/Build.lean)."#
  fix r#"`build()` hands the net copies of the builder's place and transition sets. TypeScript
`petri-net.test.ts`, "a built net keeps its places and transitions when the builder is used again
(CORE-041)" and "a channel compose after build leaves the built net intact (CORE-041)"."#
  status "fixed, unreleased"
