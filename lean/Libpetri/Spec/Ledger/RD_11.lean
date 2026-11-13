import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_020
import Libpetri.Spec.Text.MOD_020

runtime_defect RD_11
  title "A caller transition bound to two channels is not rejected"
  requirements r#"MOD-020 (ruling D72 (ii)(b): a caller transition bound to two channels of
one instance in one call is an error, AC6). The port half of the first entry is withdrawn:
every runtime rejects a port re-bound in one call with `Port '<name>' is already bound`
(ruling D72 (i)(a); `ComposeBindingsBuilder::bind_port` in `rust/libpetri-core/src/compose.rs`,
`ComposeBindings.bindPort` in `java/src/main/java/org/libpetri/core/ComposeBindings.java` and
`typescript/src/core/compose-bindings.ts`)."#
  runtimes r#"all."#
  defect r#"no runtime rejects one caller transition bound to two channels of one instance.
Rust stages the merges in a map keyed by the caller's name, so only the merge its hash order
visits last survives; Java and TypeScript add both merges under one name
(`apply_composition` in `rust/libpetri-core/src/petri_net.rs`, `applyComposition` in
`java/src/main/java/org/libpetri/core/PetriNet.java` and `typescript/src/core/petri-net.ts`)."#
  evidence r#"none; MOD-020 makes distinct caller-side names a caller obligation
(⟪mod020_fresh⟫, MOD_020.lean) and states nothing about such a call."#
  fix r#"each runtime's channel binding rejects a caller transition, compared by identity, that is
already bound to another channel of the call, with `Transition '<t>' is already bound to channel
'<c1>'; it cannot also be bound to channel '<c2>' (MOD-020)`; Python raises it as `ValueError`.
Rust `compose.rs` `bind_channel_rejects_one_caller_transition_on_two_channels_mod020` and
`compose_one_caller_transition_on_two_channels_names_both_mod020`; Java
`ChannelCompositionTest.compose_oneCallerTransitionOnTwoChannels_isRejected_MOD020_AC6`;
TypeScript `channel-composition.test.ts`, "compose_oneCallerTransitionOnTwoChannels_isRejected
(MOD-020 AC6)"; Python
`test_channel_composition.py::test_one_caller_transition_bound_to_two_channels_is_rejected`."#
  status "fixed, unreleased"
