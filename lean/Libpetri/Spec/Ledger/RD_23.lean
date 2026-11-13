import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_031
import Libpetri.Spec.Text.MOD_031

runtime_defect RD_23
  title "A channel merge drops the caller's declared places from the correspondence"
  requirements r#"MOD-031 (key-set completeness of the declared-to-actual correspondence
through every rewrite pass; ruling D69 (a) leaves the merged case out of the block)."#
  runtimes r#"Rust, Java, TypeScript, and Python through Rust."#
  defect r#"when a caller transition that carries no correspondence is merged with an instance
transition that carries one, the merged transition keeps the instance side's correspondence
whole, and a transition that carries a correspondence is never re-read from its arcs. The
caller's declared places are then no keys, so a later pass that renames one of them (fusion at
build, or instantiating the retrofitted net under MOD-014) leaves it unresolved, and the
caller's action fails its declared-place check after its inputs were consumed (EXEC-031).
`merge_local_name_maps` and `build_local_name_map` (`rust/libpetri-core/src/rewriter.rs`),
`mergePlaceAlias` (`java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java` and
`typescript/src/core/internal/subnet-rewriter.ts`). The opposite case, a caller that
carries a correspondence merged with an instance transition that carries none, drops the
instance side's declared places in the same functions."#
  evidence r#"⟪MOD_031_mergeThenPass_undecided⟫ (MOD_031.lean): after the runtimes' merge
and one pass the declared place `h` resolves to `h`, which no arc names; after the reference's
merge it resolves to `f`."#
  fix r#"a channel merge gives a side that carries no correspondence an identity entry for every
place its arcs and output specification name, merges the two sides with identity yielding to
non-identity, and drops the result when it is all identity, as the Lean reference `corrMergeVia
corrSideFull` does. Rust `mod031_place_resolution.rs`
`channel_merge_then_fusion_keeps_caller_declared_place_mod031` and `mod031_identity_roundtrip.rs`
`channel_merge_then_fusion_caller_action_fires_mod031`; Java
`ChannelCompositionTest.channelMerge_callerWithoutAlias_keepsItsDeclaredPlacesAsKeys_MOD031`,
`channelMerge_instanceWithoutAlias_keepsItsDeclaredPlacesAsKeys_MOD031` and
`NestedPlaceAliasTest.channelMergeThenFusion_callerResolvesItsDeclaredPlace_MOD031`; TypeScript
`compose-action-place-alias.test.ts`, "channel merge then fusion: caller action resolves its
declared place (MOD-031 key-set completeness)", and `channel-composition.test.ts`,
"channelMerge_callerWithoutAlias_keepsItsDeclaredPlacesAsKeys (MOD-031 key-set completeness)";
Python `test_channel_composition.py::test_caller_declared_place_survives_a_later_renaming_pass`."#
  status "fixed, unreleased"
