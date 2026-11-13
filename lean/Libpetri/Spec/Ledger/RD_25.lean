import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.MOD_026
import Libpetri.Spec.Req.MOD_061
import Libpetri.Spec.Text.MOD_026
import Libpetri.Spec.Text.MOD_061

runtime_defect RD_25
  title "A fusion set that lists its first member again drops that member"
  requirements r#"MOD-061 (step 3: the canonical member remains; lines 1 and 3) and MOD-026
(AC5: the surviving canonical place keeps its own entry; lines 1 and 2)."#
  runtimes r#"Rust, Java, TypeScript."#
  defect r#"the non-canonical members are every member after the first position, so a set
with members `[a, b, a]` counts `a` among them. Fusion then drops the declared place `a` (it
comes back only through an arc of a rewritten transition), runs the input merge on a transition
whose only input arcs are on `a`, and drops `a`'s cluster entry.
`build_with_fusion` (`rust/libpetri-core/src/petri_net.rs`), `buildWithFusion` and
`filterFusedMembership` (`java/src/main/java/org/libpetri/core/PetriNet.java` and
`typescript/src/core/petri-net.ts`). The input merge has no visible effect,
since CORE-030 already rejects two input arcs on one place; what shows is the dropped standalone
`a` and its dropped membership entry. Python was listed at first, but the binding declares no
fusion sets (MOD-060), so it has no such call."#
  evidence r#"⟪mod061_dupCanonical_kept⟫ (MOD_061.lean) and ⟪mod026_dupCanonical_kept⟫
(MOD_026.lean): the reference keeps `a` and its entry."#
  fix r#"the fusion build skips a non-canonical member equal to the canonical member, so `[a, b,
a]` keeps the declared place `a` and its entry; `nonCanonical()` itself is unchanged. Rust
`fusion.rs` `fuse_repeated_canonical_member_keeps_it_mod061` and `petri_net.rs`
`direct_compose_then_fuse_repeated_canonical_keeps_its_entry_mod026`; Java
`FusionTest.fuse_repeatedCanonicalMember_keepsIt_MOD061` and
`ComposeDirectMembershipTest.directCompose_thenFuseWithRepeatedCanonical_keepsCanonicalEntry_MOD026`;
TypeScript `fusion.test.ts`, "fuse_repeatedCanonicalMember_keepsIt (MOD-061 step 3)", and
`compose-direct-membership.test.ts`,
"directCompose_thenFuseWithRepeatedCanonical_keepsCanonicalEntry (MOD-026 AC5)"."#
  status "fixed, unreleased"
