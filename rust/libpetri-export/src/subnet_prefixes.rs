//! Prefix-derivation helpers for subnet-instance-aware export per
//! `spec/11-modular-composition.md` **MOD-040** (export grouping).
//!
//! The helpers live in `libpetri_core::subnet_prefixes`, so
//! [`PetriNet::subnet_of`](libpetri_core::petri_net::PetriNet::subnet_of) —
//! the AUTO cluster rule's public accessor — and this exporter apply one
//! rule; they are re-exported here unchanged. Mirrors
//! `org.libpetri.export.SubnetPrefixes` (Java) and
//! `typescript/src/export/subnet-prefixes.ts` (TypeScript).

pub use libpetri_core::subnet_prefixes::{instance_prefix_of, parent_of};
