//! Prefix-derivation helpers for subnet-instance-aware export per
//! `spec/11-modular-composition.md` **MOD-040** (export grouping).
//!
//! The `/` character is the prefix separator established by **MOD-010**:
//! a node named `outer/inner/leaf` belongs to the cluster tree
//! `outer -> outer/inner`, with `leaf` as the un-prefixed final segment.
//!
//! This module is observability-only — it never inspects
//! [`crate::SubnetDef`](libpetri_core::subnet_def::SubnetDef) or
//! [`crate::Instance`](libpetri_core::instance::Instance) objects, only the
//! resulting prefixed names that survived composition. Mirrors
//! `org.libpetri.export.SubnetPrefixes` (Java) and
//! `typescript/src/export/subnet-prefixes.ts` (TypeScript).

/// Returns the instance prefix carried by the given node name, or [`None`]
/// when the name has no `/` (i.e. is not part of any composed subnet
/// instance).
///
/// The prefix is the substring up to (but not including) the **last** `/`
/// — so `producer1/internal` returns `Some("producer1")` and
/// `outer/inner/leaf` returns `Some("outer/inner")`.
pub fn instance_prefix_of(node_name: &str) -> Option<&str> {
    let idx = node_name.rfind('/')?;
    if idx == 0 {
        return None;
    }
    Some(&node_name[..idx])
}

/// Returns the parent prefix of a given prefix, or [`None`] if the prefix
/// is top-level (single segment, no `/`).
pub fn parent_of(prefix: &str) -> Option<&str> {
    if prefix.is_empty() {
        return None;
    }
    let idx = prefix.rfind('/')?;
    if idx == 0 {
        return None;
    }
    Some(&prefix[..idx])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instance_prefix_strips_last_segment() {
        assert_eq!(instance_prefix_of("producer1/internal"), Some("producer1"));
        assert_eq!(instance_prefix_of("outer/inner/leaf"), Some("outer/inner"));
        assert_eq!(instance_prefix_of("flat"), None);
        assert_eq!(instance_prefix_of(""), None);
        assert_eq!(instance_prefix_of("/"), None);
    }

    #[test]
    fn parent_of_walks_one_level_up() {
        assert_eq!(parent_of("a"), None);
        assert_eq!(parent_of("a/b"), Some("a"));
        assert_eq!(parent_of("a/b/c"), Some("a/b"));
        assert_eq!(parent_of(""), None);
    }
}
