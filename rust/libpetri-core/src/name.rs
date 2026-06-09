//! ν-net token identities ([`NameId`]).
//!
//! A [`NameId`] is an **opaque correlation identity** carried by a token so
//! that a fork can mint a fresh name and a later join can re-merge exactly
//! the siblings that share it (see [`crate::match_spec::MatchSpec`]). The
//! only operation defined on names is **equality** — they support no order
//! arithmetic beyond a total order used purely for deterministic tie-breaking
//! (spec NU-001).
//!
//! Identity is a *projection* of the token payload, not a separate field on
//! [`Token`](crate::token::Token): a [`MatchSpec`](crate::match_spec::MatchSpec)
//! declares the `value -> NameId` key, and the fork mints a fresh name into the
//! payload via [`TransitionContext::fresh_name`](crate::context::TransitionContext::fresh_name).
//! This keeps `Token` (and the event/archive formats) unchanged while still
//! giving the analyzer a name-symmetric uninterpreted sort to reason about.

use std::sync::Arc;

/// An opaque correlation identity for ν-net fork/join (spec NU-001).
///
/// Equality-only semantics; the [`Ord`] impl exists solely for the
/// deterministic match tie-break (NU-020) and carries no domain meaning.
///
/// **Cross-language ordering note.** The derived [`Ord`] compares the inner
/// `str` by UTF-8 bytes (= Unicode code-point order). The match tie-break is
/// byte-identical across the Rust/Java/TS ports for ASCII/BMP names — which
/// includes every executor-minted name (`"{transition}#{n}"`, ASCII). For
/// supplementary-plane (astral) code points in *user-supplied* correlation
/// keys the order can differ from Java/TS (which compare UTF-16 code units);
/// NU-001 requires only per-implementation consistency, which holds.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NameId(Arc<str>);

impl NameId {
    /// Creates a name from any string-like value.
    pub fn new(value: impl Into<Arc<str>>) -> Self {
        Self(value.into())
    }

    /// Returns the underlying string.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns the inner `Arc<str>` (cheap clone).
    pub fn as_arc(&self) -> &Arc<str> {
        &self.0
    }
}

impl std::fmt::Display for NameId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::fmt::Debug for NameId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NameId({:?})", &self.0)
    }
}

impl From<&str> for NameId {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<String> for NameId {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality_by_value() {
        assert_eq!(NameId::new("a"), NameId::from("a"));
        assert_ne!(NameId::new("a"), NameId::new("b"));
    }

    #[test]
    fn total_order_is_lexicographic() {
        assert!(NameId::new("a") < NameId::new("b"));
    }

    #[test]
    fn display_and_as_str() {
        let n = NameId::new("corr-42");
        assert_eq!(n.as_str(), "corr-42");
        assert_eq!(format!("{n}"), "corr-42");
    }
}
