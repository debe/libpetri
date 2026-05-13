//! Lightweight, debug-UI-facing descriptor of one composed subnet instance,
//! per `spec/11-modular-composition.md` requirement **MOD-041**.
//!
//! Created by [`crate::instance::Instance::descriptor`] after a subnet has
//! been instantiated and (eventually) composed into an enclosing net. The
//! descriptor is consumed by the debug protocol's `Subscribed` response so
//! clients can render collapsed subnet clusters, per-instance highlighting,
//! and "show only this instance" filters in the debug UI.
//!
//! This struct carries only structural metadata — it is observability-only
//! and does not affect runtime behaviour of the composed flat net.

use std::sync::Arc;

/// Debug-UI descriptor for one composed subnet instance per **MOD-041**.
///
/// All names are full prefixed names (e.g. `b1/produce`, `outer/inner/x`).
/// `parent_prefix` is set when this descriptor describes a nested instance
/// per [MOD-013].
#[derive(Debug, Clone)]
pub struct SubnetInstance {
    /// The instantiation prefix (e.g. `"b1"` or `"outer/inner"` for nested
    /// instances).
    pub prefix: Arc<str>,
    /// The originating subnet definition's name.
    pub def_name: Arc<str>,
    /// Full prefixed transition names belonging to this instance.
    pub transitions: Vec<Arc<str>>,
    /// Full prefixed place names exposed as ports.
    pub exposed_places: Vec<Arc<str>>,
    /// Parent instance prefix when this is a nested instance, otherwise
    /// `None`.
    pub parent_prefix: Option<Arc<str>>,
}
