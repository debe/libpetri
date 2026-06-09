//! A name-aware state class ([NU-050], Route B): the base count + DBM state class
//! plus the abstract [`NameMarking`] partition layer.
//!
//! The base [`StateClass`] is reused verbatim, so the timing/zone dimension is
//! untouched — name×time composition is automatic (the DBM step runs exactly as
//! in the plain SCG; the name layer rides alongside).

use crate::name_marking::NameMarking;
use crate::state_class::StateClass;

#[derive(Debug, Clone)]
pub(crate) struct NameStateClass {
    pub base: StateClass,
    pub names: NameMarking,
}

impl NameStateClass {
    pub(crate) fn new(base: StateClass, names: NameMarking) -> Self {
        Self { base, names }
    }

    /// Canonical dedup key: the base key (uncoloured counts + DBM zone) joined
    /// with the symmetry-canonical name-partition key.
    pub(crate) fn canonical_key(&self, coloured_order: &[String]) -> String {
        format!(
            "{}||{}",
            self.base.canonical_key(),
            self.names.canonical_key(coloured_order)
        )
    }
}
