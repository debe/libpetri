//! A name-aware state class ([NU-050], Route B): the base count + DBM state class
//! plus the abstract [`NameMarking`] partition layer.
//!
//! The base [`StateClass`] is reused verbatim, so the timing/zone dimension is
//! untouched — name×time composition is automatic (the DBM step runs exactly as
//! in the plain SCG; the name layer rides alongside).
//!
//! Both layers are interned by `NameStateClassGraph::build` ([VER-012]): a class
//! shares its base with every class at the same marking, zone and earliest-ready
//! times, and its name layer with every class whose partition has the same
//! canonical key — a renaming of it, which every consumer of the layer is
//! invariant under (`Interning.lean`, `interned_keys_eq`).

use std::rc::Rc;

use crate::name_marking::NameMarking;
use crate::state_class::StateClass;

#[derive(Debug, Clone)]
pub(crate) struct NameStateClass {
    /// Shared with every class at the same (marking, zone, earliest-ready times).
    pub base: Rc<StateClass>,
    /// Shared with every class whose name partition has the same canonical key.
    pub names: Rc<NameMarking>,
}

impl NameStateClass {
    pub(crate) fn new(base: Rc<StateClass>, names: Rc<NameMarking>) -> Self {
        Self { base, names }
    }
}
