use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::output::Out;

/// Returns true when the actually-produced set of places satisfies the
/// transition's [`Out`] spec (AND requires all children, XOR requires at least
/// one, Timeout passes through to its child, ForwardInput requires the
/// forward target).
#[allow(dead_code)]
pub(crate) fn validate_out_spec(out: &Out, produced_places: &HashSet<Arc<str>>) -> bool {
    match out {
        Out::Place(p) => produced_places.contains(p.name()),
        Out::And(children) => children
            .iter()
            .all(|c| validate_out_spec(c, produced_places)),
        Out::Xor(children) => children
            .iter()
            .any(|c| validate_out_spec(c, produced_places)),
        Out::Timeout { child, .. } => validate_out_spec(child, produced_places),
        Out::ForwardInput { to, .. } => produced_places.contains(to.name()),
    }
}
