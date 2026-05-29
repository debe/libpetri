use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::context::OutputEntry;
use libpetri_core::output::Out;
use libpetri_core::token::{ErasedToken, Token};

/// Returns true when the actually-produced set of places satisfies the
/// transition's [`Out`] spec (AND requires all children, XOR requires
/// at least one, Timeout passes through to its child, ForwardInput
/// requires the forward target).
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

/// Build the list of outputs to produce when an [`Out::Timeout`]
/// branch fires (the async action exceeded its `after_ms` budget).
/// Each leaf [`Out::Place`] under the timeout `child` becomes one
/// unit-valued token at that place name; [`Out::And`] flattens
/// recursively.
///
/// **Unsupported under a `Timeout`:**
/// - [`Out::Xor`] — ambiguous which branch to fire on timeout.
/// - Nested [`Out::Timeout`] — meaningless; one budget per action.
/// - [`Out::ForwardInput`] — would need access to the consumed
///   inputs, which were moved into the action's
///   [`TransitionContext`](libpetri_core::context::TransitionContext)
///   and have been dropped along with the cancelled action future.
///   The Java implementation supports it; matching that here means
///   capturing input snapshots before spawn (TODO).
pub(crate) fn timeout_outputs(child: &Out) -> Vec<OutputEntry> {
    let mut out = Vec::new();
    collect_timeout_outputs(child, &mut out);
    out
}

fn collect_timeout_outputs(out: &Out, result: &mut Vec<OutputEntry>) {
    match out {
        Out::Place(p) => {
            let token = ErasedToken::from_typed(&Token::new(()));
            result.push(OutputEntry {
                place_name: Arc::clone(p.name_arc()),
                token,
            });
        }
        Out::And(children) => {
            for c in children {
                collect_timeout_outputs(c, result);
            }
        }
        Out::Xor(_) => {
            // Spec parity with Java: panicking here is a programmer
            // error — the net builder accepted an Xor under a Timeout
            // which is not a meaningful semantic.
            panic!("Out::Xor is not allowed inside Out::Timeout child");
        }
        Out::Timeout { .. } => {
            panic!("Nested Out::Timeout is not allowed");
        }
        Out::ForwardInput { .. } => {
            // See module-level note in `timeout_outputs`. Drop silently
            // for now; a follow-up will snapshot inputs pre-spawn.
        }
    }
}
