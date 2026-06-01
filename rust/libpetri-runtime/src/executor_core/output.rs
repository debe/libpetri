use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::output::Out;
// Only the async (`tokio`) timeout path consumes these; gate the imports so
// feature-free builds don't flag them as unused.
#[cfg(feature = "tokio")]
use std::collections::HashMap;
#[cfg(feature = "tokio")]
use libpetri_core::context::OutputEntry;
#[cfg(feature = "tokio")]
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
/// recursively; [`Out::ForwardInput`] re-emits the consumed input
/// token(s) at the forward target, satisfying \[EXEC-022\] criterion 3.
///
/// `forwarded` maps each `from` place name to the token(s) consumed
/// from it, snapshotted *before* the action was spawned — the action's
/// [`TransitionContext`](libpetri_core::context::TransitionContext),
/// which owns the consumed tokens, is dropped when the action future is
/// cancelled on timeout, so the values must be captured up front.
///
/// **Unsupported under a `Timeout`** (programmer errors — the builder
/// should reject them, so we panic):
/// - [`Out::Xor`] — ambiguous which branch to fire on timeout.
/// - Nested [`Out::Timeout`] — meaningless; one budget per action.
///
/// Only reachable from the async (`tokio`) path; gated so feature-free
/// builds don't flag it as dead code.
#[cfg(feature = "tokio")]
pub(crate) fn timeout_outputs(
    child: &Out,
    forwarded: &HashMap<Arc<str>, Vec<ErasedToken>>,
) -> Vec<OutputEntry> {
    let mut out = Vec::new();
    collect_timeout_outputs(child, forwarded, &mut out);
    out
}

#[cfg(feature = "tokio")]
fn collect_timeout_outputs(
    out: &Out,
    forwarded: &HashMap<Arc<str>, Vec<ErasedToken>>,
    result: &mut Vec<OutputEntry>,
) {
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
                collect_timeout_outputs(c, forwarded, result);
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
        Out::ForwardInput { from, to } => {
            // [EXEC-022] criterion 3: forward the consumed input
            // token(s) from `from` to `to`. The values were snapshotted
            // before the action spawned (see `timeout_outputs`).
            if let Some(tokens) = forwarded.get(from.name()) {
                for token in tokens {
                    result.push(OutputEntry {
                        place_name: Arc::clone(to.name_arc()),
                        token: token.clone(),
                    });
                }
            }
        }
    }
}
