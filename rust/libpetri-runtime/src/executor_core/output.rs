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

/// \[IO-015\] Checks that the actually-produced set of places satisfies
/// the transition's declared [`Out`] spec.
///
/// Semantics are the same three-language contract implemented by Java
/// (`ExecutorSupport.validateOutSpec`) and TypeScript (`validateOutSpec`):
///
/// - [`Out::Place`] / [`Out::ForwardInput`] — the named place must have
///   received at least one token.
/// - [`Out::And`] — **every** child must be satisfied.
/// - [`Out::Xor`] — **exactly one** child must be satisfied. Zero
///   satisfied branches, or two or more, is a violation — except when a
///   single satisfied branch subsumes all the other satisfied ones (e.g.
///   `xor(and(a, b, c), and(a, b))`), in which case the most specific
///   match is selected.
/// - [`Out::Timeout`] — passes through to its child.
///
/// Returns a plain `bool` so the firing hot path stays branch-and-return;
/// [`describe_out_violation`] renders the reason on the (cold) failure
/// path.
///
/// Allocation-free on the satisfied path: the walk is a pure predicate
/// over `produced_places`; only XOR ambiguity resolution (a rare,
/// usually-failing path) builds intermediate sets.
pub(crate) fn validate_out_spec(out: &Out, produced_places: &HashSet<Arc<str>>) -> bool {
    satisfied(out, produced_places).unwrap_or(false)
}

/// Explains why `produced_places` failed [`validate_out_spec`]. Cold
/// path — only called to populate a `TransitionFailed` event, so it may
/// re-walk the spec and allocate freely.
#[cold]
#[inline(never)]
pub(crate) fn describe_out_violation(out: &Out, produced_places: &HashSet<Arc<str>>) -> String {
    match satisfied(out, produced_places) {
        Err(message) => message,
        _ => format!(
            "output does not satisfy declared spec (expected {}, produced {:?})",
            describe(out),
            sorted_names(produced_places)
        ),
    }
}

/// `Ok(true)` = satisfied, `Ok(false)` = not satisfied, `Err` = a
/// structural XOR violation (which carries its own message rather than
/// collapsing into "unsatisfied", matching Java/TypeScript).
fn satisfied(out: &Out, produced: &HashSet<Arc<str>>) -> Result<bool, String> {
    match out {
        Out::Place(p) => Ok(produced.contains(p.name())),
        Out::ForwardInput { to, .. } => Ok(produced.contains(to.name())),
        Out::And(children) => {
            for child in children {
                if !satisfied(child, produced)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Out::Xor(children) => {
            let mut count = 0usize;
            for child in children {
                if satisfied(child, produced)? {
                    count += 1;
                }
            }
            match count {
                0 => Err(format!(
                    "XOR violation - no branch produced (exactly 1 required) in {}",
                    describe(out)
                )),
                1 => Ok(true),
                _ => resolve_xor_ambiguity(children, produced),
            }
        }
        Out::Timeout { child, .. } => satisfied(child, produced),
    }
}

/// Two or more XOR branches matched. When exactly one of them subsumes
/// all the others it is the intended (most specific) branch; otherwise
/// the output is genuinely ambiguous and the firing is a violation.
fn resolve_xor_ambiguity(children: &[Out], produced: &HashSet<Arc<str>>) -> Result<bool, String> {
    let claimed: Vec<HashSet<Arc<str>>> = children
        .iter()
        .filter(|c| satisfied(c, produced).unwrap_or(false))
        .map(|c| {
            let mut set = HashSet::new();
            collect_claimed(c, produced, &mut set);
            set
        })
        .collect();

    let subsuming = claimed
        .iter()
        .filter(|candidate| {
            claimed
                .iter()
                .all(|other| std::ptr::eq(*candidate, other) || other.is_subset(candidate))
        })
        .count();

    if subsuming == 1 {
        Ok(true)
    } else {
        Err("XOR violation - multiple branches produced".to_string())
    }
}

/// Collects the place names a satisfied subtree claims.
fn collect_claimed(out: &Out, produced: &HashSet<Arc<str>>, result: &mut HashSet<Arc<str>>) {
    match out {
        Out::Place(p) => {
            if let Some(name) = produced.get(p.name()) {
                result.insert(Arc::clone(name));
            }
        }
        Out::ForwardInput { to, .. } => {
            if let Some(name) = produced.get(to.name()) {
                result.insert(Arc::clone(name));
            }
        }
        Out::And(children) => {
            for child in children {
                collect_claimed(child, produced, result);
            }
        }
        Out::Xor(children) => {
            for child in children {
                if satisfied(child, produced).unwrap_or(false) {
                    collect_claimed(child, produced, result);
                }
            }
        }
        Out::Timeout { child, .. } => collect_claimed(child, produced, result),
    }
}

/// Human-readable rendering of an [`Out`] spec. Error path only.
fn describe(out: &Out) -> String {
    match out {
        Out::Place(p) => format!("'{}'", p.name()),
        Out::ForwardInput { from, to } => format!("forward('{}' -> '{}')", from.name(), to.name()),
        Out::And(children) => format!("and({})", describe_all(children)),
        Out::Xor(children) => format!("xor({})", describe_all(children)),
        Out::Timeout { after_ms, child } => {
            format!("timeout({}ms, {})", after_ms, describe(child))
        }
    }
}

fn describe_all(children: &[Out]) -> String {
    children
        .iter()
        .map(describe)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Stable rendering of the produced set. Error path only.
fn sorted_names(produced: &HashSet<Arc<str>>) -> Vec<&str> {
    let mut names: Vec<&str> = produced.iter().map(|n| &**n).collect();
    names.sort_unstable();
    names
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
