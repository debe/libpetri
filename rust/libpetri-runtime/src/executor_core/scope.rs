//! \[NU-011\] The execution scope: its validation rule and its default.
//!
//! A minted ν-name is `<transition>#<scope>:<n>`. The scope is what keeps a
//! resumed execution (\[CORE-073\]) from re-minting names its restored
//! marking already holds; `<n>` is a plain per-executor counter from 0.
//!
//! # Parsing a minted name
//!
//! A scope holds neither `':'` nor `'#'`, so a minted name splits uniquely
//! even though a *transition* name may hold both: the **last** `':'` splits
//! off the counter, then the **last** `'#'` before it splits off the scope.
//!
//! ```
//! let (head, n) = "a#b:c#seg:7".rsplit_once(':').unwrap();
//! let (transition, scope) = head.rsplit_once('#').unwrap();
//! assert_eq!((transition, scope, n), ("a#b:c", "seg", "7"));
//! ```

use std::collections::hash_map::RandomState;
use std::fmt;
use std::hash::{BuildHasher, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

/// Why a host-supplied execution scope was refused.
///
/// The rule is the same in all four implementations: a scope of length 0 is
/// rejected — **empty, not blank**; whitespace is a legal scope — and so is
/// one containing either separator of a minted name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidExecutionScope {
    /// The scope has length 0.
    Empty,
    /// The scope contains `':'` or `'#'`, carried here.
    Separator(char),
}

impl fmt::Display for InvalidExecutionScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("execution scope must not be empty (NU-011)"),
            Self::Separator(':') => f.write_str(
                "execution scope must not contain ':' (it separates scope from counter \
                 in a minted name, NU-011)",
            ),
            Self::Separator(c) => write!(
                f,
                "execution scope must not contain '{c}' (it separates transition from \
                 scope in a minted name, NU-011)"
            ),
        }
    }
}

impl std::error::Error for InvalidExecutionScope {}

/// \[NU-011\] Checks a host-supplied execution scope without panicking.
///
/// Every setter that takes a scope stores it and lets the executor's
/// construction panic on a bad one. A host deriving the scope from data it
/// does not control calls this first and handles the `Err` instead.
pub fn validate_execution_scope(scope: &str) -> Result<(), InvalidExecutionScope> {
    if scope.is_empty() {
        return Err(InvalidExecutionScope::Empty);
    }
    match scope.chars().find(|c| matches!(c, ':' | '#')) {
        Some(c) => Err(InvalidExecutionScope::Separator(c)),
        None => Ok(()),
    }
}

/// \[NU-011\] Draws a default scope: 128 random bits as exactly 32 lowercase
/// hex characters.
///
/// Random, because the names it scopes outlive the process — a snapshot is
/// persisted by one process and restored by another, and any per-process
/// counter restarts at the value the snapshot already holds. Randomness is
/// confined to this default: a pinned scope is used verbatim and `<n>` stays
/// a counter, so a host that needs a reproducible segment pins the scope
/// (NU-011 AC#3).
///
/// `std` only. [`RandomState`] is keyed from the operating system's random
/// source once per thread, so the two SipHash outputs below are 128 bits
/// derived from a 128-bit OS-random key; the process id, a process-wide
/// counter and the wall clock are folded in so that two draws on one thread
/// — or two processes handed the same keys by a fork — still differ. The
/// clock reading is entropy here, never an identifier (\[TIME-015\] contract
/// point 1), and it is the real clock on purpose: an injected one is
/// reproducible, which is the opposite of what a default scope is for.
pub(crate) fn default_execution_scope() -> Arc<str> {
    static DRAWS: AtomicU64 = AtomicU64::new(0);
    let draw = DRAWS.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let half = |salt: u8| {
        let mut hasher = RandomState::new().build_hasher();
        hasher.write_u8(salt);
        hasher.write_u32(pid);
        hasher.write_u64(draw);
        hasher.write_u128(nanos);
        hasher.finish()
    };
    Arc::from(format!("{:016x}{:016x}", half(0), half(1)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_and_both_separators_and_nothing_else() {
        assert_eq!(validate_execution_scope(""), Err(InvalidExecutionScope::Empty));
        assert_eq!(validate_execution_scope("a:b"), Err(InvalidExecutionScope::Separator(':')));
        assert_eq!(validate_execution_scope("a#b"), Err(InvalidExecutionScope::Separator('#')));
        assert_eq!(validate_execution_scope("#:"), Err(InvalidExecutionScope::Separator('#')));
        for legal in [" ", "\t", "seg1", "läuf-7", "a/b.c", "\u{1F600}"] {
            assert_eq!(validate_execution_scope(legal), Ok(()), "{legal:?}");
        }
    }

    #[test]
    fn a_default_scope_is_32_lowercase_hex_and_passes_its_own_validation() {
        let mut seen = std::collections::HashSet::new();
        for _ in 0..1_000 {
            let scope = default_execution_scope();
            assert_eq!(scope.len(), 32, "{scope}");
            assert!(scope.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')), "{scope}");
            assert_eq!(validate_execution_scope(&scope), Ok(()));
            assert!(seen.insert(scope), "a default scope repeated within one process");
        }
    }
}
