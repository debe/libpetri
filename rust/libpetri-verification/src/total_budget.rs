//! The optional total wall-clock budget of one [`SmtVerifier::verify`] call
//! ([VER-013]), and the caller's cancellation, which shares its stop.
//!
//! [`SmtVerifier::timeout`] is a per-query budget: every phase is granted it
//! afresh, so one verification can take several times the timeout, plus the
//! solver-free work (enumeration, Route B, the timed counterexample check of
//! [VER-023]) that no timeout bounds. [`SmtVerifier::total_budget`] caps the
//! whole call. It is off by default, and then nothing here does anything.
//!
//! Cancellation ([`SmtVerifier::cancel_token`], a [`CancelToken`]) is not a second
//! mechanism: the deadline becomes "deadline passed **or** cancelled", so every
//! poll below sees it at the same points, with or without a budget. The z3
//! transport additionally reads the token in its watchdog loop
//! ([`cancel_token`]) and kills a running process the moment it is cancelled.
//!
//! The scope is installed for the duration of `verify()` as a **thread-local**
//! ([`enter`]), which is how it reaches the places that have to honour it without
//! widening any public signature:
//!
//! * [`crate::z3_process::Z3Solver::run`], the single choke point for every z3
//!   process, clamps each query's budget to what is left ([`clamp`]) and
//!   starts no process once nothing is;
//! * the state-class-graph builds poll [`cut`] once per class, next to their
//!   class-budget check, and stop when the deadline has passed. A build cut
//!   that way records itself as stopped, which is how the caller (and the
//!   [`crate::state_space_cache`]) tells it from a truncation;
//! * the siphon/trap search and the semiflow enumeration poll [`cut`] inside
//!   their loops and give up without a result.
//!
//! Every stop is sticky — a deadline that passed stays passed and a token that
//! was cancelled stays cancelled — so a loop that gave up early is always
//! followed by a step that finds the scope stopped: its partial result never
//! reaches a verdict.
//!
//! `verify()` is synchronous and runs on the caller's thread, so a
//! thread-local scope is exactly one verification; [`enter`] restores the
//! previous scope on drop, so nesting is harmless.
//!
//! [`SmtVerifier::verify`]: crate::smt_verifier::SmtVerifier::verify
//! [`SmtVerifier::timeout`]: crate::smt_verifier::SmtVerifier::timeout
//! [`SmtVerifier::total_budget`]: crate::smt_verifier::SmtVerifier::total_budget
//! [`SmtVerifier::cancel_token`]: crate::smt_verifier::SmtVerifier::cancel_token

#![cfg_attr(not(feature = "z3"), allow(dead_code))]

use std::cell::RefCell;
use std::time::{Duration, Instant};

use crate::cancel::CancelToken;

/// What stopped a verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stop {
    /// The total budget ran out.
    Budget,
    /// The caller cancelled.
    Cancelled,
}

/// One verification's stop: the deadline and the token, the step running now,
/// and the step the verification was stopped in.
struct Scope {
    /// `None` when only a cancel token stops the run.
    budget_ms: Option<u64>,
    /// `None` without a budget, or when the budget reaches past what an
    /// `Instant` holds.
    deadline: Option<Instant>,
    cancel: Option<CancelToken>,
    /// The step running now, named in the reason.
    phase: String,
    /// The first step that found the verification stopped, and why.
    stopped_in: Option<(Stop, String)>,
}

thread_local! {
    static SCOPE: RefCell<Option<Scope>> = const { RefCell::new(None) };
}

/// Restores the enclosing scope (normally none) when dropped.
pub(crate) struct Guard {
    previous: Option<Scope>,
}

impl Drop for Guard {
    fn drop(&mut self) {
        let previous = self.previous.take();
        SCOPE.with(|s| *s.borrow_mut() = previous);
    }
}

/// Starts a stop scope on this thread, now: a budget of `budget_ms`, a
/// cancellation token, or both. `None` — and no scope, so nothing is polled —
/// when neither is given. The step running until the first [`step`] is
/// `net preparation`.
pub(crate) fn enter(budget_ms: Option<u64>, cancel: Option<CancelToken>) -> Option<Guard> {
    if budget_ms.is_none() && cancel.is_none() {
        return None;
    }
    let scope = Scope {
        budget_ms,
        deadline: budget_ms.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms))),
        cancel,
        phase: String::from("net preparation"),
        stopped_in: None,
    };
    let previous = SCOPE.with(|s| s.borrow_mut().replace(scope));
    Some(Guard { previous })
}

fn cancelled(scope: &Scope) -> bool {
    scope.cancel.as_ref().is_some_and(CancelToken::is_cancelled)
}

/// Milliseconds left: `0` once cancelled or once the deadline passed,
/// `u64::MAX` without a deadline.
fn remaining(scope: &Scope) -> u64 {
    if cancelled(scope) {
        return 0;
    }
    match scope.deadline {
        Some(deadline) => {
            let left = deadline.saturating_duration_since(Instant::now()).as_millis();
            u64::try_from(left).unwrap_or(u64::MAX)
        }
        None => u64::MAX,
    }
}

/// With a scope that must stop — cancelled, or past its deadline: records the
/// running step as the one it stopped in (the first such step wins) and answers
/// `true`. Cancellation wins over an elapsed budget when both apply.
fn expired_now(scope: &mut Scope) -> bool {
    let stop = if cancelled(scope) {
        Stop::Cancelled
    } else if scope.budget_ms.is_some() && remaining(scope) == 0 {
        Stop::Budget
    } else {
        return false;
    };
    if scope.stopped_in.is_none() {
        scope.stopped_in = Some((stop, scope.phase.clone()));
    }
    true
}

/// Starts pipeline step `name`. Polls first, so a stop that came during the
/// previous step is charged to that step, and answers `true` — without
/// starting `name` — when there was one; the caller then stops with
/// [`stopped_reason`]. Always `false` without a scope.
pub(crate) fn step(name: &str) -> bool {
    SCOPE.with(|s| {
        let mut slot = s.borrow_mut();
        let Some(scope) = slot.as_mut() else {
            return false;
        };
        if expired_now(scope) {
            return true;
        }
        scope.phase.clear();
        scope.phase.push_str(name);
        false
    })
}

/// True — and the running step recorded — when the verification must stop:
/// cancelled, or past its deadline. What the graph builds poll once per class
/// and the pure loops every so many iterations: one thread-local read and, with
/// a scope, one atomic load and one clock read.
pub(crate) fn cut() -> bool {
    SCOPE.with(|s| s.borrow_mut().as_mut().is_some_and(expired_now))
}

/// Whether a stop scope is in force on this thread: a budget, a token, or both.
/// A blocking wait polls [`cut`] only then.
pub(crate) fn active() -> bool {
    SCOPE.with(|s| s.borrow().is_some())
}

/// The budget a z3 query may use: `timeout_ms`, clamped to what is left. `Err`
/// — `verification cancelled; z3 not started` or `total verification budget of
/// <N> ms exhausted; z3 not started` — when the run was cancelled or nothing is
/// left, and then no process may be started; the verification's own reason names
/// the step ([`stopped_reason`]). Without a scope, or with only a token that has
/// not been cancelled, `Ok(timeout_ms)`.
pub(crate) fn clamp(timeout_ms: u64) -> Result<u64, String> {
    SCOPE.with(|s| {
        let mut slot = s.borrow_mut();
        let Some(scope) = slot.as_mut() else {
            return Ok(timeout_ms);
        };
        if expired_now(scope) {
            return Err(match scope.stopped_in {
                Some((Stop::Cancelled, _)) => "verification cancelled; z3 not started".to_string(),
                _ => format!(
                    "total verification budget of {} ms exhausted; z3 not started",
                    scope.budget_ms.unwrap_or(0)
                ),
            });
        }
        Ok(timeout_ms.min(remaining(scope)))
    })
}

/// Records the running step as stopped when the deadline passed, or the token
/// was cancelled, while a z3 query ran.
pub(crate) fn note_if_expired() {
    cut();
}

/// The cancellation token in force, if any: the z3 watchdog polls it so a
/// cancelled process is killed at once rather than at its timeout.
pub(crate) fn cancel_token() -> Option<CancelToken> {
    SCOPE.with(|s| s.borrow().as_ref().and_then(|scope| scope.cancel.clone()))
}

/// The budget in force, if any.
pub(crate) fn budget_ms() -> Option<u64> {
    SCOPE.with(|s| s.borrow().as_ref().and_then(|scope| scope.budget_ms))
}

/// What stopped the verification, once something has.
pub(crate) fn stopped_by() -> Option<Stop> {
    SCOPE.with(|s| {
        s.borrow()
            .as_ref()
            .and_then(|scope| scope.stopped_in.as_ref().map(|(stop, _)| *stop))
    })
}

fn reason_of(scope: &Scope) -> Option<String> {
    scope.stopped_in.as_ref().map(|(stop, phase)| match stop {
        Stop::Budget => reason_for(scope.budget_ms.unwrap_or(0), phase),
        Stop::Cancelled => cancelled_reason(phase),
    })
}

/// The stop reason, once the budget ran out in some step or the verification
/// was cancelled.
pub(crate) fn stopped_reason() -> Option<String> {
    SCOPE.with(|s| s.borrow().as_ref().and_then(reason_of))
}

/// `total verification budget of <N> ms exhausted during <phase>` — the
/// `Unknown` reason and the report line, the same in every implementation.
pub(crate) fn reason_for(budget_ms: u64, phase: &str) -> String {
    format!("total verification budget of {budget_ms} ms exhausted during {phase}")
}

/// `verification cancelled during <phase>` — the `Unknown` reason and the report
/// line of a cancelled verification, the same in every implementation.
pub(crate) fn cancelled_reason(phase: &str) -> String {
    format!("verification cancelled during {phase}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn without_a_budget_nothing_is_clamped_or_cut() {
        assert_eq!(clamp(60_000), Ok(60_000));
        assert!(!cut());
        assert!(!step("linear bound"));
        assert_eq!(stopped_reason(), None);
        assert_eq!(budget_ms(), None);
    }

    #[test]
    fn a_budget_clamps_and_then_refuses() {
        let g = enter(Some(60_000), None);
        let clamped = clamp(1_000_000).unwrap();
        assert!(clamped <= 60_000 && clamped > 50_000, "{clamped}");
        assert_eq!(clamp(10), Ok(10));
        drop(g);

        let _g = enter(Some(0), None);
        // A spent budget is charged to the step running when it is noticed —
        // here the first, before any step started.
        assert!(step("state-space enumeration"));
        assert_eq!(
            clamp(10),
            Err("total verification budget of 0 ms exhausted; z3 not started".to_string())
        );
        assert_eq!(
            stopped_reason().as_deref(),
            Some("total verification budget of 0 ms exhausted during net preparation")
        );
    }

    #[test]
    fn a_cancelled_token_stops_like_a_spent_budget() {
        // A token alone clamps nothing while it is not cancelled.
        let token = CancelToken::new();
        let g = enter(None, Some(token.clone()));
        assert_eq!(clamp(60_000), Ok(60_000));
        assert!(!step("linear bound"));
        assert!(!cut());
        token.cancel();
        assert!(cut());
        assert!(step("horn"));
        assert_eq!(clamp(10), Err("verification cancelled; z3 not started".to_string()));
        assert_eq!(stopped_by(), Some(Stop::Cancelled));
        drop(g);

        // With both, cancellation names the reason when both apply.
        let token = CancelToken::new();
        token.cancel();
        let _g = enter(Some(0), Some(token));
        assert!(cut());
        assert_eq!(
            stopped_reason().as_deref(),
            Some("verification cancelled during net preparation")
        );
    }

    #[test]
    fn the_scope_ends_with_its_guard() {
        {
            let _g = enter(Some(0), None);
            assert!(cut());
        }
        assert!(!cut());
    }
}
