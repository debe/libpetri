/// ~100 years in milliseconds, used for "unconstrained" intervals.
pub const MAX_DURATION_MS: u64 = 365 * 100 * 24 * 60 * 60 * 1000;

/// Firing timing specification for transitions.
///
/// Based on classical Time Petri Net (TPN) semantics:
/// - Transition CANNOT fire before earliest time (lower bound)
/// - Transition MUST fire by deadline OR become disabled (upper bound)
///
/// All durations are in milliseconds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Timing {
    /// Can fire as soon as enabled, no deadline. [0, inf)
    Immediate,
    /// Can fire immediately, must fire by deadline. [0, by]
    Deadline { by_ms: u64 },
    /// Must wait, then can fire anytime. [after, inf)
    Delayed { after_ms: u64 },
    /// Can fire within [earliest, latest].
    Window { earliest_ms: u64, latest_ms: u64 },
    /// Fires at precisely the specified time. [at, at]
    Exact { at_ms: u64 },
}

// ==================== Factory Functions ====================

/// Immediate firing: can fire as soon as enabled, no deadline.
pub fn immediate() -> Timing {
    Timing::Immediate
}

/// Immediate with deadline: can fire immediately, must fire by deadline.
///
/// # Panics
/// Panics if `by_ms` is 0.
pub fn deadline(by_ms: u64) -> Timing {
    assert!(by_ms > 0, "Deadline must be positive: {by_ms}");
    Timing::Deadline { by_ms }
}

/// Delayed firing: must wait, then can fire anytime.
///
/// # Panics
/// Panics if `after_ms` exceeds [`MAX_DURATION_MS`], the finite stand-in for "no latest
/// bound": the interval `[after, MAX_DURATION_MS]` would be empty, and a state-class graph
/// would read a transition that can fire as one that never can.
pub fn delayed(after_ms: u64) -> Timing {
    assert!(
        after_ms <= MAX_DURATION_MS,
        "Delay must be at most MAX_DURATION_MS ({MAX_DURATION_MS}): {after_ms}"
    );
    Timing::Delayed { after_ms }
}

/// Time window: can fire within [earliest, latest].
///
/// # Panics
/// Panics if `latest_ms < earliest_ms`, or if `earliest_ms` exceeds [`MAX_DURATION_MS`]
/// (as for [`delayed`]: a verifier that lifts the latest bound reads the window as
/// `delayed(earliest_ms)`).
pub fn window(earliest_ms: u64, latest_ms: u64) -> Timing {
    assert!(
        earliest_ms <= MAX_DURATION_MS,
        "Earliest must be at most MAX_DURATION_MS ({MAX_DURATION_MS}): {earliest_ms}"
    );
    assert!(
        latest_ms >= earliest_ms,
        "Latest ({latest_ms}) must be >= earliest ({earliest_ms})"
    );
    Timing::Window {
        earliest_ms,
        latest_ms,
    }
}

/// Exact timing: targets the specified time (interval `[at, at]`).
///
/// The zero-width interval is precise for verification/simulation. Under wall-clock execution it
/// is enforced *softly* — the transition fires at the first opportunity at or after `at_ms` (like
/// [`delayed`]) and is never force-disabled for being observed late (TIME-006). Prefer
/// [`delayed`] for a plain lower bound, or [`window`] for a hard bounded window.
///
/// # Panics
/// Panics if `at_ms` exceeds [`MAX_DURATION_MS`], as [`delayed`] does.
pub fn exact(at_ms: u64) -> Timing {
    assert!(
        at_ms <= MAX_DURATION_MS,
        "Exact time must be at most MAX_DURATION_MS ({MAX_DURATION_MS}): {at_ms}"
    );
    Timing::Exact { at_ms }
}

// ==================== Query Functions ====================

impl Timing {
    /// Returns the earliest time (ms) the transition can fire after enabling.
    pub fn earliest(&self) -> u64 {
        match self {
            Timing::Immediate => 0,
            Timing::Deadline { .. } => 0,
            Timing::Delayed { after_ms } => *after_ms,
            Timing::Window { earliest_ms, .. } => *earliest_ms,
            Timing::Exact { at_ms } => *at_ms,
        }
    }

    /// Returns the latest time (ms) by which the transition must fire.
    pub fn latest(&self) -> u64 {
        match self {
            Timing::Immediate => MAX_DURATION_MS,
            Timing::Deadline { by_ms } => *by_ms,
            Timing::Delayed { .. } => MAX_DURATION_MS,
            Timing::Window { latest_ms, .. } => *latest_ms,
            Timing::Exact { at_ms } => *at_ms,
        }
    }

    /// Returns true if this timing has a finite deadline.
    pub fn has_deadline(&self) -> bool {
        matches!(
            self,
            Timing::Deadline { .. } | Timing::Window { .. } | Timing::Exact { .. }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "Delay must be at most")]
    fn delayed_rejects_an_earliest_bound_past_the_open_end() {
        delayed(MAX_DURATION_MS + 1);
    }

    #[test]
    #[should_panic(expected = "Earliest must be at most")]
    fn window_rejects_an_earliest_bound_past_the_open_end() {
        window(MAX_DURATION_MS + 1, MAX_DURATION_MS + 2);
    }

    #[test]
    #[should_panic(expected = "Exact time must be at most")]
    fn exact_rejects_a_time_past_the_open_end() {
        exact(MAX_DURATION_MS + 1);
    }

    #[test]
    fn the_open_end_itself_is_accepted() {
        assert_eq!(delayed(MAX_DURATION_MS).earliest(), MAX_DURATION_MS);
        assert_eq!(window(MAX_DURATION_MS, MAX_DURATION_MS + 1).earliest(), MAX_DURATION_MS);
        assert_eq!(exact(MAX_DURATION_MS).earliest(), MAX_DURATION_MS);
    }

    #[test]
    fn immediate_bounds() {
        let t = immediate();
        assert_eq!(t.earliest(), 0);
        assert_eq!(t.latest(), MAX_DURATION_MS);
        assert!(!t.has_deadline());
    }

    #[test]
    fn deadline_bounds() {
        let t = deadline(5000);
        assert_eq!(t.earliest(), 0);
        assert_eq!(t.latest(), 5000);
        assert!(t.has_deadline());
    }

    #[test]
    fn delayed_bounds() {
        let t = delayed(100);
        assert_eq!(t.earliest(), 100);
        assert_eq!(t.latest(), MAX_DURATION_MS);
        assert!(!t.has_deadline());
    }

    #[test]
    fn window_bounds() {
        let t = window(100, 500);
        assert_eq!(t.earliest(), 100);
        assert_eq!(t.latest(), 500);
        assert!(t.has_deadline());
    }

    #[test]
    fn exact_bounds() {
        let t = exact(250);
        assert_eq!(t.earliest(), 250);
        assert_eq!(t.latest(), 250);
        assert!(t.has_deadline());
    }

    #[test]
    #[should_panic(expected = "Deadline must be positive")]
    fn deadline_zero_panics() {
        deadline(0);
    }

    #[test]
    #[should_panic(expected = "Latest")]
    fn window_inverted_panics() {
        window(500, 100);
    }
}
