use crate::marking_state::MarkingState;
use crate::p_invariant::PInvariant;

/// Verdict of a verification query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Property holds for all reachable states.
    Proven {
        /// The method that proved the property (e.g., "IC3/PDR" or "structural").
        method: String,
        /// Inductive invariant discovered by the solver, if available.
        inductive_invariant: Option<String>,
    },
    /// Property is violated with a counterexample trace.
    Violated,
    /// Solver could not determine the result.
    Unknown {
        /// Reason for the unknown result.
        reason: String,
    },
}

impl Verdict {
    pub fn is_proven(&self) -> bool {
        matches!(self, Self::Proven { .. })
    }

    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated)
    }
}


/// Which route decided a verdict ([VER-003]).
///
/// The routes do equivalent work by different means, and a consumer reading the
/// result's fields rather than its report needs to know which one answered:
/// [`Enumeration`](VerificationRoute::Enumeration) and
/// [`NuScg`](VerificationRoute::NuScg) decide by exploring a finite graph and
/// compute no P-invariants at all.
///
/// The rule for [`VerificationResult::invariants`] is about the *empty* case
/// only: an empty list from a route other than [`Smt`](VerificationRoute::Smt)
/// means "not computed", not "the net has none". A non-empty list is always real
/// — [`Unavailable`](VerificationRoute::Unavailable) in particular still carries
/// the invariants the pipeline computed before it found no usable solver, and
/// [`Structural`](VerificationRoute::Structural) carries whatever the proof
/// rested on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationRoute {
    /// The IC3/PDR pipeline: flatten, invariants, encode, solve ([VER-001]).
    Smt,
    /// Bounded state-space enumeration ([VER-017]).
    Enumeration,
    /// The ν name-partition state-class graph ([VER-012], Route B).
    NuScg,
    /// A structural proof — Commoner's theorem, or the linear bound of [VER-015].
    Structural,
    /// No route could run (no solver, an unresolved property place).
    Unavailable,
}

/// What a `Violated` verdict's counterexample means for the **timed** net
/// ([VER-003], [VER-023]).
///
/// The verdict itself is always the untimed claim of [VER-004]; this says
/// whether the counterexample is also a run of the net under its timing. Never
/// changes a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CounterexampleTiming {
    /// Every transition is `immediate`: timing cannot affect the trace.
    UntimedNet,
    /// The net is timed and the counterexample comes from the untimed
    /// abstraction, unchecked under timing: the timed check of [VER-023] was
    /// off or did not apply (environment places, match transitions).
    UntimedAbstraction,
    /// The deciding route already explores timed behaviour (Route B,
    /// [VER-012], on a timed net): the trace is a run of the timed semantics
    /// (priority-blind), not necessarily one the executor takes.
    TimedExact,
    /// The timed check ran and the timed state-class graph reaches a violating
    /// class. The trace was replaced by that graph's shortest path — a run of
    /// the timed semantics, which the graph builds priority-blind, so not
    /// necessarily one the executor takes.
    TimedConfirmed,
    /// The timed check ran, the timed graph closed, and no class violates: the
    /// property holds under timing. The verdict stays `Violated` and the
    /// untimed trace is kept.
    SpuriousUnderTiming,
    /// The timed check ran but its graph was truncated at the class budget or
    /// stopped by the total budget ([VER-013]).
    TimedUndecided,
}

impl CounterexampleTiming {
    /// The kebab-case spelling the TypeScript and Python results use
    /// (`untimed-net`, …, `timed-undecided`).
    pub fn as_str(self) -> &'static str {
        match self {
            CounterexampleTiming::UntimedNet => "untimed-net",
            CounterexampleTiming::UntimedAbstraction => "untimed-abstraction",
            CounterexampleTiming::TimedExact => "timed-exact",
            CounterexampleTiming::TimedConfirmed => "timed-confirmed",
            CounterexampleTiming::SpuriousUnderTiming => "spurious-under-timing",
            CounterexampleTiming::TimedUndecided => "timed-undecided",
        }
    }
}

/// Statistics from the verification run.
///
/// `#[non_exhaustive]`: the verifier gains diagnostics over time, so callers
/// construct this only through [`SmtVerifier::verify`](crate::smt_verifier::SmtVerifier::verify).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationStatistics {
    pub places: usize,
    pub transitions: usize,
    pub invariants_found: usize,
    pub structural_result: String,
}

/// Result of an SMT verification query.
///
/// `#[non_exhaustive]`: new diagnostic fields land here as the independent
/// validation layers grow, so callers read fields rather than destructure.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationResult {
    pub verdict: Verdict,
    /// Which route decided this verdict ([VER-003]). Read it before concluding
    /// anything from an **empty** [`VerificationResult::invariants`]: off the
    /// [`VerificationRoute::Smt`] route that means "not computed", never "none
    /// exist". A non-empty list is real whatever the route says.
    pub route: VerificationRoute,
    pub report: String,
    pub invariants: Vec<PInvariant>,
    pub discovered_invariants: Vec<String>,
    pub counterexample_trace: Vec<MarkingState>,
    pub counterexample_transitions: Vec<String>,
    /// Whether the counterexample **replays in the untimed abstraction**
    /// ([VER-003], [VER-004]) as an ordered firing sequence from the initial
    /// marking to a violating marking. A claim about the untimed, value-blind
    /// model only: `Some(true)` does not mean the run is possible under the
    /// net's timing — [`counterexample_timing`](Self::counterexample_timing)
    /// says that.
    ///
    /// Outcome of the abstract counterexample replay ([`crate::abstract_replay`]),
    /// as a TRI-STATE. **This is the canonical definition**: the PyO3 getter,
    /// the Python docstring and the sibling implementations restate it and
    /// point back here.
    ///
    /// * `None` — the replay did not apply: replay disabled, a non-violated
    ///   verdict, or a verdict from the name-coloured / Route B / structural
    ///   path;
    /// * `Some(false)` — the replay applied and did NOT confirm the
    ///   counterexample. Two shapes, both reported the same way:
    ///   * it could not conclude (nothing decodable in the proof, M₀ absent
    ///     from the decoded set, or a budget exhausted) — the `Violated`
    ///     verdict stands unconfirmed, see the report note;
    ///   * it refuted the trace outright
    ///     ([`ReplayOutcome::NoChain`](crate::abstract_replay::ReplayOutcome::NoChain):
    ///     no firing chain reaches the violation) — the verdict is downgraded
    ///     to `Unknown`. A refutation is strictly more informative than "did
    ///     not apply", so it reports `Some(false)`, never `None`;
    /// * `Some(true)` — the replay chained M₀ to a violating state.
    ///
    /// A `Some(true)` from the enumeration route ([VER-017]) means the same
    /// thing it means everywhere else — the trace is an ordered firing sequence
    /// that reaches the violation — even though it was read off the state-class
    /// graph rather than re-executed: the graph path *is* a firing sequence, so
    /// there is nothing to re-confirm. Consumers keying "are these steps
    /// ordered" off this field get the right answer without special-casing the
    /// route.
    ///
    /// A [`CounterexampleTiming::TimedConfirmed`] trace was read off the timed
    /// state-class graph and is ordered by construction, so it reports
    /// `Some(true)` as the enumeration route does ([VER-023]).
    pub counterexample_confirmed: Option<bool>,
    /// What the counterexample means for the timed net ([VER-003]): `None`
    /// unless the verdict is `Violated`; then exactly one
    /// [`CounterexampleTiming`]. Never changes a verdict.
    pub counterexample_timing: Option<CounterexampleTiming>,
    pub elapsed_ms: u64,
    pub statistics: VerificationStatistics,
}

impl VerificationResult {
    pub fn is_proven(&self) -> bool {
        self.verdict.is_proven()
    }

    pub fn is_violated(&self) -> bool {
        self.verdict.is_violated()
    }
}
