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
    pub counterexample_confirmed: Option<bool>,
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
