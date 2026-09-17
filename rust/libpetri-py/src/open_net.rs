//! Open-net verification bindings (VER-022): a subnet checked in isolation against a
//! contract, with its ports played by the environment.
//!
//! Only with the `z3` feature, because the Rust `open_net` module is gated on it: its SMT
//! route shares the verifier's transport. The facade in `libpetri/verification.py` stands
//! in for these classes when the wheel carries no SMT surface.
//!
//! Places are names here, as in the Rust contract; the facade coerces `Place` objects and
//! spreads its variadic arguments into the lists these methods take.

use libpetri::verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri::verification::open_net::{
    ContractViolation, OpenNetContract, OpenNetContractBuilder, OpenNetOptions, OpenNetResult, PortStep,
    SmtConfigurator, verify_open_net,
};
use libpetri::verification::result::Verdict;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyDict;
use pyo3::wrap_pyfunction;

use crate::error::panic_to_py;
use crate::model::{PyPetriNet, PyTransition};
use crate::verification::{bound_text, parse_count_bound, parse_semiflow_mode};

/// A marking's places with their counts, in the order the marking lists them: for the
/// closed marking, the order its builder first saw them, as a TypeScript `Map` keeps it.
fn marking_entries(marking: &MarkingState) -> Vec<(String, usize)> {
    marking.places().map(|(name, count)| (name.to_string(), count)).collect()
}

/// A dict in the order of `entries`, which a `HashMap` would not keep.
fn marking_dict<'py>(py: Python<'py>, entries: &[(String, usize)]) -> PyResult<Py<PyDict>> {
    let d = PyDict::new(py);
    for (name, count) in entries {
        d.set_item(name, count)?;
    }
    Ok(d.unbind())
}

/// Builds an `OpenNetContract`. Each method returns the builder, and a contract that
/// cannot mean anything raises `StructureError` (a `ValueError`) where it is built, with
/// the message every implementation uses, rather than coming back as a verdict.
#[pyclass(module = "_libpetri", name = "OpenNetContractBuilder")]
pub struct PyOpenNetContractBuilder {
    inner: OpenNetContractBuilder,
}

impl PyOpenNetContractBuilder {
    /// Applies `step` to a copy of the builder and keeps the result only if it did not
    /// panic. Taking the builder instead would leave an empty one behind a raised error,
    /// silently discarding everything declared before the mistake.
    fn apply(
        slf: Py<Self>,
        py: Python<'_>,
        step: impl FnOnce(OpenNetContractBuilder) -> OpenNetContractBuilder,
    ) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            let next = panic_to_py(|| step(this.inner.clone()))?;
            this.inner = next;
        }
        Ok(slf)
    }
}

#[pymethods]
impl PyOpenNetContractBuilder {
    /// Starts an empty contract: no tokens, no arrivals, no clauses, termination required.
    #[new]
    fn new() -> Self {
        Self { inner: OpenNetContract::builder() }
    }

    /// Replaces the tokens the subnet holds before anything arrives with `tokens`, a
    /// list of `(place, count)` in the order a port trace lists them.
    fn initial_marking(slf: Py<Self>, py: Python<'_>, tokens: Vec<(String, usize)>) -> PyResult<Py<Self>> {
        Self::apply(slf, py, move |b| {
            let cleared = b.initial_marking(&MarkingStateBuilder::new().build());
            tokens.into_iter().fold(cleared, |b, (place, count)| b.initial_tokens(place, count))
        })
    }

    /// Sets the tokens `place` holds before anything arrives; `0` removes it.
    fn initial_tokens(slf: Py<Self>, py: Python<'_>, place: String, count: usize) -> PyResult<Py<Self>> {
        Self::apply(slf, py, move |b| b.initial_tokens(place, count))
    }

    /// The environment delivers between `min` and `max` tokens in total, each onto one of
    /// `places`, at any point of the run. Both bounds are finite.
    fn arrive_between(
        slf: Py<Self>,
        py: Python<'_>,
        min: Bound<'_, PyAny>,
        max: Bound<'_, PyAny>,
        places: Vec<String>,
    ) -> PyResult<Py<Self>> {
        // No infinity here: a bound is both the runtime cap and the width of the claim.
        let (Some(Some(lo)), Some(Some(hi))) = (parse_count_bound(&min, false), parse_count_bound(&max, false))
        else {
            return Err(PyValueError::new_err(format!(
                "OpenNetContract: an arrival group needs whole bounds with 0 <= min <= max and max >= 1, \
                 got {}..{}. A bound is both the runtime cap and the width of the claim, so it is finite.",
                bound_text(&min),
                bound_text(&max)
            )));
        };
        Self::apply(slf, py, move |b| b.arrive_between(lo, hi, places))
    }

    /// At every quiescent marking, between `min` and `max` tokens across `places`; `max`
    /// may be `math.inf`.
    fn expect_between(
        slf: Py<Self>,
        py: Python<'_>,
        name: String,
        min: Bound<'_, PyAny>,
        max: Bound<'_, PyAny>,
        places: Vec<String>,
    ) -> PyResult<Py<Self>> {
        // Only what `usize` and `Option<usize>` cannot carry is refused here; the name,
        // the order of the bounds and the places are the Rust builder's to judge, so its
        // message is the one raised.
        let (Some(Some(lo)), Some(hi)) = (parse_count_bound(&min, false), parse_count_bound(&max, true)) else {
            return Err(PyValueError::new_err(format!(
                "OpenNetContract: clause '{name}' needs whole bounds with 0 <= min <= max, got {}..{}",
                bound_text(&min),
                bound_text(&max)
            )));
        };
        Self::apply(slf, py, move |b| b.expect_between(name, lo, hi, places))
    }

    /// Places that may hold any number of tokens at quiescence.
    fn rest(slf: Py<Self>, py: Python<'_>, places: Vec<String>) -> PyResult<Py<Self>> {
        Self::apply(slf, py, move |b| b.rest(places))
    }

    /// A designed terminal: while `marker` holds a token, lower bounds are waived and
    /// tokens may rest on `excused`. Repeated calls for one marker accumulate.
    fn terminal(slf: Py<Self>, py: Python<'_>, marker: String, excused: Vec<String>) -> PyResult<Py<Self>> {
        Self::apply(slf, py, move |b| b.terminal(marker, excused))
    }

    /// Transitions the environment fires: neighbours that react to what the subnet sends.
    /// Their actions never run.
    fn environment(slf: Py<Self>, py: Python<'_>, transitions: Vec<PyTransition>) -> PyResult<Py<Self>> {
        let transitions: Vec<_> = transitions.iter().map(|t| t.transition().clone()).collect();
        Self::apply(slf, py, move |b| b.environment(transitions))
    }

    /// Whether every run must come to rest (default `True`).
    fn require_termination(slf: Py<Self>, py: Python<'_>, required: bool) -> PyResult<Py<Self>> {
        Self::apply(slf, py, move |b| b.require_termination(required))
    }

    /// The contract declared so far. The builder stays usable.
    fn build(&self) -> PyOpenNetContract {
        PyOpenNetContract { inner: self.inner.clone().build() }
    }
}

/// A subnet's contract: the environment it assumes and what it guarantees at quiescence
/// (VER-022). Build one with `OpenNetContractBuilder`.
#[pyclass(module = "_libpetri", name = "OpenNetContract", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyOpenNetContract {
    inner: OpenNetContract,
}

#[pymethods]
impl PyOpenNetContract {
    /// Every place the contract names, in first-mention order: the places a port trace
    /// reports token changes on.
    fn places(&self) -> Vec<String> {
        self.inner.places()
    }

    /// The contract as the report prints it, one line per part.
    fn describe(&self) -> Vec<String> {
        self.inner.describe()
    }

    /// Whether every run must come to rest.
    #[getter]
    fn requires_termination(&self) -> bool {
        self.inner.requires_termination()
    }

    fn __repr__(&self) -> String {
        format!("OpenNetContract({} places)", self.inner.places().len())
    }
}

/// A firing that touches the subnet's boundary: an environment step, or a change on a
/// contract place.
#[pyclass(module = "_libpetri", name = "PortStep", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyPortStep {
    step: usize,
    transition: String,
    environment: Option<String>,
    changes: Vec<(String, i64)>,
}

impl PyPortStep {
    fn from_rust(s: &PortStep) -> Self {
        Self {
            step: s.step,
            transition: s.transition.clone(),
            environment: s.environment.map(|k| k.as_str().to_string()),
            changes: s.changes.iter().map(|c| (c.place.clone(), c.delta)).collect(),
        }
    }
}

#[pymethods]
impl PyPortStep {
    /// The firing's position in `ContractViolation.transitions`, counting from 1.
    #[getter] fn step(&self) -> usize { self.step }
    #[getter] fn transition(&self) -> String { self.transition.clone() }
    /// `"arrival"`, `"decline"` or `"transition"` when the environment fired it; `None`
    /// for the subnet.
    #[getter] fn environment(&self) -> Option<String> { self.environment.clone() }
    /// `(place, delta)` for each contract place the firing changed, in contract order.
    #[getter] fn changes(&self) -> Vec<(String, i64)> { self.changes.clone() }
}

/// One broken part of the contract, with a firing sequence that breaks it.
#[pyclass(module = "_libpetri", name = "ContractViolation", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyContractViolation {
    kind: String,
    subject: String,
    detail: String,
    transitions: Vec<String>,
    markings: Vec<Vec<(String, usize)>>,
    cycle_start: Option<usize>,
    port_trace: Vec<PyPortStep>,
    confirmed: bool,
}

impl PyContractViolation {
    fn from_rust(v: &ContractViolation) -> Self {
        Self {
            kind: v.kind.as_str().to_string(),
            subject: v.subject.clone(),
            detail: v.detail.clone(),
            transitions: v.transitions.clone(),
            markings: v.markings.iter().map(marking_entries).collect(),
            cycle_start: v.cycle_start,
            port_trace: v.port_trace.iter().map(PyPortStep::from_rust).collect(),
            confirmed: v.confirmed,
        }
    }
}

#[pymethods]
impl PyContractViolation {
    /// `"clause"`, `"stranded"` or `"termination"`.
    #[getter] fn kind(&self) -> String { self.kind.clone() }
    /// The clause's name, the stranded place(s), or `"termination"`. The graph route
    /// reports one violation per stranded place, the SMT route one for the whole query.
    #[getter] fn subject(&self) -> String { self.subject.clone() }
    #[getter] fn detail(&self) -> String { self.detail.clone() }
    /// The firing sequence from the initial marking, environment transitions included.
    #[getter] fn transitions(&self) -> Vec<String> { self.transitions.clone() }
    /// The marking before the first firing and after each one, when the route has them.
    #[getter]
    fn markings(&self, py: Python<'_>) -> PyResult<Vec<Py<PyDict>>> {
        self.markings.iter().map(|m| marking_dict(py, m)).collect()
    }
    /// For `"termination"`, the index into `transitions` where the repeating cycle starts.
    #[getter] fn cycle_start(&self) -> Option<usize> { self.cycle_start }
    #[getter] fn port_trace(&self) -> Vec<PyPortStep> { self.port_trace.clone() }
    /// Whether `transitions` is a real firing sequence in order: always on the graph
    /// route, the counterexample replay's outcome on the SMT route (VER-003).
    #[getter] fn confirmed(&self) -> bool { self.confirmed }
}

/// The outcome of `verify_open_net`.
#[pyclass(module = "_libpetri", name = "OpenNetResult", frozen, from_py_object)]
#[derive(Clone)]
pub struct PyOpenNetResult {
    verdict: String,
    method: Option<String>,
    reason: Option<String>,
    inductive_invariant: Option<String>,
    violations: Vec<PyContractViolation>,
    route: String,
    class_count: usize,
    graph_complete: bool,
    report: String,
    closed_net: PyPetriNet,
    closed_marking: Vec<(String, usize)>,
    elapsed_ms: u64,
}

impl PyOpenNetResult {
    fn from_rust(r: OpenNetResult) -> Self {
        let (verdict, method, reason, inductive_invariant) = match r.verdict {
            Verdict::Proven { method, inductive_invariant } => {
                ("proven".to_string(), Some(method), None, inductive_invariant)
            }
            Verdict::Violated => ("violated".to_string(), None, None, None),
            Verdict::Unknown { reason } => ("unknown".to_string(), None, Some(reason), None),
        };
        Self {
            verdict,
            method,
            reason,
            inductive_invariant,
            violations: r.violations.iter().map(PyContractViolation::from_rust).collect(),
            route: r.route.as_str().to_string(),
            class_count: r.class_count,
            graph_complete: r.graph_complete,
            report: r.report,
            closed_marking: marking_entries(&r.closed_marking),
            closed_net: PyPetriNet::from_net(r.closed_net),
            elapsed_ms: r.elapsed_ms,
        }
    }
}

#[pymethods]
impl PyOpenNetResult {
    /// `"proven"`, `"violated"` (see `violations`) or `"unknown"` (see `reason`).
    #[getter] fn verdict(&self) -> String { self.verdict.clone() }
    #[getter] fn method(&self) -> Option<String> { self.method.clone() }
    #[getter] fn reason(&self) -> Option<String> { self.reason.clone() }
    /// On an SMT-route proof, the invariants its queries returned, one per line labelled
    /// by contract part (`[stranding] …`). `None` on the graph route, whose closed graph is
    /// the evidence.
    #[getter] fn inductive_invariant(&self) -> Option<String> { self.inductive_invariant.clone() }
    /// Every broken part found, each with a witness.
    #[getter] fn violations(&self) -> Vec<PyContractViolation> { self.violations.clone() }
    /// `"enumeration"` or `"smt"`.
    #[getter] fn route(&self) -> String { self.route.clone() }
    /// Classes the state-class graph explored; `0` when it was skipped.
    #[getter] fn class_count(&self) -> usize { self.class_count }
    #[getter] fn graph_complete(&self) -> bool { self.graph_complete }
    #[getter] fn report(&self) -> String { self.report.clone() }
    /// The subnet closed by its environment: what every route verified.
    #[getter] fn closed_net(&self) -> PyPetriNet { self.closed_net.clone() }
    /// The initial marking of the closed net: the contract's, in the order it was given,
    /// then the token sources of the arrival groups.
    #[getter]
    fn closed_marking(&self, py: Python<'_>) -> PyResult<Py<PyDict>> {
        marking_dict(py, &self.closed_marking)
    }
    #[getter] fn elapsed_ms(&self) -> u64 { self.elapsed_ms }

    /// `True` if the verdict is `"proven"`.
    fn is_proven(&self) -> bool { self.verdict == "proven" }
    /// `True` if the verdict is `"violated"`.
    fn is_violated(&self) -> bool { self.verdict == "violated" }
}

/// Verifies `net` in isolation against `contract` (VER-022): the closed net's untimed
/// state-class graph first, within `max_classes` (`0` skips it), then, unless `smt` is
/// `False`, one SMT query per part of the contract.
///
/// The remaining keywords configure every verifier the SMT route builds, as `verify_net`
/// takes them; `termination_timeout_ms` is the firing-bound query that decides termination
/// there. Raises `StructureError` when the net violates CORE-043 or the closure's names
/// collide with the net's.
#[pyfunction(name = "verify_open_net")]
#[pyo3(signature = (net, contract, *, max_classes = 50_000, smt = true, termination_timeout_ms = 60_000, timeout_ms = 60_000, linear_bound = true, state_equation = false, state_equation_phase = true, firing_bound = true, semiflow_invariants = None))]
fn py_verify_open_net(
    py: Python<'_>,
    net: &PyPetriNet,
    contract: &PyOpenNetContract,
    max_classes: usize,
    smt: bool,
    termination_timeout_ms: u64,
    timeout_ms: u64,
    linear_bound: bool,
    state_equation: bool,
    state_equation_phase: bool,
    firing_bound: bool,
    semiflow_invariants: Option<Bound<'_, PyAny>>,
) -> PyResult<PyOpenNetResult> {
    let net = net.net().clone();
    let contract = contract.inner.clone();
    let semiflow_invariants = parse_semiflow_mode(semiflow_invariants.as_ref())?;
    // Every setting is applied, defaults included, as `verify_net` applies its own: the
    // values are the verifier's defaults, so a caller who passes nothing gets the verifier
    // the Rust entry point builds with no configurator at all.
    let configure: SmtConfigurator = Box::new(move |v| {
        v.timeout(timeout_ms)
            .linear_bound(linear_bound)
            .state_equation(state_equation)
            .state_equation_phase(state_equation_phase)
            .firing_bound(firing_bound)
            .semiflow_invariants(semiflow_invariants)
    });
    let options = OpenNetOptions { max_classes, smt, configure_smt: Some(configure), termination_timeout_ms };
    // A CORE-043 net or a closure name collision panics; it must not unwind across the FFI
    // boundary, least of all out of a detached region.
    let result = panic_to_py(|| py.detach(move || verify_open_net(&net, &contract, &options)))?;
    Ok(PyOpenNetResult::from_rust(result))
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyOpenNetContractBuilder>()?;
    m.add_class::<PyOpenNetContract>()?;
    m.add_class::<PyPortStep>()?;
    m.add_class::<PyContractViolation>()?;
    m.add_class::<PyOpenNetResult>()?;
    m.add_function(wrap_pyfunction!(py_verify_open_net, m)?)?;
    Ok(())
}
