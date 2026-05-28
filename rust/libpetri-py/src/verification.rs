//! SMT verification bindings.

use std::collections::HashMap;
use std::sync::Arc;

use libpetri::verification::harness::{SubnetVerifyExt, VerificationHarness};
use libpetri::verification::property::SmtProperty;
use libpetri::verification::result::{Verdict, VerificationResult};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

use crate::model::{PyPetriNet, PySubnetDef};
#[cfg(feature = "z3")]
use crate::value::erased_from_py;

/// An SMT property to verify against a net. Build via `deadlock_free`, `mutual_exclusion`, `place_bound`, `unreachable`.
#[pyclass(module = "_libpetri", name = "SmtProperty", from_py_object)]
#[derive(Clone)]
pub struct PySmtProperty {
    pub(crate) inner: SmtProperty,
}

#[pymethods]
impl PySmtProperty {
    /// Returns a human-readable description of the property.
    fn description(&self) -> String {
        self.inner.description()
    }
}

/// Outcome of an SMT verification run. Inspect `verdict` (`"proven"` / `"violated"` / `"unknown"`), and if violated, `counterexample_trace` / `counterexample_transitions`.
#[pyclass(module = "_libpetri", name = "VerificationResult", from_py_object)]
#[derive(Clone)]
pub struct PyVerificationResult {
    verdict: String,
    method: Option<String>,
    reason: Option<String>,
    report: String,
    discovered_invariants: Vec<String>,
    counterexample_transitions: Vec<String>,
    counterexample_trace: Vec<HashMap<String, usize>>,
    elapsed_ms: u64,
    places: usize,
    transitions: usize,
    invariants_found: usize,
    structural_result: String,
}

impl PyVerificationResult {
    fn from_rust(result: VerificationResult) -> Self {
        let (verdict, method, reason) = match result.verdict {
            Verdict::Proven {
                method,
                inductive_invariant: _,
            } => ("proven".to_string(), Some(method), None),
            Verdict::Violated => ("violated".to_string(), None, None),
            Verdict::Unknown { reason } => ("unknown".to_string(), None, Some(reason)),
        };

        let counterexample_trace = result
            .counterexample_trace
            .iter()
            .map(|state| {
                state
                    .places()
                    .map(|(name, count)| (name.to_string(), count))
                    .collect::<HashMap<_, _>>()
            })
            .collect();

        Self {
            verdict,
            method,
            reason,
            report: result.report,
            discovered_invariants: result.discovered_invariants,
            counterexample_transitions: result.counterexample_transitions,
            counterexample_trace,
            elapsed_ms: result.elapsed_ms,
            places: result.statistics.places,
            transitions: result.statistics.transitions,
            invariants_found: result.statistics.invariants_found,
            structural_result: result.statistics.structural_result,
        }
    }

    #[cfg(not(feature = "z3"))]
    fn unknown(reason: impl Into<String>) -> Self {
        Self {
            verdict: "unknown".to_string(),
            method: None,
            reason: Some(reason.into()),
            report: String::new(),
            discovered_invariants: Vec::new(),
            counterexample_transitions: Vec::new(),
            counterexample_trace: Vec::new(),
            elapsed_ms: 0,
            places: 0,
            transitions: 0,
            invariants_found: 0,
            structural_result: String::new(),
        }
    }
}

#[pymethods]
impl PyVerificationResult {
    #[getter] fn verdict(&self) -> String { self.verdict.clone() }
    #[getter] fn method(&self) -> Option<String> { self.method.clone() }
    #[getter] fn reason(&self) -> Option<String> { self.reason.clone() }
    #[getter] fn report(&self) -> String { self.report.clone() }
    #[getter] fn discovered_invariants(&self) -> Vec<String> { self.discovered_invariants.clone() }
    #[getter] fn counterexample_transitions(&self) -> Vec<String> { self.counterexample_transitions.clone() }
    #[getter] fn counterexample_trace(&self) -> Vec<HashMap<String, usize>> { self.counterexample_trace.clone() }
    #[getter] fn elapsed_ms(&self) -> u64 { self.elapsed_ms }
    #[getter] fn places(&self) -> usize { self.places }
    #[getter] fn transitions(&self) -> usize { self.transitions }
    #[getter] fn invariants_found(&self) -> usize { self.invariants_found }
    #[getter] fn structural_result(&self) -> String { self.structural_result.clone() }

    /// `True` if the verdict is `"proven"`.
    fn is_proven(&self) -> bool { self.verdict == "proven" }
    /// `True` if the verdict is `"violated"` (a counterexample is available).
    fn is_violated(&self) -> bool { self.verdict == "violated" }
}

/// A property paired with the verification outcome for that property.
#[pyclass(module = "_libpetri", name = "PropertyResult", from_py_object)]
#[derive(Clone)]
pub struct PyPropertyResult {
    property: PySmtProperty,
    result: PyVerificationResult,
}

#[pymethods]
impl PyPropertyResult {
    #[getter] fn property(&self) -> PySmtProperty { self.property.clone() }
    #[getter] fn result(&self) -> PyVerificationResult { self.result.clone() }
}

/// Result of verifying a subnet under a harness: the synthetic net used and per-property outcomes.
#[pyclass(module = "_libpetri", name = "SubnetVerificationResult", from_py_object)]
#[derive(Clone)]
pub struct PySubnetVerificationResult {
    synthetic_net: PyPetriNet,
    property_results: Vec<PyPropertyResult>,
}

#[pymethods]
impl PySubnetVerificationResult {
    /// The closed net the verifier actually checked (subnet + harness wiring).
    fn synthetic_net(&self) -> PyPetriNet { self.synthetic_net.clone() }
    /// One entry per property supplied to the harness.
    fn property_results(&self) -> Vec<PyPropertyResult> { self.property_results.clone() }
    /// `True` if every property was proven.
    fn all_proven(&self) -> bool { self.property_results.iter().all(|e| e.result.is_proven()) }
    /// `True` if any property was violated.
    fn any_violated(&self) -> bool { self.property_results.iter().any(|e| e.result.is_violated()) }
}

/// Builder for subnet verification: wires port suppliers and properties, then `verify_subnet` runs the check.
#[pyclass(module = "_libpetri", name = "VerificationHarness")]
pub struct PyVerificationHarness {
    inputs: Vec<(String, Py<PyAny>)>,
    properties: Vec<SmtProperty>,
}

#[pymethods]
impl PyVerificationHarness {
    /// Starts an empty harness.
    #[new]
    fn new() -> Self {
        Self { inputs: Vec::new(), properties: Vec::new() }
    }

    /// Wires a token supplier (zero-arg callable) to an input port. Called
    /// once per simulated event during verification.
    fn input(slf: Py<Self>, py: Python<'_>, port_name: String, supplier: Py<PyAny>) -> PyResult<Py<Self>> {
        if !supplier.bind(py).is_callable() {
            return Err(PyTypeError::new_err("verification input supplier must be callable"));
        }
        { let mut this = slf.borrow_mut(py); this.inputs.push((port_name, supplier)); }
        Ok(slf)
    }

    /// Adds a property to verify.
    fn property(slf: Py<Self>, py: Python<'_>, property: &PySmtProperty) -> PyResult<Py<Self>> {
        { let mut this = slf.borrow_mut(py); this.properties.push(property.inner.clone()); }
        Ok(slf)
    }
}

/// Property: the net has no deadlock states beyond declared sinks.
#[pyfunction(name = "deadlock_free")]
fn py_deadlock_free() -> PySmtProperty {
    PySmtProperty { inner: SmtProperty::deadlock_free() }
}

/// Property: at most one of `places` is non-empty in any reachable state.
#[pyfunction(name = "mutual_exclusion")]
fn py_mutual_exclusion(places: Vec<String>) -> PySmtProperty {
    PySmtProperty { inner: SmtProperty::mutual_exclusion(places) }
}

/// Property: `place` never holds more than `bound` tokens.
#[pyfunction(name = "place_bound")]
fn py_place_bound(place: String, bound: usize) -> PySmtProperty {
    PySmtProperty { inner: SmtProperty::place_bound(place, bound) }
}

/// Property: no reachable state has any token in any of `places`.
#[pyfunction(name = "unreachable")]
fn py_unreachable(places: Vec<String>) -> PySmtProperty {
    PySmtProperty { inner: SmtProperty::unreachable(places) }
}

/// Verifies a single property against `net` using SMT (Z3). Without the `z3`
/// feature, returns `VerificationResult` with verdict `"unknown"`.
#[pyfunction(name = "verify_net")]
#[pyo3(signature = (net, property, *, environment_places = None, sink_places = None, timeout_ms = 30_000))]
fn py_verify_net(
    py: Python<'_>,
    net: &PyPetriNet,
    property: &PySmtProperty,
    environment_places: Option<Vec<String>>,
    sink_places: Option<Vec<String>>,
    timeout_ms: u64,
) -> PyResult<PyVerificationResult> {
    #[cfg(feature = "z3")]
    {
        let net = net.net().clone();
        let property = property.inner.clone();
        let environment_places = environment_places.unwrap_or_default();
        let sink_places = sink_places.unwrap_or_default();
        let result = py.detach(move || {
            libpetri::verification::smt_verifier::SmtVerifier::for_net(&net)
                .property(property)
                .environment_places(environment_places)
                .sink_places(sink_places)
                .timeout(timeout_ms)
                .verify()
        });
        Ok(PyVerificationResult::from_rust(result))
    }
    #[cfg(not(feature = "z3"))]
    {
        let _ = (py, net, property, environment_places, sink_places, timeout_ms);
        Ok(PyVerificationResult::unknown("z3 feature not enabled"))
    }
}

/// Verifies all properties in `harness` against `subnet`. The harness's
/// input suppliers and channels are wired into a closed synthetic net.
#[pyfunction(name = "verify_subnet")]
fn py_verify_subnet(
    py: Python<'_>,
    subnet: &PySubnetDef,
    harness: &PyVerificationHarness,
) -> PyResult<PySubnetVerificationResult> {
    let mut rust_harness = VerificationHarness::<()>::new();
    #[cfg(feature = "z3")]
    {
        for (port_name, supplier) in &harness.inputs {
            let supplier = supplier.clone_ref(py);
            let token_supplier: libpetri::verification::harness::TokenSupplier = Arc::new(move || {
                Python::attach(|py| {
                    let value = supplier
                        .bind(py)
                        .call0()
                        .expect("verification supplier raised")
                        .unbind();
                    erased_from_py(value)
                })
            });
            rust_harness = rust_harness.input(port_name.clone(), token_supplier);
        }
    }
    #[cfg(not(feature = "z3"))]
    {
        // Without z3, suppliers can't be exercised (verify returns Unknown).
        // Still record port names so the harness shape matches.
        let _ = py;
        for (port_name, _) in &harness.inputs {
            let token_supplier: libpetri::verification::harness::TokenSupplier =
                Arc::new(|| panic!("z3 feature not enabled"));
            rust_harness = rust_harness.input(port_name.clone(), token_supplier);
        }
    }
    for property in &harness.properties {
        rust_harness = rust_harness.property(property.clone());
    }

    let subnet = subnet.inner.clone();
    let result = py.detach(move || subnet.verify(rust_harness));

    let property_results = result
        .per_property
        .into_iter()
        .map(|(property, result)| PyPropertyResult {
            property: PySmtProperty { inner: property },
            result: PyVerificationResult::from_rust(result),
        })
        .collect();

    Ok(PySubnetVerificationResult {
        synthetic_net: PyPetriNet::from_net(result.synthetic_net),
        property_results,
    })
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySmtProperty>()?;
    m.add_class::<PyVerificationResult>()?;
    m.add_class::<PyPropertyResult>()?;
    m.add_class::<PySubnetVerificationResult>()?;
    m.add_class::<PyVerificationHarness>()?;
    m.add_function(wrap_pyfunction!(py_deadlock_free, m)?)?;
    m.add_function(wrap_pyfunction!(py_mutual_exclusion, m)?)?;
    m.add_function(wrap_pyfunction!(py_place_bound, m)?)?;
    m.add_function(wrap_pyfunction!(py_unreachable, m)?)?;
    m.add_function(wrap_pyfunction!(py_verify_net, m)?)?;
    m.add_function(wrap_pyfunction!(py_verify_subnet, m)?)?;
    Ok(())
}
