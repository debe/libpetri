//! Python wrappers around the libpetri core model.
//!
//! Exposes places, transitions, nets, subnets, and their builders to Python,
//! plus the arc / output / timing helper functions that compose into the
//! transition builder. Composition is supported through [`PyPetriNetBuilder::compose`]
//! and the subnet builder family.

use std::collections::HashMap;
use std::sync::Arc;

use libpetri::core::instance::Instance;
use libpetri::core::interface::PortDirection;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::subnet_instance::SubnetInstance;
use libpetri::{
    BoxedAction, In, Inhibitor, Out, PetriNet, Place, Read, Reset, Timing, Transition, all, and,
    at_least, deadline, delayed, exact, exactly, fork, forward_input, immediate, inhibitor, one,
    out_place, passthrough, read, reset, timeout, window, xor,
};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;
use pyo3::wrap_pyfunction;

use crate::action::{boxed_async_action, boxed_sync_action};
use crate::error::panic_to_py;
use crate::executor::PyCompiledNet;
use crate::value::PyTokenValue;

/// A typed-but-runtime-untyped token container.
///
/// Constructed as `Place("name")`. Identity is by name. Tokens deposited in a
/// place are arbitrary Python objects — see the module docstring for the
/// typing relaxation note.
#[pyclass(module = "_libpetri", name = "Place")]
#[derive(Clone)]
pub struct PyPlace {
    inner: Place<PyTokenValue>,
}

impl PyPlace {
    pub fn place(&self) -> &Place<PyTokenValue> {
        &self.inner
    }
}

#[pymethods]
impl PyPlace {
    /// Creates a place with the given name.
    #[new]
    fn new(name: String) -> Self {
        Self {
            inner: Place::new(name),
        }
    }

    /// The place's name.
    #[getter]
    fn name(&self) -> String {
        self.inner.name().to_string()
    }

    fn __repr__(&self) -> String {
        format!("Place({:?})", self.inner.name())
    }
}

/// Opaque input-arc descriptor. Build via `one()`, `exactly()`, `all_tokens()`, `at_least()`.
#[pyclass(module = "_libpetri", name = "InputSpec")]
#[derive(Clone)]
pub struct PyInputSpec {
    pub(crate) inner: In,
}

#[pymethods]
impl PyInputSpec {
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

/// Opaque output-spec descriptor. Build via `out_place()`, `and_outputs()`, `xor_outputs()`, `timeout_output()`, `forward_input()`.
#[pyclass(module = "_libpetri", name = "OutputSpec")]
#[derive(Clone)]
pub struct PyOutputSpec {
    pub(crate) inner: Out,
}

#[pymethods]
impl PyOutputSpec {
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

/// Inhibitor arc: a transition with this arc is disabled while the place has any token.
#[pyclass(module = "_libpetri", name = "InhibitorArc")]
#[derive(Clone)]
pub struct PyInhibitorArc {
    pub(crate) inner: Inhibitor,
}

/// Read arc: a transition tests presence without consuming.
#[pyclass(module = "_libpetri", name = "ReadArc")]
#[derive(Clone)]
pub struct PyReadArc {
    pub(crate) inner: Read,
}

/// Reset arc: firing the transition clears all tokens from the place.
#[pyclass(module = "_libpetri", name = "ResetArc")]
#[derive(Clone)]
pub struct PyResetArc {
    pub(crate) inner: Reset,
}

/// Timing constraint for a transition. Build via `immediate()`, `deadline()`, `delayed()`, `window()`, `exact()`.
#[pyclass(module = "_libpetri", name = "Timing")]
#[derive(Clone, Copy)]
pub struct PyTiming {
    pub(crate) inner: Timing,
}

#[pymethods]
impl PyTiming {
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

/// A built transition. Construct via `Transition("name")...build()`.
#[pyclass(module = "_libpetri", name = "Transition")]
#[derive(Clone)]
pub struct PyTransition {
    inner: Transition,
}

impl PyTransition {
    pub fn transition(&self) -> &Transition {
        &self.inner
    }
}

#[pymethods]
impl PyTransition {
    /// The transition's name.
    #[getter]
    fn name(&self) -> String {
        self.inner.name().to_string()
    }

    fn __repr__(&self) -> String {
        format!("Transition({:?})", self.inner.name())
    }
}

/// Built-in action selector for the Python builder.
///
/// Wraps Rust's `fork()` / `passthrough()` actions so Python users can pick
/// one without writing a callback.
#[pyclass(module = "_libpetri", name = "BuiltinAction")]
#[derive(Clone, Copy)]
pub enum PyBuiltinAction {
    Passthrough,
    Fork,
}

impl PyBuiltinAction {
    fn to_rust(self) -> BoxedAction {
        match self {
            Self::Passthrough => passthrough(),
            Self::Fork => fork(),
        }
    }
}

/// Fluent builder for a transition.
///
/// Chain `.input(...)`, `.output(...)`, `.inhibitor(...)`, `.read(...)`,
/// `.reset(...)`, `.timing(...)`, `.action(...)`, `.priority(...)` then
/// `.build()` to produce a `Transition`. Each call returns the builder so
/// chaining works idiomatically.
#[pyclass(module = "_libpetri", name = "TransitionBuilder")]
pub struct PyTransitionBuilder {
    name: String,
    inputs: Vec<In>,
    output: Option<Out>,
    inhibitors: Vec<Inhibitor>,
    reads: Vec<Read>,
    resets: Vec<Reset>,
    timing: Timing,
    action: Option<PyAction>,
    priority: i32,
}

enum PyAction {
    Callback(Py<PyAny>),
    Builtin(PyBuiltinAction),
}

#[pymethods]
impl PyTransitionBuilder {
    /// Starts a transition builder with the given name.
    #[new]
    fn new(name: String) -> Self {
        Self {
            name,
            inputs: Vec::new(),
            output: None,
            inhibitors: Vec::new(),
            reads: Vec::new(),
            resets: Vec::new(),
            timing: immediate(),
            action: None,
            priority: 0,
        }
    }

    /// Adds an input arc (constructed via `one`, `exactly`, `all_tokens`, `at_least`).
    fn input(slf: Py<Self>, py: Python<'_>, spec: &PyInputSpec) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.inputs.push(spec.inner.clone());
        }
        Ok(slf)
    }

    /// Sets the output spec (built via `out_place`, `and_outputs`, `xor_outputs`, etc.).
    fn output(slf: Py<Self>, py: Python<'_>, spec: &PyOutputSpec) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.output = Some(spec.inner.clone());
        }
        Ok(slf)
    }

    /// Adds an inhibitor arc — the transition is disabled while the place has tokens.
    fn inhibitor(slf: Py<Self>, py: Python<'_>, arc: &PyInhibitorArc) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.inhibitors.push(arc.inner.clone());
        }
        Ok(slf)
    }

    /// Adds a read arc — tests presence on the place without consuming.
    fn read(slf: Py<Self>, py: Python<'_>, arc: &PyReadArc) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.reads.push(arc.inner.clone());
        }
        Ok(slf)
    }

    /// Adds a reset arc — firing the transition clears the place.
    fn reset(slf: Py<Self>, py: Python<'_>, arc: &PyResetArc) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.resets.push(arc.inner.clone());
        }
        Ok(slf)
    }

    /// Sets the timing constraint (default: `immediate()`).
    fn timing(slf: Py<Self>, py: Python<'_>, t: &PyTiming) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.timing = t.inner;
        }
        Ok(slf)
    }

    /// Sets the transition's action. Accepts a sync callable, an async
    /// coroutine function, or a builtin action (`fork`, `passthrough`).
    fn action(slf: Py<Self>, py: Python<'_>, action: Py<PyAny>) -> PyResult<Py<Self>> {
        let bound = action.bind(py);
        let resolved = if let Ok(builtin) = bound.extract::<PyBuiltinAction>() {
            PyAction::Builtin(builtin)
        } else if bound.is_callable() {
            PyAction::Callback(action)
        } else {
            return Err(PyTypeError::new_err(
                "action must be a callable or a libpetri builtin action (fork, passthrough)",
            ));
        };
        {
            let mut this = slf.borrow_mut(py);
            this.action = Some(resolved);
        }
        Ok(slf)
    }

    /// Sets the transition's priority (higher fires first on tie).
    fn priority(slf: Py<Self>, py: Python<'_>, priority: i32) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.priority = priority;
        }
        Ok(slf)
    }

    /// Builds the transition. Raises if any required arc references an undeclared place.
    fn build(&self, py: Python<'_>) -> PyResult<PyTransition> {
        let action = match &self.action {
            Some(PyAction::Callback(callback)) => {
                let inspect = py.import("inspect")?;
                let is_async: bool = inspect
                    .call_method1("iscoroutinefunction", (callback.clone_ref(py),))?
                    .extract()?;
                if is_async {
                    boxed_async_action(callback.clone_ref(py))
                } else {
                    boxed_sync_action(callback.clone_ref(py))
                }
            }
            Some(PyAction::Builtin(builtin)) => builtin.to_rust(),
            None => passthrough(),
        };

        let mut builder = Transition::builder(self.name.clone())
            .inputs(self.inputs.clone())
            .inhibitors(self.inhibitors.clone())
            .reads(self.reads.clone())
            .resets(self.resets.clone())
            .timing(self.timing)
            .priority(self.priority)
            .action(action);

        if let Some(output) = &self.output {
            builder = builder.output(output.clone());
        }

        Ok(PyTransition {
            inner: builder.build(),
        })
    }
}

/// A built Petri net definition. Build via `NetBuilder(name)...build()` or `Net(name)` shortcut, then `compile()` to run.
#[pyclass(module = "_libpetri", name = "Net")]
#[derive(Clone)]
pub struct PyPetriNet {
    inner: PetriNet,
}

impl PyPetriNet {
    pub fn net(&self) -> &PetriNet {
        &self.inner
    }

    pub(crate) fn from_net(inner: PetriNet) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl PyPetriNet {
    /// The net's name.
    #[getter]
    fn name(&self) -> String {
        self.inner.name().to_string()
    }

    /// Precompiles the net for fast execution.
    fn compile(&self) -> PyCompiledNet {
        PyCompiledNet::from_petri_net(&self.inner)
    }

    fn __repr__(&self) -> String {
        format!("Net({:?})", self.inner.name())
    }
}

/// A subnet port — frozen, read-only view of a subnet's named boundary place.
#[pyclass(module = "_libpetri", name = "Port", frozen)]
#[derive(Clone)]
pub struct PyPort {
    #[pyo3(get)]
    name: String,
    #[pyo3(get)]
    direction: String,
    #[pyo3(get)]
    place_name: String,
}

impl PyPort {
    fn from_rust(port: &libpetri::core::interface::Port) -> Self {
        let direction = match port.direction {
            PortDirection::Input => "input",
            PortDirection::Output => "output",
            PortDirection::InOut => "inout",
        };
        Self {
            name: port.name.to_string(),
            direction: direction.to_string(),
            place_name: port.place.name().to_string(),
        }
    }
}

/// A subnet channel — frozen, read-only view of a subnet's exported transition reference.
#[pyclass(module = "_libpetri", name = "Channel", frozen)]
#[derive(Clone)]
pub struct PyChannel {
    #[pyo3(get)]
    name: String,
    #[pyo3(get)]
    transition_name: String,
}

impl PyChannel {
    fn from_rust(channel: &libpetri::core::interface::Channel) -> Self {
        Self {
            name: channel.name.to_string(),
            transition_name: channel.transition_name.to_string(),
        }
    }
}

/// Frozen descriptor of an instantiated subnet — names of contained transitions, exposed places, and parent prefix.
#[pyclass(module = "_libpetri", name = "SubnetInstance", frozen)]
#[derive(Clone)]
pub struct PySubnetInstance {
    #[pyo3(get)]
    prefix: String,
    #[pyo3(get)]
    def_name: String,
    #[pyo3(get)]
    transitions: Vec<String>,
    #[pyo3(get)]
    exposed_places: Vec<String>,
    #[pyo3(get)]
    parent_prefix: Option<String>,
}

impl PySubnetInstance {
    fn from_rust(d: &SubnetInstance) -> Self {
        Self {
            prefix: d.prefix.to_string(),
            def_name: d.def_name.to_string(),
            transitions: d.transitions.iter().map(|name| name.to_string()).collect(),
            exposed_places: d
                .exposed_places
                .iter()
                .map(|name| name.to_string())
                .collect(),
            parent_prefix: d.parent_prefix.as_ref().map(|p| p.to_string()),
        }
    }
}

/// A live instance of a `SubnetDef`, bound to a prefix. Returned by `SubnetDef.instantiate(prefix)`.
#[pyclass(module = "_libpetri", name = "Instance")]
#[derive(Clone)]
pub struct PyInstance {
    inner: Instance<()>,
}

#[pymethods]
impl PyInstance {
    /// Instance prefix (e.g. `"step1"`).
    #[getter]
    fn prefix(&self) -> String {
        self.inner.prefix().to_string()
    }

    /// Name of the underlying `SubnetDef`.
    #[getter]
    fn def_name(&self) -> String {
        self.inner.def_name().to_string()
    }

    /// Looks up the prefixed place name for the given port.
    fn port_place_name(&self, name: &str) -> PyResult<String> {
        Ok(panic_to_py(|| {
            self.inner.port::<PyTokenValue>(name).name().to_string()
        })?)
    }

    /// Looks up the prefixed transition name for the given channel.
    fn channel(&self, name: &str) -> PyResult<String> {
        Ok(panic_to_py(|| self.inner.channel(name).to_string())?)
    }

    /// Returns the frozen `SubnetInstance` descriptor.
    fn descriptor(&self) -> PySubnetInstance {
        PySubnetInstance::from_rust(&self.inner.descriptor())
    }
}

/// A reusable subnet definition with named ports and channels. Build via `SubnetDefBuilder(name)`.
#[pyclass(module = "_libpetri", name = "SubnetDef")]
#[derive(Clone)]
pub struct PySubnetDef {
    pub(crate) inner: SubnetDef<()>,
}

#[pymethods]
impl PySubnetDef {
    /// The subnet's name.
    #[getter]
    fn name(&self) -> String {
        self.inner.name().to_string()
    }

    /// Number of declared ports.
    #[getter]
    fn port_count(&self) -> usize {
        self.inner.iface().port_count()
    }

    /// Number of declared channels.
    #[getter]
    fn channel_count(&self) -> usize {
        self.inner.iface().channel_count()
    }

    /// Returns the declared ports as `Port` descriptors.
    fn ports(&self) -> Vec<PyPort> {
        self.inner.iface().ports().map(PyPort::from_rust).collect()
    }

    /// Returns the declared channels as `Channel` descriptors.
    fn channels(&self) -> Vec<PyChannel> {
        self.inner
            .iface()
            .channels()
            .map(PyChannel::from_rust)
            .collect()
    }

    /// Instantiates the subnet under `prefix`, returning an `Instance` whose
    /// place / transition names are prefix-namespaced.
    fn instantiate(&self, prefix: &str) -> PyResult<PyInstance> {
        let prefix_arc = Arc::<str>::from(prefix);
        Ok(PyInstance {
            inner: panic_to_py(|| self.inner.instantiate(prefix_arc, ()))?,
        })
    }
}

/// Fluent builder for a `Net`. Add places, transitions, or composed subnets, then `.build()`.
#[pyclass(module = "_libpetri", name = "NetBuilder")]
pub struct PyPetriNetBuilder {
    name: String,
    places: Vec<libpetri::PlaceRef>,
    transitions: Vec<Transition>,
}

#[pymethods]
impl PyPetriNetBuilder {
    /// Starts a builder for a net named `name`.
    #[new]
    fn new(name: String) -> Self {
        Self {
            name,
            places: Vec::new(),
            transitions: Vec::new(),
        }
    }

    /// Adds a standalone place (typically only needed for environment places).
    fn place(slf: Py<Self>, py: Python<'_>, place: &PyPlace) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.places.push(place.place().as_ref());
        }
        Ok(slf)
    }

    /// Adds a transition. Its declared arcs implicitly bring in their places.
    fn transition(slf: Py<Self>, py: Python<'_>, t: &PyTransition) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.transitions.push(t.transition().clone());
        }
        Ok(slf)
    }

    /// Composes a subnet into this net under `instance_name`, gluing the
    /// subnet's ports to the host's places via the `port_bindings` dict.
    fn compose(
        slf: Py<Self>,
        py: Python<'_>,
        instance_name: String,
        subnet: &PySubnetDef,
        port_bindings: &Bound<'_, PyAny>,
    ) -> PyResult<Py<Self>> {
        let dict = port_bindings
            .cast::<PyDict>()
            .map_err(|_| PyTypeError::new_err("port_bindings must be a dict[str, Place]"))?;

        let mut bindings: HashMap<Arc<str>, libpetri::PlaceRef> = HashMap::new();
        for (port_name_obj, place_obj) in dict.iter() {
            let port_name: String = port_name_obj.extract()?;
            let place: PyRef<'_, PyPlace> = place_obj.extract()?;
            bindings.insert(Arc::<str>::from(port_name), place.place().as_ref());
        }

        let prefix_arc = Arc::<str>::from(instance_name);
        let subnet_inner = subnet.inner.clone();
        let instance = panic_to_py(|| subnet_inner.instantiate(prefix_arc, ()))?;
        let composed = {
            let this = slf.borrow(py);
            panic_to_py(|| {
                PetriNet::builder(this.name.clone())
                    .places(this.places.clone())
                    .transitions(this.transitions.clone())
                    .compose(&instance, bindings)
                    .build()
            })?
        };

        {
            let mut this = slf.borrow_mut(py);
            this.places = composed.places().to_vec();
            this.transitions = composed.transitions().to_vec();
        }
        Ok(slf)
    }

    /// Builds the immutable `Net`.
    fn build(&self) -> PyPetriNet {
        let net = PetriNet::builder(self.name.clone())
            .places(self.places.clone())
            .transitions(self.transitions.clone())
            .build();
        PyPetriNet { inner: net }
    }
}

/// Fluent builder for a `SubnetDef`. Add places, transitions, input/output/inout ports, and channels, then `.build()`.
#[pyclass(module = "_libpetri", name = "SubnetDefBuilder")]
pub struct PySubnetDefBuilder {
    name: String,
    places: Vec<Place<PyTokenValue>>,
    transitions: Vec<Transition>,
    input_ports: Vec<(String, Place<PyTokenValue>)>,
    output_ports: Vec<(String, Place<PyTokenValue>)>,
    inout_ports: Vec<(String, Place<PyTokenValue>)>,
    channels: Vec<(String, Transition)>,
}

#[pymethods]
impl PySubnetDefBuilder {
    #[new]
    fn new(name: String) -> Self {
        Self {
            name,
            places: Vec::new(),
            transitions: Vec::new(),
            input_ports: Vec::new(),
            output_ports: Vec::new(),
            inout_ports: Vec::new(),
            channels: Vec::new(),
        }
    }

    fn place(slf: Py<Self>, py: Python<'_>, place: &PyPlace) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.places.push(place.place().clone());
        }
        Ok(slf)
    }

    fn transition(slf: Py<Self>, py: Python<'_>, t: &PyTransition) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.transitions.push(t.transition().clone());
        }
        Ok(slf)
    }

    fn input_port(
        slf: Py<Self>,
        py: Python<'_>,
        name: String,
        place: &PyPlace,
    ) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.input_ports.push((name, place.place().clone()));
        }
        Ok(slf)
    }

    fn output_port(
        slf: Py<Self>,
        py: Python<'_>,
        name: String,
        place: &PyPlace,
    ) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.output_ports.push((name, place.place().clone()));
        }
        Ok(slf)
    }

    fn inout_port(
        slf: Py<Self>,
        py: Python<'_>,
        name: String,
        place: &PyPlace,
    ) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.inout_ports.push((name, place.place().clone()));
        }
        Ok(slf)
    }

    fn channel(
        slf: Py<Self>,
        py: Python<'_>,
        name: String,
        t: &PyTransition,
    ) -> PyResult<Py<Self>> {
        {
            let mut this = slf.borrow_mut(py);
            this.channels.push((name, t.transition().clone()));
        }
        Ok(slf)
    }

    /// Builds the immutable `SubnetDef`. Raises if port/channel wiring is invalid.
    fn build(&self) -> PyResult<PySubnetDef> {
        let mut builder = SubnetDef::<()>::builder(self.name.clone());
        for place in &self.places {
            builder = builder.place(place);
        }
        for transition in &self.transitions {
            builder = builder.transition(transition.clone());
        }
        for (name, place) in &self.input_ports {
            builder = builder.input_port(name.clone(), place);
        }
        for (name, place) in &self.output_ports {
            builder = builder.output_port(name.clone(), place);
        }
        for (name, place) in &self.inout_ports {
            builder = builder.inout_port(name.clone(), place);
        }
        for (name, transition) in &self.channels {
            builder = builder.channel(name.clone(), transition);
        }
        Ok(PySubnetDef {
            inner: panic_to_py(|| builder.build())?,
        })
    }
}

// =====================================================================
// Arc / output / timing helper functions
// =====================================================================

/// Input arc: consume exactly one token from `p`.
#[pyfunction(name = "one")]
fn py_one(p: &PyPlace) -> PyInputSpec {
    PyInputSpec {
        inner: one(p.place()),
    }
}

/// Input arc: consume exactly `count` tokens from `p`.
#[pyfunction(name = "exactly")]
fn py_exactly(count: usize, p: &PyPlace) -> PyInputSpec {
    PyInputSpec {
        inner: exactly(count, p.place()),
    }
}

/// Input arc: consume every token currently in `p`.
#[pyfunction(name = "all_tokens")]
fn py_all_tokens(p: &PyPlace) -> PyInputSpec {
    PyInputSpec {
        inner: all(p.place()),
    }
}

/// Input arc: require at least `min` tokens in `p`; consume `min` of them.
#[pyfunction(name = "at_least")]
fn py_at_least(min: usize, p: &PyPlace) -> PyInputSpec {
    PyInputSpec {
        inner: at_least(min, p.place()),
    }
}

/// Output spec: deposit one token onto `p`.
#[pyfunction(name = "out_place")]
fn py_out_place(p: &PyPlace) -> PyOutputSpec {
    PyOutputSpec {
        inner: out_place(p.place()),
    }
}

/// Output spec: AND — produce all `children` outputs in parallel.
#[pyfunction(name = "and_outputs")]
fn py_and_outputs(py: Python<'_>, children: Vec<Py<PyOutputSpec>>) -> PyResult<PyOutputSpec> {
    if children.is_empty() {
        return Err(PyValueError::new_err(
            "and_outputs requires at least one child",
        ));
    }
    let collected = children
        .into_iter()
        .map(|c| c.borrow(py).inner.clone())
        .collect();
    Ok(PyOutputSpec {
        inner: and(collected),
    })
}

/// Output spec: XOR — the action picks exactly one child to fire.
#[pyfunction(name = "xor_outputs")]
fn py_xor_outputs(py: Python<'_>, children: Vec<Py<PyOutputSpec>>) -> PyResult<PyOutputSpec> {
    if children.len() < 2 {
        return Err(PyValueError::new_err(
            "xor_outputs requires at least two children",
        ));
    }
    let collected = children
        .into_iter()
        .map(|c| c.borrow(py).inner.clone())
        .collect();
    Ok(PyOutputSpec {
        inner: xor(collected),
    })
}

/// Output spec: wrap `child` with a timeout — fires the child if it does not produce within `after_ms`.
#[pyfunction(name = "timeout_output")]
fn py_timeout_output(after_ms: u64, child: &PyOutputSpec) -> PyOutputSpec {
    PyOutputSpec {
        inner: timeout(after_ms, child.inner.clone()),
    }
}

/// Output spec: forward each consumed token from `from` to `to`.
#[pyfunction(name = "forward_input")]
fn py_forward_input(from: &PyPlace, to: &PyPlace) -> PyOutputSpec {
    PyOutputSpec {
        inner: forward_input(from.place(), to.place()),
    }
}

/// Inhibitor arc: blocks the transition while `p` holds any token.
#[pyfunction(name = "inhibitor")]
fn py_inhibitor(p: &PyPlace) -> PyInhibitorArc {
    PyInhibitorArc {
        inner: inhibitor(p.place()),
    }
}

/// Read arc: tests presence on `p` without consuming.
#[pyfunction(name = "read")]
fn py_read(p: &PyPlace) -> PyReadArc {
    PyReadArc {
        inner: read(p.place()),
    }
}

/// Reset arc: firing the transition clears every token on `p`.
#[pyfunction(name = "reset")]
fn py_reset(p: &PyPlace) -> PyResetArc {
    PyResetArc {
        inner: reset(p.place()),
    }
}

/// Timing: fire as soon as enabled (default).
#[pyfunction(name = "immediate")]
fn py_immediate() -> PyTiming {
    PyTiming {
        inner: immediate(),
    }
}

/// Timing: must fire by `by_ms` milliseconds after enablement, else is force-disabled.
#[pyfunction(name = "deadline")]
fn py_deadline(by_ms: u64) -> PyTiming {
    PyTiming {
        inner: deadline(by_ms),
    }
}

/// Timing: cannot fire before `after_ms` milliseconds after enablement.
#[pyfunction(name = "delayed")]
fn py_delayed(after_ms: u64) -> PyTiming {
    PyTiming {
        inner: delayed(after_ms),
    }
}

/// Timing: fire within the closed interval `[earliest_ms, latest_ms]` after enablement.
#[pyfunction(name = "window")]
fn py_window(earliest_ms: u64, latest_ms: u64) -> PyTiming {
    PyTiming {
        inner: window(earliest_ms, latest_ms),
    }
}

/// Timing: fire at exactly `at_ms` after enablement. NB: races deadline enforcement; prefer `window` in tests.
#[pyfunction(name = "exact")]
fn py_exact(at_ms: u64) -> PyTiming {
    PyTiming {
        inner: exact(at_ms),
    }
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyPlace>()?;
    m.add_class::<PyInputSpec>()?;
    m.add_class::<PyOutputSpec>()?;
    m.add_class::<PyInhibitorArc>()?;
    m.add_class::<PyReadArc>()?;
    m.add_class::<PyResetArc>()?;
    m.add_class::<PyTiming>()?;
    m.add_class::<PyTransition>()?;
    m.add_class::<PyTransitionBuilder>()?;
    m.add_class::<PyPetriNet>()?;
    m.add_class::<PyPort>()?;
    m.add_class::<PyChannel>()?;
    m.add_class::<PySubnetInstance>()?;
    m.add_class::<PyInstance>()?;
    m.add_class::<PySubnetDef>()?;
    m.add_class::<PyPetriNetBuilder>()?;
    m.add_class::<PySubnetDefBuilder>()?;
    m.add_class::<PyBuiltinAction>()?;

    m.add_function(wrap_pyfunction!(py_one, m)?)?;
    m.add_function(wrap_pyfunction!(py_exactly, m)?)?;
    m.add_function(wrap_pyfunction!(py_all_tokens, m)?)?;
    m.add_function(wrap_pyfunction!(py_at_least, m)?)?;
    m.add_function(wrap_pyfunction!(py_out_place, m)?)?;
    m.add_function(wrap_pyfunction!(py_and_outputs, m)?)?;
    m.add_function(wrap_pyfunction!(py_xor_outputs, m)?)?;
    m.add_function(wrap_pyfunction!(py_timeout_output, m)?)?;
    m.add_function(wrap_pyfunction!(py_forward_input, m)?)?;
    m.add_function(wrap_pyfunction!(py_inhibitor, m)?)?;
    m.add_function(wrap_pyfunction!(py_read, m)?)?;
    m.add_function(wrap_pyfunction!(py_reset, m)?)?;
    m.add_function(wrap_pyfunction!(py_immediate, m)?)?;
    m.add_function(wrap_pyfunction!(py_deadline, m)?)?;
    m.add_function(wrap_pyfunction!(py_delayed, m)?)?;
    m.add_function(wrap_pyfunction!(py_window, m)?)?;
    m.add_function(wrap_pyfunction!(py_exact, m)?)?;
    Ok(())
}
