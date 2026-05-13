//! A typed module instance produced by
//! [`crate::subnet_def::SubnetDef::instantiate`], per
//! `spec/11-modular-composition.md` requirements **MOD-010** (creation),
//! **MOD-011** (typed handle map), **MOD-012** (per-instance state isolation),
//! and **MOD-030** (action binding).
//!
//! ## Status
//!
//! [`Instance`] is constructed exclusively via the crate-internal
//! [`new_instance`] factory. Today, that factory is invoked by
//! [`crate::subnet_def::SubnetDef::instantiate`] (task #19) and will also be
//! invoked by the future subnet composer (task #20+). [`Instance::bind_actions`]
//! is implemented (task #19) on top of
//! [`crate::petri_net::PetriNet::bind_actions_with_resolver`].

use std::any::TypeId;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::action::BoxedAction;
use crate::petri_net::PetriNet;
use crate::place::{Place, PlaceRef};
use crate::subnet_instance::SubnetInstance;

/// A typed module instance produced by
/// [`crate::subnet_def::SubnetDef::instantiate`].
///
/// An instance carries:
/// - The `prefix` used to rename body elements (per [MOD-010] separator `"/"`);
/// - The originating subnet definition's `name`;
/// - The `renamed_body` — a structurally valid [`PetriNet`] per [CORE-040];
/// - Typed lookup handles for ports and channels keyed by their **original**
///   (pre-prefix) names;
/// - The `params` value supplied at instantiation.
///
/// Per **MOD-012**, two instances with distinct prefixes have disjoint state
/// as a structural consequence of distinct prefixed names.
#[derive(Debug, Clone)]
pub struct Instance<P = ()> {
    prefix: Arc<str>,
    def_name: Arc<str>,
    renamed_body: PetriNet,
    /// original-port-name -> renamed (prefixed) place reference
    port_handles: HashMap<Arc<str>, PlaceRef>,
    /// original-port-name -> originally declared `TypeId` for runtime check
    port_types: HashMap<Arc<str>, TypeId>,
    /// original-channel-name -> renamed (prefixed) transition name
    channel_handles: HashMap<Arc<str>, Arc<str>>,
    params: P,
    _phantom: PhantomData<fn() -> P>,
}

impl<P: 'static> Instance<P> {
    /// Returns the prefix string supplied at instantiation.
    pub fn prefix(&self) -> &str {
        &self.prefix
    }

    /// Returns the originating subnet definition's name.
    pub fn def_name(&self) -> &str {
        &self.def_name
    }

    /// Returns the renamed body net (structurally valid [`PetriNet`]).
    pub fn renamed_body(&self) -> &PetriNet {
        &self.renamed_body
    }

    /// Crate-internal: port-handle map keyed by original (pre-prefix) port
    /// name. Used by [`crate::petri_net::PetriNetBuilder::compose`] to
    /// resolve renamed [`PlaceRef`]s without re-deriving them from the
    /// interface's place name + prefix.
    pub(crate) fn port_handles(&self) -> &HashMap<Arc<str>, PlaceRef> {
        &self.port_handles
    }

    /// Crate-internal: resolve a channel name (original, pre-prefix) to the
    /// renamed (prefixed) instance-side transition name. Used by
    /// [`crate::petri_net::PetriNetBuilder::compose_with`] to identify the
    /// instance-side transition that participates in a channel-binding
    /// merge per **MOD-021**.
    pub(crate) fn channel_handles_get(&self, name: &str) -> Option<&Arc<str>> {
        self.channel_handles.get(name)
    }

    /// Crate-internal: enumerate channel names known to this instance
    /// (used to build the panic message when an unknown channel is bound).
    pub(crate) fn channel_handles_keys(&self) -> impl Iterator<Item = &Arc<str>> {
        self.channel_handles.keys()
    }

    /// Returns the parameter value supplied at instantiation.
    pub fn params(&self) -> &P {
        &self.params
    }

    /// Returns the renamed [`Place<T>`] corresponding to the named port per
    /// **MOD-011**.
    ///
    /// The port name is the **original** (pre-prefix) name as declared in
    /// the subnet's [`crate::interface::Interface`]. The token-type `T` is
    /// cross-checked at runtime against the port's originally declared
    /// `TypeId`; a mismatch panics with a clear message.
    ///
    /// # Panics
    /// - If the port name is not present on this instance.
    /// - If `T` does not match the originally declared port token type.
    pub fn port<T: 'static>(&self, name: &str) -> Place<T> {
        let place = self.port_handles.get(name).unwrap_or_else(|| {
            panic!(
                "No port named '{}' in instance '{}' (def '{}')",
                name, self.prefix, self.def_name
            )
        });
        let declared_type = self
            .port_types
            .get(name)
            .copied()
            .expect("port_types invariant: every port_handle has a matching type_id");
        if declared_type != TypeId::of::<T>() {
            panic!(
                "Port '{}' on instance '{}' (def '{}'): declared token type does not match \
                 requested type {}",
                name,
                self.prefix,
                self.def_name,
                std::any::type_name::<T>()
            );
        }
        Place::<T>::new(Arc::clone(place.name_arc()))
    }

    /// Returns the renamed (prefixed) transition name for the named channel
    /// per **MOD-011**.
    ///
    /// # Panics
    /// Panics if the channel name is unknown.
    pub fn channel(&self, name: &str) -> &str {
        self.channel_handles
            .get(name)
            .map(|s| s.as_ref())
            .unwrap_or_else(|| {
                panic!(
                    "No channel named '{}' in instance '{}' (def '{}')",
                    name, self.prefix, self.def_name
                )
            })
    }

    /// Returns the debug-UI descriptor for this instance per **MOD-041**.
    pub fn descriptor(&self) -> SubnetInstance {
        let transitions: Vec<Arc<str>> = self
            .renamed_body
            .transitions()
            .iter()
            .map(|t| Arc::clone(t.name_arc()))
            .collect();
        let exposed_places: Vec<Arc<str>> = self
            .port_handles
            .values()
            .map(|p| Arc::clone(p.name_arc()))
            .collect();
        SubnetInstance {
            prefix: Arc::clone(&self.prefix),
            def_name: Arc::clone(&self.def_name),
            transitions,
            exposed_places,
            parent_prefix: None,
        }
    }

    /// Produces a derived instance whose specified transitions (named by
    /// their **original**, pre-prefix names) carry the supplied actions per
    /// **MOD-030**.
    ///
    /// Lookup is performed by translating each entry's original name into
    /// the corresponding prefixed (`prefix + "/" + original_name`) name and
    /// delegating to
    /// [`crate::petri_net::PetriNet::bind_actions_with_resolver`]. Original
    /// names not present in the renamed body are silently ignored — there is
    /// no enclosing channel-merge or alias machinery yet (those land in
    /// task #20+).
    ///
    /// Per **MOD-012** the new [`Instance`] preserves all per-instance
    /// handle maps unchanged; only the renamed body's transition action
    /// references are updated.
    pub fn bind_actions(&self, actions: HashMap<Arc<str>, BoxedAction>) -> Instance<P>
    where
        P: Clone,
    {
        // Build a prefix-translated lookup: caller's original-name keys ->
        // prefixed-name keys, matching the renamed body's transition names.
        // We use an Arc<str> map so the resolver closure performs &str lookups
        // without allocating.
        let prefix = self.prefix.as_ref();
        let translated: HashMap<Arc<str>, BoxedAction> = actions
            .into_iter()
            .map(|(original, action)| {
                let prefixed: Arc<str> = Arc::from(format!("{}/{}", prefix, original));
                (prefixed, action)
            })
            .collect();

        let new_body = self
            .renamed_body
            .bind_actions_with_resolver(|name| translated.get(name).cloned());

        // Clone the per-instance handle maps unchanged. Cloning each Arc<str>
        // / PlaceRef value is refcount-only.
        Instance {
            prefix: Arc::clone(&self.prefix),
            def_name: Arc::clone(&self.def_name),
            renamed_body: new_body,
            port_handles: self.port_handles.clone(),
            port_types: self.port_types.clone(),
            channel_handles: self.channel_handles.clone(),
            params: self.params.clone(),
            _phantom: PhantomData,
        }
    }
}

/// `pub(crate)` constructor used by
/// [`crate::subnet_def::SubnetDef::instantiate`] (task #19) and by the
/// future subnet composer (task #20+). Not part of the public API surface
/// — user code constructs instances exclusively via
/// [`crate::subnet_def::SubnetDef::instantiate`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn new_instance<P: 'static>(
    prefix: Arc<str>,
    def_name: Arc<str>,
    renamed_body: PetriNet,
    port_handles: HashMap<Arc<str>, PlaceRef>,
    port_types: HashMap<Arc<str>, TypeId>,
    channel_handles: HashMap<Arc<str>, Arc<str>>,
    params: P,
) -> Instance<P> {
    Instance {
        prefix,
        def_name,
        renamed_body,
        port_handles,
        port_types,
        channel_handles,
        params,
        _phantom: PhantomData,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::transition::Transition;

    fn build_trivial_instance() -> Instance<()> {
        // Build a tiny "renamed" body by hand to test the accessors. The
        // names below imitate what the rewriter will produce in task #19.
        let p_in = Place::<String>::new("inst1/in");
        let p_out = Place::<String>::new("inst1/out");
        let t = Transition::builder("inst1/move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let body = PetriNet::builder("inst1").transition(t).build();

        let mut port_handles = HashMap::new();
        port_handles.insert(Arc::<str>::from("in"), p_in.as_ref());
        port_handles.insert(Arc::<str>::from("out"), p_out.as_ref());

        let mut port_types = HashMap::new();
        port_types.insert(Arc::<str>::from("in"), TypeId::of::<String>());
        port_types.insert(Arc::<str>::from("out"), TypeId::of::<String>());

        let mut channel_handles = HashMap::new();
        channel_handles.insert(Arc::<str>::from("move"), Arc::<str>::from("inst1/move"));

        new_instance(
            Arc::<str>::from("inst1"),
            Arc::<str>::from("Mover"),
            body,
            port_handles,
            port_types,
            channel_handles,
            (),
        )
    }

    #[test]
    fn accessors_return_expected_values() {
        let inst = build_trivial_instance();
        assert_eq!(inst.prefix(), "inst1");
        assert_eq!(inst.def_name(), "Mover");
        assert_eq!(inst.renamed_body().transitions().len(), 1);
        assert_eq!(inst.params(), &());
    }

    #[test]
    fn port_returns_typed_place() {
        let inst = build_trivial_instance();
        let p: Place<String> = inst.port::<String>("in");
        assert_eq!(p.name(), "inst1/in");
    }

    #[test]
    #[should_panic(expected = "No port named 'missing'")]
    fn port_panics_on_unknown_name() {
        let inst = build_trivial_instance();
        let _ = inst.port::<String>("missing");
    }

    #[test]
    #[should_panic(expected = "declared token type does not match")]
    fn port_panics_on_wrong_type() {
        let inst = build_trivial_instance();
        // declared as String, requested as i32
        let _ = inst.port::<i32>("in");
    }

    #[test]
    fn channel_returns_renamed_name() {
        let inst = build_trivial_instance();
        assert_eq!(inst.channel("move"), "inst1/move");
    }

    #[test]
    #[should_panic(expected = "No channel named 'missing'")]
    fn channel_panics_on_unknown_name() {
        let inst = build_trivial_instance();
        let _ = inst.channel("missing");
    }

    #[test]
    fn descriptor_lists_transitions_and_exposed_places() {
        let inst = build_trivial_instance();
        let d = inst.descriptor();
        assert_eq!(d.prefix.as_ref(), "inst1");
        assert_eq!(d.def_name.as_ref(), "Mover");
        assert_eq!(d.transitions.len(), 1);
        assert_eq!(d.transitions[0].as_ref(), "inst1/move");
        assert_eq!(d.exposed_places.len(), 2);
        assert!(d.parent_prefix.is_none());
    }

    #[test]
    fn bind_actions_replaces_action_for_named_transition() {
        let inst = build_trivial_instance();
        // Sanity: starting action is the builder default (passthrough) — the
        // important invariant is that we replace it with our new Arc.
        let new_action = crate::action::passthrough();
        let mut bindings = HashMap::new();
        bindings.insert(Arc::<str>::from("move"), Arc::clone(&new_action));

        let bound = inst.bind_actions(bindings);
        assert_eq!(bound.renamed_body().transitions().len(), 1);
        let t = &bound.renamed_body().transitions()[0];
        assert_eq!(t.name(), "inst1/move");
        assert!(
            Arc::ptr_eq(t.action(), &new_action),
            "MOD-030: bound action must be installed by reference"
        );
    }

    #[test]
    fn bind_actions_preserves_handle_maps() {
        let inst = build_trivial_instance();
        let bound = inst.bind_actions(HashMap::new());
        assert_eq!(bound.prefix(), "inst1");
        assert_eq!(bound.def_name(), "Mover");
        assert_eq!(bound.port::<String>("in").name(), "inst1/in");
        assert_eq!(bound.port::<String>("out").name(), "inst1/out");
        assert_eq!(bound.channel("move"), "inst1/move");
    }

    #[test]
    fn bind_actions_unknown_original_name_silently_ignored() {
        let inst = build_trivial_instance();
        let new_action = crate::action::passthrough();
        let mut bindings = HashMap::new();
        bindings.insert(Arc::<str>::from("nonexistent"), new_action);
        // Must not panic; transitions in the renamed body simply keep their
        // existing actions.
        let bound = inst.bind_actions(bindings);
        assert_eq!(bound.renamed_body().transitions().len(), 1);
    }
}
