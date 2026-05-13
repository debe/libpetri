//! Open Petri net fragment paired with a declared interface, per
//! `spec/11-modular-composition.md` requirement **MOD-001**.
//!
//! ## Verification ergonomics
//!
//! Local-property verification per **MOD-051** lives in the
//! `libpetri-verification` crate (which depends on `libpetri-core`, so the
//! reverse dependency cannot exist here). Import the
//! `libpetri_verification::harness::SubnetVerifyExt` extension trait to call
//! `def.verify(harness)` with the same ergonomics as Java/TS.

use std::any::TypeId;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::sync::Arc;

use crate::instance::{Instance, new_instance};
use crate::interface::{Channel, Interface, Port, PortDirection};
use crate::petri_net::{PetriNet, PetriNetBuilder};
use crate::place::{Place, PlaceRef};
use crate::rewriter;
use crate::transition::Transition;

/// An open Petri net fragment paired with a declared [`Interface`], per
/// **MOD-001**.
///
/// A subnet definition is the reusable unit of composition. It carries:
/// - A `name` (used as the originating-def label in
///   [`crate::subnet_instance::SubnetInstance`] per [MOD-041]);
/// - A `body` — a structurally complete [`PetriNet`] per [CORE-040];
/// - An `iface` — the set of exposed ports and channels per [MOD-003] /
///   [MOD-005];
/// - A `param_type` (`TypeId`) describing the parameter value supplied at
///   [`SubnetDef::instantiate`].
///
/// The default parameter type is `()` (the unit type), used for
/// unparameterised subnets.
#[derive(Debug, Clone)]
pub struct SubnetDef<P: 'static = ()> {
    name: Arc<str>,
    body: PetriNet,
    iface: Interface,
    param_type: TypeId,
    _phantom: PhantomData<fn() -> P>,
}

impl<P: 'static> SubnetDef<P> {
    /// Returns the subnet definition name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the body net (unrenamed; per [MOD-001] criterion 4).
    pub fn body(&self) -> &PetriNet {
        &self.body
    }

    /// Returns the interface declaration.
    pub fn iface(&self) -> &Interface {
        &self.iface
    }

    /// Returns the originally declared parameter type's `TypeId`.
    /// Used by [`Instance`] to runtime-check `params` (where applicable).
    pub fn param_type(&self) -> TypeId {
        self.param_type
    }

    /// Produces a renamed module instance per **MOD-010**.
    ///
    /// Algorithm (mirrors the Java [`SubnetDef.instantiate`] /
    /// TypeScript counterpart):
    /// 1. Validate the prefix: non-empty and free of `/` (the prefix
    ///    separator is reserved by **MOD-010**).
    /// 2. Walk the body net, building `place_remap` (original-name →
    ///    renamed [`PlaceRef`]) and `transition_remap` (original-name →
    ///    renamed [`Transition`]) via [`crate::rewriter::rename_net`].
    /// 3. Build typed port and channel handle maps from the interface.
    /// 4. Construct the [`Instance<P>`] via the crate-internal
    ///    [`crate::instance::new_instance`] factory.
    ///
    /// # Panics
    /// - Panics if `prefix` is empty.
    /// - Panics if `prefix` contains the reserved `/` separator (per
    ///   **MOD-010**).
    pub fn instantiate(&self, prefix: impl Into<Arc<str>>, params: P) -> Instance<P> {
        let prefix: Arc<str> = prefix.into();
        assert!(
            !prefix.is_empty(),
            "SubnetDef::instantiate: prefix must be non-empty (subnet '{}', MOD-010)",
            self.name
        );
        assert!(
            !prefix.contains('/'),
            "SubnetDef::instantiate: prefix '{}' must not contain '/' — \
             '/' is reserved as the prefix separator per MOD-010 (subnet '{}')",
            prefix,
            self.name
        );

        // Run the rename pass. The maps are populated as side effects so
        // we can build the typed handle maps below without re-walking.
        let mut place_remap: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        let mut transition_remap: HashMap<Arc<str>, Transition> = HashMap::new();
        let renamed_body = rewriter::rename_net(
            &self.body,
            prefix.as_ref(),
            &mut place_remap,
            &mut transition_remap,
        );

        // Build the per-instance typed handle maps from the interface.
        // Keys are the **original** (pre-prefix) port/channel names; values
        // are the renamed PlaceRef / renamed transition name.
        let mut port_handles: HashMap<Arc<str>, PlaceRef> =
            HashMap::with_capacity(self.iface.port_count());
        let mut port_types: HashMap<Arc<str>, TypeId> =
            HashMap::with_capacity(self.iface.port_count());
        for port in self.iface.ports() {
            let renamed = place_remap
                .get(port.place.name_arc())
                .cloned()
                .unwrap_or_else(|| {
                    panic!(
                        "SubnetDef::instantiate: port '{}' references body place '{}' \
                         which is missing from the renamed body of subnet '{}' (MOD-006/MOD-010)",
                        port.name,
                        port.place.name(),
                        self.name
                    )
                });
            port_handles.insert(Arc::clone(&port.name), renamed);
            port_types.insert(Arc::clone(&port.name), port.type_id);
        }

        let mut channel_handles: HashMap<Arc<str>, Arc<str>> =
            HashMap::with_capacity(self.iface.channel_count());
        for channel in self.iface.channels() {
            let renamed = transition_remap
                .get(channel.transition_name.as_ref())
                .map(|t| Arc::clone(t.name_arc()))
                .unwrap_or_else(|| {
                    panic!(
                        "SubnetDef::instantiate: channel '{}' references body transition '{}' \
                         which is missing from the renamed body of subnet '{}' (MOD-006/MOD-010)",
                        channel.name, channel.transition_name, self.name
                    )
                });
            channel_handles.insert(Arc::clone(&channel.name), renamed);
        }

        new_instance(
            prefix,
            Arc::clone(&self.name),
            renamed_body,
            port_handles,
            port_types,
            channel_handles,
            params,
        )
    }

    /// Creates a new [`SubnetDefBuilder`] for the supplied subnet name.
    pub fn builder(name: impl Into<Arc<str>>) -> SubnetDefBuilder<P> {
        SubnetDefBuilder::new(name)
    }
}

impl SubnetDef<()> {
    /// Convenience overload of [`SubnetDef::instantiate`] for unparameterised
    /// subnets. Equivalent to `instantiate(prefix, ())` once #19 lands.
    pub fn instantiate_unit(&self, prefix: impl Into<Arc<str>>) -> Instance<()> {
        self.instantiate(prefix, ())
    }

    /// Retrofit utility per **MOD-014**: wraps an existing closed
    /// [`PetriNet`] plus an [`Interface`] into an unparameterised
    /// `SubnetDef<()>`.
    ///
    /// Validates per **MOD-014** / **MOD-006**:
    /// - Every port's underlying place must be present in `net.places()`.
    /// - Every channel's underlying transition must be present in
    ///   `net.transitions()`.
    /// - Port and channel name uniqueness is re-validated defensively (the
    ///   [`Interface`] builder enforces this for the builder route, but a
    ///   hand-built `Interface` bypasses that path).
    ///
    /// On failure, panics with a message naming the offending element.
    /// Mirrors Java's `IllegalArgumentException` and TypeScript's `Error`
    /// retrofit-failure idioms.
    ///
    /// # Panics
    /// Panics on any of the rejection cases above.
    pub fn from_net(net: PetriNet, iface: Interface) -> SubnetDef<()> {
        // Re-validate port-name uniqueness (defense-in-depth — InterfaceBuilder
        // enforces it for the builder route). Note: ports() yields &Port; we
        // collect names into a HashSet to detect duplicates.
        let body_places = net.places();
        let body_transitions: HashSet<&str> = net
            .transitions()
            .iter()
            .map(|t| t.name())
            .collect();

        let mut seen_ports = HashSet::new();
        for port in iface.ports() {
            if !seen_ports.insert(port.name.as_ref().to_string()) {
                panic!(
                    "from_net: duplicate port name '{}' on interface for net '{}' (MOD-006)",
                    port.name,
                    net.name()
                );
            }
            if !body_places.contains(&port.place) {
                panic!(
                    "from_net: port '{}' references place '{}' which is not in net '{}' \
                     (MOD-014/MOD-006)",
                    port.name,
                    port.place.name(),
                    net.name()
                );
            }
        }

        let mut seen_channels = HashSet::new();
        for channel in iface.channels() {
            if !seen_channels.insert(channel.name.as_ref().to_string()) {
                panic!(
                    "from_net: duplicate channel name '{}' on interface for net '{}' (MOD-006)",
                    channel.name,
                    net.name()
                );
            }
            if !body_transitions.contains(channel.transition_name.as_ref()) {
                panic!(
                    "from_net: channel '{}' references transition '{}' which is not in net \
                     '{}' (MOD-014/MOD-006)",
                    channel.name,
                    channel.transition_name,
                    net.name()
                );
            }
        }

        let name = Arc::<str>::from(net.name());
        SubnetDef {
            name,
            body: net,
            iface,
            param_type: TypeId::of::<()>(),
            _phantom: PhantomData,
        }
    }
}

// ============================================================
//  Builder
// ============================================================

/// Fluent builder for [`SubnetDef`].
///
/// Validation per **MOD-006** is enforced at [`SubnetDefBuilder::build`]:
/// - Every port's underlying place must be in the body net.
/// - Every channel's underlying transition must be in the body net.
/// - Port names must be unique within the port namespace.
/// - Channel names must be unique within the channel namespace.
pub struct SubnetDefBuilder<P: 'static = ()> {
    name: Arc<str>,
    body_builder: PetriNetBuilder,
    ports: Vec<Port>,
    channels: Vec<Channel>,
    _phantom: PhantomData<fn() -> P>,
}

impl<P: 'static> SubnetDefBuilder<P> {
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        let name = name.into();
        let body_builder = PetriNet::builder(Arc::clone(&name));
        Self {
            name,
            body_builder,
            ports: Vec::new(),
            channels: Vec::new(),
            _phantom: PhantomData,
        }
    }

    // -------- body construction (delegates to PetriNetBuilder) --------

    /// Add a transition to the body net.
    pub fn transition(mut self, transition: Transition) -> Self {
        self.body_builder = self.body_builder.transition(transition);
        self
    }

    /// Add multiple transitions to the body net.
    pub fn transitions(mut self, transitions: impl IntoIterator<Item = Transition>) -> Self {
        self.body_builder = self.body_builder.transitions(transitions);
        self
    }

    /// Add an explicit place to the body net.
    pub fn place<T: 'static>(mut self, place: &Place<T>) -> Self {
        self.body_builder = self.body_builder.place(place.as_ref());
        self
    }

    // -------- interface declarations --------

    pub fn input_port<T: 'static>(mut self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.ports
            .push(Port::new(name, PortDirection::Input, place));
        self
    }

    pub fn output_port<T: 'static>(mut self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.ports
            .push(Port::new(name, PortDirection::Output, place));
        self
    }

    pub fn inout_port<T: 'static>(mut self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.ports
            .push(Port::new(name, PortDirection::InOut, place));
        self
    }

    pub fn channel(mut self, name: impl Into<Arc<str>>, transition: &Transition) -> Self {
        self.channels.push(Channel::new(name, transition));
        self
    }

    // -------- build & validate (MOD-006) --------

    /// Validate per **MOD-006** and produce an immutable [`SubnetDef<P>`].
    ///
    /// # Panics
    /// Panics if any MOD-006 invariant is violated; the message names the
    /// offending element.
    pub fn build(self) -> SubnetDef<P> {
        let built = self.body_builder.build();
        let body_places = built.places();
        let body_transitions: HashSet<&str> = built
            .transitions()
            .iter()
            .map(|t| t.name())
            .collect();

        // 1. Validate port-name uniqueness + place membership (MOD-006).
        let mut port_names = HashSet::new();
        for port in &self.ports {
            if !port_names.insert(port.name.as_ref().to_string()) {
                panic!(
                    "Subnet '{}': duplicate port name '{}'",
                    self.name, port.name
                );
            }
            if !body_places.contains(&port.place) {
                panic!(
                    "Subnet '{}': port '{}' references place '{}' which is not in the body",
                    self.name,
                    port.name,
                    port.place.name()
                );
            }
        }

        // 2. Validate channel-name uniqueness + transition membership (MOD-006).
        let mut channel_names = HashSet::new();
        for channel in &self.channels {
            if !channel_names.insert(channel.name.as_ref().to_string()) {
                panic!(
                    "Subnet '{}': duplicate channel name '{}'",
                    self.name, channel.name
                );
            }
            if !body_transitions.contains(channel.transition_name.as_ref()) {
                panic!(
                    "Subnet '{}': channel '{}' references transition '{}' which is not in \
                     the body",
                    self.name, channel.name, channel.transition_name
                );
            }
        }

        let iface = Interface::builder()
            .ports_all(self.ports)
            .channels_all(self.channels)
            .build();

        SubnetDef {
            name: self.name,
            body: built,
            iface,
            param_type: TypeId::of::<P>(),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::transition::Transition;

    #[test]
    fn subnet_def_builder_basic() {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();

        let def: SubnetDef<()> = SubnetDef::builder("Mover")
            .transition(t)
            .input_port("inp", &p_in)
            .output_port("outp", &p_out)
            .build();

        assert_eq!(def.name(), "Mover");
        assert_eq!(def.body().transitions().len(), 1);
        assert_eq!(def.iface().port_count(), 2);
        assert!(def.iface().port("inp").is_some());
        assert!(def.iface().port("outp").is_some());
        assert_eq!(def.param_type(), TypeId::of::<()>());
    }

    #[test]
    fn subnet_def_builder_with_channel() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let t = Transition::builder("attempt")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();

        let def: SubnetDef<()> = SubnetDef::builder("Retry")
            .transition(t.clone())
            .channel("attempt_ch", &t)
            .build();

        assert_eq!(def.iface().channel_count(), 1);
        assert_eq!(
            def.iface().channel("attempt_ch").unwrap().transition_name.as_ref(),
            "attempt"
        );
    }

    #[test]
    fn subnet_def_param_type_recorded() {
        let p = Place::<i32>::new("p");
        let t = Transition::builder("noop")
            .input(one(&p))
            .build();
        let def: SubnetDef<u32> = SubnetDef::<u32>::builder("Param").transition(t).build();
        assert_eq!(def.param_type(), TypeId::of::<u32>());
    }

    #[test]
    #[should_panic(expected = "duplicate port name 'p'")]
    fn rejects_duplicate_port_names() {
        let pa = Place::<i32>::new("a");
        let pb = Place::<i32>::new("b");
        let t = Transition::builder("t")
            .input(one(&pa))
            .output(out_place(&pb))
            .build();
        let _ = SubnetDef::<()>::builder("X")
            .transition(t)
            .input_port("p", &pa)
            .output_port("p", &pb)
            .build();
    }

    #[test]
    #[should_panic(expected = "references place 'orphan' which is not in the body")]
    fn rejects_port_referencing_non_body_place() {
        let pa = Place::<i32>::new("a");
        let pb = Place::<i32>::new("b");
        let orphan = Place::<i32>::new("orphan");
        let t = Transition::builder("t")
            .input(one(&pa))
            .output(out_place(&pb))
            .build();
        let _ = SubnetDef::<()>::builder("X")
            .transition(t)
            .input_port("oops", &orphan)
            .build();
    }

    #[test]
    #[should_panic(expected = "duplicate channel name 'c'")]
    fn rejects_duplicate_channel_names() {
        let pa = Place::<i32>::new("a");
        let pb = Place::<i32>::new("b");
        let t1 = Transition::builder("t1")
            .input(one(&pa))
            .output(out_place(&pb))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&pa))
            .output(out_place(&pb))
            .build();
        let _ = SubnetDef::<()>::builder("X")
            .transition(t1.clone())
            .transition(t2.clone())
            .channel("c", &t1)
            .channel("c", &t2)
            .build();
    }

    #[test]
    #[should_panic(expected = "references transition 'phantom' which is not in the body")]
    fn rejects_channel_referencing_non_body_transition() {
        let pa = Place::<i32>::new("a");
        let pb = Place::<i32>::new("b");
        let t = Transition::builder("t")
            .input(one(&pa))
            .output(out_place(&pb))
            .build();
        let phantom = Transition::builder("phantom").build();
        let _ = SubnetDef::<()>::builder("X")
            .transition(t)
            .channel("ch", &phantom)
            .build();
    }

    #[test]
    fn from_net_wraps_existing_petri_net() {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let net = PetriNet::builder("PreBuilt").transition(t.clone()).build();

        let iface = Interface::builder()
            .input_port("inp", &p_in)
            .sync_channel("ch", &t)
            .build();

        let def = SubnetDef::from_net(net, iface);
        assert_eq!(def.name(), "PreBuilt");
        assert_eq!(def.iface().port_count(), 1);
        assert_eq!(def.iface().channel_count(), 1);
        assert_eq!(def.param_type(), TypeId::of::<()>());
    }

    #[test]
    #[should_panic(expected = "is not in net 'X'")]
    fn from_net_rejects_port_referencing_non_body_place() {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let orphan = Place::<String>::new("orphan");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let net = PetriNet::builder("X").transition(t).build();
        let iface = Interface::builder().input_port("oops", &orphan).build();
        let _ = SubnetDef::from_net(net, iface);
    }

    #[test]
    #[should_panic(expected = "is not in net 'X'")]
    fn from_net_rejects_channel_referencing_non_body_transition() {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let phantom = Transition::builder("phantom").build();
        let net = PetriNet::builder("X").transition(t).build();
        let iface = Interface::builder().sync_channel("ch", &phantom).build();
        let _ = SubnetDef::from_net(net, iface);
    }

    #[test]
    fn from_net_empty_iface_succeeds() {
        // Per MOD-014: a closed PetriNet with an empty Interface is a
        // legitimate retrofit (zero ports, zero channels). Mirrors the
        // Java/TS counterparts.
        let p = Place::<i32>::new("p");
        let t = Transition::builder("noop").input(one(&p)).build();
        let net = PetriNet::builder("Empty").transition(t).build();
        let iface = Interface::builder().build();
        let def = SubnetDef::from_net(net, iface);
        assert_eq!(def.name(), "Empty");
        assert_eq!(def.iface().port_count(), 0);
        assert_eq!(def.iface().channel_count(), 0);
    }

    #[test]
    fn from_net_result_paramtype_unit() {
        // Per MOD-014: the retrofit factory always produces a SubnetDef<()>
        // (unparameterised), regardless of the body net's content.
        let p = Place::<String>::new("p");
        let t = Transition::builder("t").input(one(&p)).build();
        let net = PetriNet::builder("U").transition(t).build();
        let def = SubnetDef::from_net(net, Interface::builder().build());
        assert_eq!(def.param_type(), TypeId::of::<()>());
    }

    // ============================================================
    //  instantiate (task #19)
    // ============================================================

    fn build_mover_subnet() -> SubnetDef<()> {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");
        let move_t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        SubnetDef::<()>::builder("Mover")
            .transition(move_t.clone())
            .input_port("input", &p_in)
            .output_port("output", &p_out)
            .channel("move_ch", &move_t)
            .build()
    }

    #[test]
    fn instantiate_returns_renamed_body() {
        let def = build_mover_subnet();
        let inst = def.instantiate("b1", ());

        assert_eq!(inst.prefix(), "b1");
        assert_eq!(inst.def_name(), "Mover");
        assert_eq!(inst.renamed_body().name(), "b1/Mover");
        for place in inst.renamed_body().places() {
            assert!(
                place.name().starts_with("b1/"),
                "place '{}' missing prefix",
                place.name()
            );
        }
        for t in inst.renamed_body().transitions() {
            assert!(
                t.name().starts_with("b1/"),
                "transition '{}' missing prefix",
                t.name()
            );
        }
    }

    #[test]
    fn instantiate_handle_map_returns_renamed_port() {
        let def = build_mover_subnet();
        let inst = def.instantiate("b1", ());

        let port = inst.port::<String>("input");
        assert_eq!(port.name(), "b1/in");
        let port_out = inst.port::<String>("output");
        assert_eq!(port_out.name(), "b1/out");
    }

    #[test]
    fn instantiate_handle_map_returns_renamed_channel() {
        let def = build_mover_subnet();
        let inst = def.instantiate("b1", ());
        assert_eq!(inst.channel("move_ch"), "b1/move");
    }

    #[test]
    fn instantiate_per_instance_state_isolation() {
        let def = build_mover_subnet();
        let a = def.instantiate("a", ());
        let b = def.instantiate("b", ());

        // Disjoint place sets.
        let a_names: HashSet<&str> = a.renamed_body().places().iter().map(|p| p.name()).collect();
        let b_names: HashSet<&str> = b.renamed_body().places().iter().map(|p| p.name()).collect();
        assert!(
            a_names.is_disjoint(&b_names),
            "MOD-012: instances must have disjoint renamed places ({a_names:?} vs {b_names:?})"
        );
        // And the prefixes are reflected in handle resolution.
        assert_eq!(a.port::<String>("input").name(), "a/in");
        assert_eq!(b.port::<String>("input").name(), "b/in");
    }

    #[test]
    fn instantiate_actions_shared_by_reference() {
        // Per MOD-030: actions are carried through by reference (Arc::clone)
        // across instances of the same subnet definition.
        let p = Place::<i32>::new("p");
        let q = Place::<i32>::new("q");
        let action = crate::action::passthrough();
        let t = Transition::builder("t")
            .input(one(&p))
            .output(out_place(&q))
            .action(Arc::clone(&action))
            .build();
        let def: SubnetDef<()> = SubnetDef::builder("D").transition(t).build();

        let a = def.instantiate("a", ());
        let b = def.instantiate("b", ());

        let a_action = a.renamed_body().transitions()[0].action();
        let b_action = b.renamed_body().transitions()[0].action();
        assert!(
            Arc::ptr_eq(a_action, b_action),
            "MOD-030: actions must be shared by reference between instances"
        );
        assert!(Arc::ptr_eq(a_action, &action));
    }

    #[test]
    fn instantiate_params_accessible() {
        let p = Place::<i32>::new("p");
        let t = Transition::builder("t").input(one(&p)).build();
        let def: SubnetDef<u32> = SubnetDef::<u32>::builder("Param").transition(t).build();

        let inst = def.instantiate("i1", 42u32);
        assert_eq!(*inst.params(), 42u32);
    }

    #[test]
    fn bind_actions_overrides_only_for_this_instance() {
        // Per MOD-030 / MOD-012: rebinding actions on one instance must not
        // affect the action references seen by other instances, nor the
        // original SubnetDef body.
        let p = Place::<i32>::new("p");
        let q = Place::<i32>::new("q");
        let original_action = crate::action::passthrough();
        let t = Transition::builder("t")
            .input(one(&p))
            .output(out_place(&q))
            .action(Arc::clone(&original_action))
            .build();
        let def: SubnetDef<()> = SubnetDef::builder("D").transition(t).build();

        let a = def.instantiate("a", ());
        let b = def.instantiate("b", ());

        let new_action = crate::action::passthrough();
        let mut bindings = HashMap::new();
        bindings.insert(Arc::<str>::from("t"), Arc::clone(&new_action));

        let a_bound = a.bind_actions(bindings);
        // a_bound got the new action; b is untouched.
        let a_action = a_bound.renamed_body().transitions()[0].action();
        let b_action = b.renamed_body().transitions()[0].action();
        assert!(Arc::ptr_eq(a_action, &new_action));
        assert!(Arc::ptr_eq(b_action, &original_action));

        // The original SubnetDef body is also untouched.
        let def_action = def.body().transitions()[0].action();
        assert!(Arc::ptr_eq(def_action, &original_action));
    }

    #[test]
    #[should_panic(expected = "must not contain '/'")]
    fn instantiate_panics_on_prefix_with_slash() {
        let def = build_mover_subnet();
        let _ = def.instantiate("a/b", ());
    }

    #[test]
    #[should_panic(expected = "prefix must be non-empty")]
    fn instantiate_panics_on_empty_prefix() {
        let def = build_mover_subnet();
        let _ = def.instantiate("", ());
    }

}
