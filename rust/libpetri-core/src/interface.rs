//! Subnet interface declaration: ports (interface places) and channels
//! (interface transitions), per `spec/11-modular-composition.md` requirements
//! **MOD-003** (port declaration), **MOD-004** (advisory direction), and
//! **MOD-005** (channel declaration).
//!
//! `Interface` is a pure carrier: validation rules per **MOD-006** are
//! enforced by [`crate::subnet_def::SubnetDefBuilder::build`] at subnet build
//! time. The `Interface` builder enforces only port- and channel-name
//! uniqueness within their respective namespaces — useful both internally and
//! for hand-built interfaces fed into [`crate::subnet_def::SubnetDef::from_net`].

use std::any::TypeId;
use std::collections::HashMap;
use std::sync::Arc;

use crate::place::{Place, PlaceRef};
use crate::transition::Transition;

/// Advisory direction metadata for an interface place per **MOD-004**.
///
/// Direction is metadata only — it does NOT constrain arc flow at runtime.
/// Token movement is governed by arcs declared per CORE-030..CORE-035.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortDirection {
    Input,
    Output,
    InOut,
}

/// A typed interface place exposed for composition, per **MOD-003**.
///
/// The `type_id` field captures the originally declared `Place<T>` token type
/// so that [`crate::instance::Instance::port`] can perform a runtime type
/// check on `T` (Rust does not reify generics in `Place<T>` after erasure to
/// `PlaceRef`).
#[derive(Debug, Clone)]
pub struct Port {
    /// Port name, unique within the [`Interface`].
    pub name: Arc<str>,
    /// Direction (advisory per **MOD-004**).
    pub direction: PortDirection,
    /// The body place exposed by this port (type-erased reference).
    pub place: PlaceRef,
    /// Originally declared token-type `TypeId` for runtime type-check on
    /// [`crate::instance::Instance::port`].
    pub type_id: TypeId,
}

impl Port {
    /// Creates a port from a typed `Place<T>`. The token type's `TypeId` is
    /// captured so that downstream `Instance::port::<T>(name)` calls can
    /// runtime-verify the requested `T` matches.
    pub fn new<T: 'static>(
        name: impl Into<Arc<str>>,
        direction: PortDirection,
        place: &Place<T>,
    ) -> Self {
        Self {
            name: name.into(),
            direction,
            place: place.as_ref(),
            type_id: TypeId::of::<T>(),
        }
    }
}

/// An interface transition (synchronous channel) exposed for composition with
/// a caller-side transition, per **MOD-005**.
///
/// Channels carry the underlying transition's *name* (as `Arc<str>`), not its
/// identity. Per [CORE-001] / [MOD-005], identity-by-name suffices for the
/// rewriter (task #19) to resolve the channel against the renamed body
/// transition by prefixed name.
#[derive(Debug, Clone)]
pub struct Channel {
    /// Channel name, unique within the channel namespace.
    pub name: Arc<str>,
    /// The originally declared body transition name (pre-prefix).
    pub transition_name: Arc<str>,
}

impl Channel {
    /// Creates a channel exposing the supplied body transition by name.
    pub fn new(name: impl Into<Arc<str>>, transition: &Transition) -> Self {
        Self {
            name: name.into(),
            transition_name: Arc::clone(transition.name_arc()),
        }
    }

    /// Creates a channel from raw names (used by hand-built interfaces).
    pub fn from_names(name: impl Into<Arc<str>>, transition_name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            transition_name: transition_name.into(),
        }
    }
}

/// Immutable declaration of a subnet's interface: the set of [`Port`]
/// (interface places) and [`Channel`] (interface transitions) exposed for
/// composition with an enclosing net.
#[derive(Debug, Clone)]
pub struct Interface {
    ports: HashMap<Arc<str>, Port>,
    channels: HashMap<Arc<str>, Channel>,
}

impl Interface {
    /// Looks up a port by name.
    pub fn port(&self, name: &str) -> Option<&Port> {
        self.ports.get(name)
    }

    /// Looks up a channel by name.
    pub fn channel(&self, name: &str) -> Option<&Channel> {
        self.channels.get(name)
    }

    /// Iterates over the declared ports.
    pub fn ports(&self) -> impl Iterator<Item = &Port> {
        self.ports.values()
    }

    /// Iterates over the declared channels.
    pub fn channels(&self) -> impl Iterator<Item = &Channel> {
        self.channels.values()
    }

    /// Returns the number of declared ports.
    pub fn port_count(&self) -> usize {
        self.ports.len()
    }

    /// Returns the number of declared channels.
    pub fn channel_count(&self) -> usize {
        self.channels.len()
    }

    /// Creates a new [`InterfaceBuilder`].
    pub fn builder() -> InterfaceBuilder {
        InterfaceBuilder::new()
    }
}

/// Builder for [`Interface`] values. Enforces port- and channel-name
/// uniqueness; full body-membership validation per **MOD-006** lives in
/// [`crate::subnet_def::SubnetDefBuilder::build`].
#[derive(Debug, Default)]
pub struct InterfaceBuilder {
    ports: HashMap<Arc<str>, Port>,
    channels: HashMap<Arc<str>, Channel>,
}

impl InterfaceBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a pre-built port (rejects duplicate names).
    ///
    /// # Panics
    /// Panics if a port with the same name was already added.
    pub fn port(mut self, port: Port) -> Self {
        if self.ports.contains_key(&port.name) {
            panic!("Duplicate port name: '{}'", port.name);
        }
        self.ports.insert(Arc::clone(&port.name), port);
        self
    }

    /// Declare an input port (advisory direction).
    pub fn input_port<T: 'static>(self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.port(Port::new(name, PortDirection::Input, place))
    }

    /// Declare an output port (advisory direction).
    pub fn output_port<T: 'static>(self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.port(Port::new(name, PortDirection::Output, place))
    }

    /// Declare an in-out port (advisory direction).
    pub fn inout_port<T: 'static>(self, name: impl Into<Arc<str>>, place: &Place<T>) -> Self {
        self.port(Port::new(name, PortDirection::InOut, place))
    }

    /// Add a pre-built channel (rejects duplicate names).
    ///
    /// # Panics
    /// Panics if a channel with the same name was already added.
    pub fn channel(mut self, channel: Channel) -> Self {
        if self.channels.contains_key(&channel.name) {
            panic!("Duplicate channel name: '{}'", channel.name);
        }
        self.channels.insert(Arc::clone(&channel.name), channel);
        self
    }

    /// Declare a synchronous channel by name + transition reference.
    pub fn sync_channel(self, name: impl Into<Arc<str>>, transition: &Transition) -> Self {
        self.channel(Channel::new(name, transition))
    }

    /// Bulk-add already-validated ports. Used internally by
    /// [`crate::subnet_def::SubnetDefBuilder`].
    pub(crate) fn ports_all(mut self, ports: impl IntoIterator<Item = Port>) -> Self {
        for p in ports {
            self = self.port(p);
        }
        self
    }

    /// Bulk-add already-validated channels. Used internally by
    /// [`crate::subnet_def::SubnetDefBuilder`].
    pub(crate) fn channels_all(mut self, channels: impl IntoIterator<Item = Channel>) -> Self {
        for c in channels {
            self = self.channel(c);
        }
        self
    }

    pub fn build(self) -> Interface {
        Interface {
            ports: self.ports,
            channels: self.channels,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::place::Place;

    #[test]
    fn interface_builder_basic_ports() {
        let p_in = Place::<String>::new("in");
        let p_out = Place::<String>::new("out");

        let iface = Interface::builder()
            .input_port("inp", &p_in)
            .output_port("outp", &p_out)
            .build();

        assert_eq!(iface.port_count(), 2);
        assert_eq!(iface.channel_count(), 0);
        assert_eq!(iface.port("inp").unwrap().direction, PortDirection::Input);
        assert_eq!(iface.port("outp").unwrap().direction, PortDirection::Output);
        assert_eq!(iface.port("inp").unwrap().place.name(), "in");
        assert!(iface.port("missing").is_none());
    }

    #[test]
    fn interface_builder_inout_port() {
        let p = Place::<i32>::new("io");
        let iface = Interface::builder().inout_port("iop", &p).build();
        assert_eq!(iface.port("iop").unwrap().direction, PortDirection::InOut);
    }

    #[test]
    fn interface_builder_channel() {
        let t = Transition::builder("attempt").build();
        let iface = Interface::builder().sync_channel("ch", &t).build();
        assert_eq!(iface.channel_count(), 1);
        assert_eq!(iface.channel("ch").unwrap().transition_name.as_ref(), "attempt");
        assert!(iface.channel("missing").is_none());
    }

    #[test]
    #[should_panic(expected = "Duplicate port name: 'p'")]
    fn interface_builder_rejects_duplicate_port_name() {
        let p1 = Place::<i32>::new("a");
        let p2 = Place::<i32>::new("b");
        Interface::builder()
            .input_port("p", &p1)
            .output_port("p", &p2)
            .build();
    }

    #[test]
    #[should_panic(expected = "Duplicate channel name: 'c'")]
    fn interface_builder_rejects_duplicate_channel_name() {
        let t1 = Transition::builder("t1").build();
        let t2 = Transition::builder("t2").build();
        Interface::builder()
            .sync_channel("c", &t1)
            .sync_channel("c", &t2)
            .build();
    }

    #[test]
    fn port_carries_type_id() {
        let p_str = Place::<String>::new("str");
        let p_i32 = Place::<i32>::new("i");

        let port_str = Port::new("s", PortDirection::Input, &p_str);
        let port_i32 = Port::new("i", PortDirection::Input, &p_i32);

        assert_eq!(port_str.type_id, TypeId::of::<String>());
        assert_eq!(port_i32.type_id, TypeId::of::<i32>());
        assert_ne!(port_str.type_id, port_i32.type_id);
    }
}
