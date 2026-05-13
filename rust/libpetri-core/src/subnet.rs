//! Sum-type abstraction over Petri nets, distinguishing **closed** (runnable)
//! nets from **open** (composable) subnet fragments per
//! `spec/11-modular-composition.md` requirement **MOD-002**.
//!
//! Code that wants to accept "any net" types its parameter as
//! [`Subnet<P>`]; code that needs a runnable net continues to take
//! [`PetriNet`] (or matches the `Closed` variant); code that needs an open
//! fragment takes [`SubnetDef<P>`] (or matches the `Open` variant). The
//! [`SubnetLike`] trait exposes the shared `name()` / `body()` accessor
//! surface for both variants.
//!
//! # Generic-parameter design
//!
//! The Java sum-type uses `sealed interface Subnet permits Closed, Open` with
//! `Open` parameterised by the open subnet's type parameter `P`. In Rust we
//! mirror that by parameterising the enum itself: `Subnet<P>` defaults `P`
//! to `()` so the typical (unparameterised) case stays ergonomic
//! (`Subnet::Closed(net)` and `Subnet::Open(def)` both read naturally without
//! turbofish).
//!
//! # Example
//!
//! ```
//! use libpetri_core::petri_net::PetriNet;
//! use libpetri_core::subnet::{Subnet, SubnetLike};
//! use libpetri_core::subnet_def::SubnetDef;
//!
//! let net = PetriNet::builder("flat").build();
//! let def: SubnetDef<()> = SubnetDef::builder("Open").build();
//!
//! let any_net: Subnet = Subnet::Closed(net.clone());
//! let any_open: Subnet = Subnet::Open(def);
//!
//! assert_eq!(any_net.name(), "flat");
//! assert_eq!(any_open.name(), "Open");
//! ```

use crate::petri_net::PetriNet;
use crate::subnet_def::SubnetDef;

/// Discriminated sum-type per **MOD-002**: a net is either *closed* (a
/// runnable [`PetriNet`]) or *open* (a [`SubnetDef<P>`] for some parameter
/// type `P`).
///
/// The default `P = ()` keeps the typical unparameterised case ergonomic;
/// callers carrying a parameterised [`SubnetDef<P>`] can use `Subnet<P>`
/// explicitly to preserve the parameter type at the sum-type boundary.
#[derive(Debug, Clone)]
pub enum Subnet<P: 'static = ()> {
    /// Closed (runnable) net variant. Wraps an existing [`PetriNet`].
    Closed(PetriNet),
    /// Open (composable) net variant. Wraps a [`SubnetDef<P>`].
    Open(SubnetDef<P>),
}

/// Shared accessor surface implemented by both [`PetriNet`] (closed) and
/// [`SubnetDef`] (open). Used by code that wants to read the name and body
/// without dispatching on [`Subnet`] manually.
pub trait SubnetLike {
    /// Returns the subnet's display name.
    fn name(&self) -> &str;
    /// Returns the subnet's body net.
    fn body(&self) -> &PetriNet;
}

impl SubnetLike for PetriNet {
    fn name(&self) -> &str {
        PetriNet::name(self)
    }
    fn body(&self) -> &PetriNet {
        self
    }
}

impl<P: 'static> SubnetLike for SubnetDef<P> {
    fn name(&self) -> &str {
        SubnetDef::name(self)
    }
    fn body(&self) -> &PetriNet {
        SubnetDef::body(self)
    }
}

impl<P: 'static> SubnetLike for Subnet<P> {
    fn name(&self) -> &str {
        match self {
            Subnet::Closed(net) => net.name(),
            Subnet::Open(def) => def.name(),
        }
    }
    fn body(&self) -> &PetriNet {
        match self {
            Subnet::Closed(net) => net,
            Subnet::Open(def) => def.body(),
        }
    }
}

impl<P: 'static> Subnet<P> {
    /// Returns `true` when this subnet is the [`Subnet::Closed`] variant.
    pub fn is_closed(&self) -> bool {
        matches!(self, Subnet::Closed(_))
    }

    /// Returns `true` when this subnet is the [`Subnet::Open`] variant.
    pub fn is_open(&self) -> bool {
        matches!(self, Subnet::Open(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;
    use crate::transition::Transition;

    #[test]
    fn closed_variant_carries_petri_net() {
        let net = PetriNet::builder("flat").build();
        let s: Subnet = Subnet::Closed(net.clone());
        assert!(s.is_closed());
        assert!(!s.is_open());
        assert_eq!(s.name(), "flat");
        assert_eq!(s.body().name(), "flat");
    }

    #[test]
    fn open_variant_carries_subnet_def() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let def: SubnetDef<()> = SubnetDef::builder("Mover").transition(t).build();

        let s: Subnet = Subnet::Open(def);
        assert!(!s.is_closed());
        assert!(s.is_open());
        assert_eq!(s.name(), "Mover");
        assert_eq!(s.body().name(), "Mover");
    }

    #[test]
    fn subnet_like_implementations_agree() {
        let net = PetriNet::builder("X").build();
        let def: SubnetDef<()> = SubnetDef::builder("Y").build();

        // SubnetLike impl on PetriNet:
        assert_eq!(<PetriNet as SubnetLike>::name(&net), "X");
        // SubnetLike impl on SubnetDef:
        assert_eq!(<SubnetDef<()> as SubnetLike>::name(&def), "Y");
    }

    #[test]
    fn parameterised_open_subnet_compiles() {
        let p = Place::<i32>::new("p");
        let t = Transition::builder("t").input(one(&p)).build();
        let def: SubnetDef<u32> = SubnetDef::<u32>::builder("Param").transition(t).build();

        let s: Subnet<u32> = Subnet::Open(def);
        assert_eq!(s.name(), "Param");
    }
}
