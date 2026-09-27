//! ν-net join correlation ([`MatchSpec`]).
//!
//! A [`MatchSpec`] declares that a subset of a transition's **input** places
//! must be correlated by **name equality**: the transition is enabled only
//! when there exists a single [`NameId`] `n` such that every correlated input
//! supplies (at least) its required token count whose projected name equals
//! `n`. On firing, exactly those name-matched tokens are consumed (spec
//! NU-020).
//!
//! This is the single *decidable* predicate — equality of opaque names — and
//! is deliberately NOT a general input predicate: it correlates the *name
//! dimension across places*, which is composition-structural like cardinality,
//! rather than evaluating an arbitrary boolean per token within one place.
//! Input specifications themselves remain purely structural (IO-006); name
//! correlation is the only per-token filter the enablement check ever applies
//! (NU-021).

use std::any::Any;
use std::sync::Arc;

use crate::name::NameId;
use crate::place::{Place, PlaceRef};

/// Type-erased name projection: maps a token's value to its [`NameId`], or
/// `None` when the value's type does not match the declared key type (treated
/// as "no name" — never correlates).
pub type KeyFn = Arc<dyn Fn(&dyn Any) -> Option<NameId> + Send + Sync>;

/// One correlated input: the place plus its name projection.
#[derive(Clone)]
pub struct MatchKey {
    place: PlaceRef,
    key: KeyFn,
}

impl MatchKey {
    /// Constructs a key from an already-erased projection. Used by FFI bindings
    /// (e.g. Python) that build the `KeyFn` directly over their token wrapper
    /// rather than through the typed [`MatchSpecBuilder::key`].
    pub fn from_erased(place: PlaceRef, key: KeyFn) -> Self {
        Self { place, key }
    }

    /// The correlated place.
    pub fn place(&self) -> &PlaceRef {
        &self.place
    }

    /// The correlated place name.
    pub fn place_name(&self) -> &str {
        self.place.name()
    }

    /// Projects a (type-erased) token value to its name.
    pub fn extract(&self, value: &dyn Any) -> Option<NameId> {
        (self.key)(value)
    }

    /// The raw key projection.
    pub fn key(&self) -> &KeyFn {
        &self.key
    }
}

/// Correlated fork/join match specification (ν-net join side). See module docs.
#[derive(Clone)]
pub struct MatchSpec {
    keys: Vec<MatchKey>,
    relays: Vec<MatchKey>,
}

impl MatchSpec {
    /// Starts building a `MatchSpec`.
    pub fn builder() -> MatchSpecBuilder {
        MatchSpecBuilder {
            keys: Vec::new(),
            relays: Vec::new(),
        }
    }

    /// Constructs a spec from explicit erased keys. Used by FFI bindings; the
    /// caller is responsible for supplying at least two correlated inputs.
    pub fn from_keys(keys: Vec<MatchKey>) -> Self {
        Self {
            keys,
            relays: Vec::new(),
        }
    }

    /// Constructs a spec from explicit erased keys and relay targets (NU-054).
    /// Used by FFI bindings and by the rewriter, which remaps both lists with
    /// the same place rewrite; the transition build checks the relays.
    pub fn from_keys_and_relays(keys: Vec<MatchKey>, relays: Vec<MatchKey>) -> Self {
        Self { keys, relays }
    }

    /// The correlated inputs.
    pub fn keys(&self) -> &[MatchKey] {
        &self.keys
    }

    /// The relay targets (NU-054): output places onto which the join writes the
    /// name it matched, each with the projection that reads a produced token's
    /// name. Empty for a join that drains the name. Each is an output of the
    /// transition and appears once (checked when the transition is built); a
    /// relay target may also be one of the [`keys`](Self::keys) (a correlated
    /// self-loop). The executor checks every token a firing writes into one
    /// against the matched name, as part of output validation (IO-015).
    pub fn relays(&self) -> &[MatchKey] {
        &self.relays
    }

    /// Returns the relay projection for `place_name`, if it is a relay target.
    pub fn relay_for(&self, place_name: &str) -> Option<&KeyFn> {
        self.relays
            .iter()
            .find(|k| k.place_name() == place_name)
            .map(|k| &k.key)
    }

    /// True when `place_name` is one of the correlated inputs.
    pub fn correlates(&self, place_name: &str) -> bool {
        self.keys.iter().any(|k| k.place_name() == place_name)
    }

    /// Returns the name projection for `place_name`, if correlated.
    pub fn key_for(&self, place_name: &str) -> Option<&KeyFn> {
        self.keys
            .iter()
            .find(|k| k.place_name() == place_name)
            .map(|k| &k.key)
    }
}

impl std::fmt::Debug for MatchSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut d = f.debug_struct("MatchSpec");
        d.field(
            "places",
            &self.keys.iter().map(|k| k.place_name()).collect::<Vec<_>>(),
        );
        if !self.relays.is_empty() {
            d.field(
                "relays",
                &self.relays.iter().map(|k| k.place_name()).collect::<Vec<_>>(),
            );
        }
        d.finish()
    }
}

/// Builder for [`MatchSpec`].
pub struct MatchSpecBuilder {
    keys: Vec<MatchKey>,
    relays: Vec<MatchKey>,
}

impl MatchSpecBuilder {
    /// Adds a correlated input place together with its name projection.
    ///
    /// The projection runs on the place's typed payload; a type mismatch at
    /// runtime yields no name (the token never correlates).
    pub fn key<T, F>(mut self, place: &Place<T>, key: F) -> Self
    where
        T: Send + Sync + 'static,
        F: Fn(&T) -> NameId + Send + Sync + 'static,
    {
        let erased: KeyFn = Arc::new(move |v: &dyn Any| v.downcast_ref::<T>().map(&key));
        self.keys.push(MatchKey {
            place: place.as_ref(),
            key: erased,
        });
        self
    }

    /// Declares a relay target (NU-054): an **output** place onto which the join
    /// writes the name it matched, together with the projection that reads a
    /// produced token's name. A relay target does not count towards the two
    /// correlated inputs [`build`](Self::build) requires.
    ///
    /// The projection is infallible by type, so there is no failure to map to
    /// "no name" as the other languages do for a projection that throws. A panic
    /// in it propagates as a panic in an action does, out of whatever ran the
    /// check — the executor at completion, or the action's own task for a
    /// flushed batch. No executor wraps the check in `catch_unwind`.
    ///
    /// ```ignore
    /// Transition::builder("e")
    ///     .inputs(vec![one(&c1), one(&d1)])
    ///     .output(out_place(&p5))
    ///     .match_spec(MatchSpec::builder().key(&c1, by_case).key(&d1, by_case).relay_to(&p5, by_case).build())
    /// ```
    pub fn relay_to<T, F>(mut self, place: &Place<T>, key: F) -> Self
    where
        T: Send + Sync + 'static,
        F: Fn(&T) -> NameId + Send + Sync + 'static,
    {
        let erased: KeyFn = Arc::new(move |v: &dyn Any| v.downcast_ref::<T>().map(&key));
        self.relays.push(MatchKey {
            place: place.as_ref(),
            key: erased,
        });
        self
    }

    /// Builds the spec.
    ///
    /// # Panics
    /// Panics when fewer than two inputs are correlated — a match over a single
    /// place correlates nothing.
    pub fn build(self) -> MatchSpec {
        assert!(
            self.keys.len() >= 2,
            "MatchSpec must correlate at least 2 input places, got {}",
            self.keys.len()
        );
        MatchSpec {
            keys: self.keys,
            relays: self.relays,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct Msg {
        cid: String,
    }

    #[test]
    fn builder_records_places_and_projections() {
        let a = Place::<Msg>::new("a");
        let b = Place::<Msg>::new("b");
        let ms = MatchSpec::builder()
            .key(&a, |m: &Msg| NameId::new(m.cid.clone()))
            .key(&b, |m: &Msg| NameId::new(m.cid.clone()))
            .build();

        assert!(ms.correlates("a"));
        assert!(ms.correlates("b"));
        assert!(!ms.correlates("c"));

        let key_a = ms.key_for("a").unwrap();
        let msg = Msg { cid: "X".into() };
        assert_eq!(key_a(&msg as &dyn Any), Some(NameId::new("X")));
    }

    #[test]
    fn projection_returns_none_on_type_mismatch() {
        let a = Place::<Msg>::new("a");
        let b = Place::<Msg>::new("b");
        let ms = MatchSpec::builder()
            .key(&a, |m: &Msg| NameId::new(m.cid.clone()))
            .key(&b, |m: &Msg| NameId::new(m.cid.clone()))
            .build();
        let key_a = ms.key_for("a").unwrap();
        assert_eq!(key_a(&42i32 as &dyn Any), None);
    }

    #[test]
    #[should_panic(expected = "at least 2")]
    fn single_input_panics() {
        let a = Place::<Msg>::new("a");
        MatchSpec::builder()
            .key(&a, |m: &Msg| NameId::new(m.cid.clone()))
            .build();
    }
}
