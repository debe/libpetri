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
//! is deliberately NOT a general guard. Guards filter tokens *within one
//! place* by an arbitrary boolean (the removed IO-006 / the surviving unary
//! `In` guard); a `MatchSpec` instead correlates the *name dimension across
//! places*, which is composition-structural like cardinality. When both are
//! present the guard filter applies first, then the name correlation runs over
//! the survivors (NU-021).

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
}

impl MatchSpec {
    /// Starts building a `MatchSpec`.
    pub fn builder() -> MatchSpecBuilder {
        MatchSpecBuilder { keys: Vec::new() }
    }

    /// Constructs a spec from explicit erased keys. Used by FFI bindings; the
    /// caller is responsible for supplying at least two correlated inputs.
    pub fn from_keys(keys: Vec<MatchKey>) -> Self {
        Self { keys }
    }

    /// The correlated inputs.
    pub fn keys(&self) -> &[MatchKey] {
        &self.keys
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
        f.debug_struct("MatchSpec")
            .field(
                "places",
                &self.keys.iter().map(|k| k.place_name()).collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// Builder for [`MatchSpec`].
pub struct MatchSpecBuilder {
    keys: Vec<MatchKey>,
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

    /// Builds the spec.
    ///
    /// # Panics
    /// Panics when fewer than two inputs are correlated — a match over a single
    /// place is just a guard and should be expressed as one.
    pub fn build(self) -> MatchSpec {
        assert!(
            self.keys.len() >= 2,
            "MatchSpec must correlate at least 2 input places, got {}",
            self.keys.len()
        );
        MatchSpec { keys: self.keys }
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
