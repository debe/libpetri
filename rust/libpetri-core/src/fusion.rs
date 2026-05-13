//! N-ary place equivalence declaration applied at
//! [`crate::petri_net::PetriNetBuilder::build`] time, per
//! `spec/11-modular-composition.md` requirements **MOD-060** (fusion set
//! declaration) and **MOD-061** (fusion resolution at build).
//!
//! Fusion is **orthogonal to subnet composition**: composition merges places
//! via port-binding (one instance port place ↔ one caller place per binding);
//! fusion merges N places at once via N-ary equivalence, applied **after** all
//! `compose(...)` calls have flattened subnet instances into the enclosing
//! [`crate::petri_net::PetriNetBuilder`]. Fusion is the mechanism for modeling
//! shared cross-instance state — e.g., a global rate limiter shared by three
//! instances of a leaky-bucket subnet — without expressing the shared resource
//! as an interface port on every subnet.
//!
//! ## Canonical member
//!
//! The **first declared member** is the canonical place; the others are
//! non-canonical and get substituted away at
//! [`crate::petri_net::PetriNetBuilder::build`] time. The canonical member's
//! name and identity survive into the resulting flat net; non-canonical
//! members do not appear in the built net's place set.
//!
//! ## Token-type homogeneity (MOD-060)
//!
//! All members of a fusion set MUST share the same token type. In Rust this
//! is enforced at **compile time** via the typed `<T>` parameter on
//! [`FusionSetBuilder::member`] and [`FusionSet::of`] — every call into the
//! builder requires `&Place<T>` for the same `T`, so mixed-type sequences
//! are rejected by the type checker. The runtime [`std::any::TypeId`]
//! captured at construction is a defence-in-depth record (used by
//! diagnostics) but the surface API does not allow heterogeneous members in
//! the first place.
//!
//! ## Single-member sets
//!
//! A fusion set with a single member is degenerate but allowed: it is a no-op
//! at fusion-resolution time (the canonical member maps to itself, no
//! substitution occurs). This matches the structural semantics of an N-ary
//! equivalence with N=1.

use std::any::TypeId;
use std::sync::Arc;

use crate::place::{Place, PlaceRef};

/// A declaration that N typed places are to be treated as a single canonical
/// place in the resulting flat [`crate::petri_net::PetriNet`], per **MOD-060**
/// and **MOD-061**.
///
/// `FusionSet` is immutable after construction. The members vector is
/// declaration-ordered, with the first element guaranteed to be the canonical
/// member.
#[derive(Debug, Clone)]
pub struct FusionSet {
    name: Arc<str>,
    members: Vec<PlaceRef>,
    type_id: TypeId,
}

impl FusionSet {
    /// Optional human-readable name for this fusion set; used in error
    /// messages (e.g., overlap detection at
    /// [`crate::petri_net::PetriNetBuilder::build`]).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the canonical member — by convention, the first declared
    /// member. The canonical place's identity survives into the resulting
    /// flat net.
    pub fn canonical(&self) -> &PlaceRef {
        &self.members[0]
    }

    /// Returns the declaration-ordered slice of all members.
    pub fn members(&self) -> &[PlaceRef] {
        &self.members
    }

    /// Returns all members **except** the canonical member, in declaration
    /// order. These are the places that get substituted away at
    /// [`crate::petri_net::PetriNetBuilder::build`] time.
    ///
    /// For a single-member (degenerate) set, returns an empty slice.
    pub fn non_canonical(&self) -> &[PlaceRef] {
        if self.members.len() <= 1 {
            &[]
        } else {
            &self.members[1..]
        }
    }

    /// The `TypeId` shared by all members, established by the builder's
    /// compile-time `<T>` pinning.
    pub fn type_id(&self) -> TypeId {
        self.type_id
    }

    /// Returns a fresh [`FusionSetBuilder`] with the given human-readable
    /// name.
    pub fn builder(name: impl Into<Arc<str>>) -> FusionSetBuilder {
        FusionSetBuilder::new(name)
    }

    /// Convenience factory: builds a fusion set whose first member is `first`
    /// (the canonical) and whose remaining members are `rest`, all sharing
    /// the type `<T>`.
    ///
    /// The compile-time `<T>` parameter pins every entry to a single token
    /// type — heterogeneous sequences are rejected by the type checker.
    pub fn of<T: 'static>(
        name: impl Into<Arc<str>>,
        first: &Place<T>,
        rest: &[&Place<T>],
    ) -> FusionSet {
        let mut builder = FusionSet::builder(name).member(first);
        for p in rest {
            builder = builder.member(*p);
        }
        builder.build()
    }
}

impl std::fmt::Display for FusionSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FusionSet[{}, canonical={}, members={}]",
            self.name,
            self.canonical().name(),
            self.members.len()
        )
    }
}

/// Fluent builder for [`FusionSet`].
///
/// Members are appended in call order; the first member becomes the canonical
/// place. The typed `<T>` parameter on [`Self::member`] pins all subsequent
/// members to the same token type at compile time — heterogeneous sequences
/// are rejected by the type checker.
pub struct FusionSetBuilder {
    name: Arc<str>,
    members: Vec<PlaceRef>,
    type_id: Option<TypeId>,
}

impl FusionSetBuilder {
    /// Crate-internal constructor — instances are produced exclusively by
    /// [`FusionSet::builder`].
    fn new(name: impl Into<Arc<str>>) -> Self {
        let name = name.into();
        assert!(
            !name.is_empty(),
            "FusionSet.builder: name must be a non-empty string"
        );
        Self {
            name,
            members: Vec::new(),
            type_id: None,
        }
    }

    /// Appends a member to the fusion set. The first member becomes the
    /// canonical place per the convention documented on [`FusionSet`].
    ///
    /// The `<T>` parameter pins the member's token type — every subsequent
    /// `member` call on the same builder must use the same `<T>`, otherwise
    /// the type checker rejects the call. The runtime [`TypeId`] is recorded
    /// at the first call and re-asserted defensively on subsequent calls.
    ///
    /// # Panics
    /// Panics if a member with a different runtime [`TypeId`] is added
    /// (defence-in-depth — the compile-time `<T>` already prevents this for
    /// well-typed code).
    pub fn member<T: 'static>(mut self, place: &Place<T>) -> Self {
        let new_type_id = TypeId::of::<T>();
        match self.type_id {
            None => self.type_id = Some(new_type_id),
            Some(existing) => {
                assert_eq!(
                    existing,
                    new_type_id,
                    "FusionSet '{}': member '{}' has a different runtime token type than \
                     the first member established (MOD-060)",
                    self.name,
                    place.name()
                );
            }
        }
        self.members.push(place.as_ref());
        self
    }

    /// Builds the immutable [`FusionSet`]. Validates:
    /// - The set is non-empty (single-member sets are accepted as a
    ///   structurally degenerate no-op per [MOD-060]; the empty set is
    ///   rejected as malformed).
    ///
    /// # Panics
    /// Panics when the set has zero members.
    pub fn build(self) -> FusionSet {
        assert!(
            !self.members.is_empty(),
            "FusionSet '{}': must have at least one member (MOD-060)",
            self.name
        );
        let type_id = self
            .type_id
            .expect("type_id is Some when members is non-empty");
        FusionSet {
            name: self.name,
            members: self.members,
            type_id,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fusion_set_first_member_is_canonical() {
        let a = Place::<String>::new("A");
        let b = Place::<String>::new("B");
        let c = Place::<String>::new("C");

        let set = FusionSet::builder("limiter")
            .member(&a)
            .member(&b)
            .member(&c)
            .build();

        assert_eq!(set.canonical().name(), "A");
        assert_eq!(set.members().len(), 3);
        assert_eq!(set.members()[0].name(), "A");
        assert_eq!(set.members()[1].name(), "B");
        assert_eq!(set.members()[2].name(), "C");
        assert_eq!(set.name(), "limiter");
        assert_eq!(set.type_id(), TypeId::of::<String>());
    }

    #[test]
    #[should_panic(expected = "must have at least one member")]
    fn fusion_set_empty_panics() {
        let _ = FusionSet::builder("empty").build();
    }

    #[test]
    fn fusion_set_single_member_is_valid() {
        let only = Place::<String>::new("only");

        let set = FusionSet::builder("solo").member(&only).build();

        assert_eq!(set.canonical().name(), "only");
        assert_eq!(set.members().len(), 1);
        assert_eq!(set.non_canonical().len(), 0);
    }

    #[test]
    fn fusion_set_of_factory() {
        let a = Place::<String>::new("A");
        let b = Place::<String>::new("B");
        let c = Place::<String>::new("C");

        let set = FusionSet::of("rate", &a, &[&b, &c]);

        assert_eq!(set.canonical().name(), "A");
        assert_eq!(set.members().len(), 3);
        assert_eq!(set.non_canonical().len(), 2);
        assert_eq!(set.non_canonical()[0].name(), "B");
        assert_eq!(set.non_canonical()[1].name(), "C");
    }

    #[test]
    fn fusion_set_non_canonical_returns_all_but_first() {
        let a = Place::<i32>::new("A");
        let b = Place::<i32>::new("B");
        let c = Place::<i32>::new("C");
        let d = Place::<i32>::new("D");

        let set = FusionSet::builder("ints")
            .member(&a)
            .member(&b)
            .member(&c)
            .member(&d)
            .build();

        let nc = set.non_canonical();
        assert_eq!(nc.len(), 3);
        assert_eq!(nc[0].name(), "B");
        assert_eq!(nc[1].name(), "C");
        assert_eq!(nc[2].name(), "D");
        // canonical not in non-canonical slice
        assert!(!nc.iter().any(|p| p.name() == "A"));
    }

    #[test]
    fn fusion_set_display_is_readable() {
        let a = Place::<String>::new("A");
        let b = Place::<String>::new("B");
        let set = FusionSet::of("rate", &a, &[&b]);
        let s = format!("{}", set);
        assert!(s.contains("rate"));
        assert!(s.contains("A"));
        assert!(s.contains('2'));
    }

    #[test]
    #[should_panic(expected = "name must be a non-empty string")]
    fn fusion_set_builder_rejects_empty_name() {
        let _ = FusionSet::builder("");
    }
}
