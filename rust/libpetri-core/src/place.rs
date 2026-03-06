use std::marker::PhantomData;
use std::sync::Arc;

/// A typed place in the Petri Net that holds tokens of a specific type.
///
/// Places are the "state containers" of a Petri net. They hold tokens that
/// represent data or resources flowing through the net.
///
/// Places use name-based equality. Clone is cheap (Arc<str>).
#[derive(Debug)]
pub struct Place<T: 'static> {
    name: Arc<str>,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: 'static> Place<T> {
    /// Creates a typed place with the given name.
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            _phantom: PhantomData,
        }
    }

    /// Returns the place name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns a cheap reference to the name Arc.
    pub fn name_arc(&self) -> &Arc<str> {
        &self.name
    }

    /// Creates a type-erased PlaceRef from this place.
    pub fn as_ref(&self) -> PlaceRef {
        PlaceRef(Arc::clone(&self.name))
    }
}

impl<T: 'static> Clone for Place<T> {
    fn clone(&self) -> Self {
        Self {
            name: Arc::clone(&self.name),
            _phantom: PhantomData,
        }
    }
}

impl<T: 'static> PartialEq for Place<T> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<T: 'static> Eq for Place<T> {}

impl<T: 'static> std::hash::Hash for Place<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

/// An environment place that accepts external token injection.
/// Wraps a regular Place and marks it for external event injection.
#[derive(Debug, Clone)]
pub struct EnvironmentPlace<T: 'static> {
    place: Place<T>,
}

impl<T: 'static> EnvironmentPlace<T> {
    /// Creates an environment place with the given name.
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self {
            place: Place::new(name),
        }
    }

    /// Returns the underlying place.
    pub fn place(&self) -> &Place<T> {
        &self.place
    }

    /// Returns the place name.
    pub fn name(&self) -> &str {
        self.place.name()
    }
}

/// Type-erased reference to a place, used internally for arc storage.
///
/// Carries only the name (as Arc<str>) with no type information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlaceRef(pub(crate) Arc<str>);

impl PlaceRef {
    /// Creates a PlaceRef from a name.
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self(name.into())
    }

    /// Returns the place name.
    pub fn name(&self) -> &str {
        &self.0
    }

    /// Returns the inner Arc<str>.
    pub fn name_arc(&self) -> &Arc<str> {
        &self.0
    }
}

impl<T: 'static> From<&Place<T>> for PlaceRef {
    fn from(place: &Place<T>) -> Self {
        place.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn place_equality_by_name() {
        let p1: Place<i32> = Place::new("test");
        let p2: Place<i32> = Place::new("test");
        assert_eq!(p1, p2);
    }

    #[test]
    fn place_inequality() {
        let p1: Place<i32> = Place::new("a");
        let p2: Place<i32> = Place::new("b");
        assert_ne!(p1, p2);
    }

    #[test]
    fn place_clone_is_cheap() {
        let p: Place<i32> = Place::new("test");
        let p2 = p.clone();
        assert!(Arc::ptr_eq(p.name_arc(), p2.name_arc()));
    }

    #[test]
    fn place_ref_from_place() {
        let p: Place<i32> = Place::new("test");
        let r = PlaceRef::from(&p);
        assert_eq!(r.name(), "test");
    }

    #[test]
    fn environment_place() {
        let ep = EnvironmentPlace::<String>::new("events");
        assert_eq!(ep.name(), "events");
        assert_eq!(ep.place().name(), "events");
    }
}
