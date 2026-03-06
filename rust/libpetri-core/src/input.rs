use std::any::Any;
use std::sync::Arc;

use crate::place::{Place, PlaceRef};

/// Type-erased guard function.
pub type GuardFn = Arc<dyn Fn(&dyn Any) -> bool + Send + Sync>;

/// Input specification with cardinality and optional guard predicate.
///
/// CPN-compliant: cardinality determines how many tokens to consume,
/// guard filters which tokens are eligible.
///
/// Inputs are always AND-joined (all must be satisfied to enable transition).
#[derive(Clone)]
pub enum In {
    /// Consume exactly 1 token (standard CPN semantics).
    One {
        place: PlaceRef,
        guard: Option<GuardFn>,
    },
    /// Consume exactly N tokens (batching).
    Exactly {
        place: PlaceRef,
        count: usize,
        guard: Option<GuardFn>,
    },
    /// Consume all available tokens (must be 1+).
    All {
        place: PlaceRef,
        guard: Option<GuardFn>,
    },
    /// Wait for N+ tokens, consume all when enabled.
    AtLeast {
        place: PlaceRef,
        minimum: usize,
        guard: Option<GuardFn>,
    },
}

impl In {
    /// Returns the place reference for this input spec.
    pub fn place(&self) -> &PlaceRef {
        match self {
            In::One { place, .. }
            | In::Exactly { place, .. }
            | In::All { place, .. }
            | In::AtLeast { place, .. } => place,
        }
    }

    /// Returns the place name.
    pub fn place_name(&self) -> &str {
        self.place().name()
    }

    /// Returns whether this input spec has a guard.
    pub fn has_guard(&self) -> bool {
        match self {
            In::One { guard, .. }
            | In::Exactly { guard, .. }
            | In::All { guard, .. }
            | In::AtLeast { guard, .. } => guard.is_some(),
        }
    }

    /// Returns the guard function, if any.
    pub fn guard(&self) -> Option<&GuardFn> {
        match self {
            In::One { guard, .. }
            | In::Exactly { guard, .. }
            | In::All { guard, .. }
            | In::AtLeast { guard, .. } => guard.as_ref(),
        }
    }
}

impl std::fmt::Debug for In {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            In::One { place, guard } => f
                .debug_struct("One")
                .field("place", place)
                .field("has_guard", &guard.is_some())
                .finish(),
            In::Exactly {
                place,
                count,
                guard,
            } => f
                .debug_struct("Exactly")
                .field("place", place)
                .field("count", count)
                .field("has_guard", &guard.is_some())
                .finish(),
            In::All { place, guard } => f
                .debug_struct("All")
                .field("place", place)
                .field("has_guard", &guard.is_some())
                .finish(),
            In::AtLeast {
                place,
                minimum,
                guard,
            } => f
                .debug_struct("AtLeast")
                .field("place", place)
                .field("minimum", minimum)
                .field("has_guard", &guard.is_some())
                .finish(),
        }
    }
}

// ==================== Factory Functions ====================

/// Consume exactly 1 token from the place.
pub fn one<T: 'static>(place: &Place<T>) -> In {
    In::One {
        place: place.as_ref(),
        guard: None,
    }
}

/// Consume exactly 1 token matching the guard.
pub fn one_guarded<T: Send + Sync + 'static>(
    place: &Place<T>,
    guard: impl Fn(&T) -> bool + Send + Sync + 'static,
) -> In {
    In::One {
        place: place.as_ref(),
        guard: Some(Arc::new(move |v: &dyn Any| {
            v.downcast_ref::<T>().is_some_and(&guard)
        })),
    }
}

/// Consume exactly N tokens from the place.
///
/// # Panics
/// Panics if `count` is less than 1.
pub fn exactly<T: 'static>(count: usize, place: &Place<T>) -> In {
    assert!(count >= 1, "count must be >= 1, got: {count}");
    In::Exactly {
        place: place.as_ref(),
        count,
        guard: None,
    }
}

/// Consume exactly N tokens matching the guard.
///
/// # Panics
/// Panics if `count` is less than 1.
pub fn exactly_guarded<T: Send + Sync + 'static>(
    count: usize,
    place: &Place<T>,
    guard: impl Fn(&T) -> bool + Send + Sync + 'static,
) -> In {
    assert!(count >= 1, "count must be >= 1, got: {count}");
    In::Exactly {
        place: place.as_ref(),
        count,
        guard: Some(Arc::new(move |v: &dyn Any| {
            v.downcast_ref::<T>().is_some_and(&guard)
        })),
    }
}

/// Consume all available tokens (must be 1+).
pub fn all<T: 'static>(place: &Place<T>) -> In {
    In::All {
        place: place.as_ref(),
        guard: None,
    }
}

/// Consume all available tokens matching the guard.
pub fn all_guarded<T: Send + Sync + 'static>(
    place: &Place<T>,
    guard: impl Fn(&T) -> bool + Send + Sync + 'static,
) -> In {
    In::All {
        place: place.as_ref(),
        guard: Some(Arc::new(move |v: &dyn Any| {
            v.downcast_ref::<T>().is_some_and(&guard)
        })),
    }
}

/// Wait for N+ tokens, consume all when enabled.
///
/// # Panics
/// Panics if `minimum` is less than 1.
pub fn at_least<T: 'static>(minimum: usize, place: &Place<T>) -> In {
    assert!(minimum >= 1, "minimum must be >= 1, got: {minimum}");
    In::AtLeast {
        place: place.as_ref(),
        minimum,
        guard: None,
    }
}

/// Wait for N+ tokens matching guard, consume all when enabled.
///
/// # Panics
/// Panics if `minimum` is less than 1.
pub fn at_least_guarded<T: Send + Sync + 'static>(
    minimum: usize,
    place: &Place<T>,
    guard: impl Fn(&T) -> bool + Send + Sync + 'static,
) -> In {
    assert!(minimum >= 1, "minimum must be >= 1, got: {minimum}");
    In::AtLeast {
        place: place.as_ref(),
        minimum,
        guard: Some(Arc::new(move |v: &dyn Any| {
            v.downcast_ref::<T>().is_some_and(&guard)
        })),
    }
}

// ==================== Helper Functions ====================

/// Returns the minimum number of tokens required to enable.
pub fn required_count(spec: &In) -> usize {
    match spec {
        In::One { .. } => 1,
        In::Exactly { count, .. } => *count,
        In::All { .. } => 1,
        In::AtLeast { minimum, .. } => *minimum,
    }
}

/// Returns the actual number of tokens to consume given the available count.
///
/// # Panics
/// Panics if `available` is less than the required count.
pub fn consumption_count(spec: &In, available: usize) -> usize {
    let required = required_count(spec);
    assert!(
        available >= required,
        "Cannot consume from '{}': available={}, required={}",
        spec.place_name(),
        available,
        required
    );
    match spec {
        In::One { .. } => 1,
        In::Exactly { count, .. } => *count,
        In::All { .. } => available,
        In::AtLeast { .. } => available,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_required_count() {
        let p = Place::<i32>::new("p");
        let spec = one(&p);
        assert_eq!(required_count(&spec), 1);
    }

    #[test]
    fn exactly_required_count() {
        let p = Place::<i32>::new("p");
        let spec = exactly(3, &p);
        assert_eq!(required_count(&spec), 3);
    }

    #[test]
    fn all_required_count() {
        let p = Place::<i32>::new("p");
        let spec = all(&p);
        assert_eq!(required_count(&spec), 1);
    }

    #[test]
    fn at_least_required_count() {
        let p = Place::<i32>::new("p");
        let spec = at_least(5, &p);
        assert_eq!(required_count(&spec), 5);
    }

    #[test]
    fn consumption_count_one() {
        let p = Place::<i32>::new("p");
        let spec = one(&p);
        assert_eq!(consumption_count(&spec, 3), 1);
    }

    #[test]
    fn consumption_count_exactly() {
        let p = Place::<i32>::new("p");
        let spec = exactly(3, &p);
        assert_eq!(consumption_count(&spec, 5), 3);
    }

    #[test]
    fn consumption_count_all() {
        let p = Place::<i32>::new("p");
        let spec = all(&p);
        assert_eq!(consumption_count(&spec, 7), 7);
    }

    #[test]
    fn consumption_count_at_least() {
        let p = Place::<i32>::new("p");
        let spec = at_least(3, &p);
        assert_eq!(consumption_count(&spec, 5), 5);
    }

    #[test]
    #[should_panic(expected = "count must be >= 1")]
    fn exactly_zero_panics() {
        let p = Place::<i32>::new("p");
        exactly(0, &p);
    }

    #[test]
    #[should_panic(expected = "minimum must be >= 1")]
    fn at_least_zero_panics() {
        let p = Place::<i32>::new("p");
        at_least(0, &p);
    }

    #[test]
    #[should_panic(expected = "Cannot consume")]
    fn consumption_count_insufficient_panics() {
        let p = Place::<i32>::new("p");
        let spec = exactly(3, &p);
        consumption_count(&spec, 2);
    }

    #[test]
    fn guarded_input() {
        let p = Place::<i32>::new("p");
        let spec = one_guarded(&p, |v| *v > 5);
        assert!(spec.has_guard());
        let guard = spec.guard().unwrap();
        assert!(guard(&10i32 as &dyn Any));
        assert!(!guard(&3i32 as &dyn Any));
    }
}
