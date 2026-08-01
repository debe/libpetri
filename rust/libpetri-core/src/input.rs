use crate::place::{Place, PlaceRef};

/// Input specification with cardinality. Purely structural (IO-006): cardinality
/// determines how many tokens to consume; there is no per-token predicate.
///
/// Conditional token selection is modeled with multiple conflicting transitions
/// and XOR-on-input semantics rather than a predicate coupled to the enablement
/// check.
///
/// Inputs are always AND-joined (all must be satisfied to enable transition).
#[derive(Clone, Debug)]
pub enum In {
    /// Consume exactly 1 token (standard CPN semantics).
    One { place: PlaceRef },
    /// Consume exactly N tokens (batching).
    Exactly { place: PlaceRef, count: usize },
    /// Consume all available tokens (must be 1+).
    All { place: PlaceRef },
    /// Wait for N+ tokens, consume all when enabled.
    AtLeast { place: PlaceRef, minimum: usize },
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
}

// ==================== Factory Functions ====================

/// Consume exactly 1 token from the place.
pub fn one<T: 'static>(place: &Place<T>) -> In {
    In::One {
        place: place.as_ref(),
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
    }
}

/// Consume all available tokens (must be 1+).
pub fn all<T: 'static>(place: &Place<T>) -> In {
    In::All {
        place: place.as_ref(),
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
}
