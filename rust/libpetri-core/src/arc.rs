use crate::place::{Place, PlaceRef};

/// Inhibitor arc: blocks transition if place has tokens.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Inhibitor {
    pub place: PlaceRef,
}

/// Read arc: requires token without consuming.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Read {
    pub place: PlaceRef,
}

/// Reset arc: removes all tokens from place when firing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Reset {
    pub place: PlaceRef,
}

/// Creates an inhibitor arc for the given place.
pub fn inhibitor<T: 'static>(place: &Place<T>) -> Inhibitor {
    Inhibitor {
        place: place.as_ref(),
    }
}

/// Creates a read arc for the given place.
pub fn read<T: 'static>(place: &Place<T>) -> Read {
    Read {
        place: place.as_ref(),
    }
}

/// Creates a reset arc for the given place.
pub fn reset<T: 'static>(place: &Place<T>) -> Reset {
    Reset {
        place: place.as_ref(),
    }
}
