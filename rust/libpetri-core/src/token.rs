use std::any::Any;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use libpetri_event::TokenPayload;

/// An immutable token carrying a typed value through the Petri net.
///
/// Tokens flow from place to place as transitions fire, carrying typed
/// payloads that represent the state of a computation or workflow.
#[derive(Debug, Clone)]
pub struct Token<T> {
    value: Arc<T>,
    created_at: u64,
}

impl<T> Token<T> {
    /// Creates a token with the given value and current timestamp.
    pub fn new(value: T) -> Self {
        Self {
            value: Arc::new(value),
            created_at: now_millis(),
        }
    }

    /// Creates a token with a specific timestamp (for testing/replay).
    pub fn at(value: T, created_at: u64) -> Self {
        Self {
            value: Arc::new(value),
            created_at,
        }
    }

    /// Creates a token wrapping an existing Arc value.
    pub fn from_arc(value: Arc<T>, created_at: u64) -> Self {
        Self { value, created_at }
    }

    /// Returns a reference to the token's value.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Returns a clone of the Arc-wrapped value (cheap).
    pub fn value_arc(&self) -> Arc<T> {
        Arc::clone(&self.value)
    }

    /// Returns the creation timestamp in epoch milliseconds.
    pub fn created_at(&self) -> u64 {
        self.created_at
    }
}

/// Returns a unit token (marker with no meaningful value).
/// Used for pure control flow where presence matters but data doesn't.
pub fn unit_token() -> Token<()> {
    Token {
        value: Arc::new(()),
        created_at: 0,
    }
}

/// Type-erased token for marking storage.
///
/// Carries the original value type name captured via
/// [`std::any::type_name`] at erasure time so debug consumers can surface it
/// (archive `valueType` / `TokenInfo.type`) without needing the projector
/// registry to know about the concrete type up front.
#[derive(Debug, Clone)]
pub struct ErasedToken {
    pub value: Arc<dyn Any + Send + Sync>,
    pub created_at: u64,
    /// Fully-qualified type name of the inner value, captured at
    /// [`from_typed`](Self::from_typed) time. Example:
    /// `"my_crate::ClientMessage"`. Treat as opaque display / lookup key.
    pub value_type_name: &'static str,
}

impl ErasedToken {
    /// Wraps a typed token into an erased token, recording `T`'s type name.
    pub fn from_typed<T: Send + Sync + 'static>(token: &Token<T>) -> Self {
        Self {
            value: Arc::clone(&token.value) as Arc<dyn Any + Send + Sync>,
            created_at: token.created_at,
            value_type_name: std::any::type_name::<T>(),
        }
    }

    /// Attempts to downcast back to a typed token.
    pub fn downcast<T: Send + Sync + 'static>(&self) -> Option<Token<T>> {
        self.value.downcast_ref::<T>().map(|_| {
            // Safety: we verified the type matches, so the Arc contains T
            let value = Arc::clone(&self.value);
            // SAFETY: downcast_ref confirmed the type
            let typed: Arc<T> = unsafe {
                let raw = Arc::into_raw(value);
                Arc::from_raw(raw.cast::<T>())
            };
            Token::from_arc(typed, self.created_at)
        })
    }
}

/// Lets executors attach an `ErasedToken` directly to
/// [`NetEvent::TokenAdded`](libpetri_event::net_event::NetEvent::TokenAdded) /
/// [`TokenRemoved`](libpetri_event::net_event::NetEvent::TokenRemoved) when the
/// event store has opted into token capture.
impl TokenPayload for ErasedToken {
    fn type_name(&self) -> &str {
        self.value_type_name
    }

    fn value_any(&self) -> &(dyn Any + Send + Sync) {
        &*self.value
    }
}

pub fn now_millis() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_new_has_current_timestamp() {
        let t = Token::new(42);
        assert_eq!(*t.value(), 42);
        assert!(t.created_at() > 0);
    }

    #[test]
    fn token_at_preserves_timestamp() {
        let t = Token::at("hello", 1000);
        assert_eq!(*t.value(), "hello");
        assert_eq!(t.created_at(), 1000);
    }

    #[test]
    fn unit_token_has_zero_timestamp() {
        let t = unit_token();
        assert_eq!(*t.value(), ());
        assert_eq!(t.created_at(), 0);
    }

    #[test]
    fn token_clone_is_cheap() {
        let t = Token::new(vec![1, 2, 3]);
        let t2 = t.clone();
        assert!(Arc::ptr_eq(&t.value, &t2.value));
    }

    #[test]
    fn erased_token_roundtrip() {
        let t = Token::new(42i32);
        let erased = ErasedToken::from_typed(&t);
        let recovered = erased.downcast::<i32>().unwrap();
        assert_eq!(*recovered.value(), 42);
        assert_eq!(recovered.created_at(), t.created_at());
    }

    #[test]
    fn erased_token_wrong_type_returns_none() {
        let t = Token::new(42i32);
        let erased = ErasedToken::from_typed(&t);
        assert!(erased.downcast::<String>().is_none());
    }
}
