//! Projector registry for turning typed token payloads into JSON.
//!
//! The archive writer and debug protocol need to surface token values as
//! `serde_json::Value`. `libpetri-event` carries tokens as `Arc<dyn TokenPayload>`
//! without any serde dependency — this registry bridges the gap.
//!
//! Users register their typed token types (`registry.register::<ClientMessage>()`)
//! once at session setup; on every `TokenAdded` / `TokenRemoved` event the debug
//! converter looks up the `TypeId` and produces a structured JSON value.
//!
//! Types that are not registered fall through to a best-effort projection:
//! `{"type": <type_name>, "text": <Debug repr>}`. This mirrors Java's
//! `{valueType, text}` fallback shape (see `NetEventSerializer` in the Java
//! implementation) and keeps the archive viewer useful even for third-party
//! token types the debug environment hasn't been taught about.

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::RwLock;

use libpetri_event::TokenPayload;
use serde::Serialize;

/// Maps `TypeId` → JSON projector for known token value types.
///
/// Register types via [`register`](Self::register) (by `T: Serialize + 'static`),
/// and project payloads via [`project`](Self::project). The registry is thread-safe
/// and cheap to share via `Arc` — lookup takes a reader lock, registration takes
/// a writer lock.
pub struct TokenProjectorRegistry {
    projectors: RwLock<HashMap<TypeId, Projector>>,
}

type Projector = Box<dyn Fn(&(dyn Any + Send + Sync)) -> serde_json::Value + Send + Sync>;

impl TokenProjectorRegistry {
    /// Creates an empty registry. Types are opt-in.
    pub fn new() -> Self {
        Self {
            projectors: RwLock::new(HashMap::new()),
        }
    }

    /// Registers a JSON projector for token values of type `T`. The registered
    /// function downcasts the inner `&dyn Any` to `&T` and serializes via serde.
    /// If downcast or serialization fails the projector returns
    /// `serde_json::Value::Null` — the caller then falls back to the
    /// type-name + Debug-repr shape.
    pub fn register<T: Serialize + Send + Sync + 'static>(&self) {
        let projector: Projector = Box::new(|any: &(dyn Any + Send + Sync)| {
            match any.downcast_ref::<T>() {
                Some(value) => serde_json::to_value(value).unwrap_or(serde_json::Value::Null),
                None => serde_json::Value::Null,
            }
        });
        self.projectors
            .write()
            .expect("TokenProjectorRegistry write lock poisoned")
            .insert(TypeId::of::<T>(), projector);
    }

    /// Projects a payload into JSON.
    ///
    /// Lookup strategy:
    /// 1. If the inner value's `TypeId` has a registered projector, use it.
    /// 2. Otherwise, fall back to `{"type": <type_name>, "text": <Debug repr>}`.
    ///
    /// Returns the projected JSON value. Never returns `None` — unregistered
    /// types produce the fallback shape so the archive viewer stays useful.
    pub fn project(&self, payload: &dyn TokenPayload) -> serde_json::Value {
        let inner = payload.value_any();
        let type_id = inner.type_id();
        if let Some(projector) = self
            .projectors
            .read()
            .expect("TokenProjectorRegistry read lock poisoned")
            .get(&type_id)
        {
            return projector(inner);
        }
        // Fallback: type name + Debug repr — matches Java's "text" shape.
        serde_json::json!({
            "type": payload.type_name(),
            "text": format!("{:?}", payload),
        })
    }
}

impl Default for TokenProjectorRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for TokenProjectorRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let projectors = self
            .projectors
            .read()
            .map(|p| p.len())
            .unwrap_or_default();
        f.debug_struct("TokenProjectorRegistry")
            .field("registered_types", &projectors)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::token::{ErasedToken, Token};
    use std::sync::Arc;

    #[derive(Serialize, Debug)]
    struct Message {
        kind: String,
        body: String,
    }

    #[test]
    fn register_and_project_roundtrip() {
        let registry = TokenProjectorRegistry::new();
        registry.register::<Message>();

        let token = Token::new(Message {
            kind: "USER".into(),
            body: "hello".into(),
        });
        let erased = ErasedToken::from_typed(&token);
        let payload: Arc<dyn TokenPayload> = Arc::new(erased);

        let json = registry.project(&*payload);
        assert_eq!(json["kind"], "USER");
        assert_eq!(json["body"], "hello");
    }

    #[test]
    fn unregistered_type_falls_back_to_text() {
        let registry = TokenProjectorRegistry::new();

        // Message is *not* registered.
        let token = Token::new(Message {
            kind: "SYSTEM".into(),
            body: "bye".into(),
        });
        let erased = ErasedToken::from_typed(&token);
        let payload: Arc<dyn TokenPayload> = Arc::new(erased);

        let json = registry.project(&*payload);
        assert_eq!(
            json["type"],
            serde_json::Value::String(std::any::type_name::<Message>().to_string())
        );
        assert!(json["text"].is_string(), "text fallback must be a string");
    }

    #[test]
    fn primitives_round_trip_when_registered() {
        let registry = TokenProjectorRegistry::new();
        registry.register::<i32>();

        let erased = ErasedToken::from_typed(&Token::new(42i32));
        let payload: Arc<dyn TokenPayload> = Arc::new(erased);
        assert_eq!(registry.project(&*payload), serde_json::json!(42));
    }
}
