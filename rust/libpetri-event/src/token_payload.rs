use std::any::Any;
use std::fmt::Debug;

/// Opaque, serde-free carrier for a token value attached to a
/// [`NetEvent::TokenAdded`](crate::net_event::NetEvent::TokenAdded) or
/// [`NetEvent::TokenRemoved`](crate::net_event::NetEvent::TokenRemoved) event.
///
/// `libpetri-event` has no serde dependency, so this trait deliberately avoids
/// any serialization contract. Debug-side consumers (`libpetri-debug`) project
/// a `TokenPayload` into `serde_json::Value` via a type-id projector registry.
///
/// # Usage
///
/// - Executors wrap the in-flight token as `Arc<dyn TokenPayload>` at emit
///   time and attach it to the `token` field on `TokenAdded` / `TokenRemoved`.
///   The `Option` on that field lets production paths stay `None` when the
///   `EventStore` has opted out of token capture
///   (`EventStore::CAPTURES_TOKENS = false`).
/// - Debug consumers call [`value_any`](Self::value_any) to downcast to the
///   inner value type and project it via a registered
///   `TokenProjectorRegistry` entry.
///
/// # Why a custom trait and not `Any`
///
/// `Any` alone loses the original type name after erasure — `dyn Any` can be
/// downcast but cannot answer "what type was I?". Archive consumers need the
/// type string for display and for projector lookup, so this trait requires
/// implementers to carry it explicitly.
pub trait TokenPayload: Send + Sync + Debug + 'static {
    /// Fully-qualified Rust type name of the *inner* value (the value the
    /// user constructed their `Token<T>` around), e.g.
    /// `"my_crate::ClientMessage"`.
    ///
    /// Captured at token-creation time — see `ErasedToken::from_typed` in
    /// `libpetri-core`. Consumers treat this as an opaque display / lookup
    /// key; it is not a stable ABI.
    fn type_name(&self) -> &str;

    /// Downcast handle for the *inner* value, not the payload wrapper.
    /// Debug-side projectors key on `value_any().type_id()` to find a
    /// registered JSON serializer for the concrete type.
    fn value_any(&self) -> &(dyn Any + Send + Sync);
}
