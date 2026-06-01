use std::sync::Arc;

use libpetri_core::token::ErasedToken;
use libpetri_event::event_store::EventStore;
use libpetri_event::net_event::NetEvent;
use libpetri_event::token_payload::TokenPayload;

/// Constructs a [`NetEvent::TokenAdded`] event, attaching the token payload only
/// when the event store opts in via [`EventStore::CAPTURES_TOKENS`]. The const
/// gate monomorphizes the `Arc::new(token.clone())` away for production
/// (`NoopEventStore`) paths.
#[inline(always)]
pub(crate) fn token_added_event<E: EventStore>(
    place: Arc<str>,
    ts: u64,
    tok: &ErasedToken,
) -> NetEvent {
    if E::CAPTURES_TOKENS {
        let payload: Arc<dyn TokenPayload> = Arc::new(tok.clone());
        NetEvent::token_added_with(place, ts, payload)
    } else {
        NetEvent::token_added(place, ts)
    }
}

/// Companion to [`token_added_event`] for `TokenRemoved`.
#[inline(always)]
pub(crate) fn token_removed_event<E: EventStore>(
    place: Arc<str>,
    ts: u64,
    tok: &ErasedToken,
) -> NetEvent {
    if E::CAPTURES_TOKENS {
        let payload: Arc<dyn TokenPayload> = Arc::new(tok.clone());
        NetEvent::token_removed_with(place, ts, payload)
    } else {
        NetEvent::token_removed(place, ts)
    }
}
