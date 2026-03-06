use std::sync::Arc;

use libpetri_core::token::ErasedToken;

/// An external event to inject into the executor.
#[derive(Debug, Clone)]
pub struct ExternalEvent {
    pub place_name: Arc<str>,
    pub token: ErasedToken,
}
