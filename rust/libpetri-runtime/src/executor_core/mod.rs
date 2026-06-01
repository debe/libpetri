//! Shared pieces of the CTPN execution loop, used by both [`BitmapNetExecutor`]
//! and [`PrecompiledNetExecutor`].
//!
//! ## Module map
//!
//! - [`deadline`], [`event_payload`], [`output`] — pure helpers.
//! - [`backend`] — the internal seam: the
//!   [`ExecutorBackend`](backend::ExecutorBackend) trait that abstracts
//!   token storage, enablement representation, and dirty tracking.
//! - [`executor`] — the shared loop [`Executor`](executor::Executor)`<S, E>`,
//!   which drives the 6-phase CTPN cycle against a backend `S` (sync and,
//!   under the `tokio` feature, async).
//!
//! [`BitmapNetExecutor`]: crate::executor::BitmapNetExecutor
//! [`PrecompiledNetExecutor`]: crate::precompiled_executor::PrecompiledNetExecutor

pub(crate) mod backend;
pub(crate) mod deadline;
pub(crate) mod event_payload;
pub mod executor;
pub(crate) mod output;
