//! Shared pieces of the CTPN execution loop, used by both [`BitmapNetExecutor`]
//! and [`PrecompiledNetExecutor`].
//!
//! ## Module map
//!
//! - [`deadline`], [`event_payload`], [`output`] — pure helpers (step 1).
//! - [`backend`] — the internal seam: the
//!   [`ExecutorBackend`](backend::ExecutorBackend) trait that abstracts
//!   token storage, enablement representation, and dirty tracking.
//! - [`executor`] — the shared loop wrapper
//!   [`Executor`](executor::Executor)`<S, E>`. The struct skeleton is in
//!   place; the 5-phase loop bodies migrate here in step 3.
//!
//! [`BitmapNetExecutor`]: crate::executor::BitmapNetExecutor
//! [`PrecompiledNetExecutor`]: crate::precompiled_executor::PrecompiledNetExecutor

pub(crate) mod backend;
pub(crate) mod deadline;
pub(crate) mod event_payload;
pub mod executor;
pub(crate) mod output;
