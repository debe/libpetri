//! Shared pieces of the CTPN execution loop, used by both [`BitmapNetExecutor`]
//! and [`PrecompiledNetExecutor`].
//!
//! Step 1 of the executor-backend-seam refactor: pure helpers only. The shared
//! loop itself and the `ExecutorBackend` trait land in later steps.
//!
//! [`BitmapNetExecutor`]: crate::executor::BitmapNetExecutor
//! [`PrecompiledNetExecutor`]: crate::precompiled_executor::PrecompiledNetExecutor

pub(crate) mod deadline;
pub(crate) mod event_payload;
pub(crate) mod output;
