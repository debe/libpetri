use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use crate::context::TransitionContext;

/// Error returned by transition actions.
#[derive(Debug, Clone)]
pub struct ActionError {
    pub message: String,
}

impl ActionError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for ActionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ActionError: {}", self.message)
    }
}

impl std::error::Error for ActionError {}

/// The action executed when a transition fires.
///
/// Actions can be sync or async. Sync actions execute inline during the
/// firing phase for maximum performance. Async actions are dispatched
/// to the runtime.
pub trait TransitionAction: Send + Sync {
    /// Returns true if this action can execute synchronously.
    fn is_sync(&self) -> bool {
        false
    }

    /// Execute the action synchronously. Called when `is_sync()` returns true.
    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError>;

    /// Execute the action asynchronously.
    /// Default implementation calls `run_sync`.
    fn run_async<'a>(
        &'a self,
        mut ctx: TransitionContext,
    ) -> Pin<Box<dyn Future<Output = Result<TransitionContext, ActionError>> + Send + 'a>> {
        Box::pin(async move {
            self.run_sync(&mut ctx)?;
            Ok(ctx)
        })
    }
}

/// Type alias for boxed transition actions.
pub type BoxedAction = Arc<dyn TransitionAction>;

// ==================== Built-in Actions ====================

/// Identity action: produces no outputs. Executes synchronously.
pub fn passthrough() -> BoxedAction {
    Arc::new(Passthrough)
}

struct Passthrough;

impl TransitionAction for Passthrough {
    fn is_sync(&self) -> bool {
        true
    }

    fn run_sync(&self, _ctx: &mut TransitionContext) -> Result<(), ActionError> {
        Ok(())
    }
}

/// Transform action: applies function to context, copies result to ALL output places.
pub fn transform<F>(f: F) -> BoxedAction
where
    F: Fn(&mut TransitionContext) -> Arc<dyn std::any::Any + Send + Sync>
        + Send
        + Sync
        + 'static,
{
    Arc::new(Transform(f))
}

struct Transform<F>(F);

impl<F> TransitionAction for Transform<F>
where
    F: Fn(&mut TransitionContext) -> Arc<dyn std::any::Any + Send + Sync> + Send + Sync + 'static,
{
    fn is_sync(&self) -> bool {
        true
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        let result = (self.0)(ctx);
        for place_name in ctx.output_place_names() {
            ctx.output_raw(&place_name, Arc::clone(&result))?;
        }
        Ok(())
    }
}

/// Fork action: copies single input token to all outputs.
///
/// Requires exactly one input place.
pub fn fork() -> BoxedAction {
    Arc::new(Fork)
}

struct Fork;

impl TransitionAction for Fork {
    fn is_sync(&self) -> bool {
        true
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        let input_places = ctx.input_place_names();
        if input_places.len() != 1 {
            return Err(ActionError::new(format!(
                "Fork requires exactly 1 input place, found {}",
                input_places.len()
            )));
        }
        let place_name = input_places.into_iter().next().unwrap();
        let value = ctx.input_raw(&place_name)?;
        for output_name in ctx.output_place_names() {
            ctx.output_raw(&output_name, Arc::clone(&value))?;
        }
        Ok(())
    }
}

/// Produce action: produces a single token with the given value to the specified place.
pub fn produce<T: Send + Sync + 'static>(place_name: Arc<str>, value: T) -> BoxedAction {
    let value = Arc::new(value) as Arc<dyn std::any::Any + Send + Sync>;
    Arc::new(Produce {
        place_name,
        value,
    })
}

struct Produce {
    place_name: Arc<str>,
    value: Arc<dyn std::any::Any + Send + Sync>,
}

impl TransitionAction for Produce {
    fn is_sync(&self) -> bool {
        true
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        ctx.output_raw(&self.place_name, Arc::clone(&self.value))?;
        Ok(())
    }
}

/// Creates an action from a synchronous closure.
pub fn sync_action<F>(f: F) -> BoxedAction
where
    F: Fn(&mut TransitionContext) -> Result<(), ActionError> + Send + Sync + 'static,
{
    Arc::new(SyncAction(f))
}

struct SyncAction<F>(F);

impl<F> TransitionAction for SyncAction<F>
where
    F: Fn(&mut TransitionContext) -> Result<(), ActionError> + Send + Sync + 'static,
{
    fn is_sync(&self) -> bool {
        true
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        (self.0)(ctx)
    }
}

/// Creates an action from an async closure.
pub fn async_action<F, Fut>(f: F) -> BoxedAction
where
    F: Fn(TransitionContext) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Result<TransitionContext, ActionError>> + Send + 'static,
{
    Arc::new(AsyncAction(f))
}

struct AsyncAction<F>(F);

impl<F, Fut> TransitionAction for AsyncAction<F>
where
    F: Fn(TransitionContext) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Result<TransitionContext, ActionError>> + Send + 'static,
{
    fn run_sync(&self, _ctx: &mut TransitionContext) -> Result<(), ActionError> {
        Err(ActionError::new("Async action cannot run synchronously"))
    }

    fn run_async<'a>(
        &'a self,
        ctx: TransitionContext,
    ) -> Pin<Box<dyn Future<Output = Result<TransitionContext, ActionError>> + Send + 'a>> {
        Box::pin((self.0)(ctx))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn passthrough_is_sync() {
        let action = passthrough();
        assert!(action.is_sync());
    }

    #[test]
    fn fork_is_sync() {
        let action = fork();
        assert!(action.is_sync());
    }
}
