use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::action::ActionError;
use crate::token::ErasedToken;

/// Callback for emitting log messages from transition actions.
pub type LogFn = Arc<dyn Fn(&str, &str) + Send + Sync>;

/// An output entry: place name + erased token.
#[derive(Debug, Clone)]
pub struct OutputEntry {
    pub place_name: Arc<str>,
    pub token: ErasedToken,
}

/// Context provided to transition actions.
///
/// Provides filtered access based on structure:
/// - Input places (consumed tokens)
/// - Read places (context tokens, not consumed)
/// - Output places (where to produce tokens)
///
/// Enforces the structure contract — actions can only access places
/// declared in the transition's structure.
pub struct TransitionContext {
    transition_name: Arc<str>,
    inputs: HashMap<Arc<str>, Vec<ErasedToken>>,
    reads: HashMap<Arc<str>, Vec<ErasedToken>>,
    allowed_outputs: HashSet<Arc<str>>,
    outputs: Vec<OutputEntry>,
    execution_ctx: HashMap<String, Box<dyn Any + Send + Sync>>,
    log_fn: Option<LogFn>,
}

impl TransitionContext {
    pub fn new(
        transition_name: Arc<str>,
        inputs: HashMap<Arc<str>, Vec<ErasedToken>>,
        reads: HashMap<Arc<str>, Vec<ErasedToken>>,
        allowed_outputs: HashSet<Arc<str>>,
        log_fn: Option<LogFn>,
    ) -> Self {
        Self {
            transition_name,
            inputs,
            reads,
            allowed_outputs,
            outputs: Vec::new(),
            execution_ctx: HashMap::new(),
            log_fn,
        }
    }

    // ==================== Input Access (consumed) ====================

    /// Get single consumed input value. Returns error if place not declared or wrong type.
    pub fn input<T: Send + Sync + 'static>(&self, place_name: &str) -> Result<Arc<T>, ActionError> {
        let tokens = self.inputs.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared inputs"))
        })?;
        if tokens.len() != 1 {
            return Err(ActionError::new(format!(
                "Place '{place_name}' consumed {} tokens, use inputs() for batched access",
                tokens.len()
            )));
        }
        self.downcast_value::<T>(&tokens[0], place_name)
    }

    /// Get all consumed input values for a place.
    pub fn inputs<T: Send + Sync + 'static>(
        &self,
        place_name: &str,
    ) -> Result<Vec<Arc<T>>, ActionError> {
        let tokens = self.inputs.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared inputs"))
        })?;
        tokens
            .iter()
            .map(|t| self.downcast_value::<T>(t, place_name))
            .collect()
    }

    /// Get the raw (type-erased) value of the first input token.
    pub fn input_raw(&self, place_name: &str) -> Result<Arc<dyn Any + Send + Sync>, ActionError> {
        let tokens = self.inputs.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared inputs"))
        })?;
        if tokens.is_empty() {
            return Err(ActionError::new(format!(
                "No tokens for place '{place_name}'"
            )));
        }
        Ok(Arc::clone(&tokens[0].value))
    }

    /// Returns the names of all declared input places.
    pub fn input_place_names(&self) -> Vec<Arc<str>> {
        self.inputs.keys().cloned().collect()
    }

    // ==================== Read Access (not consumed) ====================

    /// Get read-only context value. Returns error if place not declared.
    pub fn read<T: Send + Sync + 'static>(&self, place_name: &str) -> Result<Arc<T>, ActionError> {
        let tokens = self.reads.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared reads"))
        })?;
        if tokens.is_empty() {
            return Err(ActionError::new(format!(
                "No tokens for read place '{place_name}'"
            )));
        }
        self.downcast_value::<T>(&tokens[0], place_name)
    }

    /// Get all read-only context values for a place.
    pub fn reads<T: Send + Sync + 'static>(
        &self,
        place_name: &str,
    ) -> Result<Vec<Arc<T>>, ActionError> {
        let tokens = self.reads.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared reads"))
        })?;
        tokens
            .iter()
            .map(|t| self.downcast_value::<T>(t, place_name))
            .collect()
    }

    /// Returns the names of all declared read places.
    pub fn read_place_names(&self) -> Vec<Arc<str>> {
        self.reads.keys().cloned().collect()
    }

    // ==================== Output Access ====================

    /// Add output value. Returns error if place not declared as output.
    pub fn output<T: Send + Sync + 'static>(
        &mut self,
        place_name: &str,
        value: T,
    ) -> Result<(), ActionError> {
        let name = self.require_output(place_name)?;
        self.outputs.push(OutputEntry {
            place_name: name,
            token: ErasedToken {
                value: Arc::new(value),
                created_at: crate::token::now_millis(),
                value_type_name: std::any::type_name::<T>(),
            },
        });
        Ok(())
    }

    /// Add a raw (type-erased) output value.
    pub fn output_raw(
        &mut self,
        place_name: &str,
        value: Arc<dyn Any + Send + Sync>,
    ) -> Result<(), ActionError> {
        let name = self.require_output(place_name)?;
        self.outputs.push(OutputEntry {
            place_name: name,
            token: ErasedToken {
                value,
                created_at: crate::token::now_millis(),
                // Raw path has already erased the static type — best we can surface.
                value_type_name: "dyn Any",
            },
        });
        Ok(())
    }

    /// Add multiple output values to the same place in a single call.
    ///
    /// Equivalent to calling [`output`](Self::output) once per element, but:
    /// - Validates the declared-output set **once** before iterating, so
    ///   an undeclared place returns `Err` before any element is appended.
    /// - Pre-reserves capacity on the internal output collector from the
    ///   iterator's `size_hint().0`.
    /// - Shares a single `created_at` timestamp across all produced tokens,
    ///   matching the "fired at time T" semantics of a single action firing.
    ///
    /// Accepts anything that implements [`IntoIterator`], including arrays,
    /// `Vec`, slice iterators, and iterator adaptors.
    ///
    /// # Example
    /// ```ignore
    /// ctx.output_many("out", [1, 2, 3])?;
    /// ctx.output_many("out", vec!["a", "b"])?;
    /// ctx.output_many("out", (0..5))?;
    /// ```
    pub fn output_many<T: Send + Sync + 'static>(
        &mut self,
        place_name: &str,
        values: impl IntoIterator<Item = T>,
    ) -> Result<(), ActionError> {
        let name = self.require_output(place_name)?;
        let iter = values.into_iter();
        let (lower, _) = iter.size_hint();
        self.outputs.reserve(lower);
        let created_at = crate::token::now_millis();
        for value in iter {
            self.outputs.push(OutputEntry {
                place_name: Arc::clone(&name),
                token: ErasedToken {
                    value: Arc::new(value),
                    created_at,
                    value_type_name: std::any::type_name::<T>(),
                },
            });
        }
        Ok(())
    }

    fn require_output(&self, place_name: &str) -> Result<Arc<str>, ActionError> {
        self.allowed_outputs
            .get(place_name)
            .cloned()
            .ok_or_else(|| {
                ActionError::new(format!(
                    "Place '{}' not in declared outputs: {:?}",
                    place_name,
                    self.allowed_outputs.iter().collect::<Vec<_>>()
                ))
            })
    }

    /// Returns the names of all declared output places.
    pub fn output_place_names(&self) -> Vec<Arc<str>> {
        self.allowed_outputs.iter().cloned().collect()
    }

    // ==================== Structure Info ====================

    /// Returns the transition name.
    pub fn transition_name(&self) -> &str {
        &self.transition_name
    }

    // ==================== Execution Context ====================

    /// Store an execution context value.
    pub fn set_execution_context<T: Send + Sync + 'static>(&mut self, key: &str, value: T) {
        self.execution_ctx.insert(key.to_string(), Box::new(value));
    }

    /// Retrieve an execution context value.
    pub fn execution_context<T: 'static>(&self, key: &str) -> Option<&T> {
        self.execution_ctx
            .get(key)
            .and_then(|v| v.downcast_ref::<T>())
    }

    /// Check if an execution context key exists.
    pub fn has_execution_context(&self, key: &str) -> bool {
        self.execution_ctx.contains_key(key)
    }

    // ==================== Logging ====================

    /// Emits a structured log message.
    pub fn log(&self, level: &str, message: &str) {
        if let Some(ref log_fn) = self.log_fn {
            log_fn(level, message);
        }
    }

    // ==================== Internal ====================

    /// Collects all output entries (used by executor).
    pub fn take_outputs(&mut self) -> Vec<OutputEntry> {
        std::mem::take(&mut self.outputs)
    }

    /// Reclaims the inputs HashMap for reuse (used by executor to avoid per-firing allocation).
    pub fn take_inputs(&mut self) -> HashMap<Arc<str>, Vec<ErasedToken>> {
        std::mem::take(&mut self.inputs)
    }

    /// Reclaims the reads HashMap for reuse (used by executor to avoid per-firing allocation).
    pub fn take_reads(&mut self) -> HashMap<Arc<str>, Vec<ErasedToken>> {
        std::mem::take(&mut self.reads)
    }

    /// Returns a reference to the output entries.
    pub fn outputs(&self) -> &[OutputEntry] {
        &self.outputs
    }

    fn downcast_value<T: Send + Sync + 'static>(
        &self,
        token: &ErasedToken,
        place_name: &str,
    ) -> Result<Arc<T>, ActionError> {
        // Try to downcast the inner Arc
        let any_arc = Arc::clone(&token.value);
        // First check if the type matches
        if any_arc.downcast_ref::<T>().is_none() {
            return Err(ActionError::new(format!(
                "Type mismatch for place '{place_name}': expected {}",
                std::any::type_name::<T>()
            )));
        }
        // Safety: we just verified the type
        let raw = Arc::into_raw(any_arc);
        let typed = unsafe { Arc::from_raw(raw.cast::<T>()) };
        Ok(typed)
    }
}

impl std::fmt::Debug for TransitionContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TransitionContext")
            .field("transition_name", &self.transition_name)
            .field("input_count", &self.inputs.len())
            .field("read_count", &self.reads.len())
            .field("output_count", &self.outputs.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx_with_output(place_name: &str) -> TransitionContext {
        let mut allowed = HashSet::new();
        allowed.insert(Arc::<str>::from(place_name));
        TransitionContext::new(
            Arc::from("T"),
            HashMap::new(),
            HashMap::new(),
            allowed,
            None,
        )
    }

    fn downcast_values<T: Send + Sync + 'static + Clone>(ctx: &TransitionContext) -> Vec<T> {
        ctx.outputs()
            .iter()
            .map(|e| (*e.token.value.downcast_ref::<T>().unwrap()).clone())
            .collect()
    }

    #[test]
    fn output_many_from_array_appends_in_order() {
        let mut ctx = ctx_with_output("out");
        ctx.output_many("out", [1, 2, 3]).unwrap();
        assert_eq!(downcast_values::<i32>(&ctx), vec![1, 2, 3]);
        assert!(ctx.outputs().iter().all(|e| &*e.place_name == "out"));
    }

    #[test]
    fn output_many_from_vec() {
        let mut ctx = ctx_with_output("out");
        ctx.output_many("out", vec!["a".to_string(), "b".to_string()])
            .unwrap();
        assert_eq!(
            downcast_values::<String>(&ctx),
            vec!["a".to_string(), "b".to_string()]
        );
    }

    #[test]
    fn output_many_from_range_iterator() {
        let mut ctx = ctx_with_output("out");
        ctx.output_many("out", 0..5i32).unwrap();
        assert_eq!(downcast_values::<i32>(&ctx), vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn output_many_empty_is_ok_and_no_op() {
        let mut ctx = ctx_with_output("out");
        let empty: [i32; 0] = [];
        ctx.output_many("out", empty).unwrap();
        assert!(ctx.outputs().is_empty());
    }

    #[test]
    fn output_many_undeclared_place_errors_before_appending() {
        let mut ctx = ctx_with_output("out");
        let err = ctx.output_many("nope", [1, 2, 3]).unwrap_err();
        assert!(format!("{err:?}").contains("not in declared outputs"));
        assert!(ctx.outputs().is_empty());
    }

    #[test]
    fn output_many_shares_timestamp_across_tokens() {
        let mut ctx = ctx_with_output("out");
        ctx.output_many("out", [10i32, 20, 30]).unwrap();
        let ts: Vec<_> = ctx.outputs().iter().map(|e| e.token.created_at).collect();
        assert_eq!(ts.len(), 3);
        assert!(ts.windows(2).all(|w| w[0] == w[1]));
    }

    #[test]
    fn single_output_still_works_alongside_output_many() {
        // Smoke test: the existing output() path is untouched by the bulk addition.
        let mut ctx = ctx_with_output("out");
        ctx.output("out", 42i32).unwrap();
        ctx.output_many("out", [43, 44]).unwrap();
        assert_eq!(downcast_values::<i32>(&ctx), vec![42, 43, 44]);
    }
}
