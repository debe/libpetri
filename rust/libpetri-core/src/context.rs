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
            },
        });
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
