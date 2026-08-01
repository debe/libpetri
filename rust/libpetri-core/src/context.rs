use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::action::ActionError;
use crate::name::NameId;
use crate::token::ErasedToken;

/// Callback for emitting log messages from transition actions.
pub type LogFn = Arc<dyn Fn(&str, &str) + Send + Sync>;

/// Mints a fresh ν-name. Installed by the executor so minted names are
/// monotonic and instance-prefixed per firing (spec NU-010, NU-030).
pub type FreshNameFn = Arc<dyn Fn() -> NameId + Send + Sync>;

/// Process-global fallback counter used by [`TransitionContext::fresh_name`]
/// when no executor-installed minter is present (e.g. a context constructed
/// directly in a unit test). Guarantees uniqueness; the executor installs a
/// deterministic per-run minter for replay-stable names.
static GLOBAL_FRESH_NAME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Callback that publishes a batch of output entries mid-action. Wired by
/// the async executor; see [`TransitionContext::flush`]. Sync executors do
/// not install one — sync actions complete before they can flush.
pub type FlushFn = Arc<dyn Fn(Vec<OutputEntry>) + Send + Sync>;

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
    flush_fn: Option<FlushFn>,
    /// Optional ν-name minter installed by the executor. When absent,
    /// [`fresh_name`](Self::fresh_name) falls back to a process-global counter.
    fresh_name_fn: Option<FreshNameFn>,
    /// Optional author-local → composed-name map. Inherited from the
    /// transition's [`crate::transition::Transition::local_name_map`].
    /// Bindings use it to fall back from a local-name lookup to the
    /// host name after composition. `None` when the transition is not
    /// composed (the common case).
    local_name_map: Option<Arc<HashMap<Arc<str>, Arc<str>>>>,
    /// Place names already published by [`flush`](Self::flush). `flush`
    /// *drains* the output buffer, so at completion time
    /// [`take_outputs`](Self::take_outputs) reports only what was written
    /// since the last flush. \[IO-015\] output validation unions this set
    /// with the final outputs so a streaming action is not spuriously
    /// judged to have violated its `Out` spec. Stays empty (and therefore
    /// unallocated) for actions that never flush.
    flushed_places: HashSet<Arc<str>>,
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
            flush_fn: None,
            fresh_name_fn: None,
            local_name_map: None,
            flushed_places: HashSet::new(),
        }
    }

    /// Installs a local-name → composed-name map. Wired by the
    /// executor when firing a composed transition so binding-side
    /// action contexts can fall back from local lookups to host names.
    ///
    /// **Not part of the user-facing API.** This setter exists so the
    /// runtime crate (a different compilation unit than libpetri-core)
    /// can populate the map at firing time. Calling it from outside the
    /// executor bypasses the rewriter and produces incoherent
    /// lookups — the executor is the only legitimate caller.
    #[doc(hidden)]
    pub fn set_local_name_map(&mut self, map: Arc<HashMap<Arc<str>, Arc<str>>>) {
        self.local_name_map = Some(map);
    }

    /// Returns a clone of the installed local-name map (cheap — `Arc`
    /// bump). Bindings call this from
    /// [`crate::action::TransitionAction`] adapters to thread the map
    /// into their language-side context.
    pub fn local_name_map(&self) -> Option<Arc<HashMap<Arc<str>, Arc<str>>>> {
        self.local_name_map.as_ref().map(Arc::clone)
    }

    /// Installs a mid-action flush callback. The async executor calls
    /// this before invoking the action so [`flush`](Self::flush) can
    /// publish accumulated outputs without waiting for the action to
    /// return. Sync executors do not install one.
    pub fn set_flush_fn(&mut self, flush_fn: FlushFn) {
        self.flush_fn = Some(flush_fn);
    }

    /// Returns a clone of the installed flush callback, if any. Python
    /// (or other binding) action contexts copy this so the language-side
    /// `ctx.flush()` can publish without round-tripping through the Rust
    /// context.
    pub fn flush_fn(&self) -> Option<FlushFn> {
        self.flush_fn.clone()
    }

    /// Installs the ν-name minter. Wired by the executor at firing time so
    /// that names minted by [`fresh_name`](Self::fresh_name) are monotonic
    /// across the run and instance-prefixed (spec NU-010, NU-030).
    pub fn set_fresh_name_fn(&mut self, fresh_name_fn: FreshNameFn) {
        self.fresh_name_fn = Some(fresh_name_fn);
    }

    /// Returns a clone of the installed ν-name minter, if any. Bindings copy
    /// this so a language-side `ctx.fresh_name()` mints through the same
    /// monotonic source as the Rust context.
    pub fn fresh_name_fn(&self) -> Option<FreshNameFn> {
        self.fresh_name_fn.clone()
    }

    /// Mints a fresh ν-name (the ν-binder primitive — spec NU-010).
    ///
    /// An action calls this on the fork side to create a correlation id, then
    /// writes it into the sibling output payloads (e.g. `ctx.output(place,
    /// Msg { cid: id.as_str().into(), .. })`). A later join correlates those
    /// siblings via a [`MatchSpec`](crate::match_spec::MatchSpec).
    ///
    /// Uses the executor-installed minter when present; otherwise falls back
    /// to a process-global counter prefixed by the transition name (still
    /// unique, but not replay-stable across processes).
    pub fn fresh_name(&self) -> NameId {
        match &self.fresh_name_fn {
            Some(f) => f(),
            None => {
                let n = GLOBAL_FRESH_NAME_COUNTER.fetch_add(1, Ordering::Relaxed);
                NameId::new(format!("{}#{}", self.transition_name, n))
            }
        }
    }

    /// Publishes the currently-buffered outputs immediately. Each call
    /// is its own published event boundary: if the action later fails,
    /// already-flushed tokens stay in the marking. Returns `Err` when
    /// no flush callback is installed (e.g. sync execution path).
    pub fn flush(&mut self) -> Result<(), ActionError> {
        let cb = self.flush_fn.as_ref().ok_or_else(|| {
            ActionError::new(
                "ctx.flush() is only available under async execution \
                 (run_async / start_async)",
            )
        })?;
        if self.outputs.is_empty() {
            return Ok(());
        }
        let outputs = std::mem::take(&mut self.outputs);
        // Record what leaves the buffer: `take_outputs()` at completion
        // can no longer see it, but [IO-015] validation must still count
        // it as produced.
        self.flushed_places
            .extend(outputs.iter().map(|e| Arc::clone(&e.place_name)));
        cb(outputs);
        Ok(())
    }

    /// Place names published by earlier [`flush`](Self::flush) calls.
    /// Empty unless the action streamed output mid-flight. Used by the
    /// executor for \[IO-015\] output-spec validation.
    pub fn flushed_places(&self) -> &HashSet<Arc<str>> {
        &self.flushed_places
    }

    /// Reclaims the flushed-place set (used by the executor at
    /// completion, so the common empty case moves rather than clones).
    pub fn take_flushed_places(&mut self) -> HashSet<Arc<str>> {
        std::mem::take(&mut self.flushed_places)
    }

    /// Records places published through a *copy* of this context's
    /// [`FlushFn`].
    ///
    /// Bindings (e.g. `libpetri-py`) obtain the raw callback via
    /// [`flush_fn`](Self::flush_fn) and invoke it from their own
    /// language-side context, which bypasses [`flush`](Self::flush) and
    /// therefore the automatic bookkeeping. Such a binding must report
    /// the place names back before the action completes, or \[IO-015\]
    /// validation will not count the streamed tokens.
    pub fn note_flushed(&mut self, places: impl IntoIterator<Item = Arc<str>>) {
        self.flushed_places.extend(places);
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

    /// Get all raw (type-erased) consumed input values for a place.
    pub fn input_tokens_raw(
        &self,
        place_name: &str,
    ) -> Result<Vec<Arc<dyn Any + Send + Sync>>, ActionError> {
        let tokens = self.inputs.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared inputs"))
        })?;
        Ok(tokens.iter().map(|t| Arc::clone(&t.value)).collect())
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

    /// Get all raw (type-erased) read values for a place.
    pub fn read_tokens_raw(
        &self,
        place_name: &str,
    ) -> Result<Vec<Arc<dyn Any + Send + Sync>>, ActionError> {
        let tokens = self.reads.get(place_name).ok_or_else(|| {
            ActionError::new(format!("Place '{place_name}' not in declared reads"))
        })?;
        Ok(tokens.iter().map(|t| Arc::clone(&t.value)).collect())
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
