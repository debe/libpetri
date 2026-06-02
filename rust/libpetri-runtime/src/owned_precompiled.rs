//! Owned entry point for the precompiled execution path.
//!
//! [`OwnedPrecompiledNet`] caches a fully-built [`PrecompiledNet`] behind an
//! `Arc`. Compilation work (sparse masks, opcode sequences, name arcs, etc.)
//! happens once at construction; every subsequent `run_sync` / `run_async`
//! reuses the cached program. This is the FFI-safe entry point used by the
//! Python bindings — no per-call recompilation, no borrowed lifetime in the
//! type signature.

use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::petri_net::PetriNet;
use libpetri_event::event_store::EventStore;

use crate::compiled_net::CompiledNet;
#[cfg(feature = "tokio")]
use crate::environment::ExecutorSignal;
use crate::marking::Marking;
use crate::precompiled_executor::PrecompiledNetExecutor;
use crate::precompiled_net::PrecompiledNet;

/// Owned, `'static`-safe wrapper around a fully-precompiled net.
///
/// The precompiled program is built once at construction and cached in an
/// `Arc<PrecompiledNet>`; every execution call reuses it. Cloning the wrapper
/// is cheap (`Arc::clone`).
#[derive(Debug, Clone)]
pub struct OwnedPrecompiledNet {
    program: Arc<PrecompiledNet>,
}

impl OwnedPrecompiledNet {
    /// Compiles a net all the way through to a cached precompiled program.
    pub fn compile(net: &PetriNet) -> Self {
        Self::from_arc(Arc::new(CompiledNet::compile(net)))
    }

    /// Wraps an already-compiled net by Arc-promoting it once and precompiling.
    pub fn from_compiled(compiled: CompiledNet) -> Self {
        Self::from_arc(Arc::new(compiled))
    }

    /// Wraps a shared compiled net handle, precompiling it into a cached program.
    pub fn from_arc(compiled: Arc<CompiledNet>) -> Self {
        Self {
            program: Arc::new(PrecompiledNet::from_arc(compiled)),
        }
    }

    /// Returns the cached precompiled program.
    pub fn program(&self) -> &PrecompiledNet {
        &self.program
    }

    /// Returns the underlying compiled net.
    pub fn compiled(&self) -> &CompiledNet {
        self.program.compiled()
    }

    /// Returns the underlying immutable net definition.
    pub fn net(&self) -> &PetriNet {
        self.program.net()
    }

    /// Creates a consumed builder for configuring one execution.
    pub fn builder<E: EventStore>(
        &self,
        initial_marking: Marking,
    ) -> OwnedPrecompiledExecutorBuilder<E> {
        OwnedPrecompiledExecutorBuilder {
            program: Arc::clone(&self.program),
            initial_marking,
            event_store: None,
            environment_places: HashSet::new(),
            skip_output_validation: false,
            deadline_tolerance_ms: None,
        }
    }

    /// Convenience entry for a synchronous run with default options.
    pub fn run_sync<E: EventStore>(&self, initial_marking: Marking) -> Marking {
        self.builder::<E>(initial_marking).run_sync()
    }

    /// Convenience entry for an async run with default options.
    #[cfg(feature = "tokio")]
    pub async fn run_async<E: EventStore>(
        &self,
        initial_marking: Marking,
        signal_rx: tokio::sync::mpsc::UnboundedReceiver<ExecutorSignal>,
    ) -> Marking {
        self.builder::<E>(initial_marking).run_async(signal_rx).await
    }
}

/// Consumed execution builder for an owned precompiled net.
pub struct OwnedPrecompiledExecutorBuilder<E: EventStore> {
    program: Arc<PrecompiledNet>,
    initial_marking: Marking,
    event_store: Option<E>,
    environment_places: HashSet<Arc<str>>,
    skip_output_validation: bool,
    deadline_tolerance_ms: Option<f64>,
}

impl<E: EventStore> OwnedPrecompiledExecutorBuilder<E> {
    /// Sets the event store used by the run.
    pub fn event_store(mut self, store: E) -> Self {
        self.event_store = Some(store);
        self
    }

    /// Sets the environment places that keep async execution alive for event injection.
    pub fn environment_places(mut self, places: HashSet<Arc<str>>) -> Self {
        self.environment_places = places;
        self
    }

    /// Skips output validation for trusted callers.
    pub fn skip_output_validation(mut self, skip: bool) -> Self {
        self.skip_output_validation = skip;
        self
    }

    /// Sets the deadline-enforcement tolerance (ms). The grace band beyond a hard deadline
    /// (`deadline()` / `window()`) before a transition is force-disabled (TIME-013); defaults to
    /// the library value (5ms). Does not affect `exact()` transitions, enforced softly (TIME-006).
    pub fn deadline_tolerance_ms(mut self, ms: f64) -> Self {
        debug_assert!(ms >= 0.0, "deadline tolerance must be non-negative: {ms}");
        self.deadline_tolerance_ms = Some(ms);
        self
    }

    /// Runs one synchronous execution.
    pub fn run_sync(self) -> Marking {
        let mut builder = PrecompiledNetExecutor::<E>::builder(&self.program, self.initial_marking)
            .environment_places(self.environment_places)
            .skip_output_validation(self.skip_output_validation);
        if let Some(ms) = self.deadline_tolerance_ms {
            builder = builder.deadline_tolerance_ms(ms);
        }
        if let Some(store) = self.event_store {
            builder = builder.event_store(store);
        }
        let mut executor = builder.build();
        executor.run_sync().into_owned()
    }

    /// Runs one async execution.
    #[cfg(feature = "tokio")]
    pub async fn run_async(
        self,
        signal_rx: tokio::sync::mpsc::UnboundedReceiver<ExecutorSignal>,
    ) -> Marking {
        let mut builder = PrecompiledNetExecutor::<E>::builder(&self.program, self.initial_marking)
            .environment_places(self.environment_places)
            .skip_output_validation(self.skip_output_validation);
        if let Some(ms) = self.deadline_tolerance_ms {
            builder = builder.deadline_tolerance_ms(ms);
        }
        if let Some(store) = self.event_store {
            builder = builder.event_store(store);
        }
        let mut executor = builder.build();
        executor.run_async(signal_rx).await.into_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::token::Token;
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::NoopEventStore;

    fn simple_chain() -> (PetriNet, Place<i32>, Place<i32>) {
        let input = Place::<i32>::new("input");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("move")
            .input(one(&input))
            .output(out_place(&output))
            .action(fork())
            .build();
        (PetriNet::builder("chain").transition(t).build(), input, output)
    }

    #[test]
    fn run_sync_executes_through_precompiled_path() {
        let (net, input, _output) = simple_chain();
        let owned = OwnedPrecompiledNet::compile(&net);

        let mut marking = Marking::new();
        marking.add(&input, Token::at(42, 0));

        let result = owned.run_sync::<NoopEventStore>(marking);
        assert_eq!(result.count("input"), 0);
        assert_eq!(result.count("output"), 1);
    }

    #[test]
    fn builder_run_sync_with_explicit_event_store() {
        let (net, input, _output) = simple_chain();
        let owned = OwnedPrecompiledNet::compile(&net);

        let mut marking = Marking::new();
        marking.add(&input, Token::at(1, 0));

        let result = owned
            .builder::<NoopEventStore>(marking)
            .event_store(NoopEventStore)
            .skip_output_validation(false)
            .run_sync();

        assert_eq!(result.count("output"), 1);
    }

    #[test]
    fn owned_net_is_clonable() {
        let (net, _, _) = simple_chain();
        let owned = OwnedPrecompiledNet::compile(&net);
        let cloned = owned.clone();
        assert_eq!(owned.net().name(), cloned.net().name());
    }

    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn run_async_executes_with_environment_events() {
        use crate::environment::{ExecutorSignal, ExternalEvent};
        use libpetri_core::token::ErasedToken;

        let sensor = Place::<i32>::new("sensor");
        let output = Place::<i32>::new("output");
        let t = Transition::builder("emit")
            .input(one(&sensor))
            .output(out_place(&output))
            .action(fork())
            .build();
        let net = PetriNet::builder("async").transition(t).build();
        let owned = OwnedPrecompiledNet::compile(&net);

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let task = tokio::spawn({
            let owned = owned.clone();
            async move {
                owned
                    .builder::<NoopEventStore>(Marking::new())
                    .environment_places(std::iter::once(Arc::<str>::from("sensor")).collect())
                    .run_async(rx)
                    .await
            }
        });

        tx.send(ExecutorSignal::Event(ExternalEvent {
            place_name: Arc::from("sensor"),
            token: ErasedToken::from_typed(&Token::at(7, 0)),
        }))
        .unwrap();
        tx.send(ExecutorSignal::Drain).unwrap();

        let result = task.await.unwrap();
        assert_eq!(result.count("output"), 1);
    }
}
