//! An open net closed by the environment its contract describes ([VER-022]).
//!
//! Each arrival group becomes ordinary net structure. A source place holds the tokens the
//! group must deliver, with one transition per target place that moves a token across. The
//! part the group may withhold gets a second source, whose tokens can also be declined by a
//! transition with no output. The contract's environment transitions, the neighbours that
//! react to what the subnet sends, join unchanged. Every interleaving of the environment's
//! steps with the subnet's own firings is then a run of the closed net. A run of the closed
//! net is quiescent only once the environment has delivered what it must and decided about
//! the rest.
//!
//! Nothing else changes. The closed net is a plain net, so the state-class graph and the
//! SMT pipeline verify it as they verify any other, and no route needs a notion of
//! environment.
//!
//! The closure uses ordinary places rather than the environment places of [VER-006] on
//! purpose. Under `AlwaysAvailable` or `Bounded(k)` an environment place never runs dry, so
//! a net with one is never quiescent, and every quiescence property holds vacuously. An
//! arrival group that runs dry after `max` tokens is what a bounded contract means.

use std::any::Any;
use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::action::{BoxedAction, fork, is_passthrough, transform};
use libpetri_core::input::one;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::{Place, PlaceRef};
use libpetri_core::transition::Transition;

use crate::marking_state::{MarkingState, MarkingStateBuilder};

use super::contract::{OpenNetContract, transition_places};

/// What an environment transition of the closure does, for the port trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentStep {
    /// Moves one token of arrival group `group` onto `place`.
    Arrival { group: usize, place: String },
    /// Declines one optional token of arrival group `group`.
    Decline { group: usize },
    /// One of the contract's own environment transitions.
    Transition,
}

/// [`EnvironmentStep`] without its payload: what a port trace marks a step as.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentStepKind {
    Arrival,
    Decline,
    Transition,
}

impl EnvironmentStepKind {
    /// `arrival`, `decline` or `transition`, as the report prints it.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Arrival => "arrival",
            Self::Decline => "decline",
            Self::Transition => "transition",
        }
    }
}

impl EnvironmentStep {
    pub fn kind(&self) -> EnvironmentStepKind {
        match self {
            Self::Arrival { .. } => EnvironmentStepKind::Arrival,
            Self::Decline { .. } => EnvironmentStepKind::Decline,
            Self::Transition => EnvironmentStepKind::Transition,
        }
    }
}

/// An open net and its environment, as one closed net.
#[derive(Debug, Clone)]
pub struct ClosedNet {
    pub net: PetriNet,
    pub initial_marking: MarkingState,
    /// Each environment transition by name, with what it does: the contract's own first,
    /// then each arrival group's, in the order the closure added them.
    pub environment: Vec<(String, EnvironmentStep)>,
    /// Places only the contract's environment transitions touch: the environment's own
    /// state. A token left on one at quiescence is never stranded.
    pub environment_places: Vec<String>,
    /// Places the contract names that no arc touches, in contract order. They join the
    /// closed net as places of their own, so every route resolves them. A clause over a
    /// place nothing writes then counts zero there, which is the finding, not an error.
    pub undeclared: Vec<String>,
}

impl ClosedNet {
    /// What the environment transition `transition` does, or `None` when the subnet fires
    /// it.
    pub fn environment_step(&self, transition: &str) -> Option<&EnvironmentStep> {
        self.environment.iter().find(|(name, _)| name == transition).map(|(_, step)| step)
    }
}

/// The action an environment transition that declares outputs gets when it has none: it
/// never runs, so what it would produce is immaterial.
fn environment_action() -> BoxedAction {
    transform(|_| Arc::new(()) as Arc<dyn Any + Send + Sync>)
}

/// Closes `net` with the environment of `contract`: its environment transitions, and for
/// arrival group `i` a source `env:arrivals[i]` holding `min` tokens and a source
/// `env:optional[i]` holding `max − min`, with transitions `env:arrive[i]:<place>` /
/// `env:arrive?[i]:<place>` moving a token onto each of the group's places, and
/// `env:decline[i]` discarding an optional one.
///
/// # Panics
/// When a name the closure would add is already taken in `net`.
pub fn close_open_net(net: &PetriNet, contract: &OpenNetContract) -> ClosedNet {
    let mut declared: HashSet<String> = net.places().iter().map(|p| p.name().to_string()).collect();
    let mut taken: HashSet<String> = declared.clone();
    taken.extend(net.transitions().iter().map(|t| t.name().to_string()));
    let fresh = |taken: &mut HashSet<String>, name: String| -> String {
        if taken.contains(&name) {
            panic!("VER-022: closing the net would add '{name}', which the net already declares");
        }
        taken.insert(name.clone());
        name
    };

    let mut environment: Vec<(String, EnvironmentStep)> = Vec::new();
    let mut environment_places: Vec<String> = Vec::new();
    for t in contract.environment() {
        environment.push((fresh(&mut taken, t.name().to_string()), EnvironmentStep::Transition));
        for p in transition_places(t) {
            if !declared.contains(&p) && !environment_places.contains(&p) {
                environment_places.push(p);
            }
        }
    }
    // Before the undeclared sweep below, so an environment place is never also reported as
    // a place the contract named and nothing declares.
    for p in &environment_places {
        taken.insert(p.clone());
        declared.insert(p.clone());
    }

    // Every place the contract names joins the closed net, a terminal's excused places
    // included — `OpenNetContract::places` leaves those out. This is also what keeps the
    // two routes deciding the same rest set: the SMT encoder resolves each sink and marker
    // through the flat net's place index and silently drops what does not resolve, while
    // the graph route matches by name and drops nothing. An arc-less excused place that
    // never got registered here would therefore lose its excuse on the SMT route alone, and
    // that route would report a stranding the graph route proves cannot happen.
    let mut undeclared: Vec<String> = Vec::new();
    let mut named = contract.places();
    named.extend(contract.terminals().iter().flat_map(|t| t.excused.iter().cloned()));
    for p in named {
        if declared.contains(&p) {
            continue;
        }
        declared.insert(p.clone());
        undeclared.push(p);
    }

    let mut env_transitions: Vec<Transition> = Vec::new();
    let mut marking = MarkingStateBuilder::new();
    for (place, count) in contract.initial_tokens() {
        marking = marking.tokens(place.as_str(), *count);
    }
    for (i, group) in contract.arrivals().iter().enumerate() {
        if group.min > 0 {
            let source = Place::<()>::new(fresh(&mut taken, format!("env:arrivals[{i}]")));
            marking = marking.tokens(source.name(), group.min);
            for p in &group.places {
                let name = fresh(&mut taken, format!("env:arrive[{i}]:{p}"));
                env_transitions.push(arrival_transition(&name, &source, p));
                environment.push((name, EnvironmentStep::Arrival { group: i, place: p.clone() }));
            }
        }
        if group.max > group.min {
            let source = Place::<()>::new(fresh(&mut taken, format!("env:optional[{i}]")));
            marking = marking.tokens(source.name(), group.max - group.min);
            for p in &group.places {
                let name = fresh(&mut taken, format!("env:arrive?[{i}]:{p}"));
                env_transitions.push(arrival_transition(&name, &source, p));
                environment.push((name, EnvironmentStep::Arrival { group: i, place: p.clone() }));
            }
            let name = fresh(&mut taken, format!("env:decline[{i}]"));
            env_transitions.push(Transition::builder(name.as_str()).input(one(&source)).build());
            environment.push((name, EnvironmentStep::Decline { group: i }));
        }
    }

    // An environment transition's action never runs, so it need not produce: give one that
    // declares outputs a placeholder rather than refuse it under CORE-043.
    let placeholder: HashSet<String> = contract
        .environment()
        .iter()
        .filter(|t| t.output_spec().is_some() && is_passthrough(t.action()))
        .map(|t| t.name().to_string())
        .collect();
    let closed = PetriNet::builder(format!("{}+environment", net.name()))
        .places(net.places().iter().cloned())
        .places(undeclared.iter().map(|p| PlaceRef::new(p.as_str())))
        .transitions(net.transitions().iter().cloned())
        .transitions(contract.environment().iter().cloned())
        .transitions(env_transitions)
        .build()
        .bind_actions_with_resolver(|name| placeholder.contains(name).then(environment_action));
    ClosedNet {
        net: closed,
        initial_marking: marking.build(),
        environment,
        environment_places,
        undeclared,
    }
}

/// `name`: one token from `source` onto `target`.
fn arrival_transition(name: &str, source: &Place<()>, target: &str) -> Transition {
    Transition::builder(name)
        .input(one(source))
        .output(out_place(&Place::<()>::new(target)))
        .action(fork())
        .build()
}
