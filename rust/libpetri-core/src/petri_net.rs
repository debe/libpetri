use std::collections::HashSet;
use std::sync::Arc;

use crate::action::BoxedAction;
use crate::place::PlaceRef;
use crate::transition::{Transition, rebuild_with_action};

/// Immutable definition of a Time Petri Net structure.
///
/// A PetriNet is a reusable definition that can be executed multiple times
/// with different initial markings. Places are auto-collected from transitions.
#[derive(Debug, Clone)]
pub struct PetriNet {
    name: Arc<str>,
    places: HashSet<PlaceRef>,
    transitions: Vec<Transition>,
}

impl PetriNet {
    /// Returns the net name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the set of all places in the net.
    pub fn places(&self) -> &HashSet<PlaceRef> {
        &self.places
    }

    /// Returns the transitions in the net.
    pub fn transitions(&self) -> &[Transition] {
        &self.transitions
    }

    /// Creates a new PetriNet with actions bound to transitions by name.
    /// Transitions not in the map keep their existing action.
    pub fn bind_actions(
        &self,
        bindings: &std::collections::HashMap<String, BoxedAction>,
    ) -> PetriNet {
        self.bind_actions_with_resolver(|name| bindings.get(name).cloned())
    }

    /// Creates a new PetriNet with actions bound via a resolver function.
    /// If the resolver returns None, the transition keeps its existing action.
    pub fn bind_actions_with_resolver(
        &self,
        resolver: impl Fn(&str) -> Option<BoxedAction>,
    ) -> PetriNet {
        let transitions: Vec<Transition> = self
            .transitions
            .iter()
            .map(|t: &Transition| {
                if let Some(action) = resolver(t.name()) {
                    rebuild_with_action(t, action)
                } else {
                    t.clone()
                }
            })
            .collect();

        PetriNet {
            name: Arc::clone(&self.name),
            places: self.places.clone(),
            transitions,
        }
    }

    /// Creates a new PetriNetBuilder.
    pub fn builder(name: impl Into<Arc<str>>) -> PetriNetBuilder {
        PetriNetBuilder::new(name)
    }
}

/// Builder for constructing PetriNet instances.
pub struct PetriNetBuilder {
    name: Arc<str>,
    places: HashSet<PlaceRef>,
    transitions: Vec<Transition>,
}

impl PetriNetBuilder {
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            places: HashSet::new(),
            transitions: Vec::new(),
        }
    }

    /// Add an explicit place.
    pub fn place(mut self, place: PlaceRef) -> Self {
        self.places.insert(place);
        self
    }

    /// Add explicit places.
    pub fn places(mut self, places: impl IntoIterator<Item = PlaceRef>) -> Self {
        self.places.extend(places);
        self
    }

    /// Add a transition (auto-collects places from arcs).
    pub fn transition(mut self, transition: Transition) -> Self {
        // Auto-collect places
        for spec in transition.input_specs() {
            self.places.insert(spec.place().clone());
        }
        for p in transition.output_places() {
            self.places.insert(p.clone());
        }
        for inh in transition.inhibitors() {
            self.places.insert(inh.place.clone());
        }
        for r in transition.reads() {
            self.places.insert(r.place.clone());
        }
        for r in transition.resets() {
            self.places.insert(r.place.clone());
        }
        self.transitions.push(transition);
        self
    }

    /// Add multiple transitions.
    pub fn transitions(mut self, transitions: impl IntoIterator<Item = Transition>) -> Self {
        for t in transitions {
            self = self.transition(t);
        }
        self
    }

    /// Build the PetriNet.
    pub fn build(self) -> PetriNet {
        PetriNet {
            name: self.name,
            places: self.places,
            transitions: self.transitions,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;

    #[test]
    fn petri_net_builder_auto_collects_places() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();

        let net = PetriNet::builder("test").transition(t).build();

        assert_eq!(net.places().len(), 2);
        assert!(net.places().contains(&PlaceRef::new("p1")));
        assert!(net.places().contains(&PlaceRef::new("p2")));
        assert_eq!(net.transitions().len(), 1);
    }

    #[test]
    fn petri_net_explicit_places() {
        let net = PetriNet::builder("test")
            .place(PlaceRef::new("orphan"))
            .build();

        assert_eq!(net.places().len(), 1);
        assert!(net.places().contains(&PlaceRef::new("orphan")));
    }

    #[test]
    fn petri_net_bind_actions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();

        let net = PetriNet::builder("test").transition(t).build();
        assert!(net.transitions()[0].action().is_sync());

        // Bind a new action
        let mut bindings = std::collections::HashMap::new();
        bindings.insert("t1".to_string(), crate::action::passthrough());
        let net2 = net.bind_actions(&bindings);
        assert_eq!(net2.transitions().len(), 1);
        assert_eq!(net2.transitions()[0].name(), "t1");
    }

    #[test]
    fn petri_net_collects_inhibitor_read_reset_places() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let p_inh = Place::<i32>::new("inh");
        let p_read = Place::<i32>::new("read");
        let p_reset = Place::<i32>::new("reset");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .inhibitor(crate::arc::inhibitor(&p_inh))
            .read(crate::arc::read(&p_read))
            .reset(crate::arc::reset(&p_reset))
            .build();

        let net = PetriNet::builder("test").transition(t).build();
        assert_eq!(net.places().len(), 5);
    }
}
