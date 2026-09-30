use std::collections::HashMap;

use libpetri_core::input::{self, In};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::transition::Transition;

use crate::branch_outcomes;
use crate::reaping;

/// One way a firing of a transition can end ([`branch_outcomes::outcomes`]), with its
/// pre and post vectors. A transition with one outcome gives one flat transition under
/// its own name; one with several gives one per outcome, named `<name>_b<i>`, every
/// outcome sharing the transition's pre vector and arcs.
///
/// `#[non_exhaustive]`: build one outside this crate with [`FlatTransition::new`] and
/// the `with_*` setters.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct FlatTransition {
    pub name: String,
    pub pre: Vec<i64>,
    pub post: Vec<i64>,
    pub inhibitor_places: Vec<usize>,
    pub read_places: Vec<usize>,
    pub reset_places: Vec<usize>,
    pub consume_all: Vec<usize>,
    /// Whether the executor can reap the source transition ([TIME-013]): a `deadline`
    /// or `window` one, unless the caller assumes no reaping. Its enabledness then does
    /// not keep a marking from resting, so every quiescence encoding skips it
    /// ([VER-002] reap-quiescence, [`crate::reaping`]).
    pub reapable: bool,
}

impl FlatTransition {
    /// A flat transition named `name` with these pre and post vectors, no inhibitor,
    /// read, reset or drained place, and not reapable.
    pub fn new(name: impl Into<String>, pre: Vec<i64>, post: Vec<i64>) -> Self {
        Self {
            name: name.into(),
            pre,
            post,
            inhibitor_places: Vec::new(),
            read_places: Vec::new(),
            reset_places: Vec::new(),
            consume_all: Vec::new(),
            reapable: false,
        }
    }

    /// Sets the place indices an inhibitor arc tests.
    pub fn with_inhibitor_places(mut self, places: Vec<usize>) -> Self {
        self.inhibitor_places = places;
        self
    }

    /// Sets the place indices a read arc tests.
    pub fn with_read_places(mut self, places: Vec<usize>) -> Self {
        self.read_places = places;
        self
    }

    /// Sets the place indices a reset arc clears.
    pub fn with_reset_places(mut self, places: Vec<usize>) -> Self {
        self.reset_places = places;
        self
    }

    /// Sets the place indices an `all` / `at_least` input drains.
    pub fn with_consume_all(mut self, places: Vec<usize>) -> Self {
        self.consume_all = places;
        self
    }

    /// Sets whether the executor can reap the source transition ([TIME-013]).
    pub fn with_reapable(mut self, reapable: bool) -> Self {
        self.reapable = reapable;
        self
    }
}

/// A flattened net ready for matrix computation and SMT encoding.
#[derive(Debug, Clone)]
pub struct FlatNet {
    pub places: Vec<String>,
    pub place_index: HashMap<String, usize>,
    pub place_count: usize,
    pub transitions: Vec<FlatTransition>,
}

/// Flattens a PetriNet: each way a firing can end ([`branch_outcomes::outcomes`]) is a flat transition.
///
/// A flat transition is [`reapable`](FlatTransition::reapable) exactly when its source
/// transition's timing is ([`reaping::is_reapable`]).
pub fn flatten(net: &PetriNet) -> FlatNet {
    flatten_with_reapable(net, &|t| reaping::is_reapable(t.timing()))
}

/// [`flatten`] with the caller deciding which source transitions are reapable: none
/// under `assume_no_reaping`, or a set named before a rewrite dropped the timing.
pub fn flatten_with_reapable(net: &PetriNet, reapable: &dyn Fn(&Transition) -> bool) -> FlatNet {
    // Collect and sort places for stable indexing
    let mut places: Vec<String> = net.places().iter().map(|p| p.name().to_string()).collect();
    places.sort();
    places.dedup();

    let place_count = places.len();
    let place_index: HashMap<String, usize> = places
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), i))
        .collect();

    let mut flat_transitions = Vec::new();

    for t in net.transitions() {
        // Build pre vector from input specs
        let mut base_pre = vec![0i64; place_count];
        let mut consume_all_places = Vec::new();

        for spec in t.input_specs() {
            let pid = place_index[spec.place_name()];
            let required = input::required_count(spec) as i64;
            base_pre[pid] += required;
            if matches!(spec, In::All { .. } | In::AtLeast { .. }) {
                consume_all_places.push(pid);
            }
        }

        // Inhibitor places
        let inhibitor_places: Vec<usize> = t
            .inhibitors()
            .iter()
            .map(|inh| place_index[inh.place.name()])
            .collect();

        // Read places
        let read_places: Vec<usize> = t
            .reads()
            .iter()
            .map(|r| place_index[r.place.name()])
            .collect();

        // Reset places
        let reset_places: Vec<usize> = t
            .resets()
            .iter()
            .map(|r| place_index[r.place.name()])
            .collect();

        // Build post vectors: one flat transition per way a firing can end
        // (`branch_outcomes`): each branch the action may write, one token per place
        // ([IO-016]), then the timeout outcome when it deposits differently — only the
        // timeout child's places, a forward depositing one token per consumed token
        // ([IO-013] AC5, [IO-014]).
        let outcomes = branch_outcomes::outcomes(t);
        let single = outcomes.len() == 1;
        for (bi, outcome) in outcomes.iter().enumerate() {
            let mut post = vec![0i64; place_count];
            // A forward of an `All` / `AtLeast` input deposits the drained batch, which
            // no post vector can hold; its minimum stands in, and the verifier refuses
            // the net before any flat route reads it (`branch_outcomes::drained_forward`);
            // the graph routes, which count the batch, decide it first.
            let minimum = |from: &str| {
                t.input_specs()
                    .iter()
                    .find(|s| s.place_name() == from)
                    .map_or(0, input::required_count)
            };
            for (place, n) in outcome.resolved(minimum) {
                post[place_index[place]] += n as i64;
            }
            flat_transitions.push(FlatTransition {
                name: if single {
                    t.name().to_string()
                } else {
                    format!("{}_b{}", t.name(), bi)
                },
                pre: base_pre.clone(),
                post,
                inhibitor_places: inhibitor_places.clone(),
                read_places: read_places.clone(),
                reset_places: reset_places.clone(),
                consume_all: consume_all_places.clone(),
                reapable: reapable(t),
            });
        }
    }

    FlatNet {
        places,
        place_index,
        place_count,
        transitions: flat_transitions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::{out_place, xor};
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn flatten_simple() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.place_count, 2);
        assert_eq!(flat.transitions.len(), 1);
        assert_eq!(flat.transitions[0].name, "t1");
    }

    /// [IO-014]: the timeout outcome of `xor(c, timeout(forward_input(a, b)))` on an
    /// `Exactly(2)` input deposits two tokens in `b`, as its own row after the two branches
    /// the action may write.
    #[test]
    fn flatten_forward_deposits_every_consumed_token() {
        use libpetri_core::input::exactly;
        use libpetri_core::output::{forward_input, timeout};
        let (a, b, c) = (Place::<i32>::new("a"), Place::<i32>::new("b"), Place::<i32>::new("c"));
        let t = Transition::builder("t")
            .input(exactly(2, &a))
            .output(xor(vec![out_place(&c), timeout(50, forward_input(&a, &b))]))
            .action(fork())
            .build();
        let flat = flatten(&PetriNet::builder("test").transition(t).build());
        let names: Vec<&str> = flat.transitions.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(names, ["t_b0", "t_b1", "t_b2"]);
        let (ia, ib, ic) = (flat.place_index["a"], flat.place_index["b"], flat.place_index["c"]);
        assert!(flat.transitions.iter().all(|t| t.pre[ia] == 2));
        let posts: Vec<(i64, i64)> = flat.transitions.iter().map(|t| (t.post[ib], t.post[ic])).collect();
        assert_eq!(posts, [(0, 1), (1, 0), (2, 0)]);
    }

    #[test]
    fn flatten_xor_expands() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(xor(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions.len(), 2);
        assert_eq!(flat.transitions[0].name, "t1_b0");
        assert_eq!(flat.transitions[1].name, "t1_b1");
    }
}
