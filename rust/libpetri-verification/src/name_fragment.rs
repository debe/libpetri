//! Name-correlation fragment classifier for the ν-aware state class graph
//! ([NU-050], Route B).
//!
//! Identifies the **coloured** places (the correlated inputs of ν-joins) and the
//! role of each transition in the supported **mint → matched-join** fragment:
//! a *mint* (fork) produces a freshly-named token into a coloured place, a *join*
//! consumes one shared name from every correlated input, and everything else is
//! *ordinary*. A net outside the fragment (a non-match transition that consumes a
//! coloured place, or a join that re-mints into one) yields `None`, and the
//! verifier falls back to the SMT / Route A path.
//!
//! Unlike Route A's [`crate::name_coloured_encoder`] classifier, this works over
//! the [`PetriNet`] (place names) rather than the flattened incidence net, and it
//! does **not** require a declared budget place — finiteness comes from the
//! symmetry quotient, not the budget. Route A is left byte-stable.

use std::collections::{BTreeSet, HashMap};

use libpetri_core::input::In;
use libpetri_core::petri_net::PetriNet;

use crate::state_class_graph::expand_transition;

/// A transition's role with respect to the coloured (correlation-carrying)
/// places.
#[derive(Debug, Clone)]
pub(crate) enum Role {
    /// Touches no coloured place.
    Ordinary,
    /// Minting fork: produces a freshly-named token. The actual coloured outputs
    /// are recomputed per XOR branch at exploration time (`expand_transition`).
    Mint,
    /// Matched join: enabled only when one shared name is present at the required
    /// multiplicity in every correlated input.
    Join {
        /// Correlated input place names with their required per-firing count,
        /// sorted by place name.
        coloured_in: Vec<(String, usize)>,
    },
}

/// Classification of a net for the name-aware SCG.
pub(crate) struct NameFragment {
    /// Coloured place names in fixed ascending order (the canonical-key order).
    pub coloured_order: Vec<String>,
    coloured: BTreeSet<String>,
    /// Role per transition name.
    roles: HashMap<String, Role>,
}

impl NameFragment {
    pub(crate) fn is_coloured(&self, place: &str) -> bool {
        self.coloured.contains(place)
    }

    pub(crate) fn role(&self, transition: &str) -> &Role {
        self.roles.get(transition).unwrap_or(&Role::Ordinary)
    }
}

/// Classifies `net`. Returns `None` when it is not a ν-net (no match transition)
/// or falls outside the supported mint→matched-join fragment.
pub(crate) fn classify(net: &PetriNet) -> Option<NameFragment> {
    // 1. Coloured places = union of every match transition's correlated inputs.
    let mut coloured: BTreeSet<String> = BTreeSet::new();
    let mut any_match = false;
    for t in net.transitions() {
        if let Some(ms) = t.match_spec() {
            any_match = true;
            for key in ms.keys() {
                coloured.insert(key.place_name().to_string());
            }
        }
    }
    if !any_match || coloured.is_empty() {
        return None;
    }

    // 2. Classify each transition; reject nets outside the fragment.
    let mut roles: HashMap<String, Role> = HashMap::new();
    for t in net.transitions() {
        let consumes_coloured = t
            .input_specs()
            .iter()
            .any(|s| coloured.contains(s.place_name()));
        let produces_coloured = expand_transition(t)
            .into_iter()
            .any(|(_, outs)| outs.iter().any(|p| coloured.contains(p)));

        let role = if let Some(ms) = t.match_spec() {
            // Matched join: consumes the correlated coloured inputs, mints none.
            if produces_coloured {
                return None; // re-mint onto a coloured place — out of fragment
            }
            let mut coloured_in: Vec<(String, usize)> = Vec::with_capacity(ms.keys().len());
            for key in ms.keys() {
                let place = key.place_name();
                // One/Exactly consume a fixed count of the matched name, which the
                // SCG step removes faithfully. All/AtLeast consume ALL matching
                // tokens at runtime — the fixed-count step would under-consume — so
                // drop those to the sound over-approximation.
                let required = match t.input_specs().iter().find(|s| s.place_name() == place) {
                    Some(In::One { .. }) => 1,
                    Some(In::Exactly { count, .. }) => *count,
                    _ => return None,
                };
                coloured_in.push((place.to_string(), required));
            }
            coloured_in.sort();
            Role::Join { coloured_in }
        } else if produces_coloured {
            // Minting fork: must not also consume a coloured place.
            if consumes_coloured {
                return None;
            }
            Role::Mint
        } else {
            // A non-match transition consuming a coloured token is unsupported
            // (the consumed name would be ambiguous).
            if consumes_coloured {
                return None;
            }
            Role::Ordinary
        };
        roles.insert(t.name().to_string(), role);
    }

    let coloured_order: Vec<String> = coloured.iter().cloned().collect();
    Some(NameFragment {
        coloured_order,
        coloured,
        roles,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::{at_least, one};
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn join_net(at_least_a: bool) -> PetriNet {
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");
        let a_in = if at_least_a { at_least(1, &a) } else { one(&a) };
        let join = Transition::builder("join")
            .input(a_in)
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .build();
        PetriNet::builder("join_net").transition(join).build()
    }

    /// java-1: an AtLeast correlated input consumes ALL matching tokens at
    /// runtime, which the fixed-count SCG step cannot model faithfully — classify
    /// must reject it so the verifier falls back to the sound over-approximation.
    #[test]
    fn at_least_correlated_input_is_rejected() {
        assert!(classify(&join_net(true)).is_none());
    }

    /// The same shape with One correlated inputs IS in the fragment.
    #[test]
    fn one_correlated_inputs_are_accepted() {
        assert!(classify(&join_net(false)).is_some());
    }
}
