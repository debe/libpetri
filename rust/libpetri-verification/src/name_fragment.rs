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

/// Selects which coloured-place fragment [`classify`] admits.
///
/// `Base` (default) reproduces the shipped **mint → matched-join** fragment
/// exactly. `Extended` additionally admits the opt-in **coloured-consumer**
/// role ([`Role::Consume`], drain/relay) and unions user-declared *carrier*
/// places into the coloured set (fork-threaded co-mint) — see [NU-051]. The one
/// deliberate tightening shared by both modes is the reset/read/inhibitor-on-
/// coloured guard in [`classify`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FragmentMode {
    /// Shipped mint → matched-join fragment only.
    #[default]
    Base,
    /// Base plus the coloured-consumer (drain/relay) role and carrier places.
    Extended,
}

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
    /// Coloured **consumer** (drain/relay), EXTENDED only ([NU-051]). A non-match
    /// transition that consumes **exactly one** coloured place at count **exactly
    /// one**. It *relays* the consumed name-symbol into each coloured output of
    /// the fired branch (threading `s`), or *drains* it (dead-letters `s`) when
    /// the branch produces no coloured output. Because the consumed count is
    /// fixed at one, the role carries only the input place name — no count, no
    /// list.
    ///
    /// **Documented precondition** ([NU-051]): the action MUST thread the
    /// consumed symbol (relay) or drop it (drain); it MUST NOT mint a *fresh*
    /// name into a coloured output while consuming a coloured token. Such a
    /// consume-and-remint transition is out of contract (the name layer would
    /// thread `s` where the runtime mints afresh).
    Consume {
        /// The single coloured input place consumed at count one.
        input_place: String,
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

/// Classifies `net` under `mode`. Returns `None` when it is not a ν-net (no
/// match transition) or falls outside the admitted fragment (the caller falls
/// back to the SMT / Route A path).
///
/// Under [`FragmentMode::Extended`] the declared `carriers` (intermediate places
/// that carry a fresh name from the minting fork onward to a ν-join input) are
/// unioned into the coloured set *before* role assignment, so the existing mint
/// co-mints one fresh name into all of them, and non-match transitions may take
/// the [`Role::Consume`] drain/relay role. Under [`FragmentMode::Base`] the
/// `carriers` are ignored and any non-match transition consuming a coloured
/// place rejects the net ([NU-051]).
///
/// Both modes reject a net where any coloured place carries a reset, read, or
/// inhibitor arc: those arcs would be silently misclassified `Ordinary` and the
/// name layer would drift from the base marking (a soundness guard; rejection
/// just falls back to the sound over-approximation).
pub(crate) fn classify(
    net: &PetriNet,
    mode: FragmentMode,
    carriers: &BTreeSet<String>,
) -> Option<NameFragment> {
    // 1. Coloured places = union of every match transition's correlated inputs,
    //    plus (EXTENDED only) the declared carrier places.
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
    if mode == FragmentMode::Extended {
        for c in carriers {
            coloured.insert(c.clone());
        }
    }

    // 1b. Soundness guard (BOTH modes): no coloured place may carry a reset,
    //     read, or inhibitor arc on any transition. Checked after the coloured
    //     set is finalized (a carrier could carry such an arc).
    for t in net.transitions() {
        if t.resets().iter().any(|r| coloured.contains(r.place.name()))
            || t.reads().iter().any(|r| coloured.contains(r.place.name()))
            || t
                .inhibitors()
                .iter()
                .any(|i| coloured.contains(i.place.name()))
        {
            return None;
        }
    }

    // 2. Classify each transition; reject nets outside the fragment.
    let mut roles: HashMap<String, Role> = HashMap::new();
    for t in net.transitions() {
        let coloured_inputs: Vec<&In> = t
            .input_specs()
            .iter()
            .filter(|s| coloured.contains(s.place_name()))
            .collect();
        let consumes_coloured = !coloured_inputs.is_empty();
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
        } else if consumes_coloured {
            // A non-match transition consuming a coloured token.
            match mode {
                // BASE: unsupported — the consumed name would be ambiguous.
                FragmentMode::Base => return None,
                // EXTENDED: admitted as a drain/relay ONLY when it consumes
                // exactly ONE coloured place at count EXACTLY ONE (In::One or
                // In::Exactly{count:1}). More than one coloured input, or any
                // higher / All / AtLeast count, would over-count the name layer
                // relative to the base marking (which adds exactly one token per
                // output place) — reject to the sound over-approximation.
                FragmentMode::Extended => {
                    if coloured_inputs.len() != 1 {
                        return None;
                    }
                    match coloured_inputs[0] {
                        In::One { .. } => {}
                        In::Exactly { count: 1, .. } => {}
                        _ => return None,
                    }
                    Role::Consume {
                        input_place: coloured_inputs[0].place_name().to_string(),
                    }
                }
            }
        } else if produces_coloured {
            // Minting fork: produces a coloured token, consumes none.
            Role::Mint
        } else {
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
    use libpetri_core::arc::reset;
    use libpetri_core::input::{at_least, exactly, one};
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// Empty carrier set, for the common `classify(net, mode, &no_carriers())`.
    fn no_carriers() -> BTreeSet<String> {
        BTreeSet::new()
    }

    fn carriers(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

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
        assert!(classify(&join_net(true), FragmentMode::Base, &no_carriers()).is_none());
    }

    /// The same shape with One correlated inputs IS in the fragment.
    #[test]
    fn one_correlated_inputs_are_accepted() {
        assert!(classify(&join_net(false), FragmentMode::Base, &no_carriers()).is_some());
    }

    // === EXTENDED coloured-consumer fragment ([NU-051]) ===

    /// A `mint → 2 relays → matched-join`, plus a `violation-drain` that consumes
    /// a coloured (match-key) place directly. `pre_count` sets the relay/drain
    /// input cardinality (1 for the in-fragment shape, ≥2 to trip the count-1
    /// guard). The drain consuming `branchA` (a match key) is what makes BASE
    /// reject the net.
    fn comint_relay_drain_net(relay_count: usize, drain_count: usize) -> PetriNet {
        let source = Place::<()>::new("source");
        let pre_a = Place::<String>::new("preA");
        let pre_b = Place::<String>::new("preB");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");
        let dl = Place::<()>::new("deadletter");

        let relay_in = |p: &Place<String>, c: usize| if c == 1 { one(p) } else { exactly(c, p) };

        let fork = Transition::builder("fork")
            .input(one(&source))
            .output(libpetri_core::output::and(vec![out_place(&pre_a), out_place(&pre_b)]))
            .build();
        let relay_a = Transition::builder("relayA")
            .input(relay_in(&pre_a, relay_count))
            .output(out_place(&a))
            .build();
        let relay_b = Transition::builder("relayB")
            .input(relay_in(&pre_b, relay_count))
            .output(out_place(&b))
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .build();
        let drain = Transition::builder("drain")
            .input(if drain_count == 1 { one(&a) } else { exactly(drain_count, &a) })
            .output(out_place(&dl))
            .build();

        PetriNet::builder("comint_relay_drain")
            .transitions([fork, relay_a, relay_b, join, drain])
            .build()
    }

    /// (a) EXTENDED accepts the mint → 2-relay → matched-join + violation-drain
    /// fixture (with the carriers declared); BASE rejects it (the drain consumes
    /// a coloured match-key place, which BASE cannot classify).
    #[test]
    fn extended_accepts_comint_relay_drain_base_rejects() {
        let net = comint_relay_drain_net(1, 1);
        let carriers = carriers(&["preA", "preB"]);
        assert!(
            classify(&net, FragmentMode::Extended, &carriers).is_some(),
            "EXTENDED must admit the drain/relay coloured-consumer fragment"
        );
        assert!(
            classify(&net, FragmentMode::Base, &carriers).is_none(),
            "BASE rejects a non-match transition consuming a coloured place"
        );
    }

    /// The relays and drain take the [`Role::Consume`] role naming their single
    /// coloured input; the fork is a Mint; the join is a Join.
    #[test]
    fn extended_assigns_consume_roles() {
        let net = comint_relay_drain_net(1, 1);
        let fragment = classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"]))
            .expect("in EXTENDED fragment");
        assert!(matches!(fragment.role("fork"), Role::Mint));
        assert!(matches!(fragment.role("join"), Role::Join { .. }));
        assert!(matches!(fragment.role("relayA"), Role::Consume { input_place } if input_place == "preA"));
        assert!(matches!(fragment.role("drain"), Role::Consume { input_place } if input_place == "branchA"));
    }

    /// (b) Blocker-1 regression: a coloured *relay* consuming `In::Exactly(2)`
    /// would re-emit 2 name-symbols into a coloured output while the base marking
    /// adds only 1 → the name layer over-counts → EXTENDED classify must reject.
    #[test]
    fn extended_rejects_relay_consuming_count_two() {
        let net = comint_relay_drain_net(2, 1);
        assert!(
            classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"])).is_none(),
            "a coloured consumer at count 2 must be rejected (Blocker 1)"
        );
    }

    /// (c) Blocker-2 regression: a name-blind *drain* consuming `In::Exactly(2)`
    /// from a coloured place must also be rejected (count != 1) → the verifier
    /// falls back rather than dropping a base-enabled firing.
    #[test]
    fn extended_rejects_drain_consuming_count_two() {
        let net = comint_relay_drain_net(1, 2);
        assert!(
            classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"])).is_none(),
            "a coloured drain at count 2 must be rejected (Blocker 2)"
        );
    }

    /// (e) A reset arc on a coloured place makes classify return None in BOTH
    /// modes (the reset would zero the place while the name layer keeps its
    /// symbol, breaking the count == name-total invariant).
    #[test]
    fn reset_on_coloured_place_rejected_both_modes() {
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let scratch = Place::<()>::new("scratch");
        let merged = Place::<String>::new("merged");

        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .build();
        // An unrelated transition carries a reset arc on the coloured `branchA`.
        let clear = Transition::builder("clear")
            .input(one(&scratch))
            .resets(vec![reset(&a)])
            .build();
        let net = PetriNet::builder("reset_on_coloured")
            .transitions([join, clear])
            .build();

        assert!(
            classify(&net, FragmentMode::Base, &no_carriers()).is_none(),
            "reset on a coloured place is rejected under BASE"
        );
        assert!(
            classify(&net, FragmentMode::Extended, &no_carriers()).is_none(),
            "reset on a coloured place is rejected under EXTENDED"
        );
    }
}
