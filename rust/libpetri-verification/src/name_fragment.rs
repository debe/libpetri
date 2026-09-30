//! Name-correlation fragment classifier for the ν-aware state class graph
//! ([NU-050], Route B).
//!
//! Identifies the **coloured** places (the correlated inputs of ν-joins) and the
//! role of each transition in the supported **mint → matched-join** fragment:
//! a *mint* (a declared fork) produces a freshly-named token into a coloured place, a *join*
//! consumes one shared name from every correlated input, and everything else is
//! *ordinary*. A net outside the fragment (a non-match transition that consumes a
//! coloured place, or a join that re-mints into one) yields `None`, and the
//! verifier falls back to the SMT / Route A path.
//!
//! Unlike Route A's [`crate::name_coloured_encoder`] classifier, this works over
//! the [`PetriNet`] (place names) rather than the flattened incidence net, and it
//! does **not** require a declared budget place for finiteness: that comes from the
//! symmetry quotient. A mint must still be declared ([NU-010]), by name or by
//! consuming a declared budget place ([`declared_mints`]), because nothing in the
//! net tells a minting action from one that copies a correlation id.

use std::collections::{BTreeSet, HashMap};

use libpetri_core::input::In;
use libpetri_core::petri_net::PetriNet;

use crate::branch_outcomes::{Deposit, TimeoutWrite, timeout_writes};
use crate::state_class_graph::expand_transition;

/// Selects which coloured-place fragment [`classify`] admits.
///
/// `Base` (default) reproduces the shipped **mint → matched-join** fragment
/// exactly. `Extended` additionally admits the opt-in **coloured-consumer**
/// role ([`Role::Consume`], drain/relay) and unions user-declared *carrier*
/// places into the coloured set (fork-threaded co-mint) — see [NU-051] — and
/// the declared relay targets of every join ([NU-054]), onto which a join
/// writes the name it matched. The one
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
        /// Declared relay targets ([NU-054], EXTENDED only): a firing on symbol
        /// `s` removes `s` from the keys, then adds `s` once to each relay
        /// target in the fired branch. Empty under BASE and for a join that
        /// drains the name.
        relay_to: BTreeSet<String>,
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

/// The report line naming the ν contracts a verdict rests on ([NU-010], [NU-051]):
/// the transitions read as mints, and the coloured consumers whose action writes are
/// read as relays. Empty when there are none. The analyses cannot check what an
/// action writes, so a verdict holds only while these actions keep the contracts.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn contract_note(mints: &[String], relays: &[String]) -> String {
    let mut out = String::new();
    if !mints.is_empty() {
        out.push_str(&format!(
            "Mint contract (NU-010) assumed for {}: each writes a freshly minted name into every coloured place it writes.\n",
            mints.join(", ")
        ));
    }
    if !relays.is_empty() {
        out.push_str(&format!(
            "Relay contract (NU-051) assumed for {}: each writes the name it consumed into every coloured place it writes.\n",
            relays.join(", ")
        ));
    }
    out
}

/// Classification of a net for the name-aware SCG.
pub(crate) struct NameFragment {
    /// Coloured place names in fixed ascending order (the canonical-key order).
    pub coloured_order: Vec<String>,
    coloured: BTreeSet<String>,
    /// Role per transition name.
    roles: HashMap<String, Role>,
    /// The transitions read as mints, in net order: the analysis trusts the mint
    /// contract of [NU-010] for them.
    #[cfg_attr(not(feature = "z3"), allow(dead_code))]
    pub mints: Vec<String>,
    /// The coloured consumers that write a coloured place, in net order: the analysis
    /// trusts the relay contract of [NU-051] for their action writes.
    #[cfg_attr(not(feature = "z3"), allow(dead_code))]
    pub relays: Vec<String>,
}

impl NameFragment {
    pub(crate) fn is_coloured(&self, place: &str) -> bool {
        self.coloured.contains(place)
    }

    pub(crate) fn role(&self, transition: &str) -> &Role {
        self.roles.get(transition).unwrap_or(&Role::Ordinary)
    }
}

/// The transitions of `net` declared to mint ([NU-010]): each one named in
/// `explicit` (the verifier's `mint_transitions`), plus each one that consumes a
/// declared budget place, since a budget token is what a fork consumes when it mints
/// ([NU-040]). A name in `explicit` that is not a transition of `net` is kept; the
/// verifier rejects it before any route runs.
pub fn declared_mints(
    net: &PetriNet,
    budget_places: &std::collections::HashSet<String>,
    explicit: &std::collections::HashSet<String>,
) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = explicit.iter().cloned().collect();
    for t in net.transitions() {
        if t.input_specs().iter().any(|s| budget_places.contains(s.place_name())) {
            out.insert(t.name().to_string());
        }
    }
    out
}

/// Why a mint declaration ([NU-010]) cannot be used on `net`: the declared names that
/// are not transitions of `net`, in code-point order, as
/// `declared mint transition 'x' not in the net (NU-010)`. A typo'd declaration would
/// silently leave a real mint undeclared, so every entry point rejects it:
/// `SmtVerifier::verify` answers `Unknown` with this reason,
/// `SmtVerifier::encode_scripts` panics with it, and `verify_open_net` answers `Unknown`
/// with it before either route runs. `None` when every name is a transition of `net`.
pub fn unknown_mint_reason<'a>(net: &PetriNet, declared: impl IntoIterator<Item = &'a String>) -> Option<String> {
    let mut unknown: Vec<&String> = declared
        .into_iter()
        .filter(|n| !net.transitions().iter().any(|t| t.name() == n.as_str()))
        .collect();
    if unknown.is_empty() {
        return None;
    }
    unknown.sort();
    unknown.dedup();
    Some(format!(
        "declared mint transition{} {} not in the net (NU-010)",
        if unknown.len() == 1 { "" } else { "s" },
        unknown.iter().map(|n| format!("'{n}'")).collect::<Vec<_>>().join(", ")
    ))
}

/// The transitions of `net` that write a coloured place of the fragment without
/// consuming one and are not in `mints`, in net order, when declaring them is all that
/// keeps `net` out of the fragment: [`classify`] admits `net` with every transition read
/// as a mint and rejects it with `mints`. Empty otherwise. These are the undeclared mints
/// a Route B decline points at ([NU-010]).
pub fn undeclared_mints(
    net: &PetriNet,
    mode: FragmentMode,
    carriers: &BTreeSet<String>,
    mints: &BTreeSet<String>,
) -> Vec<String> {
    if classify(net, mode, carriers, mints).is_some() {
        return Vec::new();
    }
    let every: BTreeSet<String> = net.transitions().iter().map(|t| t.name().to_string()).collect();
    match classify(net, mode, carriers, &every) {
        Some(fragment) => fragment.mints.into_iter().filter(|m| !mints.contains(m)).collect(),
        None => Vec::new(),
    }
}

/// The sentence a Route B decline adds when [`undeclared_mints`] names transitions:
/// which transitions to declare, and with what.
pub fn undeclared_mints_pointer(undeclared: &[String]) -> String {
    let names: Vec<String> = undeclared.iter().map(|t| format!("'{t}'")).collect();
    let (write, it) = if undeclared.len() == 1 { ("writes", "it") } else { ("write", "them") };
    format!(
        "{} {write} a coloured place without consuming one and {} not declared to mint (NU-010); \
         if the action writes a name minted with fresh_name, declare {it} with mint_transitions",
        names.join(", "),
        if undeclared.len() == 1 { "is" } else { "are" },
    )
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
///
/// A transition that writes a coloured place without consuming one is read as a
/// **mint** only when it is named in `mints`, the declared mint transitions
/// ([`declared_mints`]). The declaration is the net's statement that the action
/// writes a name freshly minted by `fresh_name` into each coloured place it writes
/// ([NU-010]). An action may write any value, a copied correlation id included, so
/// without the declaration the name layer cannot give the deposit a fresh symbol and
/// the net is rejected. A deposit the executor makes on timeout is never a mint,
/// declared or not: a forward copies a consumed value and an `Out::Place` writes a
/// unit token with no name ([IO-013], [IO-014]). A join's timeout may write a relay
/// target only by forwarding one of its match keys, the one write that carries the
/// matched name. The executor checks every relay deposit ([NU-054]) and fails the
/// firing on any other, so no timeout write relies on a contract.
pub(crate) fn classify(
    net: &PetriNet,
    mode: FragmentMode,
    carriers: &BTreeSet<String>,
    mints: &BTreeSet<String>,
) -> Option<NameFragment> {
    // 1. Coloured places = union of every match transition's correlated inputs,
    //    plus (EXTENDED only) the declared carrier places and every join's relay
    //    targets ([NU-054]), before the fragment rules below. BASE ignores relay
    //    declarations, as it ignores carriers.
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
        for t in net.transitions() {
            if let Some(ms) = t.match_spec() {
                for relay in ms.relays() {
                    coloured.insert(relay.place_name().to_string());
                }
            }
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
    let mut mint_names: Vec<String> = Vec::new();
    let mut relay_names: Vec<String> = Vec::new();
    for t in net.transitions() {
        let coloured_inputs: Vec<&In> = t
            .input_specs()
            .iter()
            .filter(|s| coloured.contains(s.place_name()))
            .collect();
        let consumes_coloured = !coloured_inputs.is_empty();
        let branches = expand_transition(t);
        // The name layer adds one symbol per coloured output place of a firing, as the
        // base marking adds one token per place an action writes. A timeout forward
        // deposits one token per consumed token ([IO-014]); into a coloured place at any
        // count but one, the name layer would lose track of the base marking.
        if branches.iter().any(|(_, o)| {
            o.deposits.iter().any(|(p, d)| coloured.contains(p) && *d != Deposit::Tokens(1))
        }) {
            return None;
        }
        let produces_coloured = branches
            .iter()
            .any(|(_, outs)| outs.places.iter().any(|p| coloured.contains(p)));
        // What the executor itself writes into a coloured place on timeout: a copy of
        // a consumed value (forward) or a unit token (place). Neither is a fresh name.
        let timeout_coloured: Vec<(String, TimeoutWrite)> = timeout_writes(t)
            .into_iter()
            .filter(|(p, _)| coloured.contains(p))
            .collect();

        let role = if let Some(ms) = t.match_spec() {
            // Matched join: consumes the correlated coloured inputs, and writes a
            // coloured place only as a declared relay target ([NU-054], EXTENDED);
            // any other coloured output is a re-mint — out of fragment.
            let relay_to: BTreeSet<String> = if mode == FragmentMode::Extended {
                ms.relays().iter().map(|r| r.place_name().to_string()).collect()
            } else {
                BTreeSet::new()
            };
            if branches
                .iter()
                .any(|(_, outs)| outs.places.iter().any(|p| coloured.contains(p) && !relay_to.contains(p)))
            {
                return None;
            }
            // What the executor writes into a relay target on timeout is checked like an
            // action's write ([NU-054]). Only a forward of a match key carries the matched
            // name. A unit token has none and a forward of another input carries that
            // input's name, so such a firing fails and deposits nothing, while the name
            // layer would relay the matched name.
            if timeout_coloured.iter().any(|(_, w)| {
                !matches!(w, TimeoutWrite::Forward(from) if ms.keys().iter().any(|k| k.place_name() == from))
            }) {
                return None;
            }
            // A coloured place consumed off-key is taken FIFO, whatever its name; the
            // join step only removes the matched name from the keys, so the name layer
            // would keep a symbol the base marking has lost.
            if coloured_inputs
                .iter()
                .any(|s| !ms.keys().iter().any(|k| k.place_name() == s.place_name()))
            {
                return None;
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
            Role::Join {
                coloured_in,
                relay_to,
            }
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
                    let input_place = coloured_inputs[0].place_name().to_string();
                    // A timeout deposit relays the consumed name only when it forwards
                    // the coloured input itself. A forward of another input copies a
                    // name the relay did not consume, and a unit token has none.
                    if timeout_coloured
                        .iter()
                        .any(|(_, w)| *w != TimeoutWrite::Forward(input_place.clone()))
                    {
                        return None;
                    }
                    if produces_coloured {
                        relay_names.push(t.name().to_string());
                    }
                    Role::Consume { input_place }
                }
            }
        } else if produces_coloured {
            // Minting fork: produces a coloured token, consumes none. Read as a mint
            // only when declared ([NU-010]), and never when the executor writes a
            // coloured place on timeout.
            if !mints.contains(t.name()) || !timeout_coloured.is_empty() {
                return None;
            }
            mint_names.push(t.name().to_string());
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
        mints: mint_names,
        relays: relay_names,
    })
}

/// Every transition of `net`, as the declared mints of a test that exercises
/// something other than the mint declaration ([NU-010]).
#[cfg(test)]
pub(crate) fn all_mints(net: &PetriNet) -> BTreeSet<String> {
    net.transitions().iter().map(|t| t.name().to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::arc::reset;
    use libpetri_core::input::{at_least, exactly, one};
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// Empty carrier set, for the common `classify(net, mode, &no_carriers(), &crate::name_fragment::all_mints(&net))`.
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
            .action(fork())
            .build();
        PetriNet::builder("join_net").transition(join).build()
    }

    /// java-1: an AtLeast correlated input consumes ALL matching tokens at
    /// runtime, which the fixed-count SCG step cannot model faithfully — classify
    /// must reject it so the verifier falls back to the sound over-approximation.
    #[test]
    fn at_least_correlated_input_is_rejected() {
        assert!(classify(&join_net(true), FragmentMode::Base, &no_carriers(), &crate::name_fragment::all_mints(&join_net(true))).is_none());
    }

    /// The same shape with One correlated inputs IS in the fragment.
    #[test]
    fn one_correlated_inputs_are_accepted() {
        assert!(classify(&join_net(false), FragmentMode::Base, &no_carriers(), &crate::name_fragment::all_mints(&join_net(false))).is_some());
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

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(libpetri_core::output::and(vec![out_place(&pre_a), out_place(&pre_b)]))
            .action(fork())
            .build();
        let relay_a = Transition::builder("relayA")
            .input(relay_in(&pre_a, relay_count))
            .output(out_place(&a))
            .action(fork())
            .build();
        let relay_b = Transition::builder("relayB")
            .input(relay_in(&pre_b, relay_count))
            .output(out_place(&b))
            .action(fork())
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
            .action(fork())
            .build();
        let drain = Transition::builder("drain")
            .input(if drain_count == 1 { one(&a) } else { exactly(drain_count, &a) })
            .output(out_place(&dl))
            .action(fork())
            .build();

        PetriNet::builder("comint_relay_drain")
            .transitions([t_fork, relay_a, relay_b, join, drain])
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
            classify(&net, FragmentMode::Extended, &carriers, &crate::name_fragment::all_mints(&net)).is_some(),
            "EXTENDED must admit the drain/relay coloured-consumer fragment"
        );
        assert!(
            classify(&net, FragmentMode::Base, &carriers, &crate::name_fragment::all_mints(&net)).is_none(),
            "BASE rejects a non-match transition consuming a coloured place"
        );
    }

    /// The relays and drain take the [`Role::Consume`] role naming their single
    /// coloured input; the fork is a Mint; the join is a Join.
    #[test]
    fn extended_assigns_consume_roles() {
        let net = comint_relay_drain_net(1, 1);
        let fragment = classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"]), &crate::name_fragment::all_mints(&net))
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
            classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"]), &crate::name_fragment::all_mints(&net)).is_none(),
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
            classify(&net, FragmentMode::Extended, &carriers(&["preA", "preB"]), &crate::name_fragment::all_mints(&net)).is_none(),
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
            .action(fork())
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
            classify(&net, FragmentMode::Base, &no_carriers(), &crate::name_fragment::all_mints(&net)).is_none(),
            "reset on a coloured place is rejected under BASE"
        );
        assert!(
            classify(&net, FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&net)).is_none(),
            "reset on a coloured place is rejected under EXTENDED"
        );
    }

    // ---- NU-010 / NU-051: what a timeout writes into a coloured place ----

    /// `m: S → xor(A, timeout(20, A))` and `r: A → xor(C, timeout(20, forward(A, C)))`,
    /// `j: C, B → done` with `B` minted by `mb: S → B`. `timeout_place` writes a unit
    /// token into `A` on timeout; `forward_own` makes `r`'s timeout forward its own
    /// coloured input.
    fn timeout_net(timeout_place: bool, forward_own: bool) -> PetriNet {
        use libpetri_core::output::{forward_input, timeout, xor};
        let p = |n: &str| Place::<String>::new(n);
        let key = |s: &String| NameId::new(s.clone());
        let m_out = if timeout_place {
            xor(vec![out_place(&p("A")), timeout(20, out_place(&p("A")))])
        } else {
            out_place(&p("A"))
        };
        let r_out = if forward_own {
            xor(vec![out_place(&p("C")), timeout(20, forward_input(&p("A"), &p("C")))])
        } else {
            xor(vec![out_place(&p("C")), timeout(20, forward_input(&p("R"), &p("C")))])
        };
        let m = Transition::builder("m").input(one(&p("S"))).output(m_out).action(fork()).build();
        let mb = Transition::builder("mb").input(one(&p("S"))).output(out_place(&p("B"))).action(fork()).build();
        let r = Transition::builder("r")
            .input(one(&p("A")))
            .input(one(&p("R")))
            .output(r_out)
            .action(fork())
            .build();
        let j = Transition::builder("j")
            .input(one(&p("C")))
            .input(one(&p("B")))
            .match_spec(MatchSpec::builder().key(&p("C"), key).key(&p("B"), key).build())
            .output(out_place(&p("done")))
            .action(fork())
            .build();
        PetriNet::builder("timeouts").transitions([m, mb, r, j]).build()
    }

    #[test]
    fn a_unit_token_written_on_timeout_is_not_a_mint() {
        let net = timeout_net(true, true);
        let mints = all_mints(&net);
        assert!(classify(&net, FragmentMode::Extended, &carriers(&["A"]), &mints).is_none());
        let net = timeout_net(false, true);
        assert!(classify(&net, FragmentMode::Extended, &carriers(&["A"]), &mints).is_some());
    }

    #[test]
    fn a_consumer_timeout_relays_only_by_forwarding_its_coloured_input() {
        let net = timeout_net(false, true);
        let f = classify(&net, FragmentMode::Extended, &carriers(&["A"]), &all_mints(&net))
            .expect("forwarding the consumed input on timeout is a relay");
        assert!(matches!(f.role("r"), Role::Consume { input_place } if input_place == "A"));
        let net = timeout_net(false, false);
        assert!(classify(&net, FragmentMode::Extended, &carriers(&["A"]), &all_mints(&net)).is_none());
    }

    #[test]
    fn an_undeclared_producer_of_a_coloured_place_is_not_a_mint() {
        let net = timeout_net(false, true);
        let declared: BTreeSet<String> = ["m".to_string()].into_iter().collect();
        assert!(classify(&net, FragmentMode::Extended, &carriers(&["A"]), &declared).is_none());
        let declared: BTreeSet<String> = ["m".to_string(), "mb".to_string()].into_iter().collect();
        let f = classify(&net, FragmentMode::Extended, &carriers(&["A"]), &declared).expect("declared");
        assert_eq!(f.mints, vec!["m", "mb"]);
        assert_eq!(f.relays, vec!["r"]);
    }

    // ---- NU-054: relay targets ----

    use crate::relay_nets;
    use libpetri_core::arc::{inhibitor, read};
    use libpetri_core::output::and;
    use relay_nets::{FIG_12C_CARRIERS, fig_12c, join_chain, pnid_net, without_relays};

    #[test]
    fn extended_colours_relay_targets_and_the_join_carries_them() {
        let net = pnid_net("12c", &fig_12c());
        let f = classify(&net, FragmentMode::Extended, &carriers(&FIG_12C_CARRIERS), &crate::name_fragment::all_mints(&net))
            .expect("Fig. 12(c) with the relay is in the EXTENDED fragment");
        assert!(f.is_coloured("P5"));
        let Role::Join { relay_to, .. } = f.role("e") else {
            panic!("e is a join")
        };
        assert_eq!(relay_to.iter().collect::<Vec<_>>(), vec!["P5"]);
        // f and g drain: no relay target.
        let Role::Join { relay_to, .. } = f.role("g") else {
            panic!("g is a join")
        };
        assert!(relay_to.is_empty());
    }

    #[test]
    fn extended_rejects_a_join_writing_a_coloured_place_it_does_not_declare() {
        let net = pnid_net("12c", &without_relays(&fig_12c()));
        assert!(classify(&net, FragmentMode::Extended, &carriers(&FIG_12C_CARRIERS), &crate::name_fragment::all_mints(&net)).is_none());
    }

    #[test]
    fn base_ignores_the_declaration() {
        assert!(classify(&pnid_net("12c", &fig_12c()), FragmentMode::Base, &no_carriers(), &crate::name_fragment::all_mints(&pnid_net("12c", &fig_12c()))).is_none());
        let chain = pnid_net("chain", &join_chain());
        assert!(classify(&chain, FragmentMode::Base, &no_carriers(), &crate::name_fragment::all_mints(&chain)).is_none());
        let f = classify(&chain, FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&chain)).expect("EXTENDED admits the chain");
        // BASE-shaped roles are unchanged: j2 drains.
        let Role::Join { relay_to, .. } = f.role("j2") else {
            panic!("j2 is a join")
        };
        assert!(relay_to.is_empty());
    }

    /// `fork: S → A, B, D` (mint); `j: A, B (+ extra) → C` relaying to `C`;
    /// `k: C, D → done` joins `C` downstream.
    fn relay_net(extra: &str) -> PetriNet {
        let p = |n: &str| Place::<String>::new(n);
        let key = |s: &String| NameId::new(s.clone());
        let fork_t = Transition::builder("fork")
            .input(one(&p("S")))
            .output(and(vec![out_place(&p("A")), out_place(&p("B")), out_place(&p("D"))]))
            .action(fork())
            .build();
        let mut j = Transition::builder("j")
            .input(one(&p("A")))
            .input(one(&p("B")))
            .output(out_place(&p("C")))
            .match_spec(
                MatchSpec::builder()
                    .key(&p("A"), key)
                    .key(&p("B"), key)
                    .relay_to(&p("C"), key)
                    .build(),
            )
            .action(fork());
        match extra {
            "off_key" => j = j.input(one(&p("C"))),
            "read" => j = j.read(read(&p("C"))),
            "inhibitor" => j = j.inhibitor(inhibitor(&p("C"))),
            _ => {}
        }
        let k = Transition::builder("k")
            .input(one(&p("C")))
            .input(one(&p("D")))
            .output(out_place(&p("done")))
            .match_spec(MatchSpec::builder().key(&p("C"), key).key(&p("D"), key).build())
            .action(fork())
            .build();
        let mut ts = vec![fork_t, j.build(), k];
        if extra == "reset" {
            ts.push(
                Transition::builder("r")
                    .input(one(&p("X")))
                    .resets(vec![reset(&p("C"))])
                    .build(),
            );
        }
        PetriNet::builder("relay").transitions(ts).build()
    }

    #[test]
    fn extended_accepts_the_plain_relay() {
        assert!(classify(&relay_net("none"), FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&relay_net("none"))).is_some());
    }

    #[test]
    fn extended_rejects_a_relay_target_the_join_also_consumes_off_key() {
        assert!(classify(&relay_net("off_key"), FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&relay_net("off_key"))).is_none());
    }

    #[test]
    fn extended_rejects_a_relay_target_with_a_read_inhibitor_or_reset_arc() {
        for arc in ["read", "inhibitor", "reset"] {
            assert!(
                classify(&relay_net(arc), FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&relay_net(arc))).is_none(),
                "{arc}"
            );
        }
    }

    #[test]
    fn a_relay_target_no_join_consumes_is_coloured_and_its_read_arc_rejects() {
        let rows = vec![
            relay_nets::t("fork", &["S"], &["A", "B"]),
            relay_nets::j("j", &["A", "B"], &["C"], &["A", "B"], &["C"]),
        ];
        let f = classify(&pnid_net("sinkRelay", &rows), FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&pnid_net("sinkRelay", &rows)))
            .expect("a relay into a sink place is in the fragment");
        assert!(f.is_coloured("C"));
        let p = |n: &str| Place::<String>::new(n);
        let watcher = Transition::builder("w")
            .input(one(&p("X")))
            .output(out_place(&p("Y")))
            .read(read(&p("C")))
            .action(fork())
            .build();
        let mut ts: Vec<Transition> = pnid_net("x", &rows).transitions().to_vec();
        ts.push(watcher);
        let net = PetriNet::builder("sinkRelayRead").transitions(ts).build();
        assert!(classify(&net, FragmentMode::Extended, &no_carriers(), &crate::name_fragment::all_mints(&net)).is_none());
    }
}
