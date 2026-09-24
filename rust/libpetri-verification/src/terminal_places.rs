//! Net-declared terminal places in verification ([EXEC-042], [VER-014]).
//!
//! A terminal place `P` ends the run the moment it is marked: nothing fires
//! afterwards, whatever else is enabled or in flight. The verifier states the
//! same thing in the model, with no restatement by the caller, by verifying
//! the net in which
//!
//! - `P` inhibits every transition (so no firing follows a marking of `P`),
//! - `P` is a sink ([VER-002]), and
//! - `P` is a conditional-sink marker for every place ([VER-014]),
//!   `sink_places_when(P, all places)`,
//!
//! so a quiescent marking with `P` marked is excused. This is exact for the
//! runtime's strict stop. The inhibitor half lives here; each verifier adds the
//! rest-set half to its own declarations.

use libpetri_core::arc::Inhibitor;
use libpetri_core::petri_net::PetriNet;

/// The net with every declared terminal place inhibiting every transition, or
/// `None` when the net declares no terminal place — the caller then keeps the
/// original net, so a net without terminals is verified, and scripted, exactly
/// as before ([EXEC-042] AC8).
///
/// Inhibitors are appended after each transition's own, in terminal
/// declaration order, skipping a place the transition already inhibits, so the
/// rewrite is idempotent. The result still declares its terminals.
pub fn inhibit_on_terminals(net: &PetriNet) -> Option<PetriNet> {
    if net.terminals().is_empty() {
        return None;
    }
    let inhibitors: Vec<Inhibitor> = net
        .terminals()
        .iter()
        .map(|p| Inhibitor { place: p.clone() })
        .collect();
    Some(net.map_transitions(|t| t.with_added_inhibitors(inhibitors.iter().cloned())))
}

/// Every place name of `net`, in net order: the places a terminal excuses
/// ([VER-014] `sink_places_when(P, all places)`).
pub fn all_place_names(net: &PetriNet) -> Vec<String> {
    net.places().iter().map(|p| p.name().to_string()).collect()
}
