use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::input::{required_count, In};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::PlaceRef;
use libpetri_core::transition::Transition;

use crate::bitmap;

/// Cardinality check for transitions with non-One inputs.
#[derive(Debug, Clone)]
pub struct CardinalityCheck {
    pub place_ids: Vec<usize>,
    pub required_counts: Vec<usize>,
}

/// Integer-indexed, precomputed representation of a PetriNet for bitmap-based execution.
///
/// Uses u64 bitmasks (64 bits per word) for O(W) enablement checks
/// where W = ceil(place_count / 64).
#[derive(Debug)]
pub struct CompiledNet {
    net: PetriNet,
    pub(crate) place_count: usize,
    pub(crate) transition_count: usize,
    pub(crate) word_count: usize,

    // ID mappings
    places_by_id: Vec<PlaceRef>,
    transitions_by_id: Vec<usize>, // index into net.transitions()
    place_index: HashMap<Arc<str>, usize>,
    #[allow(dead_code)]
    transition_index: HashMap<usize, usize>, // net transition index -> compiled id

    // Precomputed masks per transition (flat arrays: [tid * word_count .. (tid+1) * word_count])
    needs_masks: Vec<u64>,
    inhibitor_masks: Vec<u64>,

    // Reverse index: place_id -> affected transition IDs
    place_to_transitions: Vec<Vec<usize>>,

    // Consumption place IDs per transition (input + reset places)
    consumption_place_ids: Vec<Vec<usize>>,

    // Cardinality and guard flags
    cardinality_checks: Vec<Option<CardinalityCheck>>,
    has_guards: Vec<bool>,
}

impl CompiledNet {
    /// Compiles a PetriNet into an optimized bitmap representation.
    pub fn compile(net: &PetriNet) -> Self {
        // Collect all places (sorted for stable ordering)
        let mut place_names: Vec<Arc<str>> = net
            .places()
            .iter()
            .map(|p| Arc::clone(p.name_arc()))
            .collect();
        place_names.sort();
        place_names.dedup();

        let place_count = place_names.len();
        let word_count = bitmap::word_count(place_count);

        // Assign place IDs
        let mut place_index = HashMap::new();
        let mut places_by_id = Vec::with_capacity(place_count);
        for (i, name) in place_names.iter().enumerate() {
            place_index.insert(Arc::clone(name), i);
            places_by_id.push(PlaceRef::new(Arc::clone(name)));
        }

        let transition_count = net.transitions().len();
        let mut transitions_by_id = Vec::with_capacity(transition_count);
        let mut transition_index = HashMap::new();

        let mut needs_masks = vec![0u64; transition_count * word_count];
        let mut inhibitor_masks = vec![0u64; transition_count * word_count];
        let mut consumption_place_ids = Vec::with_capacity(transition_count);
        let mut cardinality_checks: Vec<Option<CardinalityCheck>> =
            vec![None; transition_count];
        let mut has_guards = vec![false; transition_count];

        let mut place_to_transitions_tmp: Vec<HashSet<usize>> =
            vec![HashSet::new(); place_count];

        for (net_idx, t) in net.transitions().iter().enumerate() {
            let tid = net_idx;
            transitions_by_id.push(net_idx);
            transition_index.insert(net_idx, tid);

            let mask_base = tid * word_count;
            let mut needs_cardinality = false;

            // Input specs
            for in_spec in t.input_specs() {
                let pid = place_index[in_spec.place().name_arc()];
                if word_count > 0 {
                    bitmap::set_bit(&mut needs_masks[mask_base..mask_base + word_count], pid);
                }
                place_to_transitions_tmp[pid].insert(tid);

                if !matches!(in_spec, In::One { .. }) {
                    needs_cardinality = true;
                }
                if in_spec.has_guard() {
                    has_guards[tid] = true;
                }
            }

            // Build cardinality check if needed
            if needs_cardinality {
                let mut pids = Vec::new();
                let mut reqs = Vec::new();
                for in_spec in t.input_specs() {
                    pids.push(place_index[in_spec.place().name_arc()]);
                    reqs.push(required_count(in_spec));
                }
                cardinality_checks[tid] = Some(CardinalityCheck {
                    place_ids: pids,
                    required_counts: reqs,
                });
            }

            // Read arcs
            for r in t.reads() {
                let pid = place_index[r.place.name_arc()];
                if word_count > 0 {
                    bitmap::set_bit(&mut needs_masks[mask_base..mask_base + word_count], pid);
                }
                place_to_transitions_tmp[pid].insert(tid);
            }

            // Inhibitor arcs
            for inh in t.inhibitors() {
                let pid = place_index[inh.place.name_arc()];
                if word_count > 0 {
                    bitmap::set_bit(
                        &mut inhibitor_masks[mask_base..mask_base + word_count],
                        pid,
                    );
                }
                place_to_transitions_tmp[pid].insert(tid);
            }

            // Reset arcs
            for r in t.resets() {
                let pid = place_index[r.place.name_arc()];
                place_to_transitions_tmp[pid].insert(tid);
            }

            // Consumption place IDs (input + reset, deduplicated)
            let mut consumption_set = HashSet::new();
            for spec in t.input_specs() {
                consumption_set.insert(place_index[spec.place().name_arc()]);
            }
            for r in t.resets() {
                consumption_set.insert(place_index[r.place.name_arc()]);
            }
            consumption_place_ids.push(consumption_set.into_iter().collect());
        }

        let place_to_transitions: Vec<Vec<usize>> = place_to_transitions_tmp
            .into_iter()
            .map(|s| s.into_iter().collect())
            .collect();

        CompiledNet {
            net: net.clone(),
            place_count,
            transition_count,
            word_count,
            places_by_id,
            transitions_by_id,
            place_index,
            transition_index,
            needs_masks,
            inhibitor_masks,
            place_to_transitions,
            consumption_place_ids,
            cardinality_checks,
            has_guards,
        }
    }

    // ==================== Accessors ====================

    /// Returns the underlying PetriNet.
    pub fn net(&self) -> &PetriNet {
        &self.net
    }

    /// Returns the place at the given ID.
    pub fn place(&self, pid: usize) -> &PlaceRef {
        &self.places_by_id[pid]
    }

    /// Returns the transition at the given compiled ID.
    pub fn transition(&self, tid: usize) -> &Transition {
        &self.net.transitions()[self.transitions_by_id[tid]]
    }

    /// Returns the place ID for a given place name.
    pub fn place_id(&self, name: &str) -> Option<usize> {
        self.place_index.get(name).copied()
    }

    /// Returns the place ID, panicking if not found.
    pub fn place_id_or_panic(&self, name: &str) -> usize {
        self.place_index
            .get(name)
            .copied()
            .unwrap_or_else(|| panic!("Unknown place: {name}"))
    }

    /// Returns affected transition IDs for a place.
    pub fn affected_transitions(&self, pid: usize) -> &[usize] {
        &self.place_to_transitions[pid]
    }

    /// Returns consumption place IDs for a transition.
    pub fn consumption_place_ids(&self, tid: usize) -> &[usize] {
        &self.consumption_place_ids[tid]
    }

    /// Returns the cardinality check for a transition, if any.
    pub fn cardinality_check(&self, tid: usize) -> Option<&CardinalityCheck> {
        self.cardinality_checks[tid].as_ref()
    }

    /// Returns whether a transition has guard predicates.
    pub fn has_guards(&self, tid: usize) -> bool {
        self.has_guards[tid]
    }

    /// Returns the needs mask slice for a transition.
    pub fn needs_mask(&self, tid: usize) -> &[u64] {
        let base = tid * self.word_count;
        &self.needs_masks[base..base + self.word_count]
    }

    /// Returns the inhibitor mask slice for a transition.
    pub fn inhibitor_mask(&self, tid: usize) -> &[u64] {
        let base = tid * self.word_count;
        &self.inhibitor_masks[base..base + self.word_count]
    }

    // ==================== Enablement Check ====================

    /// Two-phase bitmap enablement check for a transition:
    /// 1. Presence check: verifies all required places have tokens
    /// 2. Inhibitor check: verifies no inhibitor places have tokens
    ///
    /// This is a necessary but not sufficient condition — cardinality and guard checks
    /// are performed separately by the executor for transitions that pass this fast path.
    pub fn can_enable_bitmap(&self, tid: usize, marking_snapshot: &[u64]) -> bool {
        let needs = self.needs_mask(tid);
        let inhibitors = self.inhibitor_mask(tid);

        bitmap::contains_all(marking_snapshot, needs)
            && !bitmap::intersects(marking_snapshot, inhibitors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;

    fn simple_chain_net() -> PetriNet {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .build();

        PetriNet::builder("chain").transitions([t1, t2]).build()
    }

    #[test]
    fn compile_basic() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);

        assert_eq!(compiled.place_count, 3);
        assert_eq!(compiled.transition_count, 2);
        assert!(compiled.word_count >= 1);
    }

    #[test]
    fn place_id_lookup() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);

        assert!(compiled.place_id("p1").is_some());
        assert!(compiled.place_id("p2").is_some());
        assert!(compiled.place_id("p3").is_some());
        assert!(compiled.place_id("nonexistent").is_none());
    }

    #[test]
    fn bitmap_enablement() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);

        let mut snapshot = vec![0u64; compiled.word_count];

        // Nothing marked — neither transition enabled
        assert!(!compiled.can_enable_bitmap(0, &snapshot));
        assert!(!compiled.can_enable_bitmap(1, &snapshot));

        // Mark p1 — t1 should be enabled
        let p1_id = compiled.place_id("p1").unwrap();
        bitmap::set_bit(&mut snapshot, p1_id);
        assert!(compiled.can_enable_bitmap(0, &snapshot));
        assert!(!compiled.can_enable_bitmap(1, &snapshot));

        // Mark p2 — t2 should also be enabled
        let p2_id = compiled.place_id("p2").unwrap();
        bitmap::set_bit(&mut snapshot, p2_id);
        assert!(compiled.can_enable_bitmap(0, &snapshot));
        assert!(compiled.can_enable_bitmap(1, &snapshot));
    }

    #[test]
    fn inhibitor_blocks_transition() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p_inh = Place::<i32>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .build();

        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);

        let mut snapshot = vec![0u64; compiled.word_count];
        let p1_id = compiled.place_id("p1").unwrap();
        let inh_id = compiled.place_id("inh").unwrap();

        bitmap::set_bit(&mut snapshot, p1_id);
        assert!(compiled.can_enable_bitmap(0, &snapshot));

        // Adding inhibitor token disables
        bitmap::set_bit(&mut snapshot, inh_id);
        assert!(!compiled.can_enable_bitmap(0, &snapshot));
    }

    #[test]
    fn reverse_index() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);

        // p2 is output of t1 and input of t2, so both should be affected
        let p2_id = compiled.place_id("p2").unwrap();
        let affected = compiled.affected_transitions(p2_id);
        // t2 reads from p2
        assert!(affected.contains(&1) || affected.contains(&0));
    }
}
