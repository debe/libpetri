use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::input::In;
use libpetri_core::output::Out;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::PlaceRef;
use libpetri_core::transition::Transition;

use crate::bitmap;
use crate::compiled_net::CompiledNet;

/// Consume operation opcodes.
pub const CONSUME_ONE: u32 = 0;
pub const CONSUME_N: u32 = 1;
pub const CONSUME_ALL: u32 = 2;
pub const CONSUME_ATLEAST: u32 = 3;
pub const RESET: u32 = 4;

/// Sparse enablement mask: precomputed for efficient bitmap checks.
#[derive(Debug, Clone)]
pub enum SparseMask {
    /// No bits set (e.g. no inputs / no inhibitors).
    Empty,
    /// Exactly one non-zero word at the given index.
    Single { word_index: usize, mask: u64 },
    /// Multiple non-zero words (sparse representation).
    Multi {
        indices: Vec<usize>,
        masks: Vec<u64>,
    },
}

/// Precompiled flat-array net representation for the [`super::precompiled_executor::PrecompiledNetExecutor`].
///
/// Compiles the net topology into flat arrays and operation sequences that eliminate
/// HashMap lookups and enum pattern matching from the hot path.
#[derive(Debug)]
pub struct PrecompiledNet<'c> {
    compiled: &'c CompiledNet,

    /// Consume/reset opcodes per transition.
    pub(crate) consume_ops: Vec<Vec<u32>>,
    /// Read-arc place IDs per transition.
    pub(crate) read_ops: Vec<Vec<usize>>,

    /// Sparse enablement masks per transition.
    pub(crate) needs_sparse: Vec<SparseMask>,
    pub(crate) inhibitor_sparse: Vec<SparseMask>,

    /// Precomputed timing (milliseconds).
    pub(crate) earliest_ms: Vec<f64>,
    pub(crate) latest_ms: Vec<f64>,
    pub(crate) has_deadline: Vec<bool>,
    pub(crate) all_immediate: bool,
    pub(crate) any_deadlines: bool,

    /// Priority partitioning.
    pub(crate) priorities: Vec<i32>,
    pub(crate) transition_to_priority_index: Vec<usize>,
    #[allow(dead_code)]
    pub(crate) priority_levels: Vec<i32>,
    pub(crate) distinct_priority_count: usize,
    pub(crate) all_same_priority: bool,

    /// Simple output fast path: -2 = no spec, -1 = complex, >= 0 = Out::Place pid.
    #[allow(dead_code)]
    pub(crate) simple_output_place_id: Vec<i32>,

    /// Input place count per transition (for capacity hints).
    #[allow(dead_code)]
    pub(crate) input_place_count: Vec<usize>,

    /// Input place masks per transition (for reset-clock detection).
    pub(crate) input_place_mask_words: Vec<Vec<u64>>,

    /// Precomputed place name Arcs (indexed by place ID).
    pub(crate) place_name_arcs: Vec<Arc<str>>,
    /// Precomputed transition name Arcs (indexed by transition ID).
    pub(crate) transition_name_arcs: Vec<Arc<str>>,
    /// Precomputed output place name sets per transition.
    pub(crate) output_place_name_sets: Vec<HashSet<Arc<str>>>,
}

impl<'c> PrecompiledNet<'c> {
    /// Compiles using an existing CompiledNet to reuse its masks and indices.
    pub fn from_compiled(compiled: &'c CompiledNet) -> Self {
        let tc = compiled.transition_count;
        let wc = compiled.word_count;

        // Compile sparse enablement masks
        let mut needs_sparse = Vec::with_capacity(tc);
        let mut inhibitor_sparse = Vec::with_capacity(tc);

        for tid in 0..tc {
            needs_sparse.push(compile_sparse(compiled.needs_mask(tid)));
            inhibitor_sparse.push(compile_sparse(compiled.inhibitor_mask(tid)));
        }

        // Compile consume/read operation sequences
        let mut consume_ops = Vec::with_capacity(tc);
        let mut read_ops = Vec::with_capacity(tc);
        let mut input_place_mask_words = Vec::with_capacity(tc);
        let mut simple_output_place_id = Vec::with_capacity(tc);
        let mut input_place_count = Vec::with_capacity(tc);

        for tid in 0..tc {
            let t = compiled.transition(tid);
            consume_ops.push(compile_consume_ops(t, compiled));
            read_ops.push(compile_read_ops(t, compiled));
            input_place_mask_words.push(compile_input_mask(t, compiled, wc));

            input_place_count.push(t.input_specs().len() + t.reads().len());

            // Precompute output validation fast path
            match t.output_spec() {
                None => simple_output_place_id.push(-2),
                Some(Out::Place(p)) => {
                    simple_output_place_id.push(compiled.place_id(p.name()).unwrap_or(0) as i32);
                }
                Some(_) => simple_output_place_id.push(-1),
            }
        }

        // Precompute timing
        let mut earliest_ms = vec![0.0f64; tc];
        let mut latest_ms = vec![f64::MAX; tc];
        let mut has_deadline = vec![false; tc];
        let mut any_deadlines = false;
        let mut all_immediate = true;

        for tid in 0..tc {
            let t = compiled.transition(tid);
            earliest_ms[tid] = t.timing().earliest() as f64;
            if t.timing().has_deadline() {
                latest_ms[tid] = t.timing().latest() as f64;
                has_deadline[tid] = true;
                any_deadlines = true;
            }
            if *t.timing() != libpetri_core::timing::Timing::Immediate {
                all_immediate = false;
            }
        }

        // Precompute priorities
        let mut priorities = vec![0i32; tc];
        let mut distinct_set = std::collections::BTreeSet::new();
        for (tid, prio) in priorities.iter_mut().enumerate() {
            *prio = compiled.transition(tid).priority();
            distinct_set.insert(std::cmp::Reverse(*prio));
        }
        let priority_levels: Vec<i32> = distinct_set.into_iter().map(|r| r.0).collect();
        let distinct_priority_count = priority_levels.len();
        let all_same_priority = distinct_priority_count <= 1;

        let prio_to_index: HashMap<i32, usize> = priority_levels
            .iter()
            .enumerate()
            .map(|(i, &p)| (p, i))
            .collect();
        let transition_to_priority_index: Vec<usize> =
            (0..tc).map(|tid| prio_to_index[&priorities[tid]]).collect();

        // Precompute name Arcs for zero-allocation hot path access
        let pc = compiled.place_count;
        let place_name_arcs: Vec<Arc<str>> = (0..pc)
            .map(|pid| Arc::clone(compiled.place(pid).name_arc()))
            .collect();
        let transition_name_arcs: Vec<Arc<str>> = (0..tc)
            .map(|tid| Arc::clone(compiled.transition(tid).name_arc()))
            .collect();

        // Precompute output place name sets per transition
        let output_place_name_sets: Vec<HashSet<Arc<str>>> = (0..tc)
            .map(|tid| {
                compiled
                    .transition(tid)
                    .output_places()
                    .iter()
                    .map(|p| Arc::clone(p.name_arc()))
                    .collect()
            })
            .collect();

        PrecompiledNet {
            compiled,
            consume_ops,
            read_ops,
            needs_sparse,
            inhibitor_sparse,
            earliest_ms,
            latest_ms,
            has_deadline,
            all_immediate,
            any_deadlines,
            priorities,
            transition_to_priority_index,
            priority_levels,
            distinct_priority_count,
            all_same_priority,
            simple_output_place_id,
            input_place_count,
            input_place_mask_words,
            place_name_arcs,
            transition_name_arcs,
            output_place_name_sets,
        }
    }

    // ==================== Accessors ====================

    /// Returns the underlying CompiledNet.
    pub fn compiled(&self) -> &'c CompiledNet {
        self.compiled
    }

    /// Returns the underlying PetriNet.
    pub fn net(&self) -> &PetriNet {
        self.compiled.net()
    }

    /// Returns the place at the given ID.
    pub fn place(&self, pid: usize) -> &PlaceRef {
        self.compiled.place(pid)
    }

    /// Returns the transition at the given compiled ID.
    pub fn transition(&self, tid: usize) -> &Transition {
        self.compiled.transition(tid)
    }

    /// Returns the place ID for a given place name.
    pub fn place_id(&self, name: &str) -> Option<usize> {
        self.compiled.place_id(name)
    }

    /// Returns the number of places.
    pub fn place_count(&self) -> usize {
        self.compiled.place_count
    }

    /// Returns the number of transitions.
    pub fn transition_count(&self) -> usize {
        self.compiled.transition_count
    }

    /// Returns the word count for bitmaps.
    pub fn word_count(&self) -> usize {
        self.compiled.word_count
    }

    // ==================== Enablement Check ====================

    /// Sparse bitmap enablement check for a transition.
    pub fn can_enable_bitmap(&self, tid: usize, marking_snapshot: &[u64]) -> bool {
        // Needs check (contains_all)
        match &self.needs_sparse[tid] {
            SparseMask::Empty => {}
            SparseMask::Single { word_index, mask } => {
                if *word_index >= marking_snapshot.len()
                    || (marking_snapshot[*word_index] & mask) != *mask
                {
                    return false;
                }
            }
            SparseMask::Multi { indices, masks } => {
                for i in 0..indices.len() {
                    let w = indices[i];
                    if w >= marking_snapshot.len() || (marking_snapshot[w] & masks[i]) != masks[i] {
                        return false;
                    }
                }
            }
        }

        // Inhibitor check (intersects → must not intersect)
        match &self.inhibitor_sparse[tid] {
            SparseMask::Empty => true,
            SparseMask::Single { word_index, mask } => {
                *word_index >= marking_snapshot.len() || (marking_snapshot[*word_index] & mask) == 0
            }
            SparseMask::Multi { indices, masks } => {
                for i in 0..indices.len() {
                    let w = indices[i];
                    if w < marking_snapshot.len() && (marking_snapshot[w] & masks[i]) != 0 {
                        return false;
                    }
                }
                true
            }
        }
    }
}

// ==================== Compilation Helpers ====================

fn compile_sparse(mask_words: &[u64]) -> SparseMask {
    let mut non_zero_count = 0;
    let mut last_non_zero = 0;
    for (w, &word) in mask_words.iter().enumerate() {
        if word != 0 {
            non_zero_count += 1;
            last_non_zero = w;
        }
    }

    match non_zero_count {
        0 => SparseMask::Empty,
        1 => SparseMask::Single {
            word_index: last_non_zero,
            mask: mask_words[last_non_zero],
        },
        _ => {
            let mut indices = Vec::with_capacity(non_zero_count);
            let mut masks = Vec::with_capacity(non_zero_count);
            for (w, &word) in mask_words.iter().enumerate() {
                if word != 0 {
                    indices.push(w);
                    masks.push(word);
                }
            }
            SparseMask::Multi { indices, masks }
        }
    }
}

fn compile_consume_ops(t: &Transition, compiled: &CompiledNet) -> Vec<u32> {
    let mut ops = Vec::new();

    for in_spec in t.input_specs() {
        let pid = compiled.place_id(in_spec.place_name()).unwrap();
        match in_spec {
            In::One { .. } => {
                ops.push(CONSUME_ONE);
                ops.push(pid as u32);
            }
            In::Exactly { count, .. } => {
                ops.push(CONSUME_N);
                ops.push(pid as u32);
                ops.push(*count as u32);
            }
            In::All { .. } => {
                ops.push(CONSUME_ALL);
                ops.push(pid as u32);
            }
            In::AtLeast { minimum, .. } => {
                ops.push(CONSUME_ATLEAST);
                ops.push(pid as u32);
                ops.push(*minimum as u32);
            }
        }
    }

    for r in t.resets() {
        let pid = compiled.place_id(r.place.name()).unwrap();
        ops.push(RESET);
        ops.push(pid as u32);
    }

    ops
}

fn compile_read_ops(t: &Transition, compiled: &CompiledNet) -> Vec<usize> {
    t.reads()
        .iter()
        .map(|r| compiled.place_id(r.place.name()).unwrap())
        .collect()
}

fn compile_input_mask(t: &Transition, compiled: &CompiledNet, word_count: usize) -> Vec<u64> {
    let mut mask = vec![0u64; word_count];
    for in_spec in t.input_specs() {
        let pid = compiled.place_id(in_spec.place_name()).unwrap();
        bitmap::set_bit(&mut mask, pid);
    }
    mask
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
        let prog = PrecompiledNet::from_compiled(&compiled);

        assert_eq!(prog.place_count(), 3);
        assert_eq!(prog.transition_count(), 2);
        assert!(prog.word_count() >= 1);
        assert!(prog.all_immediate);
        assert!(prog.all_same_priority);
    }

    #[test]
    fn sparse_enablement() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut snapshot = vec![0u64; prog.word_count()];

        // Nothing marked — neither enabled
        assert!(!prog.can_enable_bitmap(0, &snapshot));
        assert!(!prog.can_enable_bitmap(1, &snapshot));

        // Mark p1 — t1 enabled
        let p1_id = prog.place_id("p1").unwrap();
        bitmap::set_bit(&mut snapshot, p1_id);
        assert!(prog.can_enable_bitmap(0, &snapshot));
        assert!(!prog.can_enable_bitmap(1, &snapshot));

        // Mark p2 — t2 also enabled
        let p2_id = prog.place_id("p2").unwrap();
        bitmap::set_bit(&mut snapshot, p2_id);
        assert!(prog.can_enable_bitmap(0, &snapshot));
        assert!(prog.can_enable_bitmap(1, &snapshot));
    }

    #[test]
    fn consume_ops_compiled() {
        let net = simple_chain_net();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        // t1: CONSUME_ONE pid(p1)
        assert_eq!(prog.consume_ops[0].len(), 2);
        assert_eq!(prog.consume_ops[0][0], CONSUME_ONE);
    }

    #[test]
    fn priority_partitioning() {
        let p = Place::<()>::new("p");
        let out = Place::<()>::new("out");

        let t_high = Transition::builder("t_high")
            .input(one(&p))
            .output(out_place(&out))
            .priority(10)
            .build();
        let t_low = Transition::builder("t_low")
            .input(one(&p))
            .output(out_place(&out))
            .priority(1)
            .build();

        let net = PetriNet::builder("prio")
            .transitions([t_high, t_low])
            .build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        assert_eq!(prog.distinct_priority_count, 2);
        assert!(!prog.all_same_priority);
        assert_eq!(prog.priority_levels[0], 10); // highest first
        assert_eq!(prog.priority_levels[1], 1);
    }

    #[test]
    fn inhibitor_sparse() {
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
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut snapshot = vec![0u64; prog.word_count()];
        let p1_id = prog.place_id("p1").unwrap();
        let inh_id = prog.place_id("inh").unwrap();

        bitmap::set_bit(&mut snapshot, p1_id);
        assert!(prog.can_enable_bitmap(0, &snapshot));

        bitmap::set_bit(&mut snapshot, inh_id);
        assert!(!prog.can_enable_bitmap(0, &snapshot));
    }
}
