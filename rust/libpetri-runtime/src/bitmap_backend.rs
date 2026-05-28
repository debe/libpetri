//! `BitmapBackend` — the bitmap-storage backend behind
//! [`BitmapNetExecutor`](crate::executor::BitmapNetExecutor).
//!
//! Owns the per-place presence bitmap, the per-transition enablement
//! flags, the dirty set, and the FIFO `Marking` token store. Implements
//! [`ExecutorBackend`] so [`Executor`](crate::executor_core::executor::Executor)
//! can drive the shared 5-phase loop against it.
//!
//! Performance: `~800 ns/transition` on a sync linear chain — about
//! 2.5× slower than `PrecompiledBackend`, which is acceptable because
//! `BitmapBackend` is the reference / verification path; high-volume
//! production workloads use the precompiled backend.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::input::In;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::token::ErasedToken;

use crate::bitmap;
use crate::compiled_net::CompiledNet;
use crate::executor_core::backend::{ConsumedInputs, EnablementChanges, ExecutorBackend};
use crate::executor_core::deadline::DEADLINE_TOLERANCE_MS;
use crate::marking::Marking;

/// Bitmap-based backend: the reference execution storage. See module
/// docs.
pub struct BitmapBackend {
    compiled: CompiledNet,
    marking: Marking,

    // Presence + dirty bitmaps.
    marked_places: Vec<u64>,
    dirty_set: Vec<u64>,
    marking_snap_buffer: Vec<u64>,
    dirty_snap_buffer: Vec<u64>,
    firing_snap_buffer: Vec<u64>,

    // Per-transition enablement state.
    enabled_at_ms: Vec<f64>,
    enabled_flags: Vec<bool>,
    has_deadline_flags: Vec<bool>,
    enabled_transition_count: usize,

    // Precomputed flags.
    all_immediate: bool,
    all_same_priority: bool,
    has_any_deadlines: bool,

    // Clock-restart detection: places drained by reset arcs this cycle
    // and per-transition input-place-name set for fast intersection.
    pending_reset_places: HashSet<Arc<str>>,
    transition_input_place_names: Vec<HashSet<Arc<str>>>,
}

impl BitmapBackend {
    /// Compile `net` and build a fresh backend loaded with
    /// `initial_marking`. The backend is ready for `Executor` to drive;
    /// no separate `initialize()` is required until the loop calls it
    /// just before the first cycle.
    pub fn new(net: &PetriNet, initial_marking: Marking) -> Self {
        let compiled = CompiledNet::compile(net);
        let word_count = compiled.word_count;
        let tc = compiled.transition_count;
        let dirty_word_count = bitmap::word_count(tc);

        let mut has_any_deadlines = false;
        let mut all_immediate = true;
        let mut all_same_priority = true;
        let first_priority = if tc > 0 {
            compiled.transition(0).priority()
        } else {
            0
        };
        let mut has_deadline_flags = vec![false; tc];

        for (tid, flag) in has_deadline_flags.iter_mut().enumerate() {
            let t = compiled.transition(tid);
            if t.timing().has_deadline() {
                *flag = true;
                has_any_deadlines = true;
            }
            if *t.timing() != libpetri_core::timing::Timing::Immediate {
                all_immediate = false;
            }
            if t.priority() != first_priority {
                all_same_priority = false;
            }
        }

        let mut transition_input_place_names = Vec::with_capacity(tc);
        for tid in 0..tc {
            let t = compiled.transition(tid);
            let names: HashSet<Arc<str>> = t
                .input_specs()
                .iter()
                .map(|s| Arc::clone(s.place().name_arc()))
                .collect();
            transition_input_place_names.push(names);
        }

        Self {
            compiled,
            marking: initial_marking,
            marked_places: vec![0u64; word_count],
            dirty_set: vec![0u64; dirty_word_count],
            marking_snap_buffer: vec![0u64; word_count],
            dirty_snap_buffer: vec![0u64; dirty_word_count],
            firing_snap_buffer: vec![0u64; word_count],
            enabled_at_ms: vec![f64::NEG_INFINITY; tc],
            enabled_flags: vec![false; tc],
            has_deadline_flags,
            enabled_transition_count: 0,
            all_immediate,
            all_same_priority,
            has_any_deadlines,
            pending_reset_places: HashSet::new(),
            transition_input_place_names,
        }
    }

    #[inline]
    fn mark_all_dirty(&mut self) {
        let tc = self.compiled.transition_count;
        let dirty_words = self.dirty_set.len();
        for w in 0..dirty_words.saturating_sub(1) {
            self.dirty_set[w] = u64::MAX;
        }
        if dirty_words > 0 {
            let last_word_bits = tc & bitmap::WORD_MASK;
            self.dirty_set[dirty_words - 1] = if last_word_bits == 0 {
                u64::MAX
            } else {
                (1u64 << last_word_bits) - 1
            };
        }
    }

    /// True when the transition has all required input/read tokens
    /// available and no inhibitor blocks it, checked against the given
    /// presence bitmap (used both with a per-cycle snapshot and with
    /// the live `marked_places` during firing recheck).
    fn can_enable(&self, tid: usize, marking_snap: &[u64]) -> bool {
        if !self.compiled.can_enable_bitmap(tid, marking_snap) {
            return false;
        }

        if let Some(card_check) = self.compiled.cardinality_check(tid) {
            for i in 0..card_check.place_ids.len() {
                let pid = card_check.place_ids[i];
                let required = card_check.required_counts[i];
                let place = self.compiled.place(pid);
                if self.marking.count(place.name()) < required {
                    return false;
                }
            }
        }

        if self.compiled.has_guards(tid) {
            let t = self.compiled.transition(tid);
            for spec in t.input_specs() {
                if let Some(guard) = spec.guard() {
                    let required = match spec {
                        In::One { .. } => 1,
                        In::Exactly { count, .. } => *count,
                        In::AtLeast { minimum, .. } => *minimum,
                        In::All { .. } => 1,
                    };
                    if self.marking.count_matching(spec.place_name(), &**guard) < required {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn has_input_from_reset_place(&self, tid: usize) -> bool {
        if self.pending_reset_places.is_empty() {
            return false;
        }
        let input_names = &self.transition_input_place_names[tid];
        for name in &self.pending_reset_places {
            if input_names.contains(name) {
                return true;
            }
        }
        false
    }

    #[inline]
    fn mark_place_dirty(&mut self, pid: usize) {
        let tids: Vec<usize> = self.compiled.affected_transitions(pid).to_vec();
        for tid in tids {
            bitmap::set_bit(&mut self.dirty_set, tid);
        }
    }

    fn update_bitmap_after_consumption(&mut self, tid: usize) {
        let consumption_pids: Vec<usize> = self.compiled.consumption_place_ids(tid).to_vec();
        for pid in consumption_pids {
            let place = self.compiled.place(pid);
            if !self.marking.has_tokens(place.name()) {
                bitmap::clear_bit(&mut self.marked_places, pid);
            }
            self.mark_place_dirty(pid);
        }
    }
}

impl ExecutorBackend for BitmapBackend {
    fn compiled(&self) -> &CompiledNet {
        &self.compiled
    }

    fn initialize(&mut self) {
        for pid in 0..self.compiled.place_count {
            let place = self.compiled.place(pid);
            if self.marking.has_tokens(place.name()) {
                bitmap::set_bit(&mut self.marked_places, pid);
            }
        }
        self.mark_all_dirty();
    }

    fn snapshot_marking(&self) -> Cow<'_, Marking> {
        Cow::Borrowed(&self.marking)
    }

    fn is_quiescent(&self) -> bool {
        self.enabled_transition_count == 0
    }

    fn has_dirty_bits(&self) -> bool {
        !bitmap::is_empty(&self.dirty_set)
    }

    fn enabled_count(&self) -> usize {
        self.enabled_transition_count
    }

    fn update_enablement(&mut self, now_ms: f64, changes: &mut EnablementChanges) {
        // Snapshot the presence bitmap.
        self.marking_snap_buffer
            .copy_from_slice(&self.marked_places);

        // Snapshot + clear the dirty set.
        let dirty_words = self.dirty_set.len();
        for w in 0..dirty_words {
            self.dirty_snap_buffer[w] = self.dirty_set[w];
            self.dirty_set[w] = 0;
        }

        let tc = self.compiled.transition_count;
        let mut dirty_tids: Vec<usize> = Vec::new();
        bitmap::for_each_set_bit(&self.dirty_snap_buffer, |tid| {
            if tid < tc {
                dirty_tids.push(tid);
            }
        });

        let marking_snap = self.marking_snap_buffer.clone();
        for tid in dirty_tids {
            let was_enabled = self.enabled_flags[tid];
            let can_now = self.can_enable(tid, &marking_snap);

            if can_now && !was_enabled {
                self.enabled_flags[tid] = true;
                self.enabled_transition_count += 1;
                self.enabled_at_ms[tid] = now_ms;
                changes.newly_enabled.push(tid);
            } else if !can_now && was_enabled {
                self.enabled_flags[tid] = false;
                self.enabled_transition_count -= 1;
                self.enabled_at_ms[tid] = f64::NEG_INFINITY;
            } else if can_now && was_enabled && self.has_input_from_reset_place(tid) {
                self.enabled_at_ms[tid] = now_ms;
                changes.clock_restarted.push(tid);
            }
        }

        self.pending_reset_places.clear();
    }

    fn has_any_deadlines(&self) -> bool {
        self.has_any_deadlines
    }

    fn enforce_deadlines(&mut self, now_ms: f64, out: &mut Vec<usize>) {
        for tid in 0..self.compiled.transition_count {
            if !self.has_deadline_flags[tid] || !self.enabled_flags[tid] {
                continue;
            }
            let t = self.compiled.transition(tid);
            let elapsed = now_ms - self.enabled_at_ms[tid];
            let latest_ms = t.timing().latest() as f64;
            if elapsed > latest_ms + DEADLINE_TOLERANCE_MS {
                self.enabled_flags[tid] = false;
                self.enabled_transition_count -= 1;
                self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                out.push(tid);
            }
        }
    }

    fn fast_path_available(&self) -> bool {
        self.all_immediate && self.all_same_priority
    }

    fn collect_ready_immediate(&mut self, out: &mut Vec<usize>) {
        for tid in 0..self.compiled.transition_count {
            if self.enabled_flags[tid] {
                out.push(tid);
            }
        }
        // Refresh the firing-snapshot buffer so subsequent
        // `recheck_can_fire` calls see the live marking.
        self.firing_snap_buffer.copy_from_slice(&self.marked_places);
    }

    fn collect_ready_general(&mut self, now_ms: f64, out: &mut Vec<usize>) {
        let mut ready: Vec<(usize, i32, f64)> = Vec::new();
        for tid in 0..self.compiled.transition_count {
            if !self.enabled_flags[tid] {
                continue;
            }
            let t = self.compiled.transition(tid);
            let enabled_ms = self.enabled_at_ms[tid];
            let elapsed = now_ms - enabled_ms;
            let earliest_ms = t.timing().earliest() as f64;
            if earliest_ms <= elapsed {
                ready.push((tid, t.priority(), enabled_ms));
            }
        }
        if ready.is_empty() {
            return;
        }

        ready.sort_by(|a, b| {
            b.1.cmp(&a.1)
                .then_with(|| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal))
        });

        self.firing_snap_buffer.copy_from_slice(&self.marked_places);
        out.extend(ready.into_iter().map(|(tid, _, _)| tid));
    }

    fn recheck_can_fire(&mut self, tid: usize) -> bool {
        if !self.enabled_flags[tid] {
            return false;
        }
        // Borrow split: clone the snap buffer so we can call &self.can_enable
        // while keeping the snap buffer field separately accessible.
        let snap = self.firing_snap_buffer.clone();
        self.can_enable(tid, &snap)
    }

    fn consume_for_firing<F>(&mut self, tid: usize, mut emit_removed: F) -> ConsumedInputs
    where
        F: FnMut(&Arc<str>, &ErasedToken),
    {
        // Clone the per-transition spec data so we can mutate the
        // marking without re-borrowing self.compiled inside the loop.
        let (input_specs, read_arcs, reset_arcs) = {
            let t = self.compiled.transition(tid);
            (
                t.input_specs().to_vec(),
                t.reads().to_vec(),
                t.resets().to_vec(),
            )
        };

        let mut inputs: HashMap<Arc<str>, Vec<ErasedToken>> = HashMap::new();
        for in_spec in &input_specs {
            let place_name = in_spec.place_name();
            let to_consume = match in_spec {
                In::One { .. } => 1,
                In::Exactly { count, .. } => *count,
                In::All { guard, .. } | In::AtLeast { guard, .. } => {
                    if guard.is_some() {
                        self.marking
                            .count_matching(place_name, &**guard.as_ref().unwrap())
                    } else {
                        self.marking.count(place_name)
                    }
                }
            };

            let place_name_arc = Arc::clone(in_spec.place().name_arc());
            for _ in 0..to_consume {
                let token = if let Some(guard) = in_spec.guard() {
                    self.marking.remove_matching(place_name, &**guard)
                } else {
                    self.marking.remove_first(place_name)
                };
                if let Some(token) = token {
                    emit_removed(&place_name_arc, &token);
                    inputs
                        .entry(Arc::clone(&place_name_arc))
                        .or_default()
                        .push(token);
                }
            }
        }

        let mut reads: HashMap<Arc<str>, Vec<ErasedToken>> = HashMap::new();
        for arc in &read_arcs {
            if let Some(queue) = self.marking.queue(arc.place.name())
                && let Some(token) = queue.front()
            {
                reads
                    .entry(Arc::clone(arc.place.name_arc()))
                    .or_default()
                    .push(token.clone());
            }
        }

        for arc in &reset_arcs {
            let removed = self.marking.remove_all(arc.place.name());
            self.pending_reset_places
                .insert(Arc::clone(arc.place.name_arc()));
            for tok in &removed {
                emit_removed(arc.place.name_arc(), tok);
            }
        }

        self.update_bitmap_after_consumption(tid);
        // Refresh the firing snapshot so the next `recheck_can_fire`
        // (for the next ready transition this cycle) sees the live
        // marking after this consumption.
        self.firing_snap_buffer.copy_from_slice(&self.marked_places);

        ConsumedInputs { inputs, reads }
    }

    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        self.marking.add_erased(place, token);
        if let Some(pid) = self.compiled.place_id(place) {
            bitmap::set_bit(&mut self.marked_places, pid);
            self.mark_place_dirty(pid);
        }
    }

    fn post_fire(&mut self, tid: usize) {
        if self.enabled_flags[tid] {
            self.enabled_flags[tid] = false;
            self.enabled_transition_count -= 1;
        }
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
        bitmap::set_bit(&mut self.dirty_set, tid);
    }

    fn disable(&mut self, tid: usize) {
        if self.enabled_flags[tid] {
            self.enabled_flags[tid] = false;
            self.enabled_transition_count -= 1;
        }
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
    }

    fn inject_external_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        self.marking.add_erased(place, token);
        if let Some(pid) = self.compiled.place_id(place) {
            bitmap::set_bit(&mut self.marked_places, pid);
            self.mark_place_dirty(pid);
        }
    }

    fn millis_until_next_timed_transition(&self, now_ms: f64) -> f64 {
        let mut min_wait = f64::INFINITY;

        for tid in 0..self.compiled.transition_count {
            if !self.enabled_flags[tid] {
                continue;
            }
            let t = self.compiled.transition(tid);
            let elapsed = now_ms - self.enabled_at_ms[tid];

            let earliest_ms = t.timing().earliest() as f64;
            let remaining_earliest = earliest_ms - elapsed;
            if remaining_earliest <= 0.0 {
                return 0.0;
            }
            min_wait = min_wait.min(remaining_earliest);

            if self.has_deadline_flags[tid] {
                let latest_ms = t.timing().latest() as f64;
                let remaining_deadline = latest_ms - elapsed;
                if remaining_deadline <= 0.0 {
                    return 0.0;
                }
                min_wait = min_wait.min(remaining_deadline);
            }
        }

        min_wait
    }
}
