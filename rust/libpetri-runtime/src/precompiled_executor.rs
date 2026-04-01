use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Instant;

use libpetri_core::context::{OutputEntry, TransitionContext};
use libpetri_core::input::In;
use libpetri_core::token::ErasedToken;

use libpetri_event::event_store::EventStore;
use libpetri_event::net_event::NetEvent;

use crate::bitmap;
use crate::marking::Marking;
use crate::precompiled_net::{
    CONSUME_ALL, CONSUME_ATLEAST, CONSUME_N, CONSUME_ONE, PrecompiledNet, RESET,
};

/// Tolerance for deadline enforcement to account for timer jitter.
const DEADLINE_TOLERANCE_MS: f64 = 5.0;

/// Initial capacity for ring buffer per place.
const INITIAL_RING_CAPACITY: usize = 4;

/// High-performance precompiled flat-array Petri net executor.
///
/// Uses ring-buffer token storage, opcode-based consume operations,
/// priority-partitioned ready queues, and two-level summary bitmaps
/// for sparse iteration. Generic over `E: EventStore` for zero-cost
/// noop event recording.
pub struct PrecompiledNetExecutor<'a, E: EventStore> {
    program: &'a PrecompiledNet<'a>,
    event_store: E,
    #[allow(dead_code)]
    environment_places: HashSet<Arc<str>>,
    has_environment_places: bool,
    #[allow(dead_code)]
    skip_output_validation: bool,

    // ==================== Flat Token Pool ====================
    token_pool: Vec<Option<ErasedToken>>,
    place_offset: Vec<usize>,
    token_counts: Vec<usize>,
    ring_head: Vec<usize>,
    ring_tail: Vec<usize>,
    ring_capacity: Vec<usize>,

    // ==================== Presence Bitmap ====================
    marking_bitmap: Vec<u64>,

    // ==================== Transition State ====================
    enabled_bitmap: Vec<u64>,
    dirty_bitmap: Vec<u64>,
    dirty_scan_buffer: Vec<u64>,
    enabled_at_ms: Vec<f64>,
    enabled_transition_count: usize,

    // ==================== Summary Bitmaps (two-level) ====================
    dirty_word_summary: Vec<u64>,
    enabled_word_summary: Vec<u64>,
    transition_words: usize,
    summary_words: usize,

    // ==================== Priority-Partitioned Ready Queues ====================
    ready_queues: Vec<Vec<usize>>,
    ready_queue_head: Vec<usize>,
    ready_queue_tail: Vec<usize>,
    ready_queue_size: Vec<usize>,

    // ==================== Reset-Clock Detection ====================
    pending_reset_words: Vec<u64>,
    has_pending_resets: bool,

    // ==================== Reusable Buffers (avoid per-firing allocation) ====================
    reusable_inputs: HashMap<Arc<str>, Vec<ErasedToken>>,
    reusable_reads: HashMap<Arc<str>, Vec<ErasedToken>>,

    // ==================== Lifecycle ====================
    start_time: Instant,
}

/// Builder for PrecompiledNetExecutor.
pub struct PrecompiledExecutorBuilder<'a, E: EventStore> {
    program: &'a PrecompiledNet<'a>,
    initial_marking: Marking,
    event_store: Option<E>,
    environment_places: HashSet<Arc<str>>,
    skip_output_validation: bool,
}

impl<'a, E: EventStore> PrecompiledExecutorBuilder<'a, E> {
    /// Sets the event store.
    pub fn event_store(mut self, store: E) -> Self {
        self.event_store = Some(store);
        self
    }

    /// Sets the environment places.
    pub fn environment_places(mut self, places: HashSet<Arc<str>>) -> Self {
        self.environment_places = places;
        self
    }

    /// Skips output validation for trusted transition actions.
    pub fn skip_output_validation(mut self, skip: bool) -> Self {
        self.skip_output_validation = skip;
        self
    }

    /// Builds the executor.
    pub fn build(self) -> PrecompiledNetExecutor<'a, E> {
        PrecompiledNetExecutor::new_inner(
            self.program,
            self.initial_marking,
            self.event_store.unwrap_or_default(),
            self.environment_places,
            self.skip_output_validation,
        )
    }
}

impl<'a, E: EventStore> PrecompiledNetExecutor<'a, E> {
    /// Creates a builder for a PrecompiledNetExecutor.
    pub fn builder(
        program: &'a PrecompiledNet<'a>,
        initial_marking: Marking,
    ) -> PrecompiledExecutorBuilder<'a, E> {
        PrecompiledExecutorBuilder {
            program,
            initial_marking,
            event_store: None,
            environment_places: HashSet::new(),
            skip_output_validation: false,
        }
    }

    /// Creates a new executor with default options.
    pub fn new(program: &'a PrecompiledNet<'a>, initial_marking: Marking) -> Self {
        Self::new_inner(
            program,
            initial_marking,
            E::default(),
            HashSet::new(),
            false,
        )
    }

    fn new_inner(
        program: &'a PrecompiledNet<'a>,
        initial_marking: Marking,
        event_store: E,
        environment_places: HashSet<Arc<str>>,
        skip_output_validation: bool,
    ) -> Self {
        let pc = program.place_count();
        let tc = program.transition_count();
        let wc = program.word_count();

        // Initialize flat token pool
        let total_slots = pc * INITIAL_RING_CAPACITY;
        let mut token_pool = vec![None; total_slots];
        let mut place_offset = vec![0usize; pc];
        let mut token_counts = vec![0usize; pc];
        let mut ring_head = vec![0usize; pc];
        let mut ring_tail = vec![0usize; pc];
        let mut ring_capacity = vec![INITIAL_RING_CAPACITY; pc];

        for (pid, offset) in place_offset.iter_mut().enumerate() {
            *offset = pid * INITIAL_RING_CAPACITY;
        }

        // Load initial tokens into ring buffers
        for pid in 0..pc {
            let place = program.place(pid);
            if let Some(queue) = initial_marking.queue(place.name()) {
                for token in queue {
                    // Ring add last
                    if token_counts[pid] == ring_capacity[pid] {
                        grow_ring_static(
                            &mut token_pool,
                            &mut place_offset,
                            &mut ring_head,
                            &mut ring_tail,
                            &mut ring_capacity,
                            &token_counts,
                            pid,
                        );
                    }
                    let tail = ring_tail[pid];
                    let offset = place_offset[pid];
                    token_pool[offset + tail] = Some(token.clone());
                    ring_tail[pid] = (tail + 1) % ring_capacity[pid];
                    token_counts[pid] += 1;
                }
            }
        }

        // Transition bitmaps
        let transition_words = bitmap::word_count(tc);
        let summary_words = bitmap::word_count(transition_words);

        // Priority-partitioned ready queues
        let prio_count = program.distinct_priority_count;
        let queue_cap = tc.max(4);
        let ready_queues = vec![vec![0usize; queue_cap]; prio_count];
        let ready_queue_head = vec![0usize; prio_count];
        let ready_queue_tail = vec![0usize; prio_count];
        let ready_queue_size = vec![0usize; prio_count];

        Self {
            program,
            event_store,
            has_environment_places: !environment_places.is_empty(),
            environment_places,
            skip_output_validation,
            token_pool,
            place_offset,
            token_counts,
            ring_head,
            ring_tail,
            ring_capacity,
            marking_bitmap: vec![0u64; wc],
            enabled_bitmap: vec![0u64; transition_words],
            dirty_bitmap: vec![0u64; transition_words],
            dirty_scan_buffer: vec![0u64; transition_words],
            enabled_at_ms: vec![f64::NEG_INFINITY; tc],
            enabled_transition_count: 0,
            dirty_word_summary: vec![0u64; summary_words],
            enabled_word_summary: vec![0u64; summary_words],
            transition_words,
            summary_words,
            ready_queues,
            ready_queue_head,
            ready_queue_tail,
            ready_queue_size,
            pending_reset_words: vec![0u64; wc],
            has_pending_resets: false,
            reusable_inputs: HashMap::new(),
            reusable_reads: HashMap::new(),
            start_time: Instant::now(),
        }
    }

    // ==================== Public API ====================

    /// Runs the executor synchronously until completion.
    /// Returns the final marking (materialized from ring buffers).
    pub fn run_sync(&mut self) -> Marking {
        self.run_to_completion()
    }

    /// Returns the materialized marking (synced from ring buffers).
    pub fn marking(&self) -> Marking {
        self.materialize_marking()
    }

    /// Returns a reference to the event store.
    pub fn event_store(&self) -> &E {
        &self.event_store
    }

    /// Returns true if the executor is quiescent.
    pub fn is_quiescent(&self) -> bool {
        self.enabled_transition_count == 0
    }

    // ==================== Ring Buffer Operations ====================

    #[inline]
    fn ring_remove_first(&mut self, pid: usize) -> ErasedToken {
        let head = self.ring_head[pid];
        let offset = self.place_offset[pid];
        let token = self.token_pool[offset + head].take().unwrap();
        self.ring_head[pid] = (head + 1) % self.ring_capacity[pid];
        self.token_counts[pid] -= 1;
        token
    }

    #[inline]
    fn ring_add_last(&mut self, pid: usize, token: ErasedToken) {
        if self.token_counts[pid] == self.ring_capacity[pid] {
            self.grow_ring(pid);
        }
        let tail = self.ring_tail[pid];
        let offset = self.place_offset[pid];
        self.token_pool[offset + tail] = Some(token);
        self.ring_tail[pid] = (tail + 1) % self.ring_capacity[pid];
        self.token_counts[pid] += 1;
    }

    #[inline]
    fn ring_peek_first(&self, pid: usize) -> Option<&ErasedToken> {
        if self.token_counts[pid] == 0 {
            return None;
        }
        self.token_pool[self.place_offset[pid] + self.ring_head[pid]].as_ref()
    }

    fn ring_remove_all(&mut self, pid: usize) -> Vec<ErasedToken> {
        let count = self.token_counts[pid];
        if count == 0 {
            return Vec::new();
        }
        let mut result = Vec::with_capacity(count);
        for _ in 0..count {
            result.push(self.ring_remove_first(pid));
        }
        result
    }

    fn grow_ring(&mut self, pid: usize) {
        grow_ring_static(
            &mut self.token_pool,
            &mut self.place_offset,
            &mut self.ring_head,
            &mut self.ring_tail,
            &mut self.ring_capacity,
            &self.token_counts,
            pid,
        );
    }

    // ==================== Bitmap Helpers ====================

    #[inline]
    fn set_enabled_bit(&mut self, tid: usize) {
        let w = tid >> bitmap::WORD_SHIFT;
        self.enabled_bitmap[w] |= 1u64 << (tid & bitmap::WORD_MASK);
        self.enabled_word_summary[w >> bitmap::WORD_SHIFT] |= 1u64 << (w & bitmap::WORD_MASK);
    }

    #[inline]
    fn clear_enabled_bit(&mut self, tid: usize) {
        let w = tid >> bitmap::WORD_SHIFT;
        self.enabled_bitmap[w] &= !(1u64 << (tid & bitmap::WORD_MASK));
        if self.enabled_bitmap[w] == 0 {
            self.enabled_word_summary[w >> bitmap::WORD_SHIFT] &=
                !(1u64 << (w & bitmap::WORD_MASK));
        }
    }

    #[inline]
    fn is_enabled(&self, tid: usize) -> bool {
        (self.enabled_bitmap[tid >> bitmap::WORD_SHIFT] & (1u64 << (tid & bitmap::WORD_MASK))) != 0
    }

    #[inline]
    fn set_marking_bit(&mut self, pid: usize) {
        bitmap::set_bit(&mut self.marking_bitmap, pid);
    }

    #[inline]
    fn clear_marking_bit(&mut self, pid: usize) {
        bitmap::clear_bit(&mut self.marking_bitmap, pid);
    }

    // ==================== Ready Queue Operations ====================

    fn ready_queue_push(&mut self, tid: usize) {
        let pi = self.program.transition_to_priority_index[tid];
        if self.ready_queue_size[pi] == self.ready_queues[pi].len() {
            let old_cap = self.ready_queues[pi].len();
            let new_cap = old_cap * 2;
            let mut new_queue = vec![0usize; new_cap];
            let head = self.ready_queue_head[pi];
            for (i, slot) in new_queue.iter_mut().enumerate().take(old_cap) {
                *slot = self.ready_queues[pi][(head + i) % old_cap];
            }
            self.ready_queues[pi] = new_queue;
            self.ready_queue_head[pi] = 0;
            self.ready_queue_tail[pi] = old_cap;
        }
        let tail = self.ready_queue_tail[pi];
        self.ready_queues[pi][tail] = tid;
        self.ready_queue_tail[pi] = (tail + 1) % self.ready_queues[pi].len();
        self.ready_queue_size[pi] += 1;
    }

    fn ready_queue_pop(&mut self, pi: usize) -> usize {
        let head = self.ready_queue_head[pi];
        let tid = self.ready_queues[pi][head];
        self.ready_queue_head[pi] = (head + 1) % self.ready_queues[pi].len();
        self.ready_queue_size[pi] -= 1;
        tid
    }

    fn clear_all_ready_queues(&mut self) {
        for pi in 0..self.program.distinct_priority_count {
            self.ready_queue_head[pi] = 0;
            self.ready_queue_tail[pi] = 0;
            self.ready_queue_size[pi] = 0;
        }
    }

    // ==================== Initialize ====================

    fn initialize_marking_bitmap(&mut self) {
        for pid in 0..self.program.place_count() {
            if self.token_counts[pid] > 0 {
                self.set_marking_bit(pid);
            }
        }
    }

    fn mark_all_dirty(&mut self) {
        let tc = self.program.transition_count();
        let last_word_bits = tc & bitmap::WORD_MASK;
        for w in 0..self.transition_words.saturating_sub(1) {
            self.dirty_bitmap[w] = u64::MAX;
        }
        if self.transition_words > 0 {
            self.dirty_bitmap[self.transition_words - 1] = if last_word_bits == 0 {
                u64::MAX
            } else {
                (1u64 << last_word_bits) - 1
            };
        }
        // Set all summary bits
        for s in 0..self.summary_words {
            let first_w = s << bitmap::WORD_SHIFT;
            let last_w = (first_w + bitmap::WORD_MASK).min(self.transition_words.saturating_sub(1));
            let count = last_w - first_w + 1;
            let last_bits = count & bitmap::WORD_MASK;
            self.dirty_word_summary[s] = if last_bits == 0 {
                u64::MAX
            } else {
                (1u64 << last_bits) - 1
            };
        }
    }

    fn should_terminate(&self) -> bool {
        if self.has_environment_places {
            return false;
        }
        self.enabled_transition_count == 0
    }

    // ==================== Dirty Set Processing ====================

    fn update_dirty_transitions(&mut self) {
        let now_ms = self.elapsed_ms();

        // Snapshot and clear dirty bitmap using summary
        for s in 0..self.summary_words {
            let mut summary = self.dirty_word_summary[s];
            self.dirty_word_summary[s] = 0;
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w < self.transition_words {
                    self.dirty_scan_buffer[w] = self.dirty_bitmap[w];
                    self.dirty_bitmap[w] = 0;
                }
            }
        }

        // Process dirty transitions
        let tc = self.program.transition_count();
        for w in 0..self.transition_words {
            let mut word = self.dirty_scan_buffer[w];
            if word == 0 {
                continue;
            }
            self.dirty_scan_buffer[w] = 0;
            while word != 0 {
                let bit = word.trailing_zeros() as usize;
                let tid = (w << bitmap::WORD_SHIFT) | bit;
                word &= word - 1;

                if tid >= tc {
                    break;
                }

                let was_enabled = self.is_enabled(tid);
                let can_now = self.can_enable(tid);

                if can_now && !was_enabled {
                    self.set_enabled_bit(tid);
                    self.enabled_transition_count += 1;
                    self.enabled_at_ms[tid] = now_ms;

                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionEnabled {
                            transition_name: Arc::clone(self.program.transition(tid).name_arc()),
                            timestamp: now_millis(),
                        });
                    }
                } else if !can_now && was_enabled {
                    self.clear_enabled_bit(tid);
                    self.enabled_transition_count -= 1;
                    self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                } else if can_now && was_enabled && self.has_input_from_reset_place(tid) {
                    self.enabled_at_ms[tid] = now_ms;
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionClockRestarted {
                            transition_name: Arc::clone(self.program.transition(tid).name_arc()),
                            timestamp: now_millis(),
                        });
                    }
                }
            }
        }

        self.clear_pending_resets();
    }

    fn can_enable(&self, tid: usize) -> bool {
        if !self.program.can_enable_bitmap(tid, &self.marking_bitmap) {
            return false;
        }

        // Cardinality check using token_counts directly (no HashMap lookup)
        if let Some(card_check) = self.program.compiled().cardinality_check(tid) {
            for i in 0..card_check.place_ids.len() {
                let pid = card_check.place_ids[i];
                let required = card_check.required_counts[i];
                if self.token_counts[pid] < required {
                    return false;
                }
            }
        }

        // Guard check (needs token access)
        if self.program.compiled().has_guards(tid) {
            let t = self.program.transition(tid);
            for spec in t.input_specs() {
                if let Some(guard) = spec.guard() {
                    let required = match spec {
                        In::One { .. } => 1,
                        In::Exactly { count, .. } => *count,
                        In::AtLeast { minimum, .. } => *minimum,
                        In::All { .. } => 1,
                    };
                    let pid = self.program.place_id(spec.place_name()).unwrap();
                    let count = self.count_matching_in_ring(pid, &**guard);
                    if count < required {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn count_matching_in_ring(
        &self,
        pid: usize,
        guard: &dyn Fn(&dyn std::any::Any) -> bool,
    ) -> usize {
        let count = self.token_counts[pid];
        if count == 0 {
            return 0;
        }
        let offset = self.place_offset[pid];
        let head = self.ring_head[pid];
        let cap = self.ring_capacity[pid];
        let mut matched = 0;
        for i in 0..count {
            let idx = offset + (head + i) % cap;
            if let Some(token) = &self.token_pool[idx]
                && guard(token.value.as_ref())
            {
                matched += 1;
            }
        }
        matched
    }

    fn has_input_from_reset_place(&self, tid: usize) -> bool {
        if !self.has_pending_resets {
            return false;
        }
        let input_mask = &self.program.input_place_mask_words[tid];
        for (im, pr) in input_mask.iter().zip(self.pending_reset_words.iter()) {
            if (im & pr) != 0 {
                return true;
            }
        }
        false
    }

    fn clear_pending_resets(&mut self) {
        if self.has_pending_resets {
            for w in &mut self.pending_reset_words {
                *w = 0;
            }
            self.has_pending_resets = false;
        }
    }

    // ==================== Deadline Enforcement ====================

    fn enforce_deadlines(&mut self, now_ms: f64) {
        for s in 0..self.summary_words {
            let mut summary = self.enabled_word_summary[s];
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w >= self.transition_words {
                    continue;
                }
                let mut word = self.enabled_bitmap[w];
                while word != 0 {
                    let bit = word.trailing_zeros() as usize;
                    let tid = (w << bitmap::WORD_SHIFT) | bit;
                    word &= word - 1;

                    if !self.program.has_deadline[tid] {
                        continue;
                    }

                    let elapsed = now_ms - self.enabled_at_ms[tid];
                    let latest_ms = self.program.latest_ms[tid];

                    if elapsed > latest_ms + DEADLINE_TOLERANCE_MS {
                        self.clear_enabled_bit(tid);
                        self.enabled_transition_count -= 1;
                        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                        self.mark_transition_dirty(tid);

                        if E::ENABLED {
                            self.event_store.append(NetEvent::TransitionTimedOut {
                                transition_name: Arc::clone(
                                    self.program.transition(tid).name_arc(),
                                ),
                                timestamp: now_millis(),
                            });
                        }
                    }
                }
            }
        }
    }

    // ==================== Firing (Sync) ====================

    fn fire_ready_immediate_sync(&mut self) {
        for s in 0..self.summary_words {
            let mut summary = self.enabled_word_summary[s];
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w >= self.transition_words {
                    continue;
                }
                let word = self.enabled_bitmap[w];
                let mut remaining = word;
                while remaining != 0 {
                    let bit = remaining.trailing_zeros() as usize;
                    let tid = (w << bitmap::WORD_SHIFT) | bit;
                    remaining &= remaining - 1;

                    if self.can_enable(tid) {
                        self.fire_transition_sync(tid);
                    } else {
                        self.clear_enabled_bit(tid);
                        self.enabled_transition_count -= 1;
                        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                    }
                }
            }
        }
    }

    fn fire_ready_general_sync(&mut self, now_ms: f64) {
        // Populate ready queues from enabled bitmap using summary
        self.clear_all_ready_queues();

        for s in 0..self.summary_words {
            let mut summary = self.enabled_word_summary[s];
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w >= self.transition_words {
                    continue;
                }
                let mut word = self.enabled_bitmap[w];
                while word != 0 {
                    let bit = word.trailing_zeros() as usize;
                    let tid = (w << bitmap::WORD_SHIFT) | bit;
                    word &= word - 1;

                    let enabled_ms = self.enabled_at_ms[tid];
                    let elapsed = now_ms - enabled_ms;

                    if self.program.earliest_ms[tid] <= elapsed {
                        self.ready_queue_push(tid);
                    }
                }
            }
        }

        // Fire from highest priority queue first
        for pi in 0..self.program.distinct_priority_count {
            while self.ready_queue_size[pi] > 0 {
                let tid = self.ready_queue_pop(pi);
                if !self.is_enabled(tid) {
                    continue;
                }

                if self.can_enable(tid) {
                    self.fire_transition_sync(tid);
                } else {
                    self.clear_enabled_bit(tid);
                    self.enabled_transition_count -= 1;
                    self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                }
            }
        }
    }

    // ==================== Opcode-Based Consume ====================

    fn fire_transition_sync(&mut self, tid: usize) {
        let has_guards = self.program.compiled().has_guards(tid);
        let transition_name = Arc::clone(&self.program.transition_name_arcs[tid]);
        let action = Arc::clone(self.program.transition(tid).action());

        // Reuse pre-allocated input/read buffers (clear entries, keep HashMap capacity)
        self.reusable_inputs.clear();
        self.reusable_reads.clear();

        if has_guards {
            // Fall back to spec-based consumption for guarded transitions
            let input_specs: Vec<In> = self.program.transition(tid).input_specs().to_vec();
            let reset_arcs: Vec<_> = self.program.transition(tid).resets().to_vec();

            for in_spec in &input_specs {
                let pid = self.program.place_id(in_spec.place_name()).unwrap();
                let place_name_arc = Arc::clone(&self.program.place_name_arcs[pid]);
                let to_consume = match in_spec {
                    In::One { .. } => 1,
                    In::Exactly { count, .. } => *count,
                    In::All { guard, .. } | In::AtLeast { guard, .. } => {
                        if guard.is_some() {
                            self.count_matching_in_ring(pid, &**guard.as_ref().unwrap())
                        } else {
                            self.token_counts[pid]
                        }
                    }
                };

                for _ in 0..to_consume {
                    let token = if let Some(guard) = in_spec.guard() {
                        self.ring_remove_matching(pid, &**guard)
                    } else {
                        Some(self.ring_remove_first(pid))
                    };
                    if let Some(token) = token {
                        if E::ENABLED {
                            self.event_store.append(NetEvent::TokenRemoved {
                                place_name: Arc::clone(&place_name_arc),
                                timestamp: now_millis(),
                            });
                        }
                        self.reusable_inputs
                            .entry(Arc::clone(&place_name_arc))
                            .or_default()
                            .push(token);
                    }
                }
            }

            // Reset arcs
            for arc in &reset_arcs {
                let pid = self.program.place_id(arc.place.name()).unwrap();
                let removed = self.ring_remove_all(pid);
                if E::ENABLED {
                    for _ in &removed {
                        self.event_store.append(NetEvent::TokenRemoved {
                            place_name: Arc::clone(arc.place.name_arc()),
                            timestamp: now_millis(),
                        });
                    }
                }
                self.pending_reset_words[pid >> bitmap::WORD_SHIFT] |=
                    1u64 << (pid & bitmap::WORD_MASK);
                self.has_pending_resets = true;
            }
        } else {
            // Fast path: opcode-based consumption (no guards, no clone)
            let ops_len = self.program.consume_ops[tid].len();
            let mut pc = 0;
            while pc < ops_len {
                let opcode = self.program.consume_ops[tid][pc];
                pc += 1;
                match opcode {
                    CONSUME_ONE => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        let token = self.ring_remove_first(pid);
                        if E::ENABLED {
                            self.event_store.append(NetEvent::TokenRemoved {
                                place_name: Arc::clone(&self.program.place_name_arcs[pid]),
                                timestamp: now_millis(),
                            });
                        }
                        self.reusable_inputs
                            .entry(Arc::clone(&self.program.place_name_arcs[pid]))
                            .or_default()
                            .push(token);
                    }
                    CONSUME_N => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        let count = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        for _ in 0..count {
                            let token = self.ring_remove_first(pid);
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TokenRemoved {
                                    place_name: Arc::clone(&self.program.place_name_arcs[pid]),
                                    timestamp: now_millis(),
                                });
                            }
                            self.reusable_inputs
                                .entry(Arc::clone(&self.program.place_name_arcs[pid]))
                                .or_default()
                                .push(token);
                        }
                    }
                    CONSUME_ALL | CONSUME_ATLEAST => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        if opcode == CONSUME_ATLEAST {
                            pc += 1;
                        }
                        let count = self.token_counts[pid];
                        for _ in 0..count {
                            let token = self.ring_remove_first(pid);
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TokenRemoved {
                                    place_name: Arc::clone(&self.program.place_name_arcs[pid]),
                                    timestamp: now_millis(),
                                });
                            }
                            self.reusable_inputs
                                .entry(Arc::clone(&self.program.place_name_arcs[pid]))
                                .or_default()
                                .push(token);
                        }
                    }
                    RESET => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        let count = self.token_counts[pid];
                        for _ in 0..count {
                            let _token = self.ring_remove_first(pid);
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TokenRemoved {
                                    place_name: Arc::clone(&self.program.place_name_arcs[pid]),
                                    timestamp: now_millis(),
                                });
                            }
                        }
                        self.pending_reset_words[pid >> bitmap::WORD_SHIFT] |=
                            1u64 << (pid & bitmap::WORD_MASK);
                        self.has_pending_resets = true;
                    }
                    _ => unreachable!("Unknown opcode: {opcode}"),
                }
            }
        }

        // Execute read program — iterate by index, no clone of ops Vec
        let read_ops_len = self.program.read_ops[tid].len();
        for i in 0..read_ops_len {
            let rpid = self.program.read_ops[tid][i];
            let token_clone = self.ring_peek_first(rpid).cloned();
            if let Some(token) = token_clone {
                let place_name = Arc::clone(&self.program.place_name_arcs[rpid]);
                self.reusable_reads
                    .entry(place_name)
                    .or_default()
                    .push(token);
            }
        }

        // Update bitmap for consumed/reset places
        self.update_bitmap_after_consumption(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        // Create context using precomputed output place names and reusable buffers
        let inputs = std::mem::take(&mut self.reusable_inputs);
        let reads = std::mem::take(&mut self.reusable_reads);
        let mut ctx = TransitionContext::new(
            Arc::clone(&transition_name),
            inputs,
            reads,
            self.program.output_place_name_sets[tid].clone(),
            None,
        );

        let result = action.run_sync(&mut ctx);

        // Reclaim buffers for reuse — keeps HashMap bucket allocations alive
        let returned_inputs = ctx.take_inputs();
        let returned_reads = ctx.take_reads();

        match result {
            Ok(()) => {
                let outputs = ctx.take_outputs();
                self.process_outputs(tid, &transition_name, outputs);

                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionCompleted {
                        transition_name: Arc::clone(&transition_name),
                        timestamp: now_millis(),
                    });
                }
            }
            Err(err) => {
                if E::ENABLED {
                    self.event_store.append(NetEvent::TransitionFailed {
                        transition_name: Arc::clone(&transition_name),
                        error: err.message,
                        timestamp: now_millis(),
                    });
                }
            }
        }

        // Return reclaimed buffers for next firing
        self.reusable_inputs = returned_inputs;
        self.reusable_reads = returned_reads;

        // Clear enabled status
        self.clear_enabled_bit(tid);
        self.enabled_transition_count -= 1;
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;

        // Mark this transition dirty for re-evaluation
        self.mark_transition_dirty(tid);
    }

    /// Removes the first token matching `guard` from the ring buffer at `pid`.
    /// Returns at most one token per call (In::One guard semantics).
    fn ring_remove_matching(
        &mut self,
        pid: usize,
        guard: &dyn Fn(&dyn std::any::Any) -> bool,
    ) -> Option<ErasedToken> {
        let count = self.token_counts[pid];
        if count == 0 {
            return None;
        }
        let offset = self.place_offset[pid];
        let head = self.ring_head[pid];
        let cap = self.ring_capacity[pid];

        // Find first matching token
        for i in 0..count {
            let idx = offset + (head + i) % cap;
            if let Some(token) = &self.token_pool[idx]
                && guard(token.value.as_ref())
            {
                let token = self.token_pool[idx].take().unwrap();
                // Compact the ring by shifting remaining elements
                for j in i..count - 1 {
                    let from = offset + (head + j + 1) % cap;
                    let to = offset + (head + j) % cap;
                    self.token_pool[to] = self.token_pool[from].take();
                }
                self.token_counts[pid] -= 1;
                self.ring_tail[pid] = if self.ring_tail[pid] == 0 {
                    cap - 1
                } else {
                    self.ring_tail[pid] - 1
                };
                return Some(token);
            }
        }
        None
    }

    fn process_outputs(
        &mut self,
        _tid: usize,
        _transition_name: &Arc<str>,
        outputs: Vec<OutputEntry>,
    ) {
        for entry in outputs {
            if let Some(pid) = self.program.place_id(&entry.place_name) {
                self.ring_add_last(pid, entry.token);
                self.set_marking_bit(pid);
                self.mark_dirty(pid);
            }

            if E::ENABLED {
                self.event_store.append(NetEvent::TokenAdded {
                    place_name: Arc::clone(&entry.place_name),
                    timestamp: now_millis(),
                });
            }
        }
    }

    fn update_bitmap_after_consumption(&mut self, tid: usize) {
        let n = self.program.compiled().consumption_place_ids(tid).len();
        for i in 0..n {
            let pid = self.program.compiled().consumption_place_ids(tid)[i];
            if self.token_counts[pid] == 0 {
                self.clear_marking_bit(pid);
            }
            self.mark_dirty(pid);
        }
    }

    // ==================== Dirty Set Helpers ====================

    fn has_dirty_bits(&self) -> bool {
        for &s in &self.dirty_word_summary {
            if s != 0 {
                return true;
            }
        }
        false
    }

    fn mark_dirty(&mut self, pid: usize) {
        let n = self.program.compiled().affected_transitions(pid).len();
        for i in 0..n {
            let tid = self.program.compiled().affected_transitions(pid)[i];
            self.mark_transition_dirty(tid);
        }
    }

    fn mark_transition_dirty(&mut self, tid: usize) {
        let w = tid >> bitmap::WORD_SHIFT;
        self.dirty_bitmap[w] |= 1u64 << (tid & bitmap::WORD_MASK);
        self.dirty_word_summary[w >> bitmap::WORD_SHIFT] |= 1u64 << (w & bitmap::WORD_MASK);
    }

    fn elapsed_ms(&self) -> f64 {
        self.start_time.elapsed().as_secs_f64() * 1000.0
    }

    // ==================== Marking Sync ====================

    fn materialize_marking(&self) -> Marking {
        let mut marking = Marking::new();
        for pid in 0..self.program.place_count() {
            let count = self.token_counts[pid];
            if count == 0 {
                continue;
            }
            let place_name = self.program.place(pid).name_arc();
            let offset = self.place_offset[pid];
            let head = self.ring_head[pid];
            let cap = self.ring_capacity[pid];
            for i in 0..count {
                let idx = offset + (head + i) % cap;
                if let Some(token) = &self.token_pool[idx] {
                    marking.add_erased(place_name, token.clone());
                }
            }
        }
        marking
    }

    /// Runs the executor synchronously and returns the final marking.
    fn run_to_completion(&mut self) -> Marking {
        self.initialize_marking_bitmap();
        self.mark_all_dirty();

        if E::ENABLED {
            let now = now_millis();
            self.event_store.append(NetEvent::ExecutionStarted {
                net_name: Arc::from(self.program.net().name()),
                timestamp: now,
            });
        }

        loop {
            self.update_dirty_transitions();

            let cycle_now = self.elapsed_ms();

            if self.program.any_deadlines {
                self.enforce_deadlines(cycle_now);
            }

            if self.should_terminate() {
                break;
            }

            if self.program.all_immediate && self.program.all_same_priority {
                self.fire_ready_immediate_sync();
            } else {
                self.fire_ready_general_sync(cycle_now);
            }

            if !self.has_dirty_bits() && self.enabled_transition_count == 0 {
                break;
            }
        }

        if E::ENABLED {
            let now = now_millis();
            self.event_store.append(NetEvent::ExecutionCompleted {
                net_name: Arc::from(self.program.net().name()),
                timestamp: now,
            });
        }

        self.materialize_marking()
    }
}

// Async path
#[cfg(feature = "tokio")]
use crate::environment::ExecutorSignal;

#[cfg(feature = "tokio")]
struct ActionCompletion {
    transition_name: Arc<str>,
    result: Result<Vec<OutputEntry>, String>,
}

#[cfg(feature = "tokio")]
impl<'a, E: EventStore> PrecompiledNetExecutor<'a, E> {
    /// Runs the executor asynchronously with tokio.
    ///
    /// External events are injected via [`ExecutorSignal::Event`]. Lifecycle
    /// signals [`ExecutorSignal::Drain`] and [`ExecutorSignal::Close`] control
    /// graceful and immediate shutdown respectively. Use
    /// [`ExecutorHandle`](crate::executor_handle::ExecutorHandle) for RAII-managed
    /// lifecycle with automatic drain on drop.
    pub async fn run_async(
        &mut self,
        mut signal_rx: tokio::sync::mpsc::UnboundedReceiver<ExecutorSignal>,
    ) -> Marking {
        let (completion_tx, mut completion_rx) =
            tokio::sync::mpsc::unbounded_channel::<ActionCompletion>();

        self.initialize_marking_bitmap();
        self.mark_all_dirty();

        let mut in_flight_count: usize = 0;
        let mut signal_channel_open = true;
        let mut draining = false;
        let mut closed = false;

        if E::ENABLED {
            let now = now_millis();
            self.event_store.append(NetEvent::ExecutionStarted {
                net_name: Arc::from(self.program.net().name()),
                timestamp: now,
            });
        }

        loop {
            // Phase 1: Process completed async actions
            while let Ok(completion) = completion_rx.try_recv() {
                in_flight_count -= 1;
                match completion.result {
                    Ok(outputs) => {
                        self.process_outputs(0, &completion.transition_name, outputs);
                        if E::ENABLED {
                            self.event_store.append(NetEvent::TransitionCompleted {
                                transition_name: Arc::clone(&completion.transition_name),
                                timestamp: now_millis(),
                            });
                        }
                    }
                    Err(err) => {
                        if E::ENABLED {
                            self.event_store.append(NetEvent::TransitionFailed {
                                transition_name: Arc::clone(&completion.transition_name),
                                error: err,
                                timestamp: now_millis(),
                            });
                        }
                    }
                }
            }

            // Phase 2: Process signals (external events + lifecycle)
            while let Ok(signal) = signal_rx.try_recv() {
                match signal {
                    ExecutorSignal::Event(event) if !draining => {
                        if let Some(pid) = self.program.place_id(&event.place_name) {
                            self.ring_add_last(pid, event.token);
                            self.set_marking_bit(pid);
                            self.mark_dirty(pid);
                        }
                        if E::ENABLED {
                            self.event_store.append(NetEvent::TokenAdded {
                                place_name: Arc::clone(&event.place_name),
                                timestamp: now_millis(),
                            });
                        }
                    }
                    ExecutorSignal::Event(_) => {
                        // Draining: discard events arriving after drain signal
                    }
                    ExecutorSignal::Drain => {
                        draining = true;
                    }
                    ExecutorSignal::Close => {
                        closed = true;
                        draining = true;
                        // Discard remaining queued signals per ENV-013.
                        // Note: events already processed earlier in this try_recv batch
                        // are kept (single-channel design); Java/TS discard all queued
                        // events via an atomic flag checked at processExternalEvents() entry.
                        while signal_rx.try_recv().is_ok() {}
                    }
                }
            }

            // Phase 3: Update dirty transitions
            self.update_dirty_transitions();

            // Phase 4: Enforce deadlines
            let cycle_now = self.elapsed_ms();
            if self.program.any_deadlines {
                self.enforce_deadlines(cycle_now);
            }

            // Termination check — O(1) flag checks
            if closed && in_flight_count == 0 {
                break; // ENV-013: immediate close, in-flight completed
            }
            if draining
                && self.enabled_transition_count == 0
                && in_flight_count == 0
            {
                break; // ENV-011: graceful drain, quiescent
            }
            if self.enabled_transition_count == 0
                && in_flight_count == 0
                && (!self.has_environment_places || !signal_channel_open)
            {
                break; // Standard termination
            }

            // Phase 5: Fire ready transitions
            let fired = self.fire_ready_async(cycle_now, &completion_tx, &mut in_flight_count);

            if fired || self.has_dirty_bits() {
                tokio::task::yield_now().await;
                continue;
            }

            // Phase 6: Await work (completion, external event, or timer)
            if in_flight_count == 0 && !self.has_environment_places
                && self.enabled_transition_count == 0
            {
                break;
            }
            if in_flight_count == 0
                && self.enabled_transition_count == 0
                && (draining || !signal_channel_open)
            {
                break;
            }

            let timer_ms = self.millis_until_next_timed_transition();

            tokio::select! {
                Some(completion) = completion_rx.recv() => {
                    in_flight_count -= 1;
                    match completion.result {
                        Ok(outputs) => {
                            self.process_outputs(0, &completion.transition_name, outputs);
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TransitionCompleted {
                                    transition_name: Arc::clone(&completion.transition_name),
                                    timestamp: now_millis(),
                                });
                            }
                        }
                        Err(err) => {
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TransitionFailed {
                                    transition_name: Arc::clone(&completion.transition_name),
                                    error: err,
                                    timestamp: now_millis(),
                                });
                            }
                        }
                    }
                }
                result = signal_rx.recv(), if signal_channel_open && !closed => {
                    match result {
                        Some(ExecutorSignal::Event(event)) if !draining => {
                            if let Some(pid) = self.program.place_id(&event.place_name) {
                                self.ring_add_last(pid, event.token);
                                self.set_marking_bit(pid);
                                self.mark_dirty(pid);
                            }
                            if E::ENABLED {
                                self.event_store.append(NetEvent::TokenAdded {
                                    place_name: Arc::clone(&event.place_name),
                                    timestamp: now_millis(),
                                });
                            }
                        }
                        Some(ExecutorSignal::Event(_)) => {
                            // Draining: discard events
                        }
                        Some(ExecutorSignal::Drain) => {
                            draining = true;
                        }
                        Some(ExecutorSignal::Close) => {
                            closed = true;
                            draining = true;
                            while signal_rx.try_recv().is_ok() {}
                        }
                        None => {
                            signal_channel_open = false;
                        }
                    }
                }
                _ = tokio::time::sleep(std::time::Duration::from_millis(
                    if timer_ms < f64::INFINITY { timer_ms as u64 } else { 60_000 }
                )) => {}
            }
        }

        if E::ENABLED {
            let now = now_millis();
            self.event_store.append(NetEvent::ExecutionCompleted {
                net_name: Arc::from(self.program.net().name()),
                timestamp: now,
            });
        }

        self.materialize_marking()
    }

    fn fire_ready_async(
        &mut self,
        now_ms: f64,
        completion_tx: &tokio::sync::mpsc::UnboundedSender<ActionCompletion>,
        in_flight_count: &mut usize,
    ) -> bool {
        let mut ready: Vec<(usize, i32, f64)> = Vec::new();

        for s in 0..self.summary_words {
            let mut summary = self.enabled_word_summary[s];
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w >= self.transition_words {
                    continue;
                }
                let mut word = self.enabled_bitmap[w];
                while word != 0 {
                    let bit = word.trailing_zeros() as usize;
                    let tid = (w << bitmap::WORD_SHIFT) | bit;
                    word &= word - 1;

                    let enabled_ms = self.enabled_at_ms[tid];
                    let elapsed = now_ms - enabled_ms;
                    if self.program.earliest_ms[tid] <= elapsed {
                        ready.push((tid, self.program.priorities[tid], enabled_ms));
                    }
                }
            }
        }

        if ready.is_empty() {
            return false;
        }

        ready.sort_by(|a, b| {
            b.1.cmp(&a.1)
                .then_with(|| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal))
        });

        let mut fired_any = false;
        for (tid, _, _) in ready {
            if self.is_enabled(tid) && self.can_enable(tid) {
                self.fire_transition_async(tid, completion_tx, in_flight_count);
                fired_any = true;
            } else if self.is_enabled(tid) {
                self.clear_enabled_bit(tid);
                self.enabled_transition_count -= 1;
                self.enabled_at_ms[tid] = f64::NEG_INFINITY;
            }
        }
        fired_any
    }

    fn fire_transition_async(
        &mut self,
        tid: usize,
        completion_tx: &tokio::sync::mpsc::UnboundedSender<ActionCompletion>,
        in_flight_count: &mut usize,
    ) {
        let t = self.program.transition(tid);
        let transition_name = Arc::clone(&self.program.transition_name_arcs[tid]);
        let input_specs: Vec<In> = t.input_specs().to_vec();
        let read_arcs: Vec<_> = t.reads().to_vec();
        let reset_arcs: Vec<_> = t.resets().to_vec();
        let output_place_names = self.program.output_place_name_sets[tid].clone();
        let action = Arc::clone(t.action());
        let is_sync = action.is_sync();

        // Consume tokens (using spec-based for simplicity in async path)
        let mut inputs: HashMap<Arc<str>, Vec<ErasedToken>> = HashMap::new();
        for in_spec in &input_specs {
            let pid = self.program.place_id(in_spec.place_name()).unwrap();
            let to_consume = match in_spec {
                In::One { .. } => 1,
                In::Exactly { count, .. } => *count,
                In::All { guard, .. } | In::AtLeast { guard, .. } => {
                    if guard.is_some() {
                        self.count_matching_in_ring(pid, &**guard.as_ref().unwrap())
                    } else {
                        self.token_counts[pid]
                    }
                }
            };

            let place_name_arc = Arc::clone(in_spec.place().name_arc());
            for _ in 0..to_consume {
                let token = if let Some(guard) = in_spec.guard() {
                    self.ring_remove_matching(pid, &**guard)
                } else {
                    Some(self.ring_remove_first(pid))
                };
                if let Some(token) = token {
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TokenRemoved {
                            place_name: Arc::clone(&place_name_arc),
                            timestamp: now_millis(),
                        });
                    }
                    inputs
                        .entry(Arc::clone(&place_name_arc))
                        .or_default()
                        .push(token);
                }
            }
        }

        // Read arcs
        let mut read_tokens: HashMap<Arc<str>, Vec<ErasedToken>> = HashMap::new();
        for arc in &read_arcs {
            let rpid = self.program.place_id(arc.place.name()).unwrap();
            if let Some(token) = self.ring_peek_first(rpid) {
                read_tokens
                    .entry(Arc::clone(arc.place.name_arc()))
                    .or_default()
                    .push(token.clone());
            }
        }

        // Reset arcs
        for arc in &reset_arcs {
            let pid = self.program.place_id(arc.place.name()).unwrap();
            let removed = self.ring_remove_all(pid);
            if E::ENABLED {
                for _ in &removed {
                    self.event_store.append(NetEvent::TokenRemoved {
                        place_name: Arc::clone(arc.place.name_arc()),
                        timestamp: now_millis(),
                    });
                }
            }
            self.pending_reset_words[pid >> bitmap::WORD_SHIFT] |=
                1u64 << (pid & bitmap::WORD_MASK);
            self.has_pending_resets = true;
        }

        self.update_bitmap_after_consumption(tid);

        if E::ENABLED {
            self.event_store.append(NetEvent::TransitionStarted {
                transition_name: Arc::clone(&transition_name),
                timestamp: now_millis(),
            });
        }

        // Clear enabled status
        self.clear_enabled_bit(tid);
        self.enabled_transition_count -= 1;
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
        self.mark_transition_dirty(tid);

        if is_sync {
            let mut ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                inputs,
                read_tokens,
                output_place_names,
                None,
            );
            let result = action.run_sync(&mut ctx);
            match result {
                Ok(()) => {
                    let outputs = ctx.take_outputs();
                    self.process_outputs(tid, &transition_name, outputs);
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionCompleted {
                            transition_name: Arc::clone(&transition_name),
                            timestamp: now_millis(),
                        });
                    }
                }
                Err(err) => {
                    if E::ENABLED {
                        self.event_store.append(NetEvent::TransitionFailed {
                            transition_name: Arc::clone(&transition_name),
                            error: err.message,
                            timestamp: now_millis(),
                        });
                    }
                }
            }
        } else {
            *in_flight_count += 1;
            let tx = completion_tx.clone();
            let name = Arc::clone(&transition_name);
            let ctx = TransitionContext::new(
                Arc::clone(&transition_name),
                inputs,
                read_tokens,
                output_place_names,
                None,
            );
            tokio::spawn(async move {
                let result = action.run_async(ctx).await;
                let completion = match result {
                    Ok(mut completed_ctx) => ActionCompletion {
                        transition_name: Arc::clone(&name),
                        result: Ok(completed_ctx.take_outputs()),
                    },
                    Err(err) => ActionCompletion {
                        transition_name: Arc::clone(&name),
                        result: Err(err.message),
                    },
                };
                let _ = tx.send(completion);
            });
        }
    }

    fn millis_until_next_timed_transition(&self) -> f64 {
        let mut min_wait = f64::INFINITY;
        let now_ms = self.elapsed_ms();

        for s in 0..self.summary_words {
            let mut summary = self.enabled_word_summary[s];
            while summary != 0 {
                let local_w = summary.trailing_zeros() as usize;
                summary &= summary - 1;
                let w = (s << bitmap::WORD_SHIFT) | local_w;
                if w >= self.transition_words {
                    continue;
                }
                let mut word = self.enabled_bitmap[w];
                while word != 0 {
                    let bit = word.trailing_zeros() as usize;
                    let tid = (w << bitmap::WORD_SHIFT) | bit;
                    word &= word - 1;

                    let elapsed = now_ms - self.enabled_at_ms[tid];
                    let remaining_earliest = self.program.earliest_ms[tid] - elapsed;
                    if remaining_earliest <= 0.0 {
                        return 0.0;
                    }
                    min_wait = min_wait.min(remaining_earliest);

                    if self.program.has_deadline[tid] {
                        let remaining_deadline = self.program.latest_ms[tid] - elapsed;
                        if remaining_deadline <= 0.0 {
                            return 0.0;
                        }
                        min_wait = min_wait.min(remaining_deadline);
                    }
                }
            }
        }

        min_wait
    }
}

// ==================== Static Helpers ====================

fn grow_ring_static(
    token_pool: &mut Vec<Option<ErasedToken>>,
    place_offset: &mut [usize],
    ring_head: &mut [usize],
    ring_tail: &mut [usize],
    ring_capacity: &mut [usize],
    token_counts: &[usize],
    pid: usize,
) {
    let old_cap = ring_capacity[pid];
    let new_cap = old_cap * 2;
    let old_offset = place_offset[pid];
    let head = ring_head[pid];
    let count = token_counts[pid];

    // Relocate to end of pool
    let new_offset = token_pool.len();
    token_pool.resize_with(new_offset + new_cap, || None);

    // Copy ring contents linearized
    for i in 0..count {
        let old_idx = old_offset + (head + i) % old_cap;
        token_pool[new_offset + i] = token_pool[old_idx].take();
    }

    place_offset[pid] = new_offset;
    ring_head[pid] = 0;
    ring_tail[pid] = count;
    ring_capacity[pid] = new_cap;
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiled_net::CompiledNet;
    use libpetri_core::action::{fork, passthrough, sync_action};
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::token::Token;
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::{InMemoryEventStore, NoopEventStore};

    fn simple_chain() -> (PetriNet, Place<i32>, Place<i32>, Place<i32>) {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(passthrough())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .action(passthrough())
            .build();

        let net = PetriNet::builder("chain").transitions([t1, t2]).build();
        (net, p1, p2, p3)
    }

    #[test]
    fn sync_passthrough_chain() {
        let (net, p1, _p2, _p3) = simple_chain();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p1"), 0);
    }

    #[test]
    fn sync_fork_chain() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(libpetri_core::output::and(vec![
                out_place(&p2),
                out_place(&p3),
            ]))
            .action(fork())
            .build();

        let net = PetriNet::builder("fork").transition(t1).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p1"), 0);
        assert_eq!(result.count("p2"), 1);
        assert_eq!(result.count("p3"), 1);
    }

    #[test]
    fn sync_linear_chain_5() {
        let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
        let transitions: Vec<Transition> = (0..5)
            .map(|i| {
                Transition::builder(format!("t{i}"))
                    .input(one(&places[i]))
                    .output(out_place(&places[i + 1]))
                    .action(fork())
                    .build()
            })
            .collect();

        let net = PetriNet::builder("chain5").transitions(transitions).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&places[0], Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p0"), 0);
        assert_eq!(result.count("p5"), 1);
    }

    #[test]
    fn sync_no_initial_tokens() {
        let (net, _, _, _) = simple_chain();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);
        let marking = Marking::new();
        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();
        assert_eq!(result.count("p1"), 0);
        assert_eq!(result.count("p2"), 0);
        assert_eq!(result.count("p3"), 0);
    }

    #[test]
    fn sync_priority_ordering() {
        let p = Place::<()>::new("p");
        let out_a = Place::<()>::new("a");
        let out_b = Place::<()>::new("b");

        let t_high = Transition::builder("t_high")
            .input(one(&p))
            .output(out_place(&out_a))
            .action(passthrough())
            .priority(10)
            .build();
        let t_low = Transition::builder("t_low")
            .input(one(&p))
            .output(out_place(&out_b))
            .action(passthrough())
            .priority(1)
            .build();

        let net = PetriNet::builder("priority")
            .transitions([t_high, t_low])
            .build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at((), 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn sync_inhibitor_blocks() {
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");
        let p_inh = Place::<()>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .action(passthrough())
            .build();

        let net = PetriNet::builder("inhibitor").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p1"), 1);
    }

    #[test]
    fn read_arc_does_not_consume() {
        let p_in = Place::<i32>::new("in");
        let p_ctx = Place::<i32>::new("ctx");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .read(libpetri_core::arc::read(&p_ctx))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                let r = ctx.read::<i32>("ctx")?;
                ctx.output("out", *v + *r)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(10, 0));
        marking.add(&p_ctx, Token::at(5, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("in"), 0);
        assert_eq!(result.count("ctx"), 1);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn reset_arc_removes_all_tokens() {
        let p_in = Place::<()>::new("in");
        let p_reset = Place::<i32>::new("reset");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .reset(libpetri_core::arc::reset(&p_reset))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at((), 0));
        marking.add(&p_reset, Token::at(1, 0));
        marking.add(&p_reset, Token::at(2, 0));
        marking.add(&p_reset, Token::at(3, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("reset"), 0);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn exactly_cardinality_consumes_n() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::exactly(3, &p))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                for v in vals {
                    ctx.output("out", *v)?;
                }
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 2);
        assert_eq!(result.count("out"), 3);
    }

    #[test]
    fn all_cardinality_consumes_everything() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::all(&p))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                ctx.output("out", vals.len() as i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn at_least_blocks_insufficient() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));
        marking.add(&p, Token::at(2, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 2);
    }

    #[test]
    fn at_least_fires_with_enough() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn guarded_input_only_consumes_matching() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 5))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));
        marking.add(&p, Token::at(10, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 1);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn guarded_input_blocks_when_no_match() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 100))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));
        marking.add(&p, Token::at(10, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("p"), 2);
        assert_eq!(result.count("out"), 0);
    }

    #[test]
    fn event_store_records_lifecycle() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::new(&prog, marking);
        let _result = executor.run_to_completion();

        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionEnabled { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionCompleted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TokenRemoved { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TokenAdded { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionCompleted { .. }))
        );
    }

    #[test]
    fn action_error_does_not_crash() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(sync_action(|_ctx| {
                Err(libpetri_core::action::ActionError::new(
                    "intentional failure",
                ))
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("in"), 0);
        assert_eq!(result.count("out"), 0);

        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
        );
    }

    #[test]
    fn multiple_input_arcs_require_all() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .input(one(&p2))
            .output(out_place(&p3))
            .action(sync_action(|ctx| {
                ctx.output("p3", 99i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        // Only p1 has token — should not fire
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();
        assert_eq!(result.count("p1"), 1);
        assert_eq!(result.count("p3"), 0);

        // Both p1 and p2 — should fire
        let compiled2 = CompiledNet::compile(&net);
        let prog2 = PrecompiledNet::from_compiled(&compiled2);
        let mut marking2 = Marking::new();
        marking2.add(&p1, Token::at(1, 0));
        marking2.add(&p2, Token::at(2, 0));
        let mut executor2 = PrecompiledNetExecutor::<NoopEventStore>::new(&prog2, marking2);
        let result2 = executor2.run_to_completion();
        assert_eq!(result2.count("p1"), 0);
        assert_eq!(result2.count("p2"), 0);
        assert_eq!(result2.count("p3"), 1);
    }

    #[test]
    fn sync_action_custom_logic() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                ctx.output("out", format!("value={v}"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn transform_action_outputs_to_all_places() {
        let p_in = Place::<i32>::new("in");
        let p_a = Place::<i32>::new("a");
        let p_b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(libpetri_core::output::and(vec![
                out_place(&p_a),
                out_place(&p_b),
            ]))
            .action(libpetri_core::action::transform(|ctx| {
                let v = ctx.input::<i32>("in").unwrap();
                Arc::new(*v * 2) as Arc<dyn std::any::Any + Send + Sync>
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(5, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        assert_eq!(result.count("a"), 1);
        assert_eq!(result.count("b"), 1);
    }

    #[test]
    fn complex_workflow() {
        use libpetri_core::output::{and, xor};

        let input = Place::<i32>::new("v_input");
        let guard_in = Place::<i32>::new("v_guardIn");
        let intent_in = Place::<i32>::new("v_intentIn");
        let search_in = Place::<i32>::new("v_searchIn");
        let output_guard_in = Place::<i32>::new("v_outputGuardIn");
        let guard_safe = Place::<i32>::new("v_guardSafe");
        let guard_violation = Place::<i32>::new("v_guardViolation");
        let _violated = Place::<i32>::new("v_violated");
        let intent_ready = Place::<i32>::new("v_intentReady");
        let topic_ready = Place::<i32>::new("v_topicReady");
        let search_ready = Place::<i32>::new("v_searchReady");
        let _output_guard_done = Place::<i32>::new("v_outputGuardDone");
        let response = Place::<i32>::new("v_response");

        let fork_trans = Transition::builder("Fork")
            .input(one(&input))
            .output(and(vec![
                out_place(&guard_in),
                out_place(&intent_in),
                out_place(&search_in),
                out_place(&output_guard_in),
            ]))
            .action(fork())
            .build();

        let guard_trans = Transition::builder("Guard")
            .input(one(&guard_in))
            .output(xor(vec![
                out_place(&guard_safe),
                out_place(&guard_violation),
            ]))
            .action(fork())
            .build();

        let handle_violation = Transition::builder("HandleViolation")
            .input(one(&guard_violation))
            .output(out_place(&_violated))
            .inhibitor(libpetri_core::arc::inhibitor(&guard_safe))
            .action(fork())
            .build();

        let intent_trans = Transition::builder("Intent")
            .input(one(&intent_in))
            .output(out_place(&intent_ready))
            .action(fork())
            .build();

        let topic_trans = Transition::builder("TopicKnowledge")
            .input(one(&intent_ready))
            .output(out_place(&topic_ready))
            .action(fork())
            .build();

        let search_trans = Transition::builder("Search")
            .input(one(&search_in))
            .output(out_place(&search_ready))
            .read(libpetri_core::arc::read(&intent_ready))
            .inhibitor(libpetri_core::arc::inhibitor(&guard_violation))
            .priority(-5)
            .action(fork())
            .build();

        let output_guard_trans = Transition::builder("OutputGuard")
            .input(one(&output_guard_in))
            .output(out_place(&_output_guard_done))
            .read(libpetri_core::arc::read(&guard_safe))
            .action(fork())
            .build();

        let compose_trans = Transition::builder("Compose")
            .input(one(&guard_safe))
            .input(one(&search_ready))
            .input(one(&topic_ready))
            .output(out_place(&response))
            .priority(10)
            .action(fork())
            .build();

        let net = PetriNet::builder("ComplexWorkflow")
            .transition(fork_trans)
            .transition(guard_trans)
            .transition(handle_violation)
            .transition(intent_trans)
            .transition(topic_trans)
            .transition(search_trans)
            .transition(output_guard_trans)
            .transition(compose_trans)
            .build();

        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(&compiled);

        let mut marking = Marking::new();
        marking.add(&input, Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_to_completion();

        // fork() produces to ALL output places, including both XOR branches.
        // This means guard_safe AND guard_violation both get tokens.
        // Search is inhibited by guard_violation, so it deadlocks.
        // The important thing is the executor doesn't crash and terminates.
        assert_eq!(result.count("v_input"), 0); // consumed by Fork
    }

    #[cfg(feature = "tokio")]
    mod async_tests {
        use super::*;
        use crate::environment::ExternalEvent;
        use libpetri_core::action::async_action;
        use libpetri_core::petri_net::PetriNet;
        use libpetri_core::token::ErasedToken;

        #[tokio::test]
        async fn async_linear_chain() {
            let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
            let transitions: Vec<Transition> = (0..5)
                .map(|i| {
                    Transition::builder(format!("t{i}"))
                        .input(one(&places[i]))
                        .output(out_place(&places[i + 1]))
                        .action(fork())
                        .build()
                })
                .collect();

            let net = PetriNet::builder("chain5").transitions(transitions).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let mut marking = Marking::new();
            marking.add(&places[0], Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p0"), 0);
            assert_eq!(result.count("p5"), 1);
        }

        #[tokio::test]
        async fn async_action_execution() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(async_action(|ctx| async { Ok(ctx) }))
                .build();

            let net = PetriNet::builder("async_test").transition(t).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p1"), 0);
        }

        // ==================== Drain/Close lifecycle tests ====================

        #[tokio::test]
        async fn async_drain_terminates_at_quiescence() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(42, 0)),
                }))
                .unwrap();
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }

        #[tokio::test]
        async fn async_drain_rejects_post_drain_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(99, 0)),
                }))
                .unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 0);
        }

        #[tokio::test]
        async fn async_close_discards_queued_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(1, 0)),
            }))
            .unwrap();
            tx.send(ExecutorSignal::Close).unwrap();
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(2, 0)),
            }))
            .unwrap();
            drop(tx);

            let result = executor.run_async(rx).await;
            assert!(result.count("p2") <= 1);
        }

        #[tokio::test]
        async fn async_close_after_drain_escalates() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Close).unwrap();
            });

            let _result = executor.run_async(rx).await;
            // Test passes if run_async returns — close escalated from drain
        }

        #[tokio::test]
        async fn async_handle_raii_drain_on_drop() {
            use crate::executor_handle::ExecutorHandle;

            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(&compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                let mut handle = ExecutorHandle::new(tx);
                handle.inject(
                    Arc::from("p1"),
                    ErasedToken::from_typed(&Token::at(7, 0)),
                );
                // handle dropped here — RAII sends Drain automatically
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }
    }
}
