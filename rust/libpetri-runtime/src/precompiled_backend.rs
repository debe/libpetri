//! `PrecompiledBackend` — the production hot-path backend behind
//! [`PrecompiledNetExecutor`](crate::precompiled_executor::PrecompiledNetExecutor).
//!
//! Owns the ring-buffer token pool, the per-transition enablement
//! bitmap with a two-level summary index, the priority-partitioned
//! ready queues, and the opcode-based consume dispatch. Implements
//! [`ExecutorBackend`] so [`Executor`](crate::executor_core::executor::Executor)
//! can drive the shared 6-phase loop against it.
//!
//! Performance: `~412 ns/transition` on a sync linear chain — about
//! 3.86× faster than [`BitmapBackend`](crate::bitmap_backend::BitmapBackend).
//! Borrows `&'a PrecompiledNet` for zero-cost program reuse across
//! executions.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::input::In;
use libpetri_core::name::NameId;
use libpetri_core::token::ErasedToken;

use crate::bitmap;
use crate::compiled_net::CompiledNet;
use crate::executor_core::backend::{ChangeTracker, ExecutorBackend};
use crate::executor_core::deadline::DEADLINE_TOLERANCE_MS;
use crate::marking::Marking;
use crate::match_engine::{NameIndex, select_match_name};
use crate::precompiled_net::{
    CONSUME_ALL, CONSUME_ATLEAST, CONSUME_N, CONSUME_ONE, PrecompiledNet, RESET,
};

/// Initial ring-buffer slot capacity per place.
const INITIAL_RING_CAPACITY: usize = 4;

/// Production-hot-path backend over a borrowed
/// [`PrecompiledNet`]. See module docs.
pub struct PrecompiledBackend<'a> {
    program: &'a PrecompiledNet,

    // ==================== Flat token pool ====================
    token_pool: Vec<Option<ErasedToken>>,
    place_offset: Vec<usize>,
    token_counts: Vec<usize>,
    ring_head: Vec<usize>,
    ring_tail: Vec<usize>,
    ring_capacity: Vec<usize>,

    // ==================== Presence bitmap ====================
    marking_bitmap: Vec<u64>,

    // ==================== Transition state ====================
    enabled_bitmap: Vec<u64>,
    dirty_bitmap: Vec<u64>,
    dirty_scan_buffer: Vec<u64>,
    enabled_at_ms: Vec<f64>,
    enabled_transition_count: usize,

    // ==================== Summary bitmaps (two-level) ====================
    dirty_word_summary: Vec<u64>,
    enabled_word_summary: Vec<u64>,
    transition_words: usize,
    summary_words: usize,

    // ==================== Priority-partitioned ready queues ====================
    ready_queues: Vec<Vec<usize>>,
    ready_queue_head: Vec<usize>,
    ready_queue_tail: Vec<usize>,
    ready_queue_size: Vec<usize>,

    // ==================== Reset-clock detection ====================
    pending_reset_words: Vec<u64>,
    has_pending_resets: bool,

    /// Grace band (ms) before a hard deadline force-disables (TIME-013).
    deadline_tolerance_ms: f64,
}

impl<'a> PrecompiledBackend<'a> {
    /// Load `initial_marking` into a fresh backend bound to `program`.
    /// The backend is ready for [`Executor`](crate::executor_core::executor::Executor)
    /// to drive; the shared loop calls `initialize` once just before
    /// the first cycle to sync the presence bitmap and dirty set.
    pub fn new(program: &'a PrecompiledNet, initial_marking: Marking) -> Self {
        let pc = program.place_count();
        let tc = program.transition_count();
        let wc = program.word_count();

        // Flat token pool with one ring of INITIAL_RING_CAPACITY slots
        // per place.
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

        // Load initial tokens into ring buffers.
        for pid in 0..pc {
            let place = program.place(pid);
            if let Some(queue) = initial_marking.queue(place.name()) {
                for token in queue {
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

        let transition_words = bitmap::word_count(tc);
        let summary_words = bitmap::word_count(transition_words);
        let prio_count = program.distinct_priority_count;
        let queue_cap = tc.max(4);
        let ready_queues = vec![vec![0usize; queue_cap]; prio_count];

        Self {
            program,
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
            ready_queue_head: vec![0usize; prio_count],
            ready_queue_tail: vec![0usize; prio_count],
            ready_queue_size: vec![0usize; prio_count],
            pending_reset_words: vec![0u64; wc],
            has_pending_resets: false,
            deadline_tolerance_ms: DEADLINE_TOLERANCE_MS,
        }
    }

    /// Overrides the deadline-enforcement tolerance (default
    /// [`DEADLINE_TOLERANCE_MS`]). The grace band beyond a hard deadline
    /// (`deadline()` / `window()`) before a transition is force-disabled.
    /// Does not affect `exact()` transitions (TIME-006).
    pub(crate) fn set_deadline_tolerance_ms(&mut self, ms: f64) {
        self.deadline_tolerance_ms = ms;
    }

    // ==================== Ring buffer ops ====================

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

    /// Removes the first token matching `guard` from the ring buffer
    /// at `pid`. Compacts the ring on hit.
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

        for i in 0..count {
            let idx = offset + (head + i) % cap;
            if let Some(token) = &self.token_pool[idx]
                && guard(token.value.as_ref())
            {
                let token = self.token_pool[idx].take().unwrap();
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

    // ==================== Bitmap helpers ====================

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

    #[inline]
    fn mark_transition_dirty(&mut self, tid: usize) {
        let w = tid >> bitmap::WORD_SHIFT;
        self.dirty_bitmap[w] |= 1u64 << (tid & bitmap::WORD_MASK);
        self.dirty_word_summary[w >> bitmap::WORD_SHIFT] |= 1u64 << (w & bitmap::WORD_MASK);
    }

    fn mark_place_dirty(&mut self, pid: usize) {
        let n = self.program.compiled().affected_transitions(pid).len();
        for i in 0..n {
            let tid = self.program.compiled().affected_transitions(pid)[i];
            self.mark_transition_dirty(tid);
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

    // ==================== Ready queue ops ====================

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

    // ==================== Enablement ====================

    fn can_enable(&self, tid: usize) -> bool {
        if !self.program.can_enable_bitmap(tid, &self.marking_bitmap) {
            return false;
        }

        if let Some(card_check) = self.program.compiled().cardinality_check(tid) {
            for i in 0..card_check.place_ids.len() {
                let pid = card_check.place_ids[i];
                let required = card_check.required_counts[i];
                if self.token_counts[pid] < required {
                    return false;
                }
            }
        }

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

        // ν-net join: a correlation name must satisfy every matched input (NU-020).
        if self.program.compiled().has_match(tid) && self.find_match_binding(tid).is_none() {
            return false;
        }

        true
    }

    /// Finds the correlation name satisfying this transition's `MatchSpec`, or
    /// `None` if the join is not currently enabled (spec NU-020). Builds a
    /// per-correlated-input name index over the ring buffers (guard-filtered)
    /// and defers the selection + tie-break to the shared
    /// [`select_match_name`].
    fn find_match_binding(&self, tid: usize) -> Option<NameId> {
        let t = self.program.transition(tid);
        let ms = t.match_spec()?;
        let mut per_place: Vec<NameIndex> = Vec::with_capacity(ms.keys().len());
        let mut requireds: Vec<usize> = Vec::with_capacity(ms.keys().len());

        for mk in ms.keys() {
            let pid = self.program.place_id(mk.place_name())?;
            let spec = t
                .input_specs()
                .iter()
                .find(|s| s.place_name() == mk.place_name());
            let required = match spec {
                Some(In::Exactly { count, .. }) => *count,
                Some(In::AtLeast { minimum, .. }) => *minimum,
                _ => 1,
            };
            let guard = spec.and_then(|s| s.guard());

            let mut index: NameIndex = HashMap::new();
            let count = self.token_counts[pid];
            let offset = self.place_offset[pid];
            let head = self.ring_head[pid];
            let cap = self.ring_capacity[pid];
            for i in 0..count {
                let slot = offset + (head + i) % cap;
                if let Some(token) = &self.token_pool[slot] {
                    if let Some(g) = guard
                        && !g(token.value.as_ref())
                    {
                        continue;
                    }
                    if let Some(name) = mk.extract(token.value.as_ref()) {
                        let entry = index.entry(name).or_insert((0usize, u64::MAX));
                        entry.0 += 1;
                        entry.1 = entry.1.min(token.created_at);
                    }
                }
            }
            per_place.push(index);
            requireds.push(required);
        }

        select_match_name(&per_place, &requireds)
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

    fn update_bitmap_after_consumption(&mut self, tid: usize) {
        let n = self.program.compiled().consumption_place_ids(tid).len();
        for i in 0..n {
            let pid = self.program.compiled().consumption_place_ids(tid)[i];
            if self.token_counts[pid] == 0 {
                self.clear_marking_bit(pid);
            }
            self.mark_place_dirty(pid);
        }
    }

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
}

impl<'a> ExecutorBackend for PrecompiledBackend<'a> {
    fn compiled(&self) -> &CompiledNet {
        self.program.compiled()
    }

    fn output_place_names(&self, tid: usize) -> HashSet<Arc<str>> {
        self.program.output_place_name_sets[tid].clone()
    }

    fn initialize(&mut self) {
        for pid in 0..self.program.place_count() {
            if self.token_counts[pid] > 0 {
                self.set_marking_bit(pid);
            }
        }
        self.mark_all_dirty();
    }

    fn snapshot_marking(&self) -> Cow<'_, Marking> {
        Cow::Owned(self.materialize_marking())
    }

    fn is_quiescent(&self) -> bool {
        self.enabled_transition_count == 0
    }

    fn has_dirty_bits(&self) -> bool {
        for &s in &self.dirty_word_summary {
            if s != 0 {
                return true;
            }
        }
        false
    }

    fn enabled_count(&self) -> usize {
        self.enabled_transition_count
    }

    fn update_enablement<T: ChangeTracker>(&mut self, now_ms: f64, tracker: &mut T) {
        // Snapshot + clear dirty bitmap via summary index.
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
                    tracker.newly_enabled(tid);
                } else if !can_now && was_enabled {
                    self.clear_enabled_bit(tid);
                    self.enabled_transition_count -= 1;
                    self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                } else if can_now && was_enabled && self.has_input_from_reset_place(tid) {
                    self.enabled_at_ms[tid] = now_ms;
                    tracker.clock_restarted(tid);
                }
            }
        }

        self.clear_pending_resets();
    }

    fn has_any_deadlines(&self) -> bool {
        self.program.any_deadlines
    }

    fn enforce_deadlines(&mut self, now_ms: f64, out: &mut Vec<usize>) {
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
                    // exact() is enforced softly — it fires at the first opportunity at/after its
                    // target and is never force-disabled (TIME-006). Only hard deadlines reaped here.
                    if self.program.is_exact[tid] {
                        continue;
                    }

                    let elapsed = now_ms - self.enabled_at_ms[tid];
                    let latest_ms = self.program.latest_ms[tid];

                    if elapsed > latest_ms + self.deadline_tolerance_ms {
                        self.clear_enabled_bit(tid);
                        self.enabled_transition_count -= 1;
                        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
                        self.mark_transition_dirty(tid);
                        out.push(tid);
                    }
                }
            }
        }
    }

    fn fast_path_available(&self) -> bool {
        self.program.all_immediate && self.program.all_same_priority
    }

    fn collect_ready_immediate(&mut self, out: &mut Vec<usize>) {
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
                    out.push(tid);
                }
            }
        }
    }

    fn collect_ready_general(&mut self, now_ms: f64, out: &mut Vec<usize>) {
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

                    let elapsed = now_ms - self.enabled_at_ms[tid];
                    if self.program.earliest_ms[tid] <= elapsed {
                        self.ready_queue_push(tid);
                    }
                }
            }
        }

        for pi in 0..self.program.distinct_priority_count {
            while self.ready_queue_size[pi] > 0 {
                out.push(self.ready_queue_pop(pi));
            }
        }
    }

    fn recheck_can_fire(&mut self, tid: usize) -> bool {
        self.is_enabled(tid) && self.can_enable(tid)
    }

    fn consume_for_firing<F>(
        &mut self,
        tid: usize,
        inputs: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        reads: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        mut emit_removed: F,
    ) where
        F: FnMut(&Arc<str>, &ErasedToken),
    {
        let has_guards = self.program.compiled().has_guards(tid);
        let has_match = self.program.compiled().has_match(tid);

        if has_guards || has_match {
            // Spec-based path for guarded and/or ν-net-correlated transitions.
            // For correlated inputs the chosen name (NU-020) plus any unary
            // guard form a combined per-token predicate (guard first, then name
            // equality — NU-021); other inputs consume FIFO as usual.
            let chosen: Option<NameId> = if has_match {
                self.find_match_binding(tid)
            } else {
                None
            };
            let match_spec = self.program.transition(tid).match_spec().cloned();
            let input_specs: Vec<In> = self.program.transition(tid).input_specs().to_vec();
            let reset_arcs: Vec<_> = self.program.transition(tid).resets().to_vec();

            for in_spec in &input_specs {
                let pid = self.program.place_id(in_spec.place_name()).unwrap();
                let place_name_arc = Arc::clone(&self.program.place_name_arcs[pid]);
                let key = match_spec
                    .as_ref()
                    .and_then(|m| m.key_for(in_spec.place_name()))
                    .cloned();
                let guard = in_spec.guard().cloned();

                if key.is_some() || guard.is_some() {
                    let chosen_name = chosen.clone();
                    let pred = move |v: &dyn std::any::Any| -> bool {
                        if let Some(g) = &guard
                            && !g(v)
                        {
                            return false;
                        }
                        match &key {
                            Some(k) => matches!(
                                (k(v), &chosen_name),
                                (Some(n), Some(c)) if n == *c
                            ),
                            None => true,
                        }
                    };
                    let to_consume = match in_spec {
                        In::One { .. } => 1,
                        In::Exactly { count, .. } => *count,
                        In::All { .. } | In::AtLeast { .. } => {
                            self.count_matching_in_ring(pid, &pred)
                        }
                    };
                    for _ in 0..to_consume {
                        if let Some(token) = self.ring_remove_matching(pid, &pred) {
                            emit_removed(&place_name_arc, &token);
                            inputs
                                .entry(Arc::clone(&place_name_arc))
                                .or_default()
                                .push(token);
                        }
                    }
                } else {
                    let to_consume = match in_spec {
                        In::One { .. } => 1,
                        In::Exactly { count, .. } => *count,
                        In::All { .. } | In::AtLeast { .. } => self.token_counts[pid],
                    };
                    for _ in 0..to_consume {
                        let token = self.ring_remove_first(pid);
                        emit_removed(&place_name_arc, &token);
                        inputs
                            .entry(Arc::clone(&place_name_arc))
                            .or_default()
                            .push(token);
                    }
                }
            }

            for arc in &reset_arcs {
                let pid = self.program.place_id(arc.place.name()).unwrap();
                let count = self.token_counts[pid];
                for _ in 0..count {
                    let token = self.ring_remove_first(pid);
                    emit_removed(arc.place.name_arc(), &token);
                }
                self.pending_reset_words[pid >> bitmap::WORD_SHIFT] |=
                    1u64 << (pid & bitmap::WORD_MASK);
                self.has_pending_resets = true;
            }
        } else {
            // Fast path: opcode-based consumption.
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
                        let place_name = Arc::clone(&self.program.place_name_arcs[pid]);
                        emit_removed(&place_name, &token);
                        inputs.entry(place_name).or_default().push(token);
                    }
                    CONSUME_N => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        let count = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        for _ in 0..count {
                            let token = self.ring_remove_first(pid);
                            let place_name = Arc::clone(&self.program.place_name_arcs[pid]);
                            emit_removed(&place_name, &token);
                            inputs.entry(place_name).or_default().push(token);
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
                            let place_name = Arc::clone(&self.program.place_name_arcs[pid]);
                            emit_removed(&place_name, &token);
                            inputs.entry(place_name).or_default().push(token);
                        }
                    }
                    RESET => {
                        let pid = self.program.consume_ops[tid][pc] as usize;
                        pc += 1;
                        let count = self.token_counts[pid];
                        for _ in 0..count {
                            let token = self.ring_remove_first(pid);
                            emit_removed(&self.program.place_name_arcs[pid], &token);
                        }
                        self.pending_reset_words[pid >> bitmap::WORD_SHIFT] |=
                            1u64 << (pid & bitmap::WORD_MASK);
                        self.has_pending_resets = true;
                    }
                    _ => unreachable!("Unknown consume opcode: {opcode}"),
                }
            }
        }

        // Read-arc tokens (no consume).
        let read_ops_len = self.program.read_ops[tid].len();
        for i in 0..read_ops_len {
            let rpid = self.program.read_ops[tid][i];
            let token_clone = self.ring_peek_first(rpid).cloned();
            if let Some(token) = token_clone {
                let place_name = Arc::clone(&self.program.place_name_arcs[rpid]);
                reads.entry(place_name).or_default().push(token);
            }
        }

        self.update_bitmap_after_consumption(tid);
    }

    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        if let Some(pid) = self.program.place_id(place) {
            self.ring_add_last(pid, token);
            self.set_marking_bit(pid);
            self.mark_place_dirty(pid);
        }
    }

    fn post_fire(&mut self, tid: usize) {
        if self.is_enabled(tid) {
            self.clear_enabled_bit(tid);
            self.enabled_transition_count -= 1;
        }
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
        self.mark_transition_dirty(tid);
    }

    fn disable(&mut self, tid: usize) {
        if self.is_enabled(tid) {
            self.clear_enabled_bit(tid);
            self.enabled_transition_count -= 1;
        }
        self.enabled_at_ms[tid] = f64::NEG_INFINITY;
    }

    fn inject_external_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        if let Some(pid) = self.program.place_id(place) {
            self.ring_add_last(pid, token);
            self.set_marking_bit(pid);
            self.mark_place_dirty(pid);
        }
    }

    fn millis_until_next_timed_transition(&self, now_ms: f64) -> f64 {
        let mut min_wait = f64::INFINITY;

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

// ==================== Ring-growth helper ====================

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
    let old_head = ring_head[pid];
    let count = token_counts[pid];

    let new_offset = token_pool.len();
    for _ in 0..new_cap {
        token_pool.push(None);
    }
    for i in 0..count {
        let from = old_offset + (old_head + i) % old_cap;
        token_pool[new_offset + i] = token_pool[from].take();
    }
    place_offset[pid] = new_offset;
    ring_head[pid] = 0;
    ring_tail[pid] = count;
    ring_capacity[pid] = new_cap;
}
