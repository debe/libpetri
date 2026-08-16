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
use crate::executor_core::backend::{ChangeTracker, ExecutorBackend, UnknownPlaceLog};
use crate::executor_core::deadline::DEADLINE_TOLERANCE_MS;
use crate::marking::Marking;
use crate::match_engine::{IncrementalMatcher, NameIndex, select_match_name};
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

    /// Tokens in places unknown to the compiled program (CORE-072 AC3). The
    /// bitmap reference keeps these in its `Marking`, so they are retained here
    /// and merged into [`materialize_marking`](Self::materialize_marking) rather
    /// than dropped. Keys are disjoint from the pool's: a name is either
    /// compiled (ring storage) or not (this map), never both.
    extra_marking: Marking,
    /// Diagnostic side of `extra_marking`: one entry per distinct unknown
    /// place, drained by the loop (CORE-072 AC4).
    unknown_places: UnknownPlaceLog,

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

    // ==================== ν-net incremental match caches (NU-020) ====================
    /// Per matched transition: an [`IncrementalMatcher`] when the transition is
    /// fast-path eligible (every correlated input is `One`/`Exactly` and is
    /// consumed only by this transition and never reset), else `None` →
    /// fall back to the O(n) rebuild [`find_match_binding`](Self::find_match_binding).
    match_caches: Vec<Option<IncrementalMatcher>>,
    /// Per place: the `(tid, key_index)` of every fast-path matched correlated
    /// input fed by this place, so token adds can be mirrored into the caches.
    place_match_targets: Vec<Vec<(usize, usize)>>,

    /// Grace band (ms) before a hard deadline force-disables (TIME-013).
    deadline_tolerance_ms: f64,
}

impl<'a> PrecompiledBackend<'a> {
    /// Load `initial_marking` into a fresh backend bound to `program`.
    /// The backend is ready for [`Executor`](crate::executor_core::executor::Executor)
    /// to drive; the shared loop calls `initialize` once just before
    /// the first cycle to sync the presence bitmap and dirty set.
    pub fn new(program: &'a PrecompiledNet, mut initial_marking: Marking) -> Self {
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

        // Retain initial tokens whose places the program does not know
        // (BitmapBackend keeps its whole Marking; dropping them loses tokens).
        let mut extra_marking = Marking::new();
        let mut unknown_places = UnknownPlaceLog::default();
        for name in initial_marking.non_empty_places() {
            if program.place_id(&name).is_none() {
                for token in initial_marking.remove_all(&name) {
                    extra_marking.add_erased(&name, token);
                }
                unknown_places.record(&name);
            }
        }

        let transition_words = bitmap::word_count(tc);
        let summary_words = bitmap::word_count(transition_words);
        let prio_count = program.distinct_priority_count;
        let queue_cap = tc.max(4);
        let ready_queues = vec![vec![0usize; queue_cap]; prio_count];

        let mut this = Self {
            program,
            token_pool,
            place_offset,
            token_counts,
            ring_head,
            ring_tail,
            ring_capacity,
            extra_marking,
            unknown_places,
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
            match_caches: Vec::new(),
            place_match_targets: vec![Vec::new(); pc],
            deadline_tolerance_ms: DEADLINE_TOLERANCE_MS,
        };
        this.init_match_caches();
        this
    }

    /// Builds the ν-net incremental match caches (NU-020). A matched transition
    /// is *fast-path eligible* — gets an [`IncrementalMatcher`] kept in lockstep
    /// with the rings — only when every correlated input is `One`/`Exactly`
    /// (fixed consume count), is consumed by no other transition, and is never a
    /// reset target. Those conditions guarantee tokens enter a correlated input
    /// only via produce/inject (mirrored by `add`) and leave only via this join's
    /// matched consume (mirrored by `consume`), so the cache can never desync.
    /// Ineligible matched transitions keep the O(n) rebuild path.
    fn init_match_caches(&mut self) {
        let tc = self.program.transition_count();
        let pc = self.program.place_count();
        self.match_caches = (0..tc).map(|_| None).collect();
        if !(0..tc).any(|tid| self.program.compiled().has_match(tid)) {
            return; // no ν-net transitions — leave everything on the fast opcode path
        }

        // Which transitions *consume* (input or reset) each place.
        let mut input_consumers: Vec<Vec<usize>> = vec![Vec::new(); pc];
        let mut reset_target: Vec<bool> = vec![false; pc];
        for tid in 0..tc {
            let t = self.program.transition(tid);
            for spec in t.input_specs() {
                if let Some(pid) = self.program.place_id(spec.place_name()) {
                    input_consumers[pid].push(tid);
                }
            }
            for arc in t.resets() {
                if let Some(pid) = self.program.place_id(arc.place.name()) {
                    reset_target[pid] = true;
                }
            }
        }

        for tid in 0..tc {
            if !self.program.compiled().has_match(tid) {
                continue;
            }
            let t = self.program.transition(tid);
            let Some(ms) = t.match_spec() else { continue };

            // Eligibility + per-key required counts (key order == ms.keys() order,
            // matching find_match_binding / the matcher's input indexing).
            let mut requireds = Vec::with_capacity(ms.keys().len());
            let mut eligible = true;
            for mk in ms.keys() {
                let Some(pid) = self.program.place_id(mk.place_name()) else {
                    eligible = false;
                    break;
                };
                let spec = t
                    .input_specs()
                    .iter()
                    .find(|s| s.place_name() == mk.place_name());
                let required = match spec {
                    Some(In::One { .. }) => 1,
                    Some(In::Exactly { count, .. }) => *count,
                    // AtLeast/All consume a variable count — not modellable by the
                    // fixed-consume matcher; fall back.
                    _ => {
                        eligible = false;
                        break;
                    }
                };
                if reset_target[pid] || input_consumers[pid] != [tid] {
                    eligible = false;
                    break;
                }
                requireds.push(required);
            }
            if !eligible {
                continue;
            }

            // Build the matcher and seed it from the initial ring contents,
            // in the same key order.
            let mut matcher = IncrementalMatcher::new(requireds);
            for (key_idx, mk) in ms.keys().iter().enumerate() {
                let pid = self.program.place_id(mk.place_name()).unwrap();
                let count = self.token_counts[pid];
                let offset = self.place_offset[pid];
                let head = self.ring_head[pid];
                let cap = self.ring_capacity[pid];
                for i in 0..count {
                    let slot = offset + (head + i) % cap;
                    if let Some(token) = &self.token_pool[slot]
                        && let Some(name) = mk.extract(token.value.as_ref())
                    {
                        matcher.add(key_idx, name, token.created_at);
                    }
                }
                self.place_match_targets[pid].push((tid, key_idx));
            }
            self.match_caches[tid] = Some(matcher);
        }
    }

    /// Mirror a token added to correlated input `pid` into every fast-path
    /// matcher that consumes it (projected to its name).
    fn cache_add_token(&mut self, pid: usize, value: &dyn std::any::Any, created_at: u64) {
        if self.place_match_targets[pid].is_empty() {
            return;
        }
        let prog = self.program; // Copy the shared reference; no borrow of self.
        let targets = std::mem::take(&mut self.place_match_targets[pid]);
        for &(tid, key_idx) in &targets {
            let t = prog.transition(tid);
            let ms = t.match_spec().expect("fast-path tid has a match spec");
            let mk = &ms.keys()[key_idx];
            if let Some(name) = mk.extract(value)
                && let Some(cache) = self.match_caches[tid].as_mut()
            {
                cache.add(key_idx, name, created_at);
            }
        }
        self.place_match_targets[pid] = targets;
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

    /// Removes the first token satisfying `predicate` from the ring buffer
    /// at `pid`. Compacts the ring on hit.
    ///
    /// The predicate is always the ν-net name-equality test (NU-020/NU-021);
    /// input specifications carry no per-token predicate of their own (IO-006).
    fn ring_remove_matching(
        &mut self,
        pid: usize,
        predicate: &dyn Fn(&dyn std::any::Any) -> bool,
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
                && predicate(token.value.as_ref())
            {
                let token = self.token_pool[idx].take().unwrap();
                // Close the gap from whichever end is nearer, so removing the
                // ring head (the common ν-net case — the matched token is the
                // oldest, hence at the front) is O(1) instead of shifting the
                // whole ring. Removal is then O(min(i, count-1-i)), which keeps
                // a draining matched join linear rather than quadratic.
                if i <= count - 1 - i {
                    // Nearer the head: slide the `i` preceding tokens forward,
                    // then advance head (tail unchanged). i == 0 ⇒ no moves.
                    for j in (0..i).rev() {
                        let from = offset + (head + j) % cap;
                        let to = offset + (head + j + 1) % cap;
                        self.token_pool[to] = self.token_pool[from].take();
                    }
                    self.ring_head[pid] = (head + 1) % cap;
                } else {
                    // Nearer the tail: slide the trailing tokens back, then
                    // retract tail (head unchanged).
                    for j in i..count - 1 {
                        let from = offset + (head + j + 1) % cap;
                        let to = offset + (head + j) % cap;
                        self.token_pool[to] = self.token_pool[from].take();
                    }
                    self.ring_tail[pid] = if self.ring_tail[pid] == 0 {
                        cap - 1
                    } else {
                        self.ring_tail[pid] - 1
                    };
                }
                self.token_counts[pid] -= 1;
                return Some(token);
            }
        }
        None
    }

    /// Counts tokens in the ring at `pid` satisfying `predicate` (the ν-net
    /// name-equality test — see [`Self::ring_remove_matching`]).
    fn count_matching_in_ring(
        &self,
        pid: usize,
        predicate: &dyn Fn(&dyn std::any::Any) -> bool,
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
                && predicate(token.value.as_ref())
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

        // ν-net join: a correlation name must satisfy every matched input (NU-020).
        // Fast-path transitions read the maintained matcher (O(1)); the rest
        // rebuild the index (O(n)).
        if self.program.compiled().has_match(tid) {
            let no_binding = match &self.match_caches[tid] {
                Some(cache) => cache.best().is_none(),
                None => self.find_match_binding(tid).is_none(),
            };
            if no_binding {
                return false;
            }
        }

        true
    }

    /// Finds the correlation name satisfying this transition's `MatchSpec`, or
    /// `None` if the join is not currently enabled (spec NU-020). Builds a
    /// per-correlated-input name index over the ring buffers and defers the
    /// selection + tie-break to the shared [`select_match_name`].
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
            let mut index: NameIndex = HashMap::new();
            let count = self.token_counts[pid];
            let offset = self.place_offset[pid];
            let head = self.ring_head[pid];
            let cap = self.ring_capacity[pid];
            for i in 0..count {
                let slot = offset + (head + i) % cap;
                if let Some(token) = &self.token_pool[slot]
                    && let Some(name) = mk.extract(token.value.as_ref())
                {
                    let entry = index.entry(name).or_insert((0usize, u64::MAX));
                    entry.0 += 1;
                    entry.1 = entry.1.min(token.created_at);
                }
            }
            per_place.push(index);
            requireds.push(required);
        }

        select_match_name(&per_place, &requireds)
    }

    /// Number of matched transitions that got a fast-path incremental matcher
    /// (the rest fall back to [`find_match_binding`](Self::find_match_binding)).
    /// Diagnostic for tests.
    pub(crate) fn fast_path_match_count(&self) -> usize {
        self.match_caches.iter().filter(|c| c.is_some()).count()
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

    /// Clones the front token of each read-arc place into `reads` (EXEC-012).
    /// Called between input consumption and reset draining so reads observe
    /// the post-input, pre-reset marking, matching `BitmapBackend`.
    fn peek_reads(&self, tid: usize, reads: &mut HashMap<Arc<str>, Vec<ErasedToken>>) {
        let read_ops_len = self.program.read_ops[tid].len();
        for i in 0..read_ops_len {
            let rpid = self.program.read_ops[tid][i];
            if let Some(token) = self.ring_peek_first(rpid).cloned() {
                let place_name = Arc::clone(&self.program.place_name_arcs[rpid]);
                reads.entry(place_name).or_default().push(token);
            }
        }
    }

    fn materialize_marking(&self) -> Marking {
        let mut marking = self.extra_marking.clone();
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

        // Ready order per priority: enablement time ASC, tid ASC tie-break
        // (EXEC-002 / CONC-023 AC4); distinct (time, tid) keys make `sort_unstable` deterministic.
        for pi in 0..self.program.distinct_priority_count {
            let size = self.ready_queue_size[pi];
            if size > 1 {
                let enabled_at = &self.enabled_at_ms;
                self.ready_queues[pi][..size].sort_unstable_by(|&a, &b| {
                    enabled_at[a].total_cmp(&enabled_at[b]).then(a.cmp(&b))
                });
            }
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
        if self.program.compiled().has_match(tid) {
            // Spec-based path for ν-net-correlated transitions. Correlated
            // inputs take the tokens whose projected name equals the chosen
            // binding (NU-020/NU-021); other inputs consume FIFO as usual.
            let chosen: Option<NameId> = match &self.match_caches[tid] {
                Some(cache) => cache.best().cloned(),
                None => self.find_match_binding(tid),
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

                if let Some(key) = key {
                    let chosen_name = chosen.clone();
                    let pred = move |v: &dyn std::any::Any| -> bool {
                        matches!(
                            (key(v), &chosen_name),
                            (Some(n), Some(c)) if n == *c
                        )
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

            // Mirror the matched consume into the fast-path matcher — the only
            // path by which tokens leave this join's correlated inputs — so it
            // stays in lockstep with the rings (NU-020).
            if let Some(name) = &chosen
                && let Some(cache) = self.match_caches[tid].as_mut()
            {
                cache.consume(name);
            }

            self.peek_reads(tid, reads);

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
            // Fast path: opcode-based consumption. Input opcodes occupy
            // `..reset_ops_start[tid]`, the RESET tail the rest; reads peek at
            // the boundary so they observe the post-input, pre-reset marking
            // (EXEC-012/EXEC-013), matching `BitmapBackend`.
            let ops_len = self.program.consume_ops[tid].len();
            let reset_start = self.program.reset_ops_start[tid];
            let mut pc = 0;
            while pc < reset_start {
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
                    _ => unreachable!("Unknown input consume opcode: {opcode}"),
                }
            }

            self.peek_reads(tid, reads);

            while pc < ops_len {
                let opcode = self.program.consume_ops[tid][pc];
                pc += 1;
                match opcode {
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
                    _ => unreachable!("Unknown reset opcode: {opcode}"),
                }
            }
        }

        self.update_bitmap_after_consumption(tid);
    }

    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        if let Some(pid) = self.program.place_id(place) {
            self.cache_add_token(pid, token.value.as_ref(), token.created_at);
            self.ring_add_last(pid, token);
            self.set_marking_bit(pid);
            self.mark_place_dirty(pid);
        } else {
            self.extra_marking.add_erased(place, token);
            self.unknown_places.record(place);
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
            self.cache_add_token(pid, token.value.as_ref(), token.created_at);
            self.ring_add_last(pid, token);
            self.set_marking_bit(pid);
            self.mark_place_dirty(pid);
        } else {
            self.extra_marking.add_erased(place, token);
            self.unknown_places.record(place);
        }
    }

    fn take_unknown_places(&mut self) -> Vec<Arc<str>> {
        self.unknown_places.take()
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

#[cfg(test)]
mod fast_path_tests {
    use super::*;
    use libpetri_core::action::sync_action;
    use libpetri_core::input::one;
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;
    use libpetri_core::token::Token;
    use libpetri_event::event_store::NoopEventStore;

    #[derive(Clone)]
    struct Msg {
        cid: String,
    }

    fn drain_net() -> (PetriNet, Place<Msg>, Place<Msg>) {
        let a = Place::<Msg>::new("branch0");
        let b = Place::<Msg>::new("branch1");
        let merged = Place::<String>::new("merged");
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |m: &Msg| NameId::new(m.cid.clone()))
                    .key(&b, |m: &Msg| NameId::new(m.cid.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(sync_action(|ctx| {
                ctx.output("merged", String::from("m"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("drain").transition(join).build();
        (net, a, b)
    }

    #[test]
    #[ignore = "timing diagnostic; run with --ignored --nocapture"]
    fn drain_timing_is_subquadratic() {
        use crate::precompiled_executor::PrecompiledNetExecutor;
        use std::time::Instant;
        let (net, a, b) = drain_net();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);
        let seed = |depth: usize| {
            let mut m = Marking::new();
            for j in 0..depth {
                m.add(&a, Token::at(Msg { cid: format!("c{j}") }, j as u64));
                m.add(&b, Token::at(Msg { cid: format!("c{j}") }, j as u64));
            }
            m
        };
        for &depth in &[100usize, 400, 1600, 6400] {
            for _ in 0..3 {
                PrecompiledNetExecutor::<NoopEventStore>::new(&prog, seed(depth)).run_sync();
            }
            let runs = 5;
            let t = Instant::now();
            for _ in 0..runs {
                let mut exec = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, seed(depth));
                let r = exec.run_sync();
                assert_eq!(r.count("merged"), depth);
            }
            let per_us = t.elapsed().as_secs_f64() / runs as f64 * 1e6;
            eprintln!("[RUST precompiled] depth {depth:>5}: {per_us:>10.1} us  {:>6.2} us/n", per_us / depth as f64);
        }

        // Same drain on the bitmap backend (FIFO Marking) for comparison.
        use crate::executor::{BitmapNetExecutor, ExecutorOptions};
        for &depth in &[100usize, 400, 1600, 6400] {
            for _ in 0..3 {
                BitmapNetExecutor::<NoopEventStore>::new(&net, seed(depth), ExecutorOptions::default())
                    .run_sync();
            }
            let runs = 5;
            let t = Instant::now();
            for _ in 0..runs {
                let mut exec = BitmapNetExecutor::<NoopEventStore>::new(
                    &net,
                    seed(depth),
                    ExecutorOptions::default(),
                );
                exec.run_sync();
                assert_eq!(exec.marking().count("merged"), depth);
            }
            let per_us = t.elapsed().as_secs_f64() / runs as f64 * 1e6;
            eprintln!("[RUST bitmap]      depth {depth:>5}: {per_us:>10.1} us  {:>6.2} us/n", per_us / depth as f64);
        }
    }

    #[test]
    fn drain_join_is_fast_path_eligible() {
        let a = Place::<Msg>::new("branch0");
        let b = Place::<Msg>::new("branch1");
        let merged = Place::<String>::new("merged");
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |m: &Msg| NameId::new(m.cid.clone()))
                    .key(&b, |m: &Msg| NameId::new(m.cid.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(sync_action(|ctx| {
                ctx.output("merged", String::from("m"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("drain").transition(join).build();
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));

        let mut marking = Marking::new();
        marking.add(&a, Token::at(Msg { cid: "c0".into() }, 0));
        marking.add(&b, Token::at(Msg { cid: "c0".into() }, 0));
        let backend = PrecompiledBackend::new(&prog, marking);
        assert_eq!(
            backend.fast_path_match_count(),
            1,
            "the canonical 2-way drain join must be fast-path eligible"
        );
    }
}
