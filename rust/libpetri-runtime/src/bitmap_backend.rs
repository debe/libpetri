//! `BitmapBackend` — the bitmap-storage backend behind
//! [`BitmapNetExecutor`](crate::executor::BitmapNetExecutor).
//!
//! Owns the per-place presence bitmap, the per-transition enablement
//! flags, the dirty set, and the FIFO `Marking` token store. Implements
//! [`ExecutorBackend`] so [`Executor`](crate::executor_core::executor::Executor)
//! can drive the shared 6-phase loop against it.
//!
//! Performance: `~800 ns/transition` on a sync linear chain — about
//! 2.5× slower than `PrecompiledBackend`, which is acceptable because
//! `BitmapBackend` is the reference / verification path; high-volume
//! production workloads use the precompiled backend.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri_core::input::In;
use libpetri_core::name::NameId;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::token::ErasedToken;

use crate::bitmap;
use crate::compiled_net::CompiledNet;
use crate::executor_core::backend::{ChangeTracker, ExecutorBackend};
use crate::executor_core::deadline::DEADLINE_TOLERANCE_MS;
use crate::marking::Marking;
use crate::match_engine::{IncrementalMatcher, NameIndex, select_match_name};

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
    /// True for `exact()` transitions — enforced softly, never force-disabled (TIME-006).
    is_exact_flags: Vec<bool>,
    enabled_transition_count: usize,

    // Precomputed flags.
    all_immediate: bool,
    all_same_priority: bool,
    has_any_deadlines: bool,
    /// Grace band (ms) before a hard deadline force-disables (TIME-013).
    deadline_tolerance_ms: f64,

    // Clock-restart detection: places drained by reset arcs this cycle
    // and per-transition input-place-name set for fast intersection.
    pending_reset_places: HashSet<Arc<str>>,
    transition_input_place_names: Vec<HashSet<Arc<str>>>,

    // ν-net incremental match caches (NU-020) — see the precompiled backend for
    // the rationale. `match_caches[tid]` is `Some` only for fast-path-eligible
    // matched joins; `place_match_targets[pid]` lists the fast-path correlated
    // inputs fed by each place so adds can be mirrored.
    match_caches: Vec<Option<IncrementalMatcher>>,
    place_match_targets: Vec<Vec<(usize, usize)>>,
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
        let mut is_exact_flags = vec![false; tc];

        for tid in 0..tc {
            let t = compiled.transition(tid);
            if t.timing().has_deadline() {
                has_deadline_flags[tid] = true;
                has_any_deadlines = true;
            }
            if matches!(t.timing(), libpetri_core::timing::Timing::Exact { .. }) {
                is_exact_flags[tid] = true;
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

        let pc = compiled.place_count;
        let mut this = Self {
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
            is_exact_flags,
            enabled_transition_count: 0,
            all_immediate,
            all_same_priority,
            has_any_deadlines,
            deadline_tolerance_ms: DEADLINE_TOLERANCE_MS,
            pending_reset_places: HashSet::new(),
            transition_input_place_names,
            match_caches: Vec::new(),
            place_match_targets: vec![Vec::new(); pc],
        };
        this.init_match_caches();
        this
    }

    /// Builds the ν-net incremental match caches (NU-020). Mirrors the
    /// precompiled backend: a matched join is fast-path eligible only when every
    /// correlated input is `One`/`Exactly`, is consumed by no other transition,
    /// and is never reset — guaranteeing the cache can never desync from the
    /// FIFO `Marking`. Ineligible matched joins keep the O(n) rebuild path.
    fn init_match_caches(&mut self) {
        let tc = self.compiled.transition_count;
        let pc = self.compiled.place_count;
        self.match_caches = (0..tc).map(|_| None).collect();
        if !(0..tc).any(|tid| self.compiled.has_match(tid)) {
            return;
        }

        let mut input_consumers: Vec<Vec<usize>> = vec![Vec::new(); pc];
        let mut reset_target: Vec<bool> = vec![false; pc];
        for tid in 0..tc {
            let t = self.compiled.transition(tid);
            for spec in t.input_specs() {
                if let Some(pid) = self.compiled.place_id(spec.place_name()) {
                    input_consumers[pid].push(tid);
                }
            }
            for arc in t.resets() {
                if let Some(pid) = self.compiled.place_id(arc.place.name()) {
                    reset_target[pid] = true;
                }
            }
        }

        for tid in 0..tc {
            if !self.compiled.has_match(tid) {
                continue;
            }
            let t = self.compiled.transition(tid);
            let Some(ms) = t.match_spec() else { continue };

            let mut requireds = Vec::with_capacity(ms.keys().len());
            let mut eligible = true;
            for mk in ms.keys() {
                let Some(pid) = self.compiled.place_id(mk.place_name()) else {
                    eligible = false;
                    break;
                };
                let required = match t
                    .input_specs()
                    .iter()
                    .find(|s| s.place_name() == mk.place_name())
                {
                    Some(In::One { .. }) => 1,
                    Some(In::Exactly { count, .. }) => *count,
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

            let mut matcher = IncrementalMatcher::new(requireds);
            for (key_idx, mk) in ms.keys().iter().enumerate() {
                let pid = self.compiled.place_id(mk.place_name()).unwrap();
                let guard = t
                    .input_specs()
                    .iter()
                    .find(|s| s.place_name() == mk.place_name())
                    .and_then(|s| s.guard())
                    .cloned();
                if let Some(queue) = self.marking.queue(mk.place_name()) {
                    for token in queue {
                        if let Some(g) = &guard
                            && !g(token.value.as_ref())
                        {
                            continue;
                        }
                        if let Some(name) = mk.extract(token.value.as_ref()) {
                            matcher.add(key_idx, name, token.created_at);
                        }
                    }
                }
                self.place_match_targets[pid].push((tid, key_idx));
            }
            self.match_caches[tid] = Some(matcher);
        }
    }

    /// Mirror a token added to correlated input `pid` into every fast-path
    /// matcher that consumes it (guard-filtered, projected to its name).
    fn cache_add_token(&mut self, pid: usize, value: &dyn std::any::Any, created_at: u64) {
        if self.place_match_targets[pid].is_empty() {
            return;
        }
        let targets = std::mem::take(&mut self.place_match_targets[pid]);
        for &(tid, key_idx) in &targets {
            let t = self.compiled.transition(tid);
            let ms = t.match_spec().expect("fast-path tid has a match spec");
            let mk = &ms.keys()[key_idx];
            let guard = t
                .input_specs()
                .iter()
                .find(|s| s.place_name() == mk.place_name())
                .and_then(|s| s.guard());
            if let Some(g) = guard
                && !g(value)
            {
                continue;
            }
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

        // ν-net join: a correlation name must satisfy every matched input (NU-020).
        if self.compiled.has_match(tid) {
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
    /// per-correlated-input name index over the FIFO `Marking` queues
    /// (guard-filtered) and defers the selection + tie-break to the shared
    /// [`select_match_name`]. Mirrors the precompiled backend exactly.
    fn find_match_binding(&self, tid: usize) -> Option<NameId> {
        let t = self.compiled.transition(tid);
        let ms = t.match_spec()?;
        let mut per_place: Vec<NameIndex> = Vec::with_capacity(ms.keys().len());
        let mut requireds: Vec<usize> = Vec::with_capacity(ms.keys().len());

        for mk in ms.keys() {
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

            let mut index: NameIndex = std::collections::HashMap::new();
            if let Some(queue) = self.marking.queue(mk.place_name()) {
                for token in queue {
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

    fn output_place_names(&self, tid: usize) -> HashSet<Arc<str>> {
        self.compiled
            .transition(tid)
            .output_places()
            .iter()
            .map(|p| Arc::clone(p.name_arc()))
            .collect()
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

    fn update_enablement<T: ChangeTracker>(&mut self, now_ms: f64, tracker: &mut T) {
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
                tracker.newly_enabled(tid);
            } else if !can_now && was_enabled {
                self.enabled_flags[tid] = false;
                self.enabled_transition_count -= 1;
                self.enabled_at_ms[tid] = f64::NEG_INFINITY;
            } else if can_now && was_enabled && self.has_input_from_reset_place(tid) {
                self.enabled_at_ms[tid] = now_ms;
                tracker.clock_restarted(tid);
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
            // exact() is enforced softly — it fires at the first opportunity at/after its target
            // and is never force-disabled (TIME-006). Only hard deadlines are reaped here.
            if self.is_exact_flags[tid] {
                continue;
            }
            let t = self.compiled.transition(tid);
            let elapsed = now_ms - self.enabled_at_ms[tid];
            let latest_ms = t.timing().latest() as f64;
            if elapsed > latest_ms + self.deadline_tolerance_ms {
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

    fn consume_for_firing<F>(
        &mut self,
        tid: usize,
        inputs: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        reads: &mut HashMap<Arc<str>, Vec<ErasedToken>>,
        mut emit_removed: F,
    ) where
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

        // ν-net join: resolve the correlation name once, then consume the
        // matched tokens (NU-020). For correlated inputs the chosen name plus
        // any unary guard form a combined predicate (guard first, then name
        // equality — NU-021); other inputs consume FIFO as usual.
        let chosen: Option<NameId> = if self.compiled.has_match(tid) {
            match &self.match_caches[tid] {
                Some(cache) => cache.best().cloned(),
                None => self.find_match_binding(tid),
            }
        } else {
            None
        };
        let match_spec = self.compiled.transition(tid).match_spec().cloned();

        for in_spec in &input_specs {
            let place_name = in_spec.place_name();
            let place_name_arc = Arc::clone(in_spec.place().name_arc());
            let key = match_spec
                .as_ref()
                .and_then(|m| m.key_for(place_name))
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
                        self.marking.count_matching(place_name, &pred)
                    }
                };
                for _ in 0..to_consume {
                    if let Some(token) = self.marking.remove_matching(place_name, &pred) {
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
                    In::All { .. } | In::AtLeast { .. } => self.marking.count(place_name),
                };
                for _ in 0..to_consume {
                    if let Some(token) = self.marking.remove_first(place_name) {
                        emit_removed(&place_name_arc, &token);
                        inputs
                            .entry(Arc::clone(&place_name_arc))
                            .or_default()
                            .push(token);
                    }
                }
            }
        }

        // Mirror the matched consume into the fast-path matcher — the only path
        // by which tokens leave this join's correlated inputs (NU-020).
        if let Some(name) = &chosen
            && let Some(cache) = self.match_caches[tid].as_mut()
        {
            cache.consume(name);
        }

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
    }

    fn produce_token(&mut self, place: &Arc<str>, token: ErasedToken) {
        if let Some(pid) = self.compiled.place_id(place) {
            self.cache_add_token(pid, token.value.as_ref(), token.created_at);
            self.marking.add_erased(place, token);
            bitmap::set_bit(&mut self.marked_places, pid);
            self.mark_place_dirty(pid);
        } else {
            self.marking.add_erased(place, token);
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
        if let Some(pid) = self.compiled.place_id(place) {
            self.cache_add_token(pid, token.value.as_ref(), token.created_at);
            self.marking.add_erased(place, token);
            bitmap::set_bit(&mut self.marked_places, pid);
            self.mark_place_dirty(pid);
        } else {
            self.marking.add_erased(place, token);
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
