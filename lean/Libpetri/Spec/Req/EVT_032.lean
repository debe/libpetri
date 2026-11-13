import Libpetri.Spec.Registry
import Libpetri.Reference.Replay
import Libpetri.Spec.Text.EVT_032

set_option linter.missingDocs true

/-!
# EVT-032: Marking Replay Cache (`spec/08-events-observability.md`)

The replay cache of the debug protocol answers the state at an event index of a recorded event
stream, replayed from the nearest cached snapshot. The requirement is a predicate over one call
of `compute_at(events, index)`, `call : CacheCall N E` (vocabulary in `Reference/Replay.lean`):
from the cache's content before the call, the stream and the index, the cache's content after
the call and the replayed state it answers. The event type `E` is a parameter and
`view : E → REv N` its replay view, the part of each event the replay reads.

This is the F part of [EVT-032] (wave W6). Under ruling D83 (a) the state is defined by the
replay, not by the run: the token counts come from `MarkingSnapshot`, `TokenAdded` and
`TokenRemoved` starting from the empty state, the enabled set is "enabled and not started since"
(an over-approximation), and the in-flight set is "started and not ended since". Both lines
assume a cache coherent with the stream: every snapshot is the replay of the stream up to its
index. Line 1: the call answers the replay of the first `i` events, which covers the clamp past
the end (AC2) and the empty state at 0 (AC1). Line 2: the cache the call leaves is coherent
again. Together they give that repeated calls on a stream that grows at its end all answer the
from-scratch replay (AC3, `evt032_repeated`). The comparison of the replayed state with a run's
marking is the B companion `EVT_032_B` (`EVT_032_B.lean`).

The witness is `refReplayCall`, the runtimes' algorithm. The wrong caches are a cache that
answers with a snapshot without replaying the delta, a read without the clamp, a cache that
stores off-by-one snapshots, a cache that stores snapshots past the end of the stream, one cache
per replay rule built over a wrong step, a snapshot that keeps the counts of the places it does
not list, and one cache per event name read by a wrong view (`recView` fixes the names).
-/

namespace Libpetri.Spec

/-! ## EVT-032: Marking Replay Cache -/

requirement EVT_032
  id "EVT-032"
  title "Marking Replay Cache"
  kind F
  scope "the replay cache of the debug protocol (Rust libpetri-debug MarkingCache, Python MarkingCache, Java org.libpetri.debug.MarkingCache, TypeScript MarkingCache in libpetri/debug)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_032.s1, EVT_032.s2, EVT_032.s3
  reading "For every replay view view : E → REv N of an event type E onto the places N, and every call of compute_at, call : CacheCall N E:"
          "for every cache c coherent with the stream es (every snapshot k of c stands for the index (k + 1) * iv, which is no greater than the length of es, and is the replay of the first (k + 1) * iv events of es) and every index i, the state the call answers is the replay of the first i events of es from the empty state (of all of es when i is past its length);"
          "and the cache the call leaves is coherent with es."
  assumes "The model is one call of compute_at(events, index), observed as call : CacheCall N E: from the cache's content before the call (Cache N: the snapshot interval and the snapshots), the event stream and the index, the cache's content after the call and the replayed state it answers (RState N). The event type E is a parameter and view : E → REv N its replay view (glossary: Replay view), which keeps of each event only what the replay reads: the count per place of a MarkingSnapshot, the place of a TokenAdded or TokenRemoved, and the transition of a TransitionEnabled, a TransitionStarted and the four end events (TransitionCompleted, TransitionFailed, TransitionTimedOut, ActionTimedOut); ExecutionStarted, ExecutionCompleted, TransitionClockRestarted and LogMessage are other. The block holds for every view, and the replay rules are fixed over the view by applyEv."
          "Which named event takes which rule (the event names of the third quoted sentence) is recView over RecEvent N, the thirteen recorded events by name with the part the replay can read, a MarkingSnapshot carried as the list of places it lists. recView gives an unlisted place the count zero, the four end events ended, and the four other events other. The forbids evidence fixes the names at that view: a cache built over a view that treats TransitionCompleted, TransitionFailed, TransitionTimedOut or ActionTimedOut as other, or that reads TransitionClockRestarted as TransitionEnabled, violates EVT-032 at recView (one theorem per name), and so does a cache whose MarkingSnapshot keeps the old count of a place it does not list (Rust apply_events without marking.clear(); EVT_032_mutant_snapMerge). The executor event model of wave W7 defines the full event type (timestamps, token values, outputs, errors); its replay view must be recView after the map that forgets what the replay does not read, and the W7 integrator ties the two."
          "The third quoted sentence is the glossary's replay step applyEv, which the two lines use through replay (the from-scratch replay) and Cache.Coherent: a definition the lines are stated with, not a line of its own. A cache that replays by any other step violates line 1, one mutant per clause: a replay that ignores MarkingSnapshot, that adds a snapshot's counts to the old ones instead of replacing them, that ignores TokenAdded, that ignores TokenRemoved, that ignores TransitionEnabled, whose TransitionStarted leaves its transition enabled, whose TransitionStarted does not put its transition in flight, whose end events leave their transition in flight, or whose other events clear the enabled set. A TransitionStarted puts its transition in flight whether or not it was enabled. The rules are those of all four bindings: Rust apply_events (rust/libpetri-debug/src/marking_cache.rs), Java DebugProtocolHandler.applyEvents, TypeScript applyEvents (typescript/src/debug/debug-protocol-handler.ts), and Python, which wraps the Rust cache (rust/libpetri-py/src/marking_cache.rs)."
          "The length bound of coherence (a snapshot stands for an index no greater than the length of the stream) is load-bearing: a cache that stores a snapshot past the end of the stream (TypeScript ensureCachedUpTo without its guard nextSnapshotIndex > events.length, where slice clamps) answers the call right and violates line 2 (EVT_032_mutant_premature); once the stream grows, the premature snapshot is read as the state at its index (evt032_premature_harm). coherentWith_append, and through it AC3, uses the bound."
          "The replayed state is compared by value: the token count of every place, and the enabled and the in-flight transition names as two sets. A ComputedState's two lists are read as sets and its marking as a count per place, because Java builds the lists from a HashSet, so a cached read and a full replay can list the same names in another order (clash evt-c#12, reproduced against the compiled classes), while Rust sorts them and TypeScript keeps insertion order. Ruling D83 (a) promises equal counts and equal sets and leaves the order unspecified; the spec edit of this wave rewords AC3 to say so. Whether the marking map lists a place with no token (a place emptied by TokenRemoved stays listed with an empty list) is not modelled: it counts zero either way."
          "AC1, reworded by ruling D83 (a) to 'compute_at(events, 0) is the empty state; compute_at(events, len) is the replay of the whole stream', is line 1 at i = 0 and i = len (evt032_zero, evt032_end). The earlier 'matches the final marking shape' compared the replay with the run's final marking, which holds for a stream that reports the initial marking in a MarkingSnapshot right after its ExecutionStarted event, as every executor's stream does (EVT-014), and can fail for a stream of a net whose initial marking is not empty that does not report it: such a stream reports no initial token (no TokenAdded for the initial marking, ruling D76 (a)), so a TokenRemoved of an initial token does nothing (replay_no_initial; clash evt-c#11). That comparison with a run is the B companion of this ID on the executor event model, the block EVT_032_B: there the replayed counts equal the marking on every declared place, and the armed transitions are a subset of the replayed enabled set."
          "The enabled set is defined by the events (a TransitionEnabled and no TransitionStarted of that transition since) and over-approximates the transitions enabled at that point of the run: a transition whose tokens another firing took, and a reaped transition, stay in it (replay_enabled_overapprox; clash evt-c#10; ruling D83 (a)). The block states the set the replay computes, never the run's enabled set; the subset relation is the W11 companion's."
          "AC2 (an index beyond the stream length is clamped to the end) is line 1 for an index past the length, since the first i events of a shorter stream are all of it (evt032_clamp). Every runtime clamps: Rust and Python (rust/libpetri-debug/src/marking_cache.rs, target_index.min(events.len()); python/tests/test_marking_cache.py tests it), TypeScript (Array.slice), and Java, whose MarkingCache.computeAt clamps the index to events.size() before subList (MarkingCacheTest computeAtBeyondStreamLengthClampsToEnd_EVT032_AC2), as its DebugProtocolHandler.computeStateAt does on the path without a subscription. Ruling D83 (a) keeps the clamp. A read that passes the index to subList unclamped throws IndexOutOfBoundsException past the end (clash evt-c#9, the behaviour RD-22 recorded); evt032_noClampCall, which meets both lines for every index up to the length and answers nothing useful past it, is that read and a mutant of line 1."
          "AC3, reworded by this wave to 'repeated calls on a stream that only grows at its end return state equal to a from-scratch replay', with a stream that changed otherwise needing invalidate() first, is lines 1 and 2 together: line 1 gives the equality for one call on a coherent cache, line 2 that the cache the call leaves is coherent again, and coherentWith_append that a coherent cache stays coherent when the stream grows at its end, so every call of a sequence on a growing stream that starts from a coherent cache answers the from-scratch replay (evt032_repeated), and after invalidate() (the empty cache, coherent with every stream: coherent_nil) a call answers the replay whatever the stream did before (evt032_after_invalidate). Whether a call reuses a snapshot rather than replaying from the start of the stream (the body's 'replayed from the nearest periodically-cached snapshot rather than from the start of the stream', and AC3's 'Reusing cached snapshots is expected for speed only') is kind Q: the answer is the same and only the time differs, so a cache that never reuses a snapshot meets both lines. The spec edit of this wave says so in the requirement."
          "Both lines assume the cache is coherent with the stream. The runtime caches are keyed by position only, so a cache filled against a stream that later changed other than by growing at its end (another session's stream, or a debug store that evicted its oldest events and so shifted every index, EVT-024) answers a state that is not the replay (evt032_incoherent) unless invalidate() emptied it first. Every debug protocol handler keeps its cache coherent so: before it computes a state it calls invalidate() whenever the evicted count of its debug store changed since the cache was last used (Java DebugProtocolHandler computeStateAt over DebugEventStore, which also compares the first retained event; TypeScript computeStateAt in typescript/src/debug/debug-protocol-handler.ts; Rust compute_state_at in rust/libpetri-debug/src/debug_protocol_handler.rs, which Python uses), the fix of RD-48 (spec/runtime-defects.md). That duty of the caller is outside this block, which states what the cache answers from a coherent cache."
          "AC4 (the marking carries token counts; replayed tokens need not carry value payloads) is the granularity of the model: the replayed state holds a count per place and no token, so no line can ask for a payload. The runtimes keep one TokenInfo per token (Java and TypeScript with the event's token data, Rust and Python with none), which the count abstracts."
          "The snapshot interval is the cache's iv, a parameter of both lines: they hold for every interval, including 0, where no snapshot is ever taken. Its value 256 (SNAPSHOT_INTERVAL in Rust, Java and TypeScript) is configuration, kind N, and the spec does not name it. The runtimes keep no interval in the cache, so a model of a runtime must read the interval from the cache's iv: a model that fixes it at 256 whatever iv says equals the reference on every cache whose iv is 256, the only caches the runtime makes, and still fails both lines on a cache of another interval. A fidelity or B-companion proof therefore models a runtime by its algorithm at iv, not at a constant."
          "The in-flight transitions are a set of names, as in every runtime, so a transition in flight twice at once (a re-entrant firing, Rust and Python under ruling D8 (b)) leaves the set when its first firing ends (evt032_reentrant; the spec edit of this wave says so). The two lines compare the cache with the replay and hold for every stream; a later line that compares the in-flight set with a run must assume a configuration that is not re-entrant (D8, later line, W11)."
          "Under ruling D20 (clash evt-c#15) the dependency on CONC-025 (the executor's lazily built Marking) is replaced by the events the replay reads: EVT-004, EVT-006 to EVT-012 and EVT-014; EVT-021 stays. The test derivation (a multi-firing run; compute_at at 0, at an intermediate index, at the end and beyond the end; clamping and snapshot reuse) is EVT_032_nonvacuous on the reference with interval 4."
  signoff "2026-11-13 c098dfbcd7d591bf ai"
  statement : ∀ {N E : Type} [DecidableEq N], (E → REv N) → CacheCall N E → Prop :=
    fun view call =>
      ∀ c es i, Cache.Coherent view c es →
        (call c es i).2 = replay view (es.take i) ∧ Cache.Coherent view (call c es i).1 es

/- The pinned readable form of EVT-032: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_032 : {N E : Type} → [DecidableEq N] → (E → REv N) → CacheCall N E → Prop :=
fun {N E} [DecidableEq N] view call =>
  ∀ (c : Cache N) (es : List E) (i : Nat),
    Cache.Coherent view c es →
      (call c es i).snd = replay view (List.take i es) ∧ Cache.Coherent view (call c es i).fst es
-/
#guard_msgs in #print EVT_032

/-- EVT-032 is `CallReplaysWith` over the replay step `applyEv`: the form the rule mutants are
stated in. -/
theorem evt032_iff {N E : Type} [DecidableEq N] (view : E → REv N) (call : CacheCall N E) :
    EVT_032 view call ↔ CallReplaysWith applyEv view call :=
  Iff.rfl

/-! ### The reference -/

/-- The reference replay cache satisfies EVT-032: from a coherent cache it answers the replay of
the first `i` events (clamped to the stream) and leaves a coherent cache. -/
@[evidence holds EVT_032]
theorem EVT_032_reference {N E : Type} [DecidableEq N] (view : E → REv N) :
    EVT_032 view (refReplayCall view) :=
  refCall_replays applyEv view

/-! ### Consequences -/

section Consequences

variable {N E : Type} [DecidableEq N] {view : E → REv N} {call : CacheCall N E}

/-- AC1, first half: at index 0 a cache that meets EVT-032 answers the empty state. -/
theorem evt032_zero (h : EVT_032 view call) {c : Cache N} {es : List E}
    (hc : c.Coherent view es) : (call c es 0).2 = RState.empty := by
  rw [(h c es 0 hc).1]
  rfl

/-- AC1, second half: at the length of the stream the answer is the replay of the whole stream. -/
theorem evt032_end (h : EVT_032 view call) {c : Cache N} {es : List E}
    (hc : c.Coherent view es) : (call c es es.length).2 = replay view es := by
  rw [(h c es _ hc).1, List.take_length]

/-- AC2: an index past the end of the stream answers what the end of the stream answers. -/
theorem evt032_clamp (h : EVT_032 view call) {c : Cache N} {es : List E}
    (hc : c.Coherent view es) {i : Nat} (hi : es.length ≤ i) :
    (call c es i).2 = replay view es := by
  rw [(h c es i hc).1, List.take_of_length_le hi]

/-- After `invalidate()` (the empty cache) every call answers the from-scratch replay. -/
theorem evt032_after_invalidate (h : EVT_032 view call) (iv : Nat) (es : List E) (i : Nat) :
    (call ⟨iv, []⟩ es i).2 = replay view (es.take i) :=
  (h _ es i (coherent_nil applyEv view iv es)).1

/-- The answers of a sequence of calls on one cache, the stream growing at its end before each
call: each query `(more, i)` appends `more` to the stream and asks for index `i`. -/
def callSeq (call : CacheCall N E) : Cache N → List E → List (List E × Nat) → List (RState N)
  | _, _, [] => []
  | c, es, (more, i) :: qs =>
    let r := call c (es ++ more) i
    r.2 :: callSeq call r.1 (es ++ more) qs

/-- The from-scratch replays of the same sequence of queries. -/
def scratchSeq (view : E → REv N) : List E → List (List E × Nat) → List (RState N)
  | _, [] => []
  | es, (more, i) :: qs => replay view ((es ++ more).take i) :: scratchSeq view (es ++ more) qs

/-- AC3: repeated calls on a stream that grows at its end, from a cache coherent with the stream,
all answer the from-scratch replay. -/
theorem evt032_repeated (h : EVT_032 view call) :
    ∀ (qs : List (List E × Nat)) (c : Cache N) (es : List E), c.Coherent view es →
      callSeq call c es qs = scratchSeq view es qs := by
  intro qs
  induction qs with
  | nil => intro _ _ _; rfl
  | cons q qs ih =>
    intro c es hc
    obtain ⟨more, i⟩ := q
    have hc' : c.Coherent view (es ++ more) := coherentWith_append applyEv view hc more
    obtain ⟨h1, h2⟩ := h c (es ++ more) i hc'
    simp only [callSeq, scratchSeq]
    rw [h1, ih _ _ h2]

end Consequences

/-- The coherence premise is needed: the reference, given a cache filled against another stream
(its one snapshot, for index 2, says one token in place 0; the stream adds none), answers at index
3 a count the replay of the stream does not have. -/
theorem evt032_incoherent :
    ((refReplayCall (N := Nat) id ⟨2, [replay id [REv.other, REv.added 0]]⟩
        [REv.other, REv.other, REv.other] 3).2.cnt 0 = 1) ∧
      (replay (N := Nat) id [REv.other, REv.other, REv.other]).cnt 0 = 0 := by
  decide

/-! ### Wrong caches, one per line -/

section Mutants

variable {N E : Type} [DecidableEq N]

/-- Line 2 alone: the cache a call leaves is coherent with the stream. -/
def KeepsCoherent (view : E → REv N) (call : CacheCall N E) : Prop :=
  ∀ c es i, Cache.Coherent view c es → (call c es i).1.Coherent view es

/-- A cache that extends its snapshots like the reference but answers with the highest snapshot
at or below the index without replaying the events after it. -/
def evt032_staleCall (view : E → REv N) : CacheCall N E := fun c es i =>
  let c' := extendWith applyEv view c es i
  let j := min i es.length
  (c', match min (j / c'.iv) c'.snaps.length with
    | 0 => replay view (es.take j)
    | k + 1 => (c'.snaps[k]?).getD (replay view (es.take j)))

/-- Lines 1 and 2 for an index up to the length of the stream only. -/
def AnswersWithin (view : E → REv N) (call : CacheCall N E) : Prop :=
  ∀ c es i, Cache.Coherent view c es → i ≤ es.length →
    (call c es i).2 = replay view (es.take i) ∧ (call c es i).1.Coherent view es

/-- A read without the clamp (`subList(0, targetIndex)`, the behaviour RD-22 recorded). Past the
end it throws; the model answers the empty state there, which stands for any answer other than the
replay of the whole stream. -/
def evt032_noClampCall (view : E → REv N) : CacheCall N E := fun c es i =>
  if i ≤ es.length then refReplayCall view c es i else (c, RState.empty)

/-- Line 1 alone: a call answers the replay of the first `i` events. -/
def Answers (view : E → REv N) (call : CacheCall N E) : Prop :=
  ∀ c es i, Cache.Coherent view c es → (call c es i).2 = replay view (es.take i)

/-- A cache that answers every call by a from-scratch replay but stores each new snapshot one
interval early: snapshot `k` is the replay of the first `k * iv` events, not `(k + 1) * iv`. A
later call that read the snapshot would answer wrongly. -/
def evt032_offByOneCall (view : E → REv N) : CacheCall N E := fun c es i =>
  let want := min (i / c.iv) (es.length / c.iv)
  let early := (List.range' c.snaps.length (want - c.snaps.length)).map
    (fun j => replay view (es.take (j * c.iv)))
  ({ c with snaps := c.snaps ++ early }, replay view (es.take i))

end Mutants

/-- ✗ A cache that answers with the snapshot and skips the delta keeps its cache coherent and
violates EVT-032 (line 1): with interval 2 and three `TokenAdded` on place 0, the call at index
3 answers the snapshot at index 2, two tokens instead of three. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_stale :
    KeepsCoherent (id : REv Nat → REv Nat) (evt032_staleCall id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (evt032_staleCall id) := by
  refine ⟨fun c es i hc => extendWith_coherent applyEv id hc i, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨2, []⟩ [REv.added 0, REv.added 0, REv.added 0] 3 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A read without the clamp meets both lines for every index up to the length and
violates EVT-032 (line 1, AC2): past the end of a one-event stream it does not answer the replay
of the stream. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noClamp :
    AnswersWithin (id : REv Nat → REv Nat) (evt032_noClampCall id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (evt032_noClampCall id) := by
  refine ⟨fun c es i hc hi => ?_, fun h => ?_⟩
  · simp only [evt032_noClampCall, if_pos hi]
    exact EVT_032_reference id c es i hc
  · have := congrArg (fun s => s.cnt 0)
      (h ⟨1, []⟩ [REv.added 0] 2 (coherent_nil _ _ _ _)).1
    revert this
    decide

/-- ✗ A cache that stores each snapshot one interval early answers every call correctly and
violates EVT-032 (line 2): after a call at index 1 of a one-`TokenAdded` stream, its snapshot for
index 1 counts no token. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_offByOne :
    Answers (id : REv Nat → REv Nat) (evt032_offByOneCall id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (evt032_offByOneCall id) := by
  refine ⟨fun _ _ _ _ => rfl, fun h => ?_⟩
  have h2 := (h ⟨1, []⟩ [REv.added 0] 1 (coherent_nil _ _ _ _)).2 0
    (replay id ([] : List (REv Nat))) rfl
  have := congrArg (fun s => s.cnt 0) h2.2
  revert this
  decide

/-- A cache that stores snapshots past the end of the stream (TypeScript `ensureCachedUpTo`
without its guard `nextSnapshotIndex > events.length`, where `slice` clamps): it wants `i / iv`
snapshots whatever the length of the stream, each the replay of the events up to its index, and
reads like the reference. -/
def evt032_prematureCall {N E : Type} [DecidableEq N] (view : E → REv N) : CacheCall N E :=
  fun c es i =>
    let more := snapsFrom applyEv view c.iv es c.snaps.length (i / c.iv - c.snaps.length)
    let c' : Cache N := ⟨c.iv, c.snaps ++ more⟩
    (c', readWith applyEv view c' es i)

/-- The premature cache answers every call right: its read never takes a snapshot above the
clamped index. -/
theorem evt032_premature_answers {N E : Type} [DecidableEq N] (view : E → REv N) :
    Answers view (evt032_prematureCall view) := by
  intro c es i hc
  apply readWith_replay_of
  intro k s hk _
  simp only at hk
  rcases Nat.lt_or_ge k c.snaps.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    exact (hc k s hk).2
  · rw [List.getElem?_append_right hge] at hk
    simp only [snapsFrom, List.getElem?_map] at hk
    by_cases hn : k - c.snaps.length < i / c.iv - c.snaps.length
    · rw [List.getElem?_range' hn] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      have hk' : c.snaps.length + 1 * (k - c.snaps.length) = k := by omega
      rw [hk']
    · rw [List.getElem?_eq_none (by simp; omega)] at hk
      simp at hk

/-- The harm the premature snapshot does: after a call at index 4 on a one-`TokenAdded` stream
(interval 2), the stream grows to three `TokenAdded`, and the next call at index 3 reads the
snapshot stored for index 2 (one token) plus one event: two tokens instead of three. -/
theorem evt032_premature_harm :
    (evt032_prematureCall (N := Nat) id (evt032_prematureCall (N := Nat) id ⟨2, []⟩
        [REv.added 0] 4).1 [REv.added 0, REv.added 0, REv.added 0] 3).2.cnt 0 = 2 ∧
      (replay (N := Nat) id [REv.added 0, REv.added 0, REv.added 0]).cnt 0 = 3 := by
  decide

/-- ✗ A cache that stores snapshots past the end of the stream answers every call right and
violates EVT-032 (line 2, the length bound): after a call at index 4 on a one-event stream with
interval 2, it holds a snapshot for index 2. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_premature :
    Answers (id : REv Nat → REv Nat) (evt032_prematureCall id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (evt032_prematureCall id) := by
  refine ⟨evt032_premature_answers id, fun h => ?_⟩
  have h2 := (h ⟨2, []⟩ [REv.added 0] 4 (coherent_nil _ _ _ _)).2 0
    (replay id [REv.added 0]) rfl
  have := h2.1
  revert this
  decide

/-! ### Wrong replay rules, one per clause of the third quoted sentence -/

section Steps

variable {N : Type} [DecidableEq N]

/-- A replay that ignores `MarkingSnapshot`. -/
def stepNoSnap (s : RState N) : REv N → RState N
  | .snapshot _ => s
  | e => applyEv s e

/-- A replay that adds a snapshot's counts to the counts it had instead of replacing them. -/
def stepSnapAdds (s : RState N) : REv N → RState N
  | .snapshot m => { s with cnt := fun p => s.cnt p + m p }
  | e => applyEv s e

/-- A replay that ignores `TokenAdded`. -/
def stepNoAdd (s : RState N) : REv N → RState N
  | .added _ => s
  | e => applyEv s e

/-- A replay that ignores `TokenRemoved`. -/
def stepNoRemove (s : RState N) : REv N → RState N
  | .removed _ => s
  | e => applyEv s e

/-- A replay that ignores `TransitionEnabled`. -/
def stepNoEnable (s : RState N) : REv N → RState N
  | .enabled _ => s
  | e => applyEv s e

/-- A replay whose `TransitionStarted` leaves the transition enabled. -/
def stepStartKeepsEnabled (s : RState N) : REv N → RState N
  | .started t => { s with fl := setAt s.fl t true }
  | e => applyEv s e

/-- A replay whose `TransitionStarted` does not put the transition in flight. -/
def stepStartNotInFlight (s : RState N) : REv N → RState N
  | .started t => { s with en := setAt s.en t false }
  | e => applyEv s e

/-- A replay whose end events leave the transition in flight. -/
def stepNoEnd (s : RState N) : REv N → RState N
  | .ended _ => s
  | e => applyEv s e

/-- A replay whose other events (for example `ExecutionCompleted`) clear the enabled set. -/
def stepOtherClears (s : RState N) : REv N → RState N
  | .other => { s with en := fun _ => false }
  | e => applyEv s e

end Steps

/-- ✗ A cache that replays without `MarkingSnapshot` meets both lines over its own step and
violates EVT-032: after a token is added and a snapshot of five tokens, it counts one. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noSnap :
    CallReplaysWith stepNoSnap (id : REv Nat → REv Nat) (refCallWith stepNoSnap id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepNoSnap id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨1, []⟩ [REv.added 0, REv.snapshot (fun _ => 5)] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose snapshot adds to the counts instead of replacing them violates EVT-032:
after a token is added and a snapshot of five tokens, it counts six. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_snapAdds :
    CallReplaysWith stepSnapAdds (id : REv Nat → REv Nat) (refCallWith stepSnapAdds id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepSnapAdds id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨1, []⟩ [REv.added 0, REv.snapshot (fun _ => 5)] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that ignores `TokenAdded` violates EVT-032: one added token counts zero. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noAdd :
    CallReplaysWith stepNoAdd (id : REv Nat → REv Nat) (refCallWith stepNoAdd id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepNoAdd id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨1, []⟩ [REv.added 0] 1 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that ignores `TokenRemoved` violates EVT-032: a token added and removed still
counts one. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noRemove :
    CallReplaysWith stepNoRemove (id : REv Nat → REv Nat) (refCallWith stepNoRemove id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepNoRemove id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨1, []⟩ [REv.added 0, REv.removed 0] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that ignores `TransitionEnabled` violates EVT-032: an enabled transition is not
listed as enabled. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noEnable :
    CallReplaysWith stepNoEnable (id : REv Nat → REv Nat) (refCallWith stepNoEnable id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepNoEnable id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.en "a")
    (h ⟨1, []⟩ [REv.enabled "a"] 1 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose `TransitionStarted` leaves the transition enabled violates EVT-032: a
started transition is still listed as enabled. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_startKeepsEnabled :
    CallReplaysWith stepStartKeepsEnabled (id : REv Nat → REv Nat)
        (refCallWith stepStartKeepsEnabled id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepStartKeepsEnabled id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.en "a")
    (h ⟨1, []⟩ [REv.enabled "a", REv.started "a"] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose `TransitionStarted` does not put the transition in flight violates EVT-032:
a started transition is not listed as in flight. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_startNotInFlight :
    CallReplaysWith stepStartNotInFlight (id : REv Nat → REv Nat)
        (refCallWith stepStartNotInFlight id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepStartNotInFlight id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [REv.enabled "a", REv.started "a"] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose end events leave the transition in flight violates EVT-032: a completed
transition is still listed as in flight. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_noEnd :
    CallReplaysWith stepNoEnd (id : REv Nat → REv Nat) (refCallWith stepNoEnd id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepNoEnd id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [REv.started "a", REv.ended "a"] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose other events clear the enabled set violates EVT-032: an enabled transition
is dropped by a later `LogMessage`. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_otherClears :
    CallReplaysWith stepOtherClears (id : REv Nat → REv Nat) (refCallWith stepOtherClears id) ∧
      ¬ EVT_032 (id : REv Nat → REv Nat) (refCallWith stepOtherClears id) := by
  refine ⟨refCall_replays _ _, fun h => ?_⟩
  have := congrArg (fun s => s.en "a")
    (h ⟨1, []⟩ [REv.enabled "a", REv.other] 2 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-! ### Event names: `recView` fixes which event takes which rule -/

section Names

variable {N : Type} [DecidableEq N]

/-- A replay view that treats the event named `n` as other and every other event as `recView`
does. -/
def recViewIgnoring (n : String) (e : RecEvent N) : REv N :=
  if e.name = n then .other else recView e

/-- A replay view that reads `TransitionClockRestarted` as `TransitionEnabled`. -/
def recViewClockEnables : RecEvent N → REv N
  | .transitionClockRestarted t => .enabled t
  | e => recView e

/-- The replay step over the recorded events without `marking.clear()` (Rust `apply_events`
with the clear dropped from the `MarkingSnapshot` arm): a snapshot overwrites the places it lists
and keeps the old count of every other place. -/
def snapMergeStep (s : RState N) : RecEvent N → RState N
  | .markingSnapshot l => { s with cnt := fun p => (l.lookup p).getD (s.cnt p) }
  | e => applyEv s (recView e)

/-- A cache that answers every call by a from-scratch replay with `snapMergeStep` and leaves its
content as it was. -/
def evt032_snapMergeCall : CacheCall N (RecEvent N) := fun c es i =>
  (c, (es.take i).foldl snapMergeStep RState.empty)

end Names

/-- Each wrong view is the reference of its own view: it meets EVT-032 for the view it uses. -/
theorem evt032_wrong_view_is_reference (n : String) :
    EVT_032 (recViewIgnoring (N := Nat) n) (refReplayCall (recViewIgnoring n)) ∧
      EVT_032 (recViewClockEnables (N := Nat)) (refReplayCall recViewClockEnables) :=
  ⟨EVT_032_reference _, EVT_032_reference _⟩

/-- ✗ A cache that treats `TransitionCompleted` as other violates EVT-032 at `recView`: a
completed transition stays in flight. -/
@[evidence forbids EVT_032]
theorem EVT_032_forbids_completedOther :
    ¬ EVT_032 (recView (N := Nat)) (refReplayCall (recViewIgnoring "TransitionCompleted")) := by
  intro h
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [RecEvent.transitionStarted "a", RecEvent.transitionCompleted "a"] 2
      (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that treats `TransitionFailed` as other violates EVT-032 at `recView`: a failed
transition stays in flight. -/
@[evidence forbids EVT_032]
theorem EVT_032_forbids_failedOther :
    ¬ EVT_032 (recView (N := Nat)) (refReplayCall (recViewIgnoring "TransitionFailed")) := by
  intro h
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [RecEvent.transitionStarted "a", RecEvent.transitionFailed "a"] 2
      (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that treats `TransitionTimedOut` as other violates EVT-032 at `recView`: a timed
out transition stays in flight. -/
@[evidence forbids EVT_032]
theorem EVT_032_forbids_timedOutOther :
    ¬ EVT_032 (recView (N := Nat)) (refReplayCall (recViewIgnoring "TransitionTimedOut")) := by
  intro h
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [RecEvent.transitionStarted "a", RecEvent.transitionTimedOut "a"] 2
      (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that treats `ActionTimedOut` as other violates EVT-032 at `recView`: a transition
whose action timed out stays in flight. -/
@[evidence forbids EVT_032]
theorem EVT_032_forbids_actionTimedOutOther :
    ¬ EVT_032 (recView (N := Nat)) (refReplayCall (recViewIgnoring "ActionTimedOut")) := by
  intro h
  have := congrArg (fun s => s.fl "a")
    (h ⟨1, []⟩ [RecEvent.transitionStarted "a", RecEvent.actionTimedOut "a"] 2
      (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache that reads `TransitionClockRestarted` as `TransitionEnabled` violates EVT-032 at
`recView`: a restarted clock lists its transition as enabled. -/
@[evidence forbids EVT_032]
theorem EVT_032_forbids_clockEnables :
    ¬ EVT_032 (recView (N := Nat)) (refReplayCall recViewClockEnables) := by
  intro h
  have := congrArg (fun s => s.en "a")
    (h ⟨1, []⟩ [RecEvent.transitionClockRestarted "a"] 1 (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- ✗ A cache whose `MarkingSnapshot` keeps the old count of a place it does not list (Rust
`apply_events` without `marking.clear()`) leaves its cache coherent and violates EVT-032 at
`recView` (line 1): a token in place 0, then a snapshot that lists only place 1, counts one token
in place 0 instead of zero. -/
@[evidence mutant EVT_032]
theorem EVT_032_mutant_snapMerge :
    KeepsCoherent (recView (N := Nat)) evt032_snapMergeCall ∧
      ¬ EVT_032 (recView (N := Nat)) evt032_snapMergeCall := by
  refine ⟨fun _ _ _ hc => hc, fun h => ?_⟩
  have := congrArg (fun s => s.cnt 0)
    (h ⟨1, []⟩ [RecEvent.tokenAdded 0, RecEvent.markingSnapshot [(1, 3)]] 2
      (coherent_nil _ _ _ _)).1
  revert this
  decide

/-- The in-flight transitions are a set of names: a transition started twice and ended once is
no longer listed as in flight (a re-entrant firing, Rust and Python under ruling D8 (b)). -/
theorem evt032_reentrant :
    (replay (N := Nat) recView [RecEvent.transitionStarted "a", RecEvent.transitionStarted "a",
      RecEvent.transitionCompleted "a"]).fl "a" = false := by
  decide

/-! ### Non-vacuity: the test derivation on the reference -/

/-- A multi-firing stream of ten events: a snapshot of one token in place 0, then `t1` moves it
to place 1 and completes, then `t2` starts moving it to place 2 and is still in flight. -/
def evt032_stream : List (REv Nat) :=
  [.snapshot (fun p => if p = 0 then 1 else 0),
   .enabled "t1", .started "t1", .removed 0, .added 1, .ended "t1",
   .enabled "t2", .started "t2", .removed 1, .added 2]

/-- The test derivation on the reference, interval 4, starting from the empty cache: index 0 is
the empty state; at index 5 the token is in place 1 and `t1` is in flight; at the end it is in
place 2 and `t2` is in flight; an index beyond the end answers the end. The call at index 9
leaves two snapshots (indexes 4 and 8), and a later call at index 6 from that cache, which
starts from the snapshot at index 4, answers what a call from the empty cache answers. -/
@[evidence nonvacuous EVT_032]
theorem EVT_032_nonvacuous :
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 0).2.cnt 0 = 0 ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 5).2.cnt 1 = 1 ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 5).2.fl "t1" = true ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 10).2.cnt 2 = 1 ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 10).2.fl "t2" = true ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 10).2.en "t1" = false ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 99).2.cnt 2 = 1 ∧
    (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 9).1.snaps.length = 2 ∧
    (refReplayCall id (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 9).1
        evt032_stream 6).2.cnt 1 =
      (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 6).2.cnt 1 ∧
    (refReplayCall id (refReplayCall id (⟨4, []⟩ : Cache Nat) evt032_stream 9).1
        evt032_stream 6).2.fl "t1" = false := by
  decide

end Libpetri.Spec
