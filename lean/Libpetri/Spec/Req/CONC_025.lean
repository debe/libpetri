import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryQueue
import Libpetri.Refinement

set_option linter.missingDocs true

/-!
# CONC-025: Lazy marking synchronization (`spec/05-concurrency.md`)

The precompiled executor keeps its tokens in a token store, one queue per place id
([CONC-022]), and builds a `Marking` from it only when one is asked for. The requirement this
block encodes is AC3: the `Marking` it builds is the store's current content. It is a predicate
over an abstract executor that materialises (`Materialiser`): a state type, the states a run
starts from, a step relation, the token store inside a state, read through CONC-022's store
interface `MarkingOps`, and the marking the executor hands out at a state. The line holds at the
start state and at every state that steps reach from it. It is checked against the reference
(`refMaterialiser`: the precompiled cycle `pcCycle` and single firing `pcFire` over `PBState`,
materialising with `Pool.proj`, the field-for-field model of `materialize_marking`) and against
six wrong executors: one that materialises once and keeps the result, one that reads each ring
from the start of its block instead of from its head, one that hands out the initial tokens
twice, one whose cache is built before the store is loaded, one that materialises from a copy
of its rings, and one that refreshes its marking only at the end of a cycle; and against a
mutant reading that asks for the line at the start of a run only.

When the executor materialises (AC2) and that it creates no `Marking` object in a normal cycle
(AC1) are not observable in a state model: both are quality criteria, named in the assumptions.
-/

namespace Libpetri.Spec

open Libpetri

/-! ## The materialising executor -/

/-- An executor that keeps its tokens in the token store `S` ([CONC-022]) and materialises a
marking on demand ([CONC-025]). `init s` says that a run can start from `s`: the executor is
built and its store is loaded from the initial marking, before any cycle. `step s s'` says that
the executor moves from `s` to `s'` between two moments at which a marking can be asked for (one
firing, or one whole cycle). `store s` is the token store inside `s`, the one the firings consume
from and deposit to, whose queues `S.view` reads; `mat s` is the marking the executor hands out
when one is asked for at `s`, each place's tokens oldest first (glossary: Queue order). -/
structure Materialiser (S : MarkingOps PlaceId Colour) where
  /-- The executor state. -/
  σ : Type
  /-- The states a run starts from: the store loaded from the initial marking, no cycle run. -/
  init : σ → Prop
  /-- One move of the executor between two moments at which a marking can be asked for. -/
  step : σ → σ → Prop
  /-- The token store inside a state, the one the firings consume from and deposit to. -/
  store : σ → S.σ
  /-- The marking materialised at a state, each place's tokens oldest first. -/
  mat : σ → QueueMarking PlaceId Colour

/-- The reference: the precompiled backend's state `PBState`, whose token store is the ring pool
`ring` (`refRingStore`, [CONC-022]). A run starts from any state whose pool is well formed. A
step is one precompiled executor cycle `pcCycle`, or one firing `pcFire` inside it of a
transition that passes the recheck `pcRecheck`, of some net and action emission (`Refinement/Model.lean`), and the marking handed out is the ring pool's
projection `Pool.proj`, which reads each ring from its head for its stored count, as
`materialize_marking` does (`precompiled_backend.rs`, `Ring/Core.lean`: "`proj p` is the whole
FIFO queue and is exactly what `materialize_marking` emits for place `p`"). -/
def refMaterialiser : Materialiser refRingStore where
  σ := PBState
  init st := Pool.WF st.ring
  step st st' := ∃ net emit, st' = pcCycle net emit st ∨
    ∃ tid, pcRecheck net st tid = true ∧ st' = pcFire net emit st tid
  store st := st.ring
  mat st := st.ring.proj

#spec_witness refMaterialiser

/-! ## CONC-025: Lazy marking synchronization -/

requirement CONC_025
  id "CONC-025"
  title "Lazy Marking Synchronization"
  kind B
  scope "precompiled executor"
  source verbatim "spec/05-concurrency.md"
  quote "The materialized Marking accurately reflects the current ring buffer state."
        "*When* the executor materializes a Marking, it *shall* give each place the token storage holds a queue for exactly the tokens of that queue at that moment, in queue order."
  reading "For every executor X over the token store S:"
          "at every state that zero or more steps reach from a state a run starts from, the start state included, the materialised marking gives each place S holds a queue for exactly the queue S holds for it, oldest first."
  assumes "The executor is a Materialiser over the store interface MarkingOps of CONC-022 (glossary: Queue order): a state type, the states a run starts from (init: the executor is built and its store loaded from the initial marking, before any cycle), a step relation, the token store inside a state and the marking materialised at a state. A ring buffer is read as the store's queue for a place, S.view, and 'a place that has a ring buffer' (AC3), which the EARS sentence words as 'each place the token storage holds a queue for' in CONC-022's vocabulary, as S.ok. The witness store is refRingStore, the ring pool Libpetri.Pool. The TypeScript precompiled executor keeps a plain array per place instead of a ring (clash conc-b#5, typescript/src/runtime/precompiled-net-executor.ts:179); the statement is over the store interface, so it reads an array store alike. The words 'ring buffer' stay only in the AC3 quote until ruling D20, which would move them to an implementation note."
          "The fields describe the executor; they are not chosen to suit the line. init holds of every state a run can start from, store is the token storage the firings consume from and deposit to, and step is every move between two moments at which a marking can be asked for. A description with no start state, with steps that skip such a moment, or with a store field that names a copy the firings never touch says nothing about the executor, as for every abstract relation a requirement block is stated over. Under that reading the snapshot hazard is caught: an executor that materialises from a copy of its rings taken at the start is rejected once store is its live storage (CONC_025_forbids_snapshot)."
          "'Current' and 'at that moment' are read as: at a start state and at every state steps reach from it (Relation.ReflTransGen, whose reflexive case is the start state). So a materialisation asked for before the first cycle is constrained (CONC_025_forbids_earlyCache: a cache built before the store is loaded hands out nothing), and an executor that is wrong from the start is rejected there (CONC_025_forbids_seeded hands out every initial token twice, at every state it reaches). A store changed by something other than a step, such as the restore of a snapshot ([CORE-073]), starts a new run, so the state after it is a start state. The line does not require agreement at a state no run reaches: an honest cache whose stale states are unreachable satisfies it."
          "A step has the granularity at which a marking can be asked for. AC2's occasions include event emission ([EVT-014]), which the shipped executors do after each firing inside a cycle, so a step is one firing as well as one whole cycle. An executor that refreshes its marking only at the end of a cycle hands out a stale marking between two firings and is rejected (CONC_025_forbids_cycleRefresh). The step relation is abstract, so the line constrains no firing rule and needs no fragment limit: it holds or fails of one executor, timed or not. The reference steps are pcCycle and pcFire, the untimed immediate synchronous cycle of Refinement/Model.lean and one firing in it, but the reference satisfies the line whatever its steps do, because it materialises by reading the store, at every state (CONC_025_reference). A step relation of the executor model RefExec (W5) can be checked against the same statement."
          "The holds proof is definitional: the reference's mat is S.view composed with its store field, so CONC_025_reference is rfl at every state, reached or not, and by itself says nothing about the steps. The behavioural content, that the store the reference reads is the one its firings change and that its materialised marking agrees with the bitmap executor's after any number of cycles, is conc025_matches_bitmap (cited, marking_agreement). Tying the Materialiser's step on its store to the queue firing relation of the joint model, so that store cannot be a copy the firings never touch, is a W5 item for the executor model (RefExec)."
          "S.ok includes the well-formedness of the store (for refRingStore, Pool.WF and a place id below the compiled place count), which the requirement does not state. It is the store interface's reading of 'holds a queue': a store that is not well formed holds no queue view reads faithfully, which is CONC-022's subject. The precompiled cycle keeps the pool well formed and its place count fixed on a compiled net (pcCycle_rel in Refinement), so on the reference every compiled place stays in S.ok at every state a run reaches from a well-formed start. Splitting ok into 'place known' and a separate well-formedness hypothesis would change the store interface CONC-022 is stated over, so the line uses S.ok as CONC-022 does."
          "Places outside the store are not constrained (clash conc-b#8): every shipped precompiled executor also merges into the materialised marking the tokens it keeps for unknown places (rust/libpetri-runtime/src/precompiled_backend.rs:880-881 extra_marking, java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:1587 extraTokens, typescript/src/runtime/precompiled-net-executor.ts:1767-1771 unknownPlaceTokens), which no ring holds. That retention is CORE-072's subject (AC3 there); the line neither requires nor forbids it on places outside the store. On a place the store holds a queue for it forbids it: a side marking seeded with the whole initial marking, known places included, hands those tokens out twice (CONC_025_forbids_seeded). The editorial rewording of AC3 that names those tokens waits for ruling D20."
          "AC1 (normal execution cycles do not create or update a Marking object) is not encoded: whether an object is allocated or written is not observable in a state model, so AC1 is a quality criterion, shown by the test derivation (a run with a noop event store creates no Marking until the result is requested), which is not encoded either. That a token deposited on an unknown place updates the retained marking in a normal cycle (clash conc-b#8) is AC1's and waits for D20 with it. The Kind line is B, the kind of its one encoded line, following the one-letter convention of the signed blocks; the laziness of the title and AC1 are quality criteria with no line, and whether the Kind line changes for Q content is ruling D21, which is open."
          "AC2 (the Marking is materialized on demand for event emission, debug or the result) is not encoded: when the executor materialises is the subject of the requirements that ask for a marking ([EVT-014], [EXEC-041], and the snapshot request of [ENV-014], which the body's list of occasions omits, clash conc-b#8). The line says what every materialisation returns, at whatever reachable state it is asked for."
          "AC3 is the line. CONC_025_forbids_stale rejects an executor that materialises once and hands out that marking after later cycles (the hazard the TypeScript getMarking docstring names, typescript/src/runtime/precompiled-net-executor.ts:1778-1794; caching outside a run, which TypeScript does, is allowed, since no step runs between). CONC_025_forbids_blockOrder rejects one that reads each ring from the start of its block instead of from its head: it hands out the right tokens in the wrong order once a ring has wrapped, so 'accurately reflects' is read with queue order, as the EARS sentence says."
  signoff "pending"
  statement : (S : MarkingOps PlaceId Colour) → Materialiser S → Prop :=
    fun S X => ∀ s₀ s, X.init s₀ → Relation.ReflTransGen X.step s₀ s →
      ∀ p, S.ok (X.store s) p → X.mat s p = S.view (X.store s) p

/- The pinned readable form of CONC-025: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_025 : (S : MarkingOps PlaceId Colour) → Materialiser S → Prop :=
fun S X =>
  ∀ (s₀ s : X.σ),
    X.init s₀ →
      Relation.ReflTransGen X.step s₀ s → ∀ (p : PlaceId), S.ok (X.store s) p → X.mat s p = S.view (X.store s) p
-/
#guard_msgs in #print CONC_025

/-! ### The reference -/

/-- The reference satisfies CONC-025: it materialises by reading the ring pool (`Pool.proj`),
so at every state, reached or not, the marking it hands out is the store's queues. -/
@[evidence holds CONC_025]
theorem CONC_025_reference : CONC_025 refRingStore refMaterialiser :=
  fun _ _ _ _ _ _ => rfl

/-- On the untimed immediate synchronous fragment, the marking the reference materialises after
any number of cycles is the bitmap executor's marking on every compiled place
(`marking_agreement`): the store the materialisation reads is the right one. -/
@[evidence cites "CONC-025" "on the untimed immediate synchronous fragment the marking the precompiled executor materialises after any number of cycles equals the bitmap reference executor's marking on every compiled place (marking_agreement)"]
theorem conc025_matches_bitmap {n : Nat} {net : Net} {emit : Emit} {st₀ : PBState}
    {bb₀ : BBState} (hrel : Rel n st₀ bb₀) (hok : NetOK net n) (hemit : EmitOK emit n) :
    ∀ k p, p < n →
      refMaterialiser.mat (iterate (pcCycle net emit) k st₀) p
        = (iterate (bbCycle net emit) k bb₀).marking p :=
  marking_agreement hrel hok hemit

/-! ### Examples -/

/-- The ring pool of the examples: one place, `0`, whose ring of capacity 2 is full with the
tokens `5` (slot 0, the head) and `6` (slot 1). -/
def conc025_pool : Pool where
  pool idx := if idx = 0 then some 5 else if idx = 1 then some 6 else none
  len := 2
  offset _ := 0
  head _ := 0
  tail _ := 0
  cnt _ := 2
  cap _ := 2
  nplaces := 1

/-- `conc025_pool` is well formed (RB1-RB3). -/
theorem conc025_pool_wf : Pool.WF conc025_pool := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _; simp [conc025_pool]
  · intro _ _; simp [conc025_pool]
  · intro _ _; simp [conc025_pool]
  · intro _ _; simp [conc025_pool, ringPos]
  · intro _ _; simp [conc025_pool]
  · intro p _ i hi
    have hi' : i < 2 := hi
    simp only [Pool.slot, conc025_pool, ringPos, Nat.zero_add, Nat.mod_eq_of_lt hi']
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
  · intro _ _ i h1 h2
    have : 2 ≤ i := h1
    have : i < 2 := h2
    omega
  · intro p q hp hq hne
    have : p < 1 := hp
    have : q < 1 := hq
    omega

/-- The executor state of the examples: the pool `conc025_pool`, every transition dirty, so the
first cycle evaluates its enablement. -/
def conc025_st : PBState := ⟨conc025_pool, fun p => decide (p = 0), fun _ => false, fun _ => true⟩

/-- The start state of the examples has place `0` in the store. -/
theorem conc025_st_ok : refRingStore.ok conc025_st.ring 0 := ⟨conc025_pool_wf, by decide⟩

/-- The net of the examples: one transition with a `one()` input on place `0`. -/
def conc025_net : Net :=
  [{ name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }]

/-- The action of the examples: every firing emits the token `7` to place `0`. -/
def conc025_emit : Emit := fun _ _ _ => [(0, 7)]

/-- The state after one cycle: `t` consumed the head `5` and deposited `7`. The ring's head moved
to slot 1, and `7` went to slot 0: the ring has wrapped. -/
def conc025_st₁ : PBState := pcCycle conc025_net conc025_emit conc025_st

/-- The state inside the first cycle once enablement has been evaluated: the same pool, `t`
enabled, nothing dirty. -/
def conc025_stE : PBState :=
  ⟨conc025_pool, fun p => decide (p = 0), fun t => decide (t = 0), fun _ => false⟩

/-- The state after the firing of `t` from `conc025_stE`, inside the cycle: `t` consumed the
head `5` and deposited `7`. -/
def conc025_stF : PBState := pcFire conc025_net conc025_emit conc025_stE 0

/-- `t` passes the recheck at `conc025_stE`: it is enabled and place `0` is marked. -/
theorem conc025_recheck : pcRecheck conc025_net conc025_stE 0 = true := by decide

/-- The bitmap executor's state that `conc025_st` refines. -/
def conc025_bb : BBState := ⟨conc025_pool.proj, conc025_st.enabled, conc025_st.dirty⟩

/-- The net of the examples is compile-clean and references only place `0`. -/
theorem conc025_net_ok : NetOK conc025_net 1 := by
  intro t ht
  simp only [conc025_net, List.mem_singleton] at ht
  subst ht
  exact ⟨by simp [DistinctInputPlaces], ⟨by simp, by simp, by simp, by simp⟩⟩

/-- The action of the examples emits only to place `0`. -/
theorem conc025_emit_ok : EmitOK conc025_emit 1 := by
  intro _ _ _ e he
  simp only [conc025_emit, List.mem_singleton] at he
  subst he
  decide

/-- The pool after one cycle is well formed and still has place `0` (`pcCycle_rel`). -/
theorem conc025_st₁_ok : refRingStore.ok conc025_st₁.ring 0 := by
  have h := pcCycle_rel (n := 1) (bb := conc025_bb) ⟨conc025_pool_wf, rfl, fun _ _ => rfl, rfl, rfl⟩
    conc025_net_ok conc025_emit_ok
  exact ⟨h.wf, by
    have h1 : conc025_st₁.ring.nplaces = 1 := h.np
    rw [h1]; decide⟩

/-- The pool after the firing of `t` is well formed and still has place `0` (`pcFire_rel`). -/
theorem conc025_stF_ok : refRingStore.ok conc025_stF.ring 0 := by
  have h := pcFire_rel (n := 1) (bb := ⟨conc025_pool.proj, conc025_stE.enabled, conc025_stE.dirty⟩)
    ⟨conc025_pool_wf, rfl, fun _ _ => rfl, rfl, rfl⟩ conc025_net_ok conc025_emit_ok conc025_recheck
  exact ⟨h.wf, by
    have h1 : conc025_stF.ring.nplaces = 1 := h.np
    rw [h1]; decide⟩

/-! ### Violation: a marking materialised once -/

/-- An executor that materialises once, at the start, and keeps the result: the state carries
the marking handed out, which a cycle leaves as it was. -/
def conc025_stale : Materialiser refRingStore where
  σ := PBState × QueueMarking PlaceId Colour
  init s := s.2 = s.1.ring.proj
  step s s' := (∃ net emit, s'.1 = pcCycle net emit s.1) ∧ s'.2 = s.2
  store s := s.1.ring
  mat s := s.2

/-- ✗ An executor that materialises once violates CONC-025: from the start state, materialised
as `5, 6`, one cycle moves place `0`'s queue to `6, 7`, and the executor still hands out
`5, 6`. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_stale : ¬ CONC_025 refRingStore conc025_stale := by
  intro h
  have := h (conc025_st, conc025_st.ring.proj) (conc025_st₁, conc025_st.ring.proj)
    rfl (Relation.ReflTransGen.single ⟨⟨_, _, rfl⟩, rfl⟩) 0 conc025_st₁_ok
  revert this
  decide

/-- Mutant reading of CONC-025 that reads "the current ring buffer state" at the start of a run
only: the marking handed out at a start state is the store's queues, and nothing is asked of a
state that steps reach. -/
def CONC_025_mutant_startOnly (S : MarkingOps PlaceId Colour) (X : Materialiser S) : Prop :=
  ∀ s, X.init s → ∀ p, S.ok (X.store s) p → X.mat s p = S.view (X.store s) p

/-- The executor that materialises once kills the start-only mutant: at a start state it hands
out the store's queues, so it meets the mutant reading, but after one cycle it still hands out
the start marking, which CONC-025 rejects (`CONC_025_forbids_stale`). -/
@[evidence mutant CONC_025]
theorem CONC_025_mutant_startOnly_killed :
    CONC_025_mutant_startOnly refRingStore conc025_stale ∧ ¬ CONC_025 refRingStore conc025_stale :=
  ⟨fun _ hs _ _ => congrFun hs _, CONC_025_forbids_stale⟩

/-! ### Violation: rings read in block order -/

/-- An executor that reads each ring from the start of its block, slot by slot up to its
capacity, instead of from its head: it hands out the tokens a ring holds, in the order of the
slots. -/
def conc025_blockOrder : Materialiser refRingStore where
  σ := PBState
  init st := Pool.WF st.ring
  step st st' := ∃ net emit, st' = pcCycle net emit st
  store st := st.ring
  mat st p := (List.range (st.ring.cap p)).filterMap (fun i => st.ring.pool (st.ring.offset p + i))

/-- ✗ An executor that reads its rings in block order violates CONC-025: at the start state the
ring has not wrapped and it hands out `5, 6`, which is right; after one cycle the ring has
wrapped, place `0`'s queue is `6, 7`, and it hands out `7, 6`. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_blockOrder : ¬ CONC_025 refRingStore conc025_blockOrder := by
  intro h
  have := h conc025_st conc025_st₁ conc025_pool_wf (Relation.ReflTransGen.single ⟨_, _, rfl⟩) 0
    conc025_st₁_ok
  revert this
  decide

/-! ### Violation: the initial tokens handed out twice -/

/-- An executor that keeps a side marking for tokens no ring holds (the retained marking of
[CORE-072]) and merges it into every materialisation, but seeds it from the whole initial
marking, known places included. The store was loaded from the same marking, so every initial
token of a known place is handed out twice, at the start and after every cycle, which leaves the
side marking as it was. -/
def conc025_seeded : Materialiser refRingStore where
  σ := PBState × QueueMarking PlaceId Colour
  init s := s.2 = s.1.ring.proj
  step s s' := (∃ net emit, s'.1 = pcCycle net emit s.1) ∧ s'.2 = s.2
  store s := s.1.ring
  mat s p := s.2 p ++ s.1.ring.proj p

/-- ✗ An executor that hands out the initial tokens twice violates CONC-025 at the start state:
place `0`'s queue is `5, 6`, and it hands out `5, 6, 5, 6`. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_seeded : ¬ CONC_025 refRingStore conc025_seeded := by
  intro h
  have := h (conc025_st, conc025_st.ring.proj) (conc025_st, conc025_st.ring.proj) rfl
    Relation.ReflTransGen.refl 0 conc025_st_ok
  revert this
  decide

/-! ### Violation: a cache built before the store is loaded -/

/-- An executor that caches the materialised marking and refreshes the cache at the end of every
cycle, but builds the cache when it is constructed, before the store is loaded from the initial
marking: a materialisation asked for before the first cycle (an initial marking event, a debug
subscription on attach, a request before the run) hands out the empty marking. -/
def conc025_earlyCache : Materialiser refRingStore where
  σ := PBState × QueueMarking PlaceId Colour
  init s := s.2 = fun _ => []
  step s s' := (∃ net emit, s'.1 = pcCycle net emit s.1) ∧ s'.2 = s'.1.ring.proj
  store s := s.1.ring
  mat s := s.2

/-- ✗ An executor whose cache is built before the store is loaded violates CONC-025 at the start
state: place `0`'s queue is `5, 6`, and it hands out nothing. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_earlyCache : ¬ CONC_025 refRingStore conc025_earlyCache := by
  intro h
  have := h (conc025_st, fun _ => []) (conc025_st, fun _ => []) rfl
    Relation.ReflTransGen.refl 0 conc025_st_ok
  revert this
  decide

/-! ### Violation: materialised from a copy of the rings -/

/-- An executor that materialises from a copy of its ring pool taken at the start, while its
cycles fire from the live pool, which is its token storage. -/
def conc025_snapshot : Materialiser refRingStore where
  σ := PBState × Pool
  init s := s.2 = s.1.ring
  step s s' := (∃ net emit, s'.1 = pcCycle net emit s.1) ∧ s'.2 = s.2
  store s := s.1.ring
  mat s := s.2.proj

/-- ✗ An executor that materialises from a copy of its rings violates CONC-025: after one cycle
the live ring of place `0` holds `6, 7`, and it still hands out `5, 6`. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_snapshot : ¬ CONC_025 refRingStore conc025_snapshot := by
  intro h
  have := h (conc025_st, conc025_pool) (conc025_st₁, conc025_pool) rfl
    (Relation.ReflTransGen.single ⟨⟨_, _, rfl⟩, rfl⟩) 0 conc025_st₁_ok
  revert this
  decide

/-! ### Violation: refreshed only at the end of a cycle -/

/-- An executor that materialises at the start and refreshes its marking at the end of every
cycle, but not after a firing inside a cycle: between two firings, where events are emitted, it
hands out the marking of the end of the last cycle. -/
def conc025_cycleRefresh : Materialiser refRingStore where
  σ := PBState × QueueMarking PlaceId Colour
  init s := s.2 = s.1.ring.proj
  step s s' := (∃ net emit, s'.1 = pcCycle net emit s.1 ∧ s'.2 = s'.1.ring.proj) ∨
    (∃ net emit tid, pcRecheck net s.1 tid = true ∧ s'.1 = pcFire net emit s.1 tid ∧ s'.2 = s.2)
  store s := s.1.ring
  mat s := s.2

/-- ✗ An executor refreshed only at the end of a cycle violates CONC-025: from a start state
with `t` enabled, materialised as `5, 6`, the firing of `t` moves place `0`'s queue to `6, 7`,
and it still hands out `5, 6`. -/
@[evidence forbids CONC_025]
theorem CONC_025_forbids_cycleRefresh : ¬ CONC_025 refRingStore conc025_cycleRefresh := by
  intro h
  have := h (conc025_stE, conc025_stE.ring.proj) (conc025_stF, conc025_stE.ring.proj) rfl
    (Relation.ReflTransGen.single (Or.inr ⟨_, _, 0, conc025_recheck, rfl, rfl⟩)) 0 conc025_stF_ok
  revert this
  decide

/-! ### The line exercised -/

/-- The line is exercised by the reference: the start state materialises place `0` as `5, 6`;
one cycle consumes `5` and deposits `7`, which wraps the ring (its head moves to slot 1, `7` goes
to slot 0); the state it reaches still has place `0` in the store, and the reference
materialises it as `6, 7`, which neither a marking kept from the start (`5, 6`) nor a reading in
block order (`7, 6`) gives. -/
@[evidence nonvacuous CONC_025]
theorem CONC_025_nonvacuous :
    refMaterialiser.init conc025_st ∧
      refMaterialiser.step conc025_st conc025_st₁ ∧
      refRingStore.ok (refMaterialiser.store conc025_st₁) 0 ∧
      refMaterialiser.mat conc025_st 0 = [5, 6] ∧
      refMaterialiser.mat conc025_st₁ 0 = [6, 7] ∧
      conc025_blockOrder.mat conc025_st₁ 0 = [7, 6] ∧
      conc025_st₁.ring.head 0 = 1 :=
  ⟨conc025_pool_wf, ⟨_, _, Or.inl rfl⟩, conc025_st₁_ok, by decide, by decide, by decide,
    by decide⟩

end Libpetri.Spec
