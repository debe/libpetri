import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# CONC-022: Flat-array token storage (`spec/05-concurrency.md`)

CONC-022 is a pure-function requirement (kind F): it fixes that the precompiled executor's token
storage holds a queue for each place of its net, and what it does when a token is added to a
place, when the first token of a place is removed or read, and when the count of a place is
asked for. The statement is a predicate over a token store by place id,
`MarkingOps PlaceId Colour` (glossary `GlossaryQueue.lean`, the one store interface CORE-070
also uses), read through its `view`: the queue each place holds, oldest token first (glossary:
Queue order).

The witness is `refRingStore`, the flat ring pool `Libpetri.Pool` of `Ring/Core.lean` and
`Ring/Grow.lean`, the field-for-field model of the Rust precompiled backend's `ring_add_last`,
`ring_remove_first`, `ring_peek_first` and `grow_ring_static`. The existing ring lemmas
(`Pool.addLast_proj_self`, `Pool.removeFirst_proj_self`, `Pool.peekFirst_eq_head`,
`Pool.proj_length` and their frame and well-formedness companions) are the holds proof. The
queue marking itself (`refQOps`, a plain list per place, as the TypeScript precompiled executor
keeps it) satisfies the block too: the block states the queue behaviour of the storage, not the
ring.

Wrong stores are killed on small concrete pools and queue markings: a store that holds no place
or only one, a ring that never grows (it overwrites its oldest token when full), a growth that
copies the ring from the start of its block instead of from its head (a wrapped ring comes out
reordered), a growth in place that runs on into the next place's block, a LIFO removal, a peek
of the newest token, a peek that invents a token on an empty place, a count that reports
presence only, and one queue shared by every place. One wrong store the block cannot see is
recorded as allowed (`CONC_022_allows_noGrowCap1`): the store's own `ok` may leave out the
states it fails on.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## CONC-022: Flat-Array Token Storage -/

requirement CONC_022
  id "CONC-022"
  title "Flat-Array Token Storage"
  kind F
  scope "the precompiled executor's token storage"
  source verbatim "spec/05-concurrency.md"
  quote "The precompiled executor's token storage *shall* hold a dedicated queue for each place of the net it is built for."
        "*When* a token is added to a place the token storage holds a queue for, the token storage *shall* append it at the tail of the place's queue whatever the capacity of the place's storage, *shall* keep holding a queue for every place it held, and *shall* leave the queue of every other place unchanged."
        "*When* the first token of a marked place the token storage holds a queue for is removed, the token storage *shall* return the head of the place's queue, keep the rest of that queue in queue order, keep holding a queue for every place it held, and leave the queue of every other place unchanged."
        "*When* the first token of a place the token storage holds a queue for is read without removing it, the token storage *shall* return the head of the place's queue, or nothing when the place is not marked."
        "The token storage *shall* report as the token count of a place it holds a queue for the length of the place's queue."
  reading "For a token store S by place id:"
          "for every number n, some state of S holds a queue for each of the place ids below n;"
          "and for every state s of S and place p for which s is a well-formed store holding a queue for p (S.ok s p):"
          "adding a token x to p appends x at the tail of p's queue; every place q the store held a queue for still has one, and every such q other than p keeps its queue;"
          "if p is marked, removing the first token of p returns the head of p's queue and leaves p its queue without the head, in order; every place q the store held a queue for still has one, and every such q other than p keeps its queue;"
          "peeking p returns the head of p's queue, which is nothing when p's queue is empty;"
          "the count of p is the length of p's queue."
  assumes "The model is a token store by place id (glossary: MarkingOps, at place ids PlaceId and token values Colour). Its state type is σ; view s p is the queue place p holds in s, oldest token first (glossary: Queue order); ok s p says that s is a well-formed store that holds a queue for p. A store whose places are fixed when the net is compiled (the ring pool sized per place id) holds queues for those places only, so lines 2 to 5 are stated at the places the store holds, as the quoted sentences are ('a place the token storage holds a queue for')."
          "Line 1 is the first quoted sentence. The interface has no net, so 'each place of the net it is built for' is read on place ids: a compiled net of n places numbers them 0 to n - 1 (CONC-020; which name gets which id, and where tokens on a place outside the net go, are CONC-020's and CORE-072's subject), and line 1 asks for a state holding a queue for each of them, for every n. It rules out a store with no well-formed state (CONC_022_forbids_noPlace) and a store that holds a queue for one place only, which satisfies lines 2 to 5 with their frame halves empty (CONC_022_mutant_heldFree_killed). It does not say that the state is empty, nor that it is the state an executor starts from: the interface has no constructor for the store of a net, so neither can be stated (see the ok assumption below)."
          "The scope is the precompiled executor's token storage: the section stands under the heading 'Precompiled Flat-Array Executor', and the first quoted sentence names it; the later sentences say 'the token storage' for the same storage. The Bitmap reference executor's marking is CORE-070's subject, over the same interface."
          "Which states are ok is the implementation's choice, made by its refinement to its runtime, and the statement only constrains ok states. A store can therefore hide a fault by leaving out of ok every state it fails on, provided the states it keeps are closed under the operations: a ring pool whose growth (new capacity cap + cap / 2) leaves a ring of capacity 1 at capacity 1, with ok asking every ring to have capacity 2 or more, satisfies the block (CONC_022_allows_noGrowCap1) although it loses a token on the capacity-1 ring that the reference grows (conc022_noGrowCap1_wrong). The reference's ok (Pool.WF and a place id below nplaces) is the widest one: it holds every well-formed pool, capacity-1 rings included, and conc022_fullPool shows such a ring grow. The Rust runtime starts every ring at capacity 4 and doubles it (rust/libpetri-runtime/src/precompiled_backend.rs:34, 162, grow_ring_static at :1412). Closing the gap needs the store an executor starts from in the interface (a constructor of MarkingOps, a glossary change) or in the executor model (CONC-025's Materialiser, RefExec in W5); neither is in this block."
          "Token values are Colour (a natural number). No line inspects a value, so the choice of value type does not matter; it is fixed because the witness, the ring pool, stores Colour."
          "The two prose sentences of the section ('Token storage uses ring buffers indexed by place ID for O(1) access.' and 'Each place has a dedicated ring buffer that preserves FIFO ordering [CORE-013] and grows dynamically when capacity is exceeded.') are not quoted. Their behaviour is the five shall sentences: 'indexed by place ID' is the store being addressed by place id, 'each place has a dedicated' buffer is line 1 with the frame halves of lines 2 and 3, 'preserves FIFO ordering' is lines 3 and 4 (AC2), 'grows dynamically when capacity is exceeded' is line 2 whatever the capacity. 'Ring buffer', 'grows dynamically' as a mechanism, and 'O(1)' are data structure and cost (kind Q): any unbounded store meets line 2 without growing, and the TypeScript precompiled executor keeps a plain array per place (typescript/src/runtime/precompiled-net-executor.ts:179) and removes the head with Array.shift, while Rust and Java keep ring buffers. How that wording is migrated is ruling D20 (clash conc-b#5, recommendation CB-4), which is open; the block is written against the behaviour, which every runtime has, so neither outcome of D20 changes it. The section's Kind line is F, the kind of its one block, following the one-letter convention of the signed blocks (spec/04-execution-model.md:41, EXEC-002, Kind F with Q content); whether the Kind line changes for Q content is ruling D21, which is open."
          "Line 2 is the second quoted sentence. 'Whatever the capacity of the place's storage' is the growth of AC3: the store accepts the add at a full place too, and the token lands at the tail with every earlier token in order; the line does not test fullness, it holds at every capacity. 'Keep holding a queue for every place it held' is the S.ok conjunct, which keeps a bounded store from escaping the line by making ok false at a full place. A ring that never grows overwrites its oldest token (CONC_022_forbids_noGrow), and a growth that copies the ring from the start of its block instead of from its head reorders a wrapped ring (CONC_022_forbids_badGrow). The frame half ('leave the queue of every other place unchanged') is the section's 'dedicated' buffer: one queue shared by all places violates it (CONC_022_forbids_shared), and so does a growth in place whose new slots run on into the next place's block (CONC_022_forbids_inPlaceGrow)."
          "Lines 2 and 3 are stated at a place the store holds, frame half included: an add or a removal at a place id the store does not hold is not constrained, and may change any queue. The quoted sentences say the same ('a place the token storage holds a queue for'). The ring model needs this: its fields are total functions, and Pool.addLast at a place id at or above nplaces grows into a block that may overlap a held place's. No runtime makes that call: Rust routes a token on a place outside the net to extra_marking (rust/libpetri-runtime/src/precompiled_backend.rs:1331), and ring_add_last indexes place_offset by the place id, which panics out of range. Where such a token goes is CORE-072's subject."
          "Line 3 is the third quoted sentence, stated for a marked place (glossary: Marked) on the count of the view. Removing the first token of an unmarked place is not a call the precompiled executor makes (ring_remove_first unwraps the head slot, rust/libpetri-runtime/src/precompiled_backend.rs:396-403, and the ring pool's well-formedness does not survive a removal at count zero), so it is left out; what a marking does there is CORE-070's subject. A LIFO removal is the mutant CONC_022_mutant_lifo."
          "Line 3 is about the storage operation that removes the first token, not about which tokens a firing consumes. Which tokens a firing consumes is EXEC-010's subject (oldest first, except on a correlated ν input, ruling D16); a correlated ν input removes the first matching token through a different operation (ring_remove_matching, Libpetri.Pool.removeMatching in Ring.lean), which this interface does not have. Whether AC2's text gets D16's exclusion is ruling D30 (recommendation CB-3), which is open; line 3 makes no claim that either outcome would contradict."
          "Line 4 is the fourth quoted sentence: the token storage reads a place's first token (the read arc's peek, glossary Queue order 'reads the head') without changing the store; peek takes the state and returns only a token, so it changes nothing by its type. On an unmarked place the head of the queue is nothing (glossary Head), which is the sentence's 'or nothing when the place is not marked'. A peek of the newest token violates the line (CONC_022_forbids_peekNewest), and so does a peek that returns a default token on an empty place (CONC_022_forbids_peekDefault)."
          "Line 5 is the fifth quoted sentence, on the glossary's Token count of the view. A count that reports only whether the place is marked violates it (CONC_022_forbids_presenceCount)."
          "AC1 (token access is O(1) by place ID, no hashing or map lookup) is cost, kind Q, and is not encoded: the statement only fixes that the store is addressed by place id. AC1 is false of the TypeScript precompiled executor's removal (Array.shift on a plain array, typescript/src/runtime/precompiled-net-executor.ts:1098) and of tokens on places the compiled net does not know, which TypeScript keeps in a map keyed by name (unknownPlaceTokens, typescript/src/runtime/precompiled-net-executor.ts:181-188, CORE-072); the wording is D20's."
          "AC2 (FIFO ordering is preserved, oldest token consumed first) is lines 3 and 4, together with line 2's tail append: a token added later is removed and read later (CONC_022_nonvacuous). The ν exception is the line 3 assumption above."
          "AC3 (ring buffers grow dynamically when capacity is exceeded) is line 2 at a full place (CONC_022_nonvacuous: a full wrapped ring of capacity 2 takes a third token in order; CONC_022_nonvacuous_frame: a full ring grows next to another place's block and that place keeps its queue)."
          "AC4 (token count per place is available in O(1)) is line 5; the cost is kind Q, not encoded."
          "The test derivation (add and consume tokens in various orders, verify FIFO ordering and counts) is CONC_022_nonvacuous and CONC_022_nonvacuous_frame on the ring pool."
          "The section depends on CORE-013 (token FIFO ordering). Both blocks use the glossary term Queue order; CORE-013 states it over the queue firing relation, and CONC_022_refQOps shows that the queue marking the EXEC and CORE-013 blocks step (refQOps, view the identity) is itself a store this block accepts. The consistency theorem spec_consistent_queue puts CONC-022 and CORE-070 on one store, the ring pool with its removal guarded by the count (core070_ringMarking, CONC_022_ringMarking)."
  signoff "pending"
  statement : MarkingOps PlaceId Colour → Prop :=
    fun S =>
      (∀ n, ∃ s, ∀ p, p < n → S.ok s p) ∧
      (∀ s p x, S.ok s p →
        S.view (S.add s p x) p = S.view s p ++ [x] ∧
        ∀ q, S.ok s q → S.ok (S.add s p x) q ∧
          (q ≠ p → S.view (S.add s p x) q = S.view s q)) ∧
      (∀ s p, S.ok s p → Marked (Counts (S.view s)) p →
        (S.removeFirst s p).1 = Head (S.view s) p ∧
        S.view (S.removeFirst s p).2 p = (S.view s p).tail ∧
        ∀ q, S.ok s q → S.ok (S.removeFirst s p).2 q ∧
          (q ≠ p → S.view (S.removeFirst s p).2 q = S.view s q)) ∧
      (∀ s p, S.ok s p → S.peek s p = Head (S.view s) p) ∧
      (∀ s p, S.ok s p → S.count s p = Counts (S.view s) p)

/- The pinned readable form of CONC-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_022 : MarkingOps PlaceId Colour → Prop :=
fun S =>
  (∀ (n : PlaceId), ∃ s, ∀ p < n, S.ok s p) ∧
    (∀ (s : S.σ) (p : PlaceId) (x : Colour),
        S.ok s p →
          S.view (S.add s p x) p = S.view s p ++ [x] ∧
            ∀ (q : PlaceId), S.ok s q → S.ok (S.add s p x) q ∧ (q ≠ p → S.view (S.add s p x) q = S.view s q)) ∧
      (∀ (s : S.σ) (p : PlaceId),
          S.ok s p →
            Marked (Counts (S.view s)) p →
              (S.removeFirst s p).1 = Head (S.view s) p ∧
                S.view (S.removeFirst s p).2 p = (S.view s p).tail ∧
                  ∀ (q : PlaceId),
                    S.ok s q → S.ok (S.removeFirst s p).2 q ∧ (q ≠ p → S.view (S.removeFirst s p).2 q = S.view s q)) ∧
        (∀ (s : S.σ) (p : PlaceId), S.ok s p → S.peek s p = Head (S.view s) p) ∧
          ∀ (s : S.σ) (p : PlaceId), S.ok s p → S.count s p = Counts (S.view s) p
-/
#guard_msgs in #print CONC_022

/-! ### The reference: the flat ring pool -/

/-- `ring_add_last` keeps the number of places of the pool, through the grow path too. -/
theorem conc022_addLast_nplaces (s : Pool) (p : PlaceId) (c : Colour) :
    (s.addLast p c).nplaces = s.nplaces := by
  unfold Pool.addLast
  split <;> simp

/-- A pool sized for a net of `n` places: place `q` has an empty ring of capacity `c` at
`c * q`, as the precompiled backend lays the pool out when it compiles a net (one block of
`INITIAL_RING_CAPACITY` slots per place id, `precompiled_backend.rs:154-165`). -/
def conc022_blank (n c : Nat) : Pool where
  pool _ := none
  len := c * n
  offset q := c * q
  head _ := 0
  tail _ := 0
  cnt _ := 0
  cap _ := c
  nplaces := n

/-- `conc022_blank n c` is well formed when the capacity is positive. -/
theorem conc022_blank_wf (n : Nat) {c : Nat} (hc : 0 < c) : Pool.WF (conc022_blank n c) := by
  constructor
  · intro _ _; exact hc
  · intro _ _; exact Nat.zero_le _
  · intro _ _; exact hc
  · intro _ _; simp [conc022_blank, ringPos]
  · intro q hq
    show c * q + c ≤ c * n
    have := Nat.mul_le_mul_left c (show q + 1 ≤ n from hq)
    rwa [Nat.mul_succ] at this
  · intro _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
  · intro _ _ _ _ _; rfl
  · intro p q _ _ hne
    show c * p + c ≤ c * q ∨ c * q + c ≤ c * p
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left
      have := Nat.mul_le_mul_left c (show p + 1 ≤ q from h)
      rwa [Nat.mul_succ] at this
    · right
      have := Nat.mul_le_mul_left c (show q + 1 ≤ p from h)
      rwa [Nat.mul_succ] at this

/-- The flat ring pool satisfies CONC-022: a pool sized for `n` places holds a queue for each
(`conc022_blank`); `Pool.addLast` appends at the tail of the projection through the grow path
too (`Pool.addLast_proj_self`), keeps the pool well formed (`Pool.addLast_wf`) and every other
place's projection (`Pool.addLast_proj_other`); `Pool.removeFirst` on a marked place drops the
head (`Pool.removeFirst_proj_self`), returning `peekFirst`, the head (`Pool.peekFirst_eq_head`),
keeps the pool well formed (`Pool.removeFirst_wf`) and every other place
(`Pool.removeFirst_proj_other`); the stored count is the length of the projection
(`Pool.proj_length`). -/
@[evidence holds CONC_022]
theorem CONC_022_reference : CONC_022 refRingStore := by
  refine ⟨fun n => ⟨conc022_blank n 1, fun _ hp => ⟨conc022_blank_wf n Nat.one_pos, hp⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro s p x ⟨hwf, hp⟩
    refine ⟨Pool.addLast_proj_self hwf hp x, fun q ⟨_, hq⟩ =>
      ⟨⟨Pool.addLast_wf hwf hp x, ?_⟩, fun hne => Pool.addLast_proj_other hwf hp hq hne x⟩⟩
    show q < (s.addLast p x).nplaces
    rw [conc022_addLast_nplaces]
    exact hq
  · rintro s p ⟨hwf, hp⟩ hm
    have hc : 0 < s.cnt p := by
      have : (s.proj p).length ≠ 0 := hm
      rw [Pool.proj_length hwf hp] at this
      omega
    refine ⟨Pool.peekFirst_eq_head hwf hp, Pool.removeFirst_proj_self hwf hp hc,
      fun q ⟨_, hq⟩ => ⟨⟨Pool.removeFirst_wf hwf hp hc, ?_⟩,
        fun hne => Pool.removeFirst_proj_other hwf hp hq hne⟩⟩
    show q < (s.removeFirst p).nplaces
    rw [Pool.removeFirst_nplaces]
    exact hq
  · rintro s p ⟨hwf, hp⟩
    exact Pool.peekFirst_eq_head hwf hp
  · rintro s p ⟨hwf, hp⟩
    exact (Pool.proj_length hwf hp).symm

/-- The queue marking as a store (`refQOps`, a plain list per place, view the identity) also
satisfies CONC-022: it holds a queue for every place, `qAppendOne` appends at the tail of the
place and leaves the others, `removeFirst` returns the head and leaves the tail
(`removeFirst_fst`, `removeFirst_self`, `removeFirst_other`), `peek` is `Head` and `count` is
`Counts`. The block states the queue behaviour of the storage, not the ring. -/
@[evidence holds CONC_022]
theorem CONC_022_refQOps : CONC_022 (refQOps (N := PlaceId) (T := Colour)) := by
  refine ⟨fun _ => ⟨qEmpty, fun _ _ => trivial⟩,
    fun M p x _ => ⟨?_, fun q _ => ⟨trivial, fun hne => ?_⟩⟩,
    fun M p _ _ => ⟨removeFirst_fst M p, removeFirst_self M p,
      fun q _ => ⟨trivial, fun hne => removeFirst_other M hne⟩⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · show qAppendOne M p x p = M p ++ [x]
    simp [qAppendOne]
  · show qAppendOne M p x q = M q
    simp [qAppendOne, hne]

/-! ### Example pools -/

/-- A one-place pool whose ring of capacity 1 is full and holds the token `9`. -/
def conc022_fullPool : Pool :=
  { pool := fun idx => if idx = 0 then some 9 else none
    len := 1, offset := fun _ => 0, head := fun _ => 0, tail := fun _ => 0
    cnt := fun _ => 1, cap := fun _ => 1, nplaces := 1 }

/-- `conc022_fullPool` is well formed. -/
theorem conc022_fullPool_wf : Pool.WF conc022_fullPool := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro p
  · intro _; simp [conc022_fullPool]
  · intro _; simp [conc022_fullPool]
  · intro _; simp [conc022_fullPool]
  · intro _; simp [conc022_fullPool, ringPos]
  · intro _; simp [conc022_fullPool]
  · intro _ i hi
    have : i = 0 := by simp [conc022_fullPool] at hi; omega
    subst this
    simp [conc022_fullPool, Pool.slot, ringPos]
  · intro _ i h1 h2
    simp [conc022_fullPool] at h1 h2
    omega
  · intro q hp hq hne
    simp [conc022_fullPool] at hp hq
    omega

/-- A one-place pool whose ring of capacity 2 is full and wrapped: the head is slot `1`, which
holds the oldest token `1`, and slot `0` holds the newer token `2`. Its queue is `1, 2`. -/
def conc022_wrapPool : Pool :=
  { pool := fun idx => if idx = 0 then some 2 else if idx = 1 then some 1 else none
    len := 2, offset := fun _ => 0, head := fun _ => 1, tail := fun _ => 1
    cnt := fun _ => 2, cap := fun _ => 2, nplaces := 1 }

/-- `conc022_wrapPool` is well formed. -/
theorem conc022_wrapPool_wf : Pool.WF conc022_wrapPool := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro p
  · intro _; simp [conc022_wrapPool]
  · intro _; simp [conc022_wrapPool]
  · intro _; simp [conc022_wrapPool]
  · intro _; simp [conc022_wrapPool, ringPos]
  · intro _; simp [conc022_wrapPool]
  · intro _ i hi
    have : i = 0 ∨ i = 1 := by simp [conc022_wrapPool] at hi; omega
    rcases this with rfl | rfl <;> simp [conc022_wrapPool, Pool.slot, ringPos]
  · intro _ i h1 h2
    simp [conc022_wrapPool] at h1 h2
    omega
  · intro q hp hq hne
    simp [conc022_wrapPool] at hp hq
    omega

/-- A two-place pool, both rings full. Place `1` has a ring of capacity 1 at slot `0` holding
`4`. Place `0` has a wrapped ring of capacity 2 in slots `1` and `2`, right after place `1`'s
block: its head is slot `2`, holding the oldest token `1`, and slot `1` holds the newer token
`2`. Its queue is `1, 2`. -/
def conc022_pairPool : Pool :=
  { pool := fun idx => if idx = 0 then some 4 else if idx = 1 then some 2
      else if idx = 2 then some 1 else none
    len := 3
    offset := fun q => if q = 0 then 1 else 0
    head := fun q => if q = 0 then 1 else 0
    tail := fun q => if q = 0 then 1 else 0
    cnt := fun q => if q = 0 then 2 else 1
    cap := fun q => if q = 0 then 2 else 1
    nplaces := 2 }

/-- `conc022_pairPool` is well formed. -/
theorem conc022_pairPool_wf : Pool.WF conc022_pairPool := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool]
  · intro p hp
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool]
  · intro p hp
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool]
  · intro p hp
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool, ringPos]
  · intro p hp
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool]
  · intro p hp i hi
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl
    · have : i = 0 ∨ i = 1 := by simp [conc022_pairPool] at hi; omega
      rcases this with rfl | rfl <;> simp [conc022_pairPool, Pool.slot, ringPos]
    · have : i = 0 := by simp [conc022_pairPool] at hi; omega
      subst this
      simp [conc022_pairPool, Pool.slot, ringPos]
  · intro p hp i h1 h2
    have : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    rcases this with rfl | rfl <;> simp [conc022_pairPool] at h1 h2 <;> omega
  · intro p q hp hq hne
    have hp' : p = 0 ∨ p = 1 := by simp [conc022_pairPool] at hp; omega
    have hq' : q = 0 ∨ q = 1 := by simp [conc022_pairPool] at hq; omega
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;>
      simp [conc022_pairPool] at hne ⊢

/-- The ring store holds a queue for place `0` of `conc022_wrapPool`. -/
theorem conc022_wrapPool_ok : refRingStore.ok conc022_wrapPool 0 :=
  ⟨conc022_wrapPool_wf, by decide⟩

/-- The ring store holds a queue for place `0` of `conc022_fullPool`. -/
theorem conc022_fullPool_ok : refRingStore.ok conc022_fullPool 0 :=
  ⟨conc022_fullPool_wf, by decide⟩

/-- The ring store holds a queue for place `0` of `conc022_pairPool`. -/
theorem conc022_pairPool_ok0 : refRingStore.ok conc022_pairPool 0 :=
  ⟨conc022_pairPool_wf, by decide⟩

/-- The ring store holds a queue for place `1` of `conc022_pairPool`. -/
theorem conc022_pairPool_ok1 : refRingStore.ok conc022_pairPool 1 :=
  ⟨conc022_pairPool_wf, by decide⟩

/-! ### Violation: a store that holds no place -/

/-- The queue marking store with no well-formed state. -/
def conc022_noPlace : MarkingOps PlaceId Colour :=
  { refQOps (N := PlaceId) (T := Colour) with ok := fun _ _ => False }

/-- ✗ A store with no well-formed state violates CONC-022 (line 1): no state holds a queue for
place `0`. Lines 2 to 5 hold of it, vacuously. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_noPlace : ¬ CONC_022 conc022_noPlace := by
  intro h
  obtain ⟨_, hs⟩ := h.1 1
  exact hs 0 (by decide)

/-! ### Mutant: a store that holds one place -/

/-- One queue, held for place `0` only: the shared queue of `conc022_shared` below, with `ok`
narrowed to the one place. -/
def conc022_sharedOne : MarkingOps PlaceId Colour where
  σ := List Colour
  ok _ p := p = 0
  view s _ := s
  empty := []
  add s _ x := s ++ [x]
  removeFirst s _ := (s.head?, s.tail)
  peek s _ := s.head?
  count s _ := s.length

/-- Mutant reading of CONC-022 without line 1: only the operation lines, at the places the store
chooses to hold. -/
def CONC_022_mutant_heldFree (S : MarkingOps PlaceId Colour) : Prop :=
  (∀ s p x, S.ok s p →
    S.view (S.add s p x) p = S.view s p ++ [x] ∧
    ∀ q, S.ok s q → S.ok (S.add s p x) q ∧
      (q ≠ p → S.view (S.add s p x) q = S.view s q)) ∧
  (∀ s p, S.ok s p → Marked (Counts (S.view s)) p →
    (S.removeFirst s p).1 = Head (S.view s) p ∧
    S.view (S.removeFirst s p).2 p = (S.view s p).tail ∧
    ∀ q, S.ok s q → S.ok (S.removeFirst s p).2 q ∧
      (q ≠ p → S.view (S.removeFirst s p).2 q = S.view s q)) ∧
  (∀ s p, S.ok s p → S.peek s p = Head (S.view s) p) ∧
  (∀ s p, S.ok s p → S.count s p = Counts (S.view s) p)

/-- The one-place store kills the mutant: it satisfies the operation lines, whose frame halves
are empty because it holds no second place, but no state holds a queue for places `0` and `1`
together, as a net of two places needs (line 1). -/
@[evidence mutant CONC_022]
theorem CONC_022_mutant_heldFree_killed :
    CONC_022_mutant_heldFree conc022_sharedOne ∧ ¬ CONC_022 conc022_sharedOne := by
  refine ⟨⟨fun s p x hp => ⟨rfl, fun q hq => ⟨hq, fun hne => ?_⟩⟩,
      fun s p hp _ => ⟨rfl, rfl, fun q hq => ⟨hq, fun hne => ?_⟩⟩,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun h => ?_⟩
  · exact absurd ((hq : q = 0).trans (hp : p = 0).symm) hne
  · exact absurd ((hq : q = 0).trans (hp : p = 0).symm) hne
  · obtain ⟨_, hs⟩ := h.1 2
    have h1 : (1 : Nat) = 0 := hs 1 (by decide)
    exact absurd h1 (by decide)

/-! ### Violation: a ring that never grows -/

/-- The ring pool with the grow branch of `ring_add_last` removed: `add` is `Pool.pushLast`
alone, which on a full ring writes the tail slot, the slot of the oldest token. -/
def conc022_noGrow : MarkingOps PlaceId Colour where
  σ := Pool
  ok s p := Pool.WF s ∧ p < s.nplaces
  view := Pool.proj
  empty := emptyPool
  add := Pool.pushLast
  removeFirst s p := (s.peekFirst p, s.removeFirst p)
  peek := Pool.peekFirst
  count := Pool.cnt

/-- ✗ A ring that never grows violates CONC-022 (line 2, AC3): adding `7` to the full ring of
capacity 1 that holds `9` overwrites `9`, so the queue reads `7, 7` instead of `9, 7`. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_noGrow : ¬ CONC_022 conc022_noGrow := by
  intro h
  have := (h.2.1 conc022_fullPool 0 7 conc022_fullPool_ok).1
  revert this
  decide

/-! ### Violation: a growth that copies from the start of the block -/

/-- `grow_ring_static` with the copy loop reading `old_offset + i` instead of
`old_offset + (old_head + i) % old_cap`: the live tokens are copied in slot order, not in queue
order. -/
def conc022_badGrowRing (s : Pool) (p : PlaceId) : Pool :=
  { s.growRing p with
    pool := fun idx =>
      if s.len ≤ idx ∧ idx < s.len + s.cnt p then s.pool (s.offset p + (idx - s.len))
      else (s.growRing p).pool idx }

/-- The ring pool whose growth copies from the start of the block. -/
def conc022_badGrow : MarkingOps PlaceId Colour where
  σ := Pool
  ok s p := Pool.WF s ∧ p < s.nplaces
  view := Pool.proj
  empty := emptyPool
  add s p c := if s.cnt p = s.cap p then (conc022_badGrowRing s p).pushLast p c
    else s.pushLast p c
  removeFirst s p := (s.peekFirst p, s.removeFirst p)
  peek := Pool.peekFirst
  count := Pool.cnt

/-- ✗ A growth that copies from the start of the block violates CONC-022 (line 2, AC3): adding
`3` to the full wrapped ring that holds `1, 2` gives the queue `2, 1, 3` instead of `1, 2, 3`. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_badGrow : ¬ CONC_022 conc022_badGrow := by
  intro h
  have := (h.2.1 conc022_wrapPool 0 3 conc022_wrapPool_ok).1
  revert this
  decide

/-! ### Violation: a growth in place -/

/-- `grow_ring_static` without the relocation: the ring of the place doubles its capacity where
it is and keeps its head, so its new slots run on into the next place's block. -/
def conc022_inPlaceGrowRing (s : Pool) (p : PlaceId) : Pool :=
  { s with
    cap := fun q => if q = p then 2 * s.cap p else s.cap q
    tail := fun q => if q = p then ringPos (s.head p) (s.cnt p) (2 * s.cap p) else s.tail q }

/-- The ring pool whose growth doubles a ring in place. -/
def conc022_inPlaceGrow : MarkingOps PlaceId Colour where
  σ := Pool
  ok s p := Pool.WF s ∧ p < s.nplaces
  view := Pool.proj
  empty := emptyPool
  add s p c := if s.cnt p = s.cap p then (conc022_inPlaceGrowRing s p).pushLast p c
    else s.pushLast p c
  removeFirst s p := (s.peekFirst p, s.removeFirst p)
  peek := Pool.peekFirst
  count := Pool.cnt

/-- ✗ A growth in place violates CONC-022 (line 2, the frame half, the 'dedicated' buffer):
adding `7` to place `1` of `conc022_pairPool`, whose ring of capacity 1 is full, writes `7` into
slot `1`, which belongs to place `0`, so place `0`'s queue reads `1, 7` instead of `1, 2`. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_inPlaceGrow : ¬ CONC_022 conc022_inPlaceGrow := by
  intro h
  have := ((h.2.1 conc022_pairPool 1 7 conc022_pairPool_ok1).2 0 conc022_pairPool_ok0).2
    (by decide)
  revert this
  decide

/-! ### Violation: one queue for every place -/

/-- A store with one queue shared by every place: no place has a dedicated buffer. -/
def conc022_shared : MarkingOps PlaceId Colour where
  σ := List Colour
  ok _ _ := True
  view s _ := s
  empty := []
  add s _ x := s ++ [x]
  removeFirst s _ := (s.head?, s.tail)
  peek s _ := s.head?
  count s _ := s.length

/-- ✗ One shared queue violates CONC-022 (line 2, the frame half): adding `5` to place `0`
changes the queue of place `1`. Removal, peek and count at the place itself are as lines 3 to 5
ask. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_shared : ¬ CONC_022 conc022_shared := by
  intro h
  have := ((h.2.1 [] 0 5 trivial).2 1 trivial).2 (by decide)
  revert this
  decide

/-! ### Violation: a peek of the newest token -/

/-- The queue marking store whose peek returns the newest token of the place. -/
def conc022_peekNewest : MarkingOps PlaceId Colour :=
  { refQOps (N := PlaceId) (T := Colour) with peek := fun M p => (M p).getLast? }

/-- The queue marking of the examples: place `0` holds `1, 2`, every other place is empty. -/
def conc022_M : QueueMarking PlaceId Colour := fun p => if p = 0 then [1, 2] else []

/-- ✗ A peek of the newest token violates CONC-022 (line 4): place `0` holding `1, 2` peeks `2`,
not its head `1`. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_peekNewest : ¬ CONC_022 conc022_peekNewest := by
  intro h
  have := h.2.2.2.1 conc022_M 0 trivial
  revert this
  decide

/-! ### Violation: a peek that invents a token on an empty place -/

/-- The queue marking store whose peek returns the token `0` when the place is empty. -/
def conc022_peekDefault : MarkingOps PlaceId Colour :=
  { refQOps (N := PlaceId) (T := Colour) with peek := fun M p => some ((M p).headD 0) }

/-- ✗ A peek that returns a default token on an empty place violates CONC-022 (line 4, 'or
nothing when the place is not marked'): place `1` of `conc022_M` is empty and peeks `0`. On a
marked place it peeks the head, as line 4 asks. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_peekDefault : ¬ CONC_022 conc022_peekDefault := by
  intro h
  have := h.2.2.2.1 conc022_M 1 trivial
  revert this
  decide

/-! ### Violation: a count that reports presence -/

/-- The queue marking store whose count reports only whether the place is marked. -/
def conc022_presenceCount : MarkingOps PlaceId Colour :=
  { refQOps (N := PlaceId) (T := Colour) with count := fun M p => min 1 (M p).length }

/-- ✗ A count that reports presence only violates CONC-022 (line 5, AC4): place `0` holding
`1, 2` counts `1`, not `2`. -/
@[evidence forbids CONC_022]
theorem CONC_022_forbids_presenceCount : ¬ CONC_022 conc022_presenceCount := by
  intro h
  have := h.2.2.2.2 conc022_M 0 trivial
  revert this
  decide

/-! ### Mutant: LIFO removal -/

/-- The queue marking store whose removal takes the newest token of the place (a stack). -/
def conc022_lifo : MarkingOps PlaceId Colour :=
  { refQOps (N := PlaceId) (T := Colour) with
    removeFirst := fun M p => ((M p).getLast?, fun q => if q = p then (M q).dropLast else M q) }

/-- Mutant reading of CONC-022 in which removal is LIFO: line 3 returns the newest token of a
marked place and leaves it its queue without that token. The other lines are as in CONC-022. -/
def CONC_022_mutant_lifo (S : MarkingOps PlaceId Colour) : Prop :=
  (∀ n, ∃ s, ∀ p, p < n → S.ok s p) ∧
  (∀ s p x, S.ok s p →
    S.view (S.add s p x) p = S.view s p ++ [x] ∧
    ∀ q, S.ok s q → S.ok (S.add s p x) q ∧
      (q ≠ p → S.view (S.add s p x) q = S.view s q)) ∧
  (∀ s p, S.ok s p → Marked (Counts (S.view s)) p →
    (S.removeFirst s p).1 = (S.view s p).getLast? ∧
    S.view (S.removeFirst s p).2 p = (S.view s p).dropLast ∧
    ∀ q, S.ok s q → S.ok (S.removeFirst s p).2 q ∧
      (q ≠ p → S.view (S.removeFirst s p).2 q = S.view s q)) ∧
  (∀ s p, S.ok s p → S.peek s p = Head (S.view s) p) ∧
  (∀ s p, S.ok s p → S.count s p = Counts (S.view s) p)

/-- The LIFO store kills the mutant: it satisfies the mutant reading, but not CONC-022. Removing
the first token of place `0` holding `1, 2` returns `2`, not the head `1` (AC2). -/
@[evidence mutant CONC_022]
theorem CONC_022_mutant_lifo_killed :
    CONC_022_mutant_lifo conc022_lifo ∧ ¬ CONC_022 conc022_lifo := by
  refine ⟨⟨fun _ => ⟨qEmpty, fun _ _ => trivial⟩,
      fun M p x _ => ⟨?_, fun q _ => ⟨trivial, fun hne => ?_⟩⟩,
      fun M p _ _ => ⟨rfl, ?_, fun q _ => ⟨trivial, fun hne => ?_⟩⟩,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun h => ?_⟩
  · show qAppendOne M p x p = M p ++ [x]
    simp [qAppendOne]
  · show qAppendOne M p x q = M q
    simp [qAppendOne, hne]
  · show (if p = p then (M p).dropLast else M p) = (M p).dropLast
    simp
  · show (if q = p then (M q).dropLast else M q) = M q
    simp [hne]
  · have := (h.2.2.1 conc022_M 0 trivial (by decide)).1
    revert this
    decide

/-! ### Allowed: a fault hidden by the store's own `ok` -/

/-- A ring pool whose growth policy is `new_cap = cap + cap / 2`, which leaves a ring of
capacity 1 at capacity 1: on a full capacity-1 ring `add` writes the oldest token's slot, as
`conc022_noGrow` does. Its `ok` asks every ring of the pool to have capacity 2 or more, a set of
states closed under add (growth only raises capacity) and removal (capacity does not change). -/
def conc022_noGrowCap1 : MarkingOps PlaceId Colour where
  σ := Pool
  ok s p := Pool.WF s ∧ p < s.nplaces ∧ ∀ q, q < s.nplaces → 2 ≤ s.cap q
  view := Pool.proj
  empty := emptyPool
  add s p c := if s.cap p = 1 then s.pushLast p c else s.addLast p c
  removeFirst s p := (s.peekFirst p, s.removeFirst p)
  peek := Pool.peekFirst
  count := Pool.cnt

/-- `ring_add_last` never lowers a capacity. -/
theorem conc022_addLast_cap_ge (s : Pool) (p q : PlaceId) (c : Colour) :
    s.cap q ≤ (s.addLast p c).cap q := by
  unfold Pool.addLast
  split
  · rw [Pool.pushLast_cap]
    by_cases h : q = p
    · subst h; rw [Pool.growRing_cap_self]; omega
    · rw [Pool.growRing_cap_other s h]
  · rw [Pool.pushLast_cap]

/-- ✓ Known limit of the block, recorded: CONC-022 allows `conc022_noGrowCap1`, although the
spec text forbids it (see `conc022_noGrowCap1_wrong`). Every line after the first is guarded by
the store's own `ok`, and this store's `ok` leaves out the capacity-1 rings it fails on; line 1
is met by pools whose rings all have capacity 2. The interface has no constructor for the store
of a net, so the block cannot ask that the states an executor starts from are `ok` (assumption
'Which states are ok'). -/
@[evidence allows CONC_022]
theorem CONC_022_allows_noGrowCap1 : CONC_022 conc022_noGrowCap1 := by
  refine ⟨fun n => ⟨conc022_blank n 2, fun _ hp =>
      ⟨conc022_blank_wf n (by decide), hp, fun _ _ => Nat.le_refl 2⟩⟩, ?_, ?_, ?_, ?_⟩
  · rintro s p x ⟨hwf, hp, h2⟩
    have hne1 : s.cap p ≠ 1 := by have := h2 p hp; omega
    have hadd : (if s.cap p = 1 then s.pushLast p x else s.addLast p x) = s.addLast p x :=
      if_neg hne1
    refine ⟨?_, fun q hq' => ⟨?_, fun hne => ?_⟩⟩
    · show (if s.cap p = 1 then s.pushLast p x else s.addLast p x).proj p = s.proj p ++ [x]
      rw [hadd]; exact Pool.addLast_proj_self hwf hp x
    · obtain ⟨_, hq, _⟩ := hq'
      show Pool.WF (if s.cap p = 1 then s.pushLast p x else s.addLast p x) ∧
        q < (if s.cap p = 1 then s.pushLast p x else s.addLast p x).nplaces ∧
        ∀ r, r < (if s.cap p = 1 then s.pushLast p x else s.addLast p x).nplaces →
          2 ≤ (if s.cap p = 1 then s.pushLast p x else s.addLast p x).cap r
      rw [hadd, conc022_addLast_nplaces]
      exact ⟨Pool.addLast_wf hwf hp x, hq,
        fun r hr => Nat.le_trans (h2 r hr) (conc022_addLast_cap_ge s p r x)⟩
    · obtain ⟨_, hq, _⟩ := hq'
      show (if s.cap p = 1 then s.pushLast p x else s.addLast p x).proj q = s.proj q
      rw [hadd]; exact Pool.addLast_proj_other hwf hp hq hne x
  · rintro s p ⟨hwf, hp, h2⟩ hm
    have hc : 0 < s.cnt p := by
      have : (s.proj p).length ≠ 0 := hm
      rw [Pool.proj_length hwf hp] at this
      omega
    refine ⟨Pool.peekFirst_eq_head hwf hp, Pool.removeFirst_proj_self hwf hp hc,
      fun q ⟨_, hq, _⟩ => ⟨?_, fun hne => Pool.removeFirst_proj_other hwf hp hq hne⟩⟩
    show Pool.WF (s.removeFirst p) ∧ q < (s.removeFirst p).nplaces ∧
      ∀ r, r < (s.removeFirst p).nplaces → 2 ≤ (s.removeFirst p).cap r
    rw [Pool.removeFirst_nplaces, Pool.removeFirst_cap]
    exact ⟨Pool.removeFirst_wf hwf hp hc, hq, h2⟩
  · rintro s p ⟨hwf, hp, _⟩
    exact Pool.peekFirst_eq_head hwf hp
  · rintro s p ⟨hwf, hp, _⟩
    exact (Pool.proj_length hwf hp).symm

/-- What the spec forbids and the block cannot see: on the well-formed capacity-1 ring holding
`9` (`conc022_fullPool`, which the reference grows), `conc022_noGrowCap1` adding `7` loses `9`,
and that state is not `ok` for the store. -/
theorem conc022_noGrowCap1_wrong :
    conc022_noGrowCap1.view (conc022_noGrowCap1.add conc022_fullPool 0 7) 0 ≠ [9, 7] ∧
      ¬ conc022_noGrowCap1.ok conc022_fullPool 0 ∧
      refRingStore.view (refRingStore.add conc022_fullPool 0 7) 0 = [9, 7] := by
  refine ⟨by decide, fun ⟨_, _, h⟩ => ?_, by decide⟩
  have := h 0 (by decide)
  simp [conc022_fullPool] at this

/-! ### Every line exercised -/

/-- Every operation line of CONC-022 is exercised by the ring pool on the full wrapped ring
`conc022_wrapPool` (capacity 2, head at slot 1, queue `1, 2`), which the store holds a queue
for: adding `3` finds the ring full, grows it, and the queue reads `1, 2, 3` (line 2, AC3);
removing the first token returns the head `1` and leaves `2` (line 3, AC2); peeking returns `1`
without removing it (line 4); the count is `2` (line 5, AC4). The test derivation's FIFO check:
the token added last is behind both earlier ones. Line 1 holds of the ring pool for every `n`
(`conc022_blank`); here the pool sized for three places holds each of them. -/
@[evidence nonvacuous CONC_022]
theorem CONC_022_nonvacuous :
    (∀ p, p < 3 → refRingStore.ok (conc022_blank 3 4) p) ∧
      refRingStore.ok conc022_wrapPool 0 ∧
      conc022_wrapPool.cnt 0 = conc022_wrapPool.cap 0 ∧
      refRingStore.view conc022_wrapPool 0 = [1, 2] ∧
      refRingStore.view (refRingStore.add conc022_wrapPool 0 3) 0 = [1, 2, 3] ∧
      refRingStore.ok (refRingStore.add conc022_wrapPool 0 3) 0 ∧
      Marked (Counts (refRingStore.view conc022_wrapPool)) 0 ∧
      (refRingStore.removeFirst conc022_wrapPool 0).1 = some 1 ∧
      refRingStore.view (refRingStore.removeFirst conc022_wrapPool 0).2 0 = [2] ∧
      refRingStore.peek conc022_wrapPool 0 = some 1 ∧
      refRingStore.count conc022_wrapPool 0 = 2 :=
  ⟨fun _ hp => ⟨conc022_blank_wf 3 (by decide), hp⟩,
    conc022_wrapPool_ok, rfl, by decide, by decide,
    (CONC_022_reference.2.1 conc022_wrapPool 0 3 conc022_wrapPool_ok).2 0 conc022_wrapPool_ok |>.1,
    by decide, by decide, by decide, by decide, rfl⟩

/-- The frame halves of lines 2 and 3 are exercised by the ring pool on `conc022_pairPool`,
two full rings in adjacent blocks: growing place `1`'s ring (adding `5`) relocates it and
leaves place `0`'s wrapped ring `1, 2` as it was; growing place `0`'s ring (adding `3`) gives
`1, 2, 3` and leaves place `1`'s `4`; removing place `0`'s first token leaves place `1`'s `4`.
Each place has its own buffer, and growth does not touch the neighbour's (the section's
'dedicated' ring buffer). -/
@[evidence nonvacuous CONC_022]
theorem CONC_022_nonvacuous_frame :
    refRingStore.ok conc022_pairPool 0 ∧ refRingStore.ok conc022_pairPool 1 ∧
      refRingStore.view conc022_pairPool 0 = [1, 2] ∧
      refRingStore.view conc022_pairPool 1 = [4] ∧
      conc022_pairPool.cnt 1 = conc022_pairPool.cap 1 ∧
      conc022_pairPool.cnt 0 = conc022_pairPool.cap 0 ∧
      refRingStore.view (refRingStore.add conc022_pairPool 1 5) 1 = [4, 5] ∧
      refRingStore.view (refRingStore.add conc022_pairPool 1 5) 0 = [1, 2] ∧
      refRingStore.view (refRingStore.add conc022_pairPool 0 3) 0 = [1, 2, 3] ∧
      refRingStore.view (refRingStore.add conc022_pairPool 0 3) 1 = [4] ∧
      refRingStore.view (refRingStore.removeFirst conc022_pairPool 0).2 1 = [4] :=
  ⟨conc022_pairPool_ok0, conc022_pairPool_ok1, by decide, by decide, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide⟩

end Libpetri.Spec
