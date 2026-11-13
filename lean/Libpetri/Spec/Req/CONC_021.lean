import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.CONC_022
import Libpetri.Spec.Req.CORE_070
import Libpetri.Refinement
import Libpetri.RetrodictExec

set_option linter.missingDocs true

/-!
# CONC-021: Opcode-based consume operations (`spec/05-concurrency.md`)

CONC-021 is a pure-function requirement (kind F): it fixes what the precompiled executor's
consume operations do to its token storage and hand the action when a transition without a
match specification fires. The statement is a predicate over a token store `S`, CONC-022's
store interface `MarkingOps PlaceId Colour` (glossary `GlossaryQueue.lean`), and an abstract
consume program `X : ConsumeProgram S`: from a store state and a compiled transition, the store
after the consume phase, the tokens handed to the action as inputs and the read tokens. Its
three lines compare the program with the reference arc semantics on the store's queue view: the
Bitmap reference executor's consume (`bbInputsBag`, `bbReadsBag` after `bbPostInput`,
`bbConsumeMarking`, `Refinement/Model.lean`), which is AC4's "the same observable behavior as
the corresponding arc types" and the test derivation's "matches bitmap executor".

The witness is `refConsume`, the opcode interpreter `consumeForFiring` of `Conservation.lean`
over the ring pool `refRingStore` (the field-for-field model of the Rust precompiled backend's
`consume_for_firing` fast path: the input opcodes of `compile_consume_ops`, the read peek at the
`reset_ops_start` boundary, then the RESET tail). The holds proof is the refinement lemmas
`inputs_bag_rel`, `reads_bag_rel` and `consume_marking_rel` at the store's own view.

Wrong programs are killed on one concrete pool that exercises all five opcodes: `CONSUME_ATLEAST`
taking only its minimum, the RESET tail run before the input opcodes, a RESET tail that hands
the drained tokens to the action, `CONSUME_N` taking the newest tokens, the read peek after the
RESET tail (the pre-fix order of `RetrodictExec.lean`), a read compiled as a consuming opcode, a
program without the RESET tail, a program that hands the right tokens but shrinks the ring from
its tail, and one that forgets the places of the store. Two more are killed on their own small
examples: the read peek before the input opcodes, and a store that gains places it did not hold.
-/

namespace Libpetri.Spec

open Libpetri

/-! ## The consume program -/

/-- What one firing's consume phase produces over a store with state type `σ`: the store after
it, the tokens handed to the action as inputs, and the read tokens, both by place id, oldest
first. -/
structure ConsumeOut (σ : Type) where
  /-- The store after the consume phase. -/
  store : σ
  /-- The tokens handed to the action from its input places. -/
  inputs : TokenBag
  /-- The tokens handed to the action as read tokens. -/
  reads : TokenBag

/-- A consume program over the token store `S` ([CONC-022]): from a store state and a compiled
transition, what the consume phase of one firing of the transition produces. -/
abbrev ConsumeProgram (S : MarkingOps PlaceId Colour) := S.σ → Transition → ConsumeOut S.σ

/-- The reference: the opcode interpreter `consumeForFiring` over the ring pool. The input
opcodes of `compileConsumeOps` run first, the reads peek the pool they leave, and the RESET tail
drains last (`Conservation.lean`, `precompiled_backend.rs` `consume_for_firing`). -/
def refConsume : ConsumeProgram refRingStore := fun s t =>
  ⟨(consumeForFiring s t).1.pool, (consumeForFiring s t).1.inputs, (consumeForFiring s t).2⟩

#spec_witness refConsume

/-! ## CONC-021: Opcode-based consume operations -/

requirement CONC_021
  id "CONC-021"
  title "Opcode-Based Consume Operations"
  kind F
  scope "the precompiled executor, transitions without a match specification"
  source verbatim "spec/05-concurrency.md"
  quote "*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action from each input place the oldest tokens the place holds, as many as the consumption count of the input arc ([IO-007]) for the number of tokens the firing may drain ([EXEC-003] AC5), in queue order, and nothing from any other place."
        "*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* hand the action for each read arc the head of the read place's queue as it is after the input operations and before the reset operations."
        "*When* the precompiled executor fires a transition that has no match specification ([NU-020]), its consume operations *shall* remove from each reset place every token the firing may drain ([EXEC-003] AC5), leave each other input place its queue without the tokens handed to the action, leave the queue of every other place unchanged, and hold a queue for every place the token storage held and for no other place."
  reading "For a token store S by place id and a consume program X over it, for every store state s and compiled transition t such that S holds a queue for every place t has an arc on, t has no two input arcs on one place, and t is enabled on the queues of s by the reference enablement:"
          "the inputs X hands the action are the reference's: from each input place the first tokens of its queue, in queue order, as many as the consumption count of the arc on the queue's length (One 1, Exactly n, All and AtLeast every token), and nothing from any other place;"
          "the read tokens X hands the action are the reference's: for each read arc, in arc order, the head of the read place's queue after the input consumption;"
          "after X, S holds a queue for exactly the places it held one for in s, and at each of them the queue is the reference's: empty at a reset place, the queue without its consumed prefix at any other input place, unchanged at every other place."
  assumes "The model is a token store S (glossary: MarkingOps, at place ids PlaceId and token values Colour), CONC-022's interface: view s p is the queue place p holds in s, oldest first (glossary: Queue order), and S.ok s p says that s is a well-formed store holding a queue for p. The consume program X maps a store state and a compiled transition (Libpetri.Transition of Basic.lean: input arcs with their cardinality, inhibitor, read and reset places, by place id) to a ConsumeOut: the store after the consume phase and the input and read tokens the action receives, by place id. The tokens a reset destroys are not handed to the action, so they are not a field; that they are reported to the event store is EVT's subject. The right-hand sides are the Bitmap reference executor's consume (Refinement/Model.lean: bbInputsBag, bbReadsBag over bbPostInput, bbConsumeMarking), applied to the store's view, and the enablement premise is the reference enablement bbCanEnable on the view, not the program's own enablement check."
          "Scope: transitions without a match specification (ruling D30, the consequence of D16 for EXEC-010). A transition with a match specification consumes its correlated inputs by name ([NU-020]) and does not run the input opcodes (rust/libpetri-runtime/src/precompiled_backend.rs:1146, java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:2332-2335, typescript/src/runtime/precompiled-net-executor.ts:1085-1088). The compiled Transition has no match specification, so every transition the statement quantifies over is one the EARS sentences speak of; the ν consume path is NU-020's subject. Each quoted sentence carries the scope in its trigger, and the prose sentence on iterating the opcode array states it as its exception."
          "The premises are the build-time guarantees under which the precompiled executor fires: every place a transition has an arc on is a compiled place id (the store holds a queue for it; CompiledNet::compile interns every referenced place), no two input arcs of a transition are on one place (DistinctInputPlaces, CORE-030 AC3, rejected at build time; with duplicate inputs the opcode interpreter is not total, canEnable_insufficient_for_totality in RetrodictExec.lean), and the transition is enabled ('fires' presupposes it). Guards are not modelled: input guards were removed from the spec (IO-006), and the guard field of the Lean InSpec is ignored by both the reference and the interpreter."
          "The statement does not assume ruling D15 (no input arc and read arc on one place, EXEC-012): the reference peeks the reads after input consumption whatever the arcs, and so does the precompiled executor. Under D15, which the build enforces, a read place is never an input place, so 'after the input operations' is not observable on a transition that builds: CONC_021_forbids_readsBeforeInputs kills a peek before the input opcodes only on a transition with an input arc and a read arc on one place, so on buildable nets that half of line 2 is stricter than the build needs. 'Before the reset operations' is observable, for a place that is both a read place and a reset place, which EXEC-013 allows and which CONC_021_forbids_readsAfterReset tests."
          "Draining opcodes are modelled with no same-pass deposit outstanding (clash conc-b#10, ruling D20). The opcode table and the first and third EARS sentences say 'the tokens the firing may drain ([EXEC-003] AC5)': a draining arc or reset that fires later in a firing pass takes only the tokens present when the pass began, and tokens a same-pass synchronous action deposited survive it (rust/libpetri-runtime/src/precompiled_backend.rs:1276-1279 and :1300, drainable at :690-695; java/src/main/java/org/libpetri/runtime/PrecompiledNetExecutor.java:791). A consume program here sees one firing and no pass, so every token is one the firing may drain, the available count of line 1 is the queue's length, line 1 reads 'every token' for All and AtLeast, and line 3 reads 'empty' at a reset place (the module header of Conservation.lean states the same limit). The deposited case is the Phase 2 executor model's (RefExec, W5) and EXEC-003's. For the same reason a program that also drains the inhibitor places with the RESET tail meets the lines: an enabled transition's inhibitor places are empty, and only a same-pass deposit between the enablement check and the consume could tell the two apart, which is for that model's mutant list."
          "Line 1 is the first EARS sentence. 'The oldest tokens the place holds, as many as the consumption count of the input arc ([IO-007]) for the number of tokens the firing may drain' is the queue's prefix of length consumptionCount(available), with available the queue's length (consumeCountAt). 'Nothing from any other place' is the bag equality off the input places: a reset place that is not an input place hands the action nothing. CONSUME_ATLEAST taking only its minimum is killed (CONC_021_forbids_atLeastMin), the RESET tail run before the input opcodes, which hands an input place that is also a reset place nothing, is killed (CONC_021_forbids_resetFirst), a RESET tail that hands the tokens it drains to the action is killed at the reset-only place 1 (CONC_021_forbids_resetHandsTokens, 'nothing from any other place'), and CONSUME_N taking the newest tokens of its place is killed (CONC_021_forbids_newestFirst, 'the oldest tokens ... in queue order')."
          "Line 2 is the second EARS sentence: per read arc the head of the read place's queue after the input consumption and before the drain, by bbReadsBag, which adds one head per read arc in arc order. A peek after the RESET tail, the order the Rust precompiled executor had before fix (b) (preFixReads, read_reset_order_diverges in RetrodictExec.lean), hands a read place that is also a reset place nothing and is killed (CONC_021_forbids_readsAfterReset); a peek before the input opcodes is killed as the D15 paragraph says. The sentence presupposes the read place's queue is not empty after the input operations; bbReadsBag hands nothing when it is, which only a read place that is also a draining input place can reach, and D15 rejects that transition at build time."
          "Line 3 is the third EARS sentence. Its view half is bbConsumeMarking: a reset place ends empty, any other input place keeps its queue without the consumed prefix, in order, every other place (read places and inhibitor places included) keeps its queue. A read compiled as a consuming opcode (AC2: reads do not consume) removes the read token and is killed (CONC_021_forbids_readConsumes), so is a program without the RESET tail (CONC_021_forbids_noReset), and so is one that hands the right tokens but shrinks the ring from its tail, leaving the input place its newest tokens removed instead of its oldest (CONC_021_forbids_tailShrink, 'its queue without the tokens handed to the action'). Its S.ok half is 'hold a queue for every place the token storage held and for no other place', both directions of the frame condition that lets one firing's store be the next firing's: a program that hands back a store with the right queues but no places is killed (CONC_021_forbids_forgetPlaces), and so is one that hands back a store holding places, with tokens, that the store before did not hold (CONC_021_forbids_seedPlaces, a lazily allocated pool reseeded from a cached template). Token conservation (the queue before is the delivered tokens, then the reset-destroyed tokens, then the queue after) is a consequence on the places the store holds, token_conservation in Conservation.lean."
          "Not quoted: the prose sentences 'Each transition's input and reset arcs are compiled into a flat integer array of opcodes.', 'During firing, the executor iterates the opcode array instead of pattern-matching on sealed arc types, except for a transition with a match specification, whose inputs are consumed through the match path (its correlated inputs by name, [NU-020]).' and 'Read arcs are compiled into a separate place-ID array.', and the opcode table. They describe the compiled representation and how firing walks it, which a consume program's observable behaviour does not show: a program that dispatches on arc types and one that runs an opcode array satisfy the lines alike. Only the by-name exception of the second sentence is used, as the scope above. The witness has the structure (compileConsumeOps: the input opcodes in declaration order, then the RESET tail; reads outside it, consumeForFiring_eq_program, cited by conc021_program). The u32 encoding and the pc walk are not modelled (Compile.lean header)."
          "The witness is the Rust ring pool. The Java precompiled executor keeps rings too; the TypeScript one keeps a plain array per place (clash conc-b#5, typescript/src/runtime/precompiled-net-executor.ts:179). The statement is over CONC-022's store interface and reads the store through its view, so a consume program over an array store is in its domain alike. CONC_021_ringMarking shows the reference over core070_ringMarking, the store of the consistency theorem spec_consistent_queue."
          "AC1 (each transition has a precompiled consume operation array) and AC2's first half (read arcs compiled into a separate place-ID array) are the compiled representation, kind Q, not lines; the witness's compileConsumeOps has that shape (conc021_program). AC2's second half (reads do not consume) is line 3 at a read place (CONC_021_forbids_readConsumes)."
          "AC3 (firing iterates the opcode array without type dispatch, except for a transition with a match specification, whose inputs are consumed through the match path, its correlated inputs by name) is a cost and structure criterion, kind Q, not a line; its by-name exception is the scope assumption above."
          "AC4 (all five opcodes produce the same observable behaviour as the corresponding arc types) is the three lines: the right-hand sides are the reference arc semantics, and CONC_021_nonvacuous runs one transition with all five opcodes (One, Exactly 2, All, AtLeast 2, two resets), two read arcs and an inhibitor arc. The test derivation (compile a net with all arc types, fire, compare with the bitmap executor) is the same example; over whole runs on the untimed immediate synchronous fragment the comparison is precompiled_refines_bitmap_immediate (Refinement.lean), which cites CONC-021."
          "The Kind line is F, the kind of its one block (ruling D21: one letter); the structure sentences are Q content without a line."
  signoff "2026-11-13 90f801704231c404 ai"
  statement : (S : MarkingOps PlaceId Colour) → ConsumeProgram S → Prop :=
    fun S X => ∀ s t, (∀ p, touches t p → S.ok s p) → DistinctInputPlaces t →
      bbCanEnable (S.view s) t = true →
        (X s t).inputs = bbInputsBag (S.view s) t ∧
        (X s t).reads = bbReadsBag (bbPostInput (S.view s) t) t.reads ∧
        ∀ q, (S.ok (X s t).store q ↔ S.ok s q) ∧
          (S.ok s q → S.view (X s t).store q = bbConsumeMarking (S.view s) t q)

/- The pinned readable form of CONC-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_021 : (S : MarkingOps PlaceId Colour) → ConsumeProgram S → Prop :=
fun S X =>
  ∀ (s : S.σ) (t : Transition),
    (∀ (p : PlaceId), touches t p → S.ok s p) →
      DistinctInputPlaces t →
        bbCanEnable (S.view s) t = true →
          (X s t).inputs = bbInputsBag (S.view s) t ∧
            (X s t).reads = bbReadsBag (bbPostInput (S.view s) t) t.reads ∧
              ∀ (q : PlaceId),
                (S.ok (X s t).store q ↔ S.ok s q) ∧
                  (S.ok s q → S.view (X s t).store q = bbConsumeMarking (S.view s) t q)
-/
#guard_msgs in #print CONC_021

/-! ### The reference -/

/-- The ring pool related to its own view: the refinement relation `Rel` of
`Refinement/Model.lean` between a well-formed pool and the reference state whose marking is the
pool's projection (control bits play no part in the consume phase). -/
theorem conc021_rel {s : Pool} (hwf : Pool.WF s) :
    Rel s.nplaces ⟨s, fun _ => false, fun _ => false, fun _ => false⟩
      ⟨s.proj, fun _ => false, fun _ => false⟩ :=
  ⟨hwf, rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A transition that has an arc on no place: its consume phase leaves the store as it is and
hands the action nothing. -/
theorem conc021_noArc {s : Pool} {t : Transition} (h : ∀ p, ¬ touches t p) :
    refConsume s t = ⟨s, emptyBag, emptyBag⟩ ∧ bbInputsBag s.proj t = emptyBag ∧
      bbReadsBag (bbPostInput s.proj t) t.reads = emptyBag := by
  have hin : t.inputs = [] := by
    cases hi : t.inputs with
    | nil => rfl
    | cons sp _ => exact absurd (Or.inl ⟨sp, by simp [hi], rfl⟩) (h sp.place)
  have hrd : t.reads = [] := by
    cases hr : t.reads with
    | nil => rfl
    | cons p _ => exact absurd (Or.inr (Or.inl (by simp [hr]))) (h p)
  have hrs : t.resets = [] := by
    cases hr : t.resets with
    | nil => rfl
    | cons p _ => exact absurd (Or.inr (Or.inr (Or.inr (by simp [hr])))) (h p)
  refine ⟨?_, ?_, ?_⟩
  · simp [refConsume, consumeForFiring, hin, hrd, hrs, execOpsFrom, peekReads]
  · funext p
    simp [bbInputsBag, specAt, hin, emptyBag]
  · simp [bbReadsBag, hrd]

/-- The reference satisfies CONC-021: on a well-formed pool related to its own view, the opcode
interpreter hands the action the reference inputs (`inputs_bag_rel`) and reads
(`reads_bag_rel`), leaves the reference marking (`consume_marking_rel`) and keeps the pool well
formed with exactly its places (`consumeForFiring_wf`); the reference enablement on the view is
the interpreter's (`canEnable_rel`). A transition with an arc on no place leaves the store as it
is (`conc021_noArc`). -/
@[evidence holds CONC_021]
theorem CONC_021_reference : CONC_021 refRingStore refConsume := by
  intro s t hok hd hen
  by_cases hwf : Pool.WF s
  · have hb : PlacesInBounds t s.nplaces :=
      ⟨fun sp hm => (hok sp.place (Or.inl ⟨sp, hm, rfl⟩)).2,
        fun p hm => (hok p (Or.inr (Or.inl hm))).2,
        fun p hm => (hok p (Or.inr (Or.inr (Or.inl hm)))).2,
        fun p hm => (hok p (Or.inr (Or.inr (Or.inr hm)))).2⟩
    have hrel := conc021_rel hwf
    have hce : canEnable s t = true := by rw [canEnable_rel hrel hb]; exact hen
    obtain ⟨hwf', hnp'⟩ := consumeForFiring_wf hwf hd hb hce
    refine ⟨inputs_bag_rel hrel hd hb hce, reads_bag_rel hrel hd hb hce, fun q => ⟨?_, ?_⟩⟩
    · show Pool.WF (consumeForFiring s t).1.pool ∧ q < (consumeForFiring s t).1.pool.nplaces
        ↔ Pool.WF s ∧ q < s.nplaces
      rw [hnp']
      exact ⟨fun h => ⟨hwf, h.2⟩, fun h => ⟨hwf', h.2⟩⟩
    · exact fun ⟨_, hq⟩ => consume_marking_rel hrel hd hb hce q hq
  · obtain ⟨h1, h2, h3⟩ := conc021_noArc (s := s) (t := t) fun p hp => hwf (hok p hp).1
    refine ⟨?_, ?_, fun q => ⟨by rw [h1], fun hq => absurd hq.1 hwf⟩⟩
    · show (refConsume s t).inputs = bbInputsBag s.proj t
      rw [h1, h2]
    · show (refConsume s t).reads = bbReadsBag (bbPostInput s.proj t) t.reads
      rw [h1, h3]

/-- The reference over `core070_ringMarking`, the ring pool with its removal guarded by the
count, which the consistency theorem `spec_consistent_queue` puts CORE-070, CONC-022 and
CONC-025 on: it has the ring pool's state, `ok` and `view`, so the reference consume program is a
program over it and satisfies CONC-021 there too. -/
theorem CONC_021_ringMarking : CONC_021 core070_ringMarking refConsume :=
  CONC_021_reference

/-- The witness has the compiled structure of AC1 and AC2: its store and inputs are the compiled
consume program `compileConsumeOps` (the input opcodes in declaration order, then the RESET
tail) run start to finish, and its reads are peeked outside that program, at the boundary
(`consumeForFiring_eq_program`). -/
@[evidence cites "CONC-021" "AC1 and AC2's first half for the Rust model: the store after the consume phase and the delivered inputs are the compiled opcode list compileConsumeOps (input opcodes in declaration order, then the RESET tail) run start to finish; the read peek is outside the opcode list; the u32 encoding and the pc walk are not modelled"]
theorem conc021_program (s : Pool) (t : Transition) :
    (refConsume s t).store = (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (compileConsumeOps t)).pool ∧
      (refConsume s t).inputs
        = (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (compileConsumeOps t)).inputs := by
  exact ⟨congrArg ConsumeResult.pool (consumeForFiring_eq_program s t),
    congrArg ConsumeResult.inputs (consumeForFiring_eq_program s t)⟩

/-! ### Examples -/

/-- Adding a list of tokens to a pool, one `Pool.addLast` per token, in list order. -/
def conc021_addAll (s : Pool) (l : List (PlaceId × Colour)) : Pool :=
  l.foldl (fun s x => s.addLast x.1 x.2) s

/-- Adding tokens to places of a well-formed pool keeps it well formed with its places. -/
theorem conc021_addAll_wf {s : Pool} (hwf : Pool.WF s) {l : List (PlaceId × Colour)}
    (hl : ∀ x ∈ l, x.1 < s.nplaces) :
    Pool.WF (conc021_addAll s l) ∧ (conc021_addAll s l).nplaces = s.nplaces := by
  induction l generalizing s with
  | nil => exact ⟨hwf, rfl⟩
  | cons x l ih =>
    have hx := hl x (by simp)
    have hn := conc022_addLast_nplaces s x.1 x.2
    have := ih (s := s.addLast x.1 x.2) (Pool.addLast_wf hwf hx x.2)
      (fun y hy => hn ▸ hl y (by simp [hy]))
    exact ⟨this.1, this.2.trans hn⟩

/-- The pool of the examples: seven places with rings of capacity 4. Place `0` holds `10, 11,
12`; place `1` holds `20, 21`; place `2` holds `30, 31`; place `3` holds `40`; place `4` holds
`50, 51, 52`; place `5` holds `60, 61`; place `6` is empty. -/
def conc021_pool : Pool :=
  conc021_addAll (conc022_blank 7 4)
    [(0, 10), (0, 11), (0, 12), (1, 20), (1, 21), (2, 30), (2, 31), (3, 40), (4, 50), (4, 51),
      (4, 52), (5, 60), (5, 61)]

/-- The example pool is well formed over seven places. -/
theorem conc021_pool_wf : Pool.WF conc021_pool ∧ conc021_pool.nplaces = 7 :=
  conc021_addAll_wf (conc022_blank_wf 7 (by decide)) (by decide)

/-- The transition of the examples, one arc of every kind and all five opcodes: `AtLeast 2` on
place `0`, `One` on place `2`, `Exactly 2` on place `4`, `All` on place `5`; read arcs on places
`1` and `3`; an inhibitor arc on place `6`; reset arcs on places `1` (also a read place) and `2`
(also an input place). -/
def conc021_t : Transition :=
  { name := "t"
    inputs := [⟨0, .atLeast 2, none⟩, ⟨2, .one, none⟩, ⟨4, .exactly 2, none⟩, ⟨5, .all, none⟩]
    inhibitors := [6]
    reads := [1, 3]
    resets := [1, 2] }

/-- The example meets the premises of CONC-021: the pool holds a queue for every place of the
transition, its input places are distinct, and it is enabled on the pool's queues. -/
theorem conc021_premises :
    (∀ p, touches conc021_t p → refRingStore.ok conc021_pool p) ∧
      DistinctInputPlaces conc021_t ∧
      bbCanEnable (refRingStore.view conc021_pool) conc021_t = true := by
  refine ⟨fun p hp => ⟨conc021_pool_wf.1, ?_⟩, by unfold DistinctInputPlaces; decide, by decide⟩
  rw [conc021_pool_wf.2]
  simp [touches, conc021_t] at hp
  rcases hp with ((h | h | h | h) | (h | h) | h | h | h) <;> subst h <;> decide

/-- CONC-021 is not vacuous: on the example the premises hold and the reference hands the action
`10, 11, 12` from place `0` (AtLeast drains), `30` from place `2` (One, then the reset drains
`31`), `50, 51` from place `4` (Exactly 2), `60, 61` from place `5` (All) and nothing from the
reset place `1`; it reads `20` (the head of place `1` before the drain) and `40`; and it leaves
places `0`, `1`, `2` and `5` empty, place `3` with `40` (a read does not consume) and place `4`
with `52`. -/
@[evidence nonvacuous CONC_021]
theorem CONC_021_nonvacuous :
    ((∀ p, touches conc021_t p → refRingStore.ok conc021_pool p) ∧
      DistinctInputPlaces conc021_t ∧
      bbCanEnable (refRingStore.view conc021_pool) conc021_t = true) ∧
    (refConsume conc021_pool conc021_t).inputs 0 = [10, 11, 12] ∧
    (refConsume conc021_pool conc021_t).inputs 1 = [] ∧
    (refConsume conc021_pool conc021_t).inputs 2 = [30] ∧
    (refConsume conc021_pool conc021_t).inputs 4 = [50, 51] ∧
    (refConsume conc021_pool conc021_t).inputs 5 = [60, 61] ∧
    (refConsume conc021_pool conc021_t).reads 1 = [20] ∧
    (refConsume conc021_pool conc021_t).reads 3 = [40] ∧
    (refConsume conc021_pool conc021_t).store.proj 0 = [] ∧
    (refConsume conc021_pool conc021_t).store.proj 1 = [] ∧
    (refConsume conc021_pool conc021_t).store.proj 2 = [] ∧
    (refConsume conc021_pool conc021_t).store.proj 3 = [40] ∧
    (refConsume conc021_pool conc021_t).store.proj 4 = [52] ∧
    (refConsume conc021_pool conc021_t).store.proj 5 = [] :=
  ⟨conc021_premises, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A consume program that satisfies CONC-021 meets its three lines on the example. -/
theorem conc021_at {X : ConsumeProgram refRingStore} (h : CONC_021 refRingStore X) :
    (X conc021_pool conc021_t).inputs = bbInputsBag (refRingStore.view conc021_pool) conc021_t ∧
    (X conc021_pool conc021_t).reads
      = bbReadsBag (bbPostInput (refRingStore.view conc021_pool) conc021_t) conc021_t.reads ∧
    ∀ q, (refRingStore.ok (X conc021_pool conc021_t).store q ↔ refRingStore.ok conc021_pool q) ∧
      (refRingStore.ok conc021_pool q →
        refRingStore.view (X conc021_pool conc021_t).store q
          = bbConsumeMarking (refRingStore.view conc021_pool) conc021_t q) :=
  h conc021_pool conc021_t conc021_premises.1 conc021_premises.2.1 conc021_premises.2.2

/-- The example pool holds a queue for each place below `7`. -/
theorem conc021_pool_ok {q : PlaceId} (hq : q < 7) : refRingStore.ok conc021_pool q :=
  ⟨conc021_pool_wf.1, by rw [conc021_pool_wf.2]; exact hq⟩

/-! ### Violation: `CONSUME_ATLEAST` takes only its minimum (line 1) -/

/-- An input opcode compiler that compiles `AtLeast m` as `CONSUME_N` of the minimum `m`, as if
the opcode's operand were its consumption count. -/
def conc021_atLeastMinOp (sp : InSpec) : ConsumeOp :=
  match sp.card with
  | .atLeast m => .n sp.place m
  | _ => opOfSpec sp

/-- The consume program with `conc021_atLeastMinOp` for the input opcodes, otherwise the
reference's. -/
def conc021_atLeastMin : ConsumeProgram refRingStore := fun s t =>
  let r₁ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map conc021_atLeastMinOp)
  ⟨(execOpsFrom r₁ (t.resets.map .reset)).pool, r₁.inputs, peekReads r₁.pool t.reads⟩

/-- An `AtLeast` opcode that takes only its minimum violates line 1: from place `0` (`AtLeast 2`
on `10, 11, 12`) it hands the action `10, 11`, where the arc consumes every token. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_atLeastMin : ¬ CONC_021 refRingStore conc021_atLeastMin := by
  intro h
  have h0 := congrFun (conc021_at h).1 0
  revert h0
  decide

/-! ### Violation: the RESET tail before the input opcodes (line 1) -/

/-- The consume program that runs the RESET tail before the input opcodes; its reads are the
reference's. -/
def conc021_resetFirst : ConsumeProgram refRingStore := fun s t =>
  let r₀ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.resets.map .reset)
  let r₁ := execOpsFrom r₀ (t.inputs.map opOfSpec)
  ⟨r₁.pool, r₁.inputs, (consumeForFiring s t).2⟩

/-- Draining before consuming violates line 1: place `2` is an input place (`One`) and a reset
place, and the drain leaves the input nothing to hand the action, where the reference hands it
`30`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_resetFirst : ¬ CONC_021 refRingStore conc021_resetFirst := by
  intro h
  have h2 := congrFun (conc021_at h).1 2
  revert h2
  decide

/-! ### Violation: the RESET tail hands its tokens to the action (line 1) -/

/-- The consume program that compiles each reset arc as `CONSUME_ALL`, so the RESET tail hands
the tokens it drains to the action as inputs; its store and reads are the reference's. -/
def conc021_resetHandsTokens : ConsumeProgram refRingStore := fun s t =>
  let r₁ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)
  let r₂ := execOpsFrom r₁ (t.resets.map .all)
  ⟨r₂.pool, r₂.inputs, peekReads r₁.pool t.reads⟩

/-- Handing the drained tokens to the action violates line 1's 'nothing from any other place':
place `1` is a reset place and no input place, and the program hands the action `20, 21` from
it, where the reference hands nothing. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_resetHandsTokens :
    ¬ CONC_021 refRingStore conc021_resetHandsTokens := by
  intro h
  have h1 := congrFun (conc021_at h).1 1
  revert h1
  decide

/-! ### Violation: `CONSUME_N` takes the newest tokens (line 1), the ring shrinks from its tail
(line 3) -/

/-- Removing the newest token of place `p` from the ring: the slot before the tail is freed, the
tail steps back and the count drops by one. -/
def conc021_removeLast (s : Pool) (p : PlaceId) : Pool :=
  { s with
    pool := fun idx => if idx = s.slot p (s.cnt p - 1) then none else s.pool idx
    tail := fun q => if q = p then (s.tail q + s.cap q - 1) % s.cap q else s.tail q
    cnt  := fun q => if q = p then s.cnt q - 1 else s.cnt q }

/-- Popping the `k` newest tokens of place `p` from the ring, returned in queue order. -/
def conc021_popLastN (s : Pool) (p : PlaceId) : Nat → Pool × List Colour
  | 0 => (s, [])
  | k + 1 =>
    let x := if s.cnt p = 0 then [] else (s.pool (s.slot p (s.cnt p - 1))).toList
    let r := conc021_popLastN (conc021_removeLast s p) p k
    (r.1, r.2 ++ x)

/-- One input opcode where `CONSUME_N` pops from the tail of the ring instead of its head; the
other opcodes are the reference's. -/
def conc021_newestOp (r : ConsumeResult) (sp : InSpec) : ConsumeResult :=
  match sp.card with
  | .exactly k =>
    { r with pool := (conc021_popLastN r.pool sp.place k).1
             inputs := addBag r.inputs sp.place (conc021_popLastN r.pool sp.place k).2 }
  | _ => execOp r (opOfSpec sp)

/-- The input opcodes with `conc021_newestOp`, from a pool. -/
def conc021_newestInputs (s : Pool) (t : Transition) : ConsumeResult :=
  t.inputs.foldl conc021_newestOp ⟨s, emptyBag, emptyBag⟩

/-- The consume program whose `CONSUME_N` takes the newest tokens of its place: it hands them to
the action and removes them; the reads and the RESET tail are the reference's. -/
def conc021_newestFirst : ConsumeProgram refRingStore := fun s t =>
  let r₁ := conc021_newestInputs s t
  ⟨(execOpsFrom r₁ (t.resets.map .reset)).pool, r₁.inputs, peekReads r₁.pool t.reads⟩

/-- Taking the newest tokens violates line 1's 'the oldest tokens ... in queue order': from
place `4` (`Exactly 2` on `50, 51, 52`) the program hands the action `51, 52`, where the
reference hands it `50, 51`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_newestFirst : ¬ CONC_021 refRingStore conc021_newestFirst := by
  intro h
  have h4 := congrFun (conc021_at h).1 4
  revert h4
  decide

/-- The consume program that hands the action the reference's tokens but removes the newest
tokens of a `CONSUME_N` place from its ring, as if the copy read from the head and the removal
shrank the ring from its tail. -/
def conc021_tailShrink : ConsumeProgram refRingStore := fun s t =>
  ⟨(conc021_newestFirst s t).store, (refConsume s t).inputs, (refConsume s t).reads⟩

/-- Shrinking the ring from its tail violates line 3's 'its queue without the tokens handed to
the action': place `4` is left `50`, where the reference leaves it `52`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_tailShrink : ¬ CONC_021 refRingStore conc021_tailShrink := by
  intro h
  have h4 := ((conc021_at h).2.2 4).2 (conc021_pool_ok (by decide))
  revert h4
  decide

/-! ### Violation: the read peek after the RESET tail (line 2) -/

/-- The consume program whose reads peek the pool after the RESET tail (`preFixReads`, the
order of the Rust precompiled executor before fix (b), `RetrodictExec.lean`). -/
def conc021_readsAfterReset : ConsumeProgram refRingStore := fun s t =>
  ⟨(consumeForFiring s t).1.pool, (consumeForFiring s t).1.inputs, preFixReads s t⟩

/-- Peeking after the drain violates line 2: place `1` is a read place and a reset place, and the
read finds it drained, where the reference reads its head `20`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_readsAfterReset : ¬ CONC_021 refRingStore conc021_readsAfterReset := by
  intro h
  have h1 := congrFun (conc021_at h).2.1 1
  revert h1
  decide

/-! ### Violation: the read peek before the input opcodes (line 2) -/

/-- The consume program whose reads peek the pool before the input opcodes run, as if the read
tokens were collected during the enablement check; its store and inputs are the reference's. -/
def conc021_readsBeforeInputs : ConsumeProgram refRingStore := fun s t =>
  ⟨(refConsume s t).store, (refConsume s t).inputs, peekReads s t.reads⟩

/-- `One` on place `0` and a read arc on place `0`: a transition ruling D15 (EXEC-012) rejects at
build time, and the only kind on which a read before the input opcodes differs from a read after
them. -/
def conc021_inputRead_t : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [0], resets := [] }

/-- The example pool meets the premises of CONC-021 for `conc021_inputRead_t`. -/
theorem conc021_inputRead_premises :
    (∀ p, touches conc021_inputRead_t p → refRingStore.ok conc021_pool p) ∧
      DistinctInputPlaces conc021_inputRead_t ∧
      bbCanEnable (refRingStore.view conc021_pool) conc021_inputRead_t = true := by
  refine ⟨fun p hp => conc021_pool_ok ?_, by unfold DistinctInputPlaces; decide, by decide⟩
  simp [touches, conc021_inputRead_t] at hp
  rcases hp with h | h <;> subst h <;> decide

/-- Peeking before the input opcodes violates line 2's 'after the input operations': place `0`
holds `10, 11, 12`, `One` hands the action `10`, and the program reads `10`, where the reference
reads the head after the consumption, `11`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_readsBeforeInputs :
    ¬ CONC_021 refRingStore conc021_readsBeforeInputs := by
  intro h
  have h0 := congrFun (h conc021_pool conc021_inputRead_t conc021_inputRead_premises.1
    conc021_inputRead_premises.2.1 conc021_inputRead_premises.2.2).2.1 0
  revert h0
  decide

/-! ### Violation: a read compiled as a consuming opcode (line 3) -/

/-- The consume program that compiles each read arc as `CONSUME_ONE` after the input opcodes and
hands the removed tokens to the action as read tokens. -/
def conc021_readConsumes : ConsumeProgram refRingStore := fun s t =>
  let r₁ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)
  let r₂ := execOpsFrom ⟨r₁.pool, emptyBag, emptyBag⟩ (t.reads.map .one)
  ⟨(execOpsFrom r₂ (t.resets.map .reset)).pool, r₁.inputs, r₂.inputs⟩

/-- A consuming read violates line 3 (AC2: reads do not consume): it hands the action the right
read tokens, but place `3`, a read place only, ends empty, where the reference leaves it `40`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_readConsumes : ¬ CONC_021 refRingStore conc021_readConsumes := by
  intro h
  have h3 := ((conc021_at h).2.2 3).2 (conc021_pool_ok (by decide))
  revert h3
  decide

/-! ### Violation: no RESET tail (line 3) -/

/-- The consume program that runs the input opcodes and the read peek but not the RESET tail. -/
def conc021_noReset : ConsumeProgram refRingStore := fun s t =>
  let r₁ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)
  ⟨r₁.pool, r₁.inputs, peekReads r₁.pool t.reads⟩

/-- Skipping the drain violates line 3: the reset place `1` keeps `20, 21`, where the reference
leaves it empty. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_noReset : ¬ CONC_021 refRingStore conc021_noReset := by
  intro h
  have h1 := ((conc021_at h).2.2 1).2 (conc021_pool_ok (by decide))
  revert h1
  decide

/-! ### Violation: the store after forgets its places (line 3) -/

/-- The reference consume, except that the store it hands back records no place: its queues are
the reference's, but it holds a queue for no place. -/
def conc021_forgetPlaces : ConsumeProgram refRingStore := fun s t =>
  ⟨{ (consumeForFiring s t).1.pool with nplaces := 0 }, (consumeForFiring s t).1.inputs,
    (consumeForFiring s t).2⟩

/-- Forgetting the places violates line 3's 'hold a queue for every place the token storage
held': the store after has the reference's queues but no longer holds one for place `0`. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_forgetPlaces : ¬ CONC_021 refRingStore conc021_forgetPlaces := by
  intro h
  have h0 := (((conc021_at h).2.2 0).1.2 (conc021_pool_ok (by decide))).2
  exact absurd h0 (Nat.lt_irrefl 0)

/-! ### Violation: the store after gains places (line 3) -/

/-- The consume program that, on a store holding no place, hands back the example pool, as an
implementation that lazily allocates its token pool from a cached template would; otherwise, and
for its inputs and reads, it is the reference. -/
def conc021_seedPlaces : ConsumeProgram refRingStore := fun s t =>
  if s.nplaces = 0 then ⟨conc021_pool, (refConsume s t).inputs, (refConsume s t).reads⟩
  else refConsume s t

/-- A transition with no arc. -/
def conc021_noArc_t : Transition :=
  { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] }

/-- The empty pool, which holds no place, meets the premises of CONC-021 for `conc021_noArc_t`. -/
theorem conc021_noArc_premises :
    (∀ p, touches conc021_noArc_t p → refRingStore.ok (conc022_blank 0 4) p) ∧
      DistinctInputPlaces conc021_noArc_t ∧
      bbCanEnable (refRingStore.view (conc022_blank 0 4)) conc021_noArc_t = true := by
  refine ⟨fun p hp => ?_, by unfold DistinctInputPlaces; decide, by decide⟩
  simp [touches, conc021_noArc_t] at hp

/-- Gaining places violates line 3's 'and for no other place': from the empty pool and a
transition with no arc, the store after holds a queue for place `0` (with `10, 11, 12`), where
the store before held a queue for no place. -/
@[evidence forbids CONC_021]
theorem CONC_021_forbids_seedPlaces : ¬ CONC_021 refRingStore conc021_seedPlaces := by
  intro h
  have hs : (conc021_seedPlaces (conc022_blank 0 4) conc021_noArc_t).store = conc021_pool := by
    simp [conc021_seedPlaces, conc022_blank]
  have hq := ((h (conc022_blank 0 4) conc021_noArc_t conc021_noArc_premises.1
    conc021_noArc_premises.2.1 conc021_noArc_premises.2.2).2.2 0).1
  have h0 := (hq.1 (by rw [hs]; exact conc021_pool_ok (by decide))).2
  exact absurd h0 (Nat.lt_irrefl 0)

end Libpetri.Spec
