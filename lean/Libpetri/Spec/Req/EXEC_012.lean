import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# EXEC-012: Read arc peek (`spec/04-execution-model.md`)

The model is a pair. `Build` is the transition builder, read as the message it rejects a
transition with (`none`: the transition builds), as in IO-011 and IO-013. `Q` is a queue firing
relation (`QFireRel`, glossary `GlossaryQueue.lean`): a firing from a queue marking, with what it
delivers to the action, what the action emits and the queue marking it leaves. The witness pair
is the reference builder `refBuild` (glossary: Build-time checks), which runs the
[IO-002]/[IO-004] count checks and the ruling D15 check between the [CORE-030] input-arc check
and the output-spec checks, and the reference queue firing `RefQFire`. The same `refBuild` is
the builder of the CORE and IO blocks, so one builder witnesses all of them
(`spec_consistent_queue`).

The two firing lines speak of transitions that have no input arc and read arc on one place
(`NoInputRead`): ruling D15 rejects every other transition when it is built, which the four
build lines state. On those transitions the head of a read place after input consumption is its
head before the firing (`exec012_head_postInput`), so "the oldest token the place holds" has one
reading, and reset draining comes after the peek ([EXEC-013] AC4).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The build rule of ruling D15 -/

section Build

variable {N : Type}

/-- The place the check names is a read place and an input place of `t`. -/
theorem firstInputRead_some [DecidableEq N] {t : Trans N} {p : N}
    (h : firstInputRead t = some p) : ReadArc t p ∧ p ∈ inPlaces t := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

/-- **The reference builder without the D15 check**: [CORE-030]'s input-arc check, then the
output-spec checks of `checkOut`, as `refBuild` was before ruling D15 (and without the
[IO-002]/[IO-004] count checks). EXEC-012's build lines forbid it (`EXEC_012_forbids_noCheck`). -/
def exec012_buildNoCheck [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  if ¬ InputsDistinct t then some "CORE-030"
  else match t.out with
    | none => none
    | some o => checkOut t (inPlaces t) o

/-- [CORE-030]'s stand-in message is not [EXEC-012]'s, for any transition and place. -/
theorem core030_msg_ne_msgInputRead [ToString N] (t : Trans N) (p : N) :
    ("CORE-030" : String) ≠ msgInputRead t p := by
  intro h
  have := congrArg String.length h
  simp only [msgInputRead, String.length_append] at this
  have h8 : ("CORE-030" : String).length = 8 := by decide
  have h12 : ("Transition '" : String).length = 12 := by decide
  omega

/-- The count checks' stand-in message is not [EXEC-012]'s, for any transition and place. -/
theorem msgCount_ne_msgInputRead [ToString N] (t : Trans N) (p : N) :
    msgCount ≠ msgInputRead t p := by
  intro h
  have := congrArg String.length h
  simp only [msgCount, msgInputRead, String.length_append] at this
  have h13 : ("IO-002/IO-004" : String).length = 13 := by decide
  have h49 : ("' declares an input arc and a read arc on place '" : String).length = 49 := by
    decide
  omega

/-- A string that starts with `a` starts with `a`'s first character. -/
theorem exec012_head_append {a b : String} {c : Char} (h : a.toList.head? = some c) :
    (a ++ b).toList.head? = some c := by
  rw [String.toList_append, List.head?_append, h]; rfl

/-- [EXEC-012]'s message starts with `T`. -/
theorem msgInputRead_head [ToString N] (t : Trans N) (p : N) :
    (msgInputRead t p).toList.head? = some 'T' := by
  unfold msgInputRead; simp only [String.append_assoc]; exact exec012_head_append (by decide)

/-- Every message of the output-spec checks starts with `o` (`output spec of transition ...`),
except [IO-014] AC3's (`msgNonInput`). -/
theorem checkOut_shape [DecidableEq N] [ToString N] {t : Trans N} {ins : List N} {o : Out N}
    {m : String} (h : checkOut t ins o = some m) :
    m.toList.head? = some 'o' ∨ ∃ s, m = msgNonInput t s := by
  unfold checkOut at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h
       first
        | exact .inr ⟨_, rfl⟩
        | (left
           first
            | (unfold msgDup; simp only [String.append_assoc])
            | (unfold msgTimeouts; simp only [String.append_assoc])
            | (unfold msgXorInTimeout; simp only [String.append_assoc])
            | (unfold msgForward; simp only [String.append_assoc])
            | (unfold msgAmbiguous; simp only [String.append_assoc])
           exact exec012_head_append (by decide)))

/-- [IO-014] AC3's message is not [EXEC-012]'s: after `Transition '<t>'` one goes on with `:`,
the other with ` declares`. -/
theorem msgNonInput_ne_msgInputRead [ToString N] (t : Trans N) (s p : N) :
    msgNonInput t s ≠ msgInputRead t p := by
  intro h
  have := congrArg String.toList h
  change ("Transition '" ++ t.core.name ++ "': ForwardInput references non-input place '" ++
    toString s ++ "'").toList = _ at this
  simp only [msgInputRead, String.append_assoc, String.toList_append,
    List.append_cancel_left_eq] at this
  simp at this

/-- **The output-spec checks never fail with [EXEC-012]'s message**: every message of
`checkOut` starts with `o`, or is [IO-014] AC3's, and neither is this one. -/
theorem checkOut_ne_msgInputRead [DecidableEq N] [ToString N] (t : Trans N) (ins : List N)
    (o : Out N) (p : N) : checkOut t ins o ≠ some (msgInputRead t p) := by
  intro h
  rcases checkOut_shape h with ho | ⟨s, hs⟩
  · rw [msgInputRead_head] at ho
    exact absurd (Option.some.inj ho) (by decide)
  · exact msgNonInput_ne_msgInputRead t s p hs.symm

/-- **The builder without the D15 check never fails with [EXEC-012]'s message**: its messages
are [CORE-030]'s stand-in and the output-spec checks', none of which is this one. -/
theorem exec012_buildNoCheck_ne_msgInputRead [DecidableEq N] [ToString N] (t : Trans N)
    (p : N) : exec012_buildNoCheck t ≠ some (msgInputRead t p) := by
  unfold exec012_buildNoCheck
  intro h
  split at h
  · exact core030_msg_ne_msgInputRead t p (Option.some.inj h)
  · split at h
    · simp at h
    · exact checkOut_ne_msgInputRead t _ _ p h

end Build

/-! ## EXEC-012: Read Arc Peek -/

requirement EXEC_012
  id "EXEC-012"
  title "Read Arc Peek"
  kind B
  scope "all executors and transition builders"
  source verbatim "spec/04-execution-model.md"
  quote "When a transition fires, read arc values are provided to the action without consuming the tokens."
        "The oldest token in the read place is peeked."
        "*When* a transition fires, its action *shall* receive, for each of its read places, the oldest token the place holds."
        "*When* a transition fires, its action *shall* receive read tokens only from the read places of the transition."
        "*When* a transition fires, each of its read places that is not one of its reset places *shall* end the firing holding the tokens it held before the firing, in the same queue order, followed by the tokens the firing deposits there."
        "*If* a transition declares an input arc and a read arc on the same place, *then* building the transition *shall* fail with"
        "The message is the same, byte for byte, in every implementation."
        "\"The same place\" is the implementation's own `Place` equality, as for [CORE-030] ([CORE-002]; name-and-type in Java, name-only in TypeScript and Rust)."
        "It runs after every input-arc check ([CORE-030], [IO-002], [IO-004]) and before the timing check ([TIME-001]) and the output-spec checks ([IO-011]–[IO-014])."
        "It walks the read arcs in declaration order and names the place of the first read arc whose place is an input place of the transition."
  reading "Let Build be the builder (Build t = none: t builds; Build t = some msg: building t fails with msg) and Q the queue firings."
          "For every transition t with no input arc and read arc on one place, every read place p of t, every delivery δ and every emission e, every firing of t from the queue marking M that delivers δ and emits e delivers at p the head of p's queue in M: the first token delivered at p is the head of M at p, every token delivered at p is that head, and when t has one read arc on p at most one token is delivered there;"
          "for every such t, every read place p of t that is not a reset place of t, every δ and every e, every firing of t from M to M' that delivers δ and emits e leaves at p the queue M held at p, identity and order, followed by the tokens e emits to p in emission order (AppendedAtTail);"
          "every transition with an input arc and a read arc on one place fails to build;"
          "every transition whose input places are distinct and whose input arcs each require at least one token, and whose first read arc on an input place, in declaration order, is on p, fails to build with the message msgInputRead t p;"
          "no transition whose input places are not distinct, or one of whose input arcs requires fewer than one token, fails to build with this message, for any place;"
          "no transition with no input arc and read arc on one place fails to build with this message, for any place;"
          "for every transition t, every place p that is not a read place of t, every δ and every e, no firing of t that delivers δ and emits e delivers a read token at p."
  assumes "The model is the pair (Build, Q). Build is the transition builder, read as the message building a transition fails with, none when it builds; the witness is the reference builder refBuild (glossary: Build-time checks), which runs the [IO-002]/[IO-004] count checks (stand-in message msgCount) and the D15 check after its CORE-030 check and before its output-spec checks; it is the builder of the CORE and IO blocks too. Q is a queue firing relation (glossary: Queue order; QFireRel in GlossaryQueue.lean): a firing of t from the queue marking M, the head of each queue the oldest token, that delivers δ (the consumed input tokens and the read tokens, per place) to the action, whose action emits e (places and tokens, in emission order), and that leaves M'. The witness is the reference queue firing RefQFire. Timing and priority play no part."
          "Ruling D17: a Q step is a firing whose completion the executor admits and whose produced tokens pass output validation ([EXEC-020], [EXEC-021]), so e is what the firing deposits. A firing whose completion is not admitted (its timeout outcome [EXEC-022], a stop on a terminal place [EXEC-042], an immediate termination [ENV-015]) or whose output validation fails ([EXEC-021], TransitionFailed) is not a Q step, and line 2 says nothing about it; what such a firing leaves in its read places (the queue, plus the tokens [IO-015] already published) is [EXEC-020]'s and [EXEC-021]'s. The witness RefQFire has only admitted, validated firings (deposit ... = some (e.map fst))."
          "Firings are atomic: line 2 is the firing's own effect on p, with no other firing consuming from p or depositing to p between the firing's start and its completion. In the runtimes an action can be in flight while other firings consume from a shared read place or deposit to it first ([EXEC-003]; ruling D7, live intermediate marking), so the second shall sentence read of the whole interval does not hold of them; which of the two the sentence means is not ruled and is not encoded."
          "Ruling D15: the third shall sentence is lines 3 to 6. The firing lines (1 and 2) speak only of transitions with no input arc and read arc on one place (NoInputRead), because line 3 rejects every other transition when it is built, so no executor holds one. On those transitions the queue of a read place after input consumption is its queue before the firing (exec012_head_postInput), so the read sees the head 'after input consumption' ([EXEC-013] AC4) and 'the oldest token the place holds' at once; and draining a reset place comes after the peek, so a read and a reset on one place deliver the pre-drain head (line 1 reads M, before the drain; [EXEC-013])."
          "Line 1 reads 'receive, for each of its read places, the oldest token the place holds' as: every token the firing delivers at the read place is the head of its queue, the first is the head, and a single read arc on p delivers at most one token there, so a marked p with one read arc delivers exactly its head (a firing that hands the head over twice is killed as EXEC_012_mutant_noCount). How many copies a transition that declares two read arcs on one place gets is not fixed by the sentence, so for it the line constrains only which token they are. That a firing needs its read places marked is [CORE-032]'s and [CORE-022]'s; on an unmarked read place line 1 forbids a delivered token (its head is none)."
          "Line 2 is the second shall sentence and 'without consuming the tokens': the read place keeps its queue, identity and order, and the firing's deposits there follow at the tail ([EXEC-020]). A read place that is also a reset place is drained ([EXEC-013], [CORE-034]) and is excluded, as the sentence says. Keeping only the count (a firing that reorders the read place) is killed as EXEC_012_mutant_countOnly, and a read that consumes the head as EXEC_012_mutant_readConsumes."
          "Line 7 is the third shall sentence, the counterpart of line 1 at every other place: the action receives no read token from a place that is not a read place of the transition, an input, reset, inhibitor or output place included. CORE-063 cites it for its sentence that an executor hands an action read tokens only from the read places of its transition, and with EXEC-010's line 3 it gives CORE-061's delivery by arcs (core061_byArcs_of). All runtimes meet it: Rust collects the read tokens from the transition's read arcs only, into a map of its own (consume_for_firing, rust/libpetri-runtime/src/bitmap_backend.rs, and peek_reads over the read opcodes in precompiled_backend.rs); Java and TypeScript peek the head of each read arc's place in fireTransition (java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java, typescript/src/runtime/bitmap-net-executor.ts, and the read opcodes of the precompiled executors); the Python binding copies only the read places Rust delivered (rust/libpetri-py/src/action.rs). An executor that hands the consumed tokens over as read tokens too breaks line 7 (EXEC_012_forbids_mergedReads)."
          "Lines 4 to 6 are the check order and the named place. The message is msgInputRead, the fenced message with <t> the transition's name and <p> the place; exec012_msg pins the template byte for byte, and how an implementation renders <t> and <p> follows its sibling build messages (ruling D15: Java may differ only there). Line 4 names the first read arc, in declaration order, whose place is an input place (firstInputRead), when the input-arc checks that run before it pass: distinct input places ([CORE-030], InputsDistinct) and input arcs that each require at least one token ([IO-002] AC1, [IO-004] AC1; InputCountsPositive). Line 5 is 'after every input-arc check': a transition that fails one of them fails with that check's message, not this one (two input arcs on one place: the [CORE-030] stand-in, EXEC_012_forbids_early; an exactly(0) input arc: the count stand-in, EXEC_012_forbids_beforeCounts). Line 6 says the message names only an input-and-read pair: a builder that also rejects a read and a reset on one place with it is forbidden as EXEC_012_forbids_readReset."
          "'Before the output-spec checks' is encoded by line 4, which asks for this message whatever the output spec, so a transition that also breaks an output-spec check fails with this message (EXEC_012_before_output). 'Before the timing check ([TIME-001])' is quoted but not encoded: the transition of this model carries no timing (timing is TimedNet's, and TIME-001's builder is a separate contract over timings), so this builder never runs that check, and nothing here tells the order against it apart."
          "'The same place' is equality on N, read as the implementation's own Place identity ([CORE-002]): N is abstract with decidable equality (the place name in TypeScript and Rust, name and type in Java), and ToString N renders the place's name in the message. 'On every construction path' (channel merge [MOD-021], instantiation [MOD-020], fusion [MOD-061]) is not encoded: Build reads one transition definition, and the construction paths that reach it are the composition model's."
          "AC1 (read place has tokens A, B; the action receives A; both A and B remain after firing) is EXEC_012_nonvacuous: a reference firing with one input arc on place 0 and one read arc on place 1, which holds 20 then 21, delivers 20 at 1 and leaves 20, 21 there, followed by the token 30 the action emits to 1."
          "AC2 (a one() input arc and a read arc on one place is rejected with the message, and so are all(), exactly(2) and atLeast(1)) is EXEC_012_ac2, under the reference builder."
          "AC3 (inputs on a and b with reads declared b then a names b; two input arcs on p and a read on p give the CORE-030 message) is EXEC_012_ac3; the CORE-030 message is the reference builder's stand-in, which line 5 keeps apart from this message."
          "AC4 (an input on a and a read on b builds; a read and a reset on one place builds) is EXEC_012_ac4 for the witness. The statement asks of AC4's transitions only that they do not fail with this message (line 6); that they build at all is the build-time checks' (glossary: Builds), not this requirement's."
          "Without ruling D15 a read on an input place could be read as a peek before consumption. That reading (a builder with no D15 check and a firing that reads the pre-firing head on every transition) is EXEC_012_mutant_preFixReads. It is killed by the build line alone: on transitions with no input arc and read arc on one place its pre-consumption peek and RefQFire agree, as D15 intends. The reference builder without the check (exec012_buildNoCheck, refBuild as it was before ruling D15) is forbidden as EXEC_012_forbids_noCheck."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N] [ToString N], (Trans N → Option String) →
      QFireRel N T → Prop :=
    fun {N T} [DecidableEq N] [ToString N] Build Q =>
      (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
        ReadArc t p → on (fun M M' => Q t M δ e M'), shall (fun M _ =>
          (δ.reads p).head? = Head M p ∧ (∀ y ∈ δ.reads p, Head M p = some y) ∧
            (t.core.reads.count p = 1 → (δ.reads p).length ≤ 1))) ∧
      (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
        ReadArc t p → ¬ ResetArc t p →
        on (fun M M' => Q t M δ e M'), shall (fun M M' => AppendedAtTail M M' e p)) ∧
      ((∀ t : Trans N, ¬ NoInputRead t → Build t ≠ none) ∧
        (∀ (t : Trans N) (p : N), InputsDistinct t → InputCountsPositive t →
          firstInputRead t = some p → Build t = some (msgInputRead t p)) ∧
        (∀ (t : Trans N) (p : N), ¬ InputsDistinct t ∨ ¬ InputCountsPositive t →
          Build t ≠ some (msgInputRead t p)) ∧
        (∀ (t : Trans N) (p : N), NoInputRead t → Build t ≠ some (msgInputRead t p))) ∧
      (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), ¬ ReadArc t p →
        on (fun M M' => Q t M δ e M'), shall (fun _ _ => δ.reads p = []))

/- The pinned readable form of EXEC-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_012 : {N T : Type} →
  [DecidableEq N] → [ToString N] → (Reference.Trans N → Option String) → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] [ToString N] Build Q =>
  (∀ (t : Reference.Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)),
      NoInputRead t →
        ReadArc t p →
          on fun M M' => Q t M δ e M', shall fun M x =>
            (δ.reads p).head? = Head M p ∧
              (∀ y ∈ δ.reads p, Head M p = some y) ∧ (List.count p t.core.reads = 1 → (δ.reads p).length ≤ 1)) ∧
    (∀ (t : Reference.Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)),
        NoInputRead t →
          ReadArc t p → ¬ResetArc t p → on fun M M' => Q t M δ e M', shall fun M M' => AppendedAtTail M M' e p) ∧
      ((∀ (t : Reference.Trans N), ¬NoInputRead t → Build t ≠ none) ∧
          (∀ (t : Reference.Trans N) (p : N),
              InputsDistinct t →
                InputCountsPositive t → firstInputRead t = some p → Build t = some (msgInputRead t p)) ∧
            (∀ (t : Reference.Trans N) (p : N),
                ¬InputsDistinct t ∨ ¬InputCountsPositive t → Build t ≠ some (msgInputRead t p)) ∧
              ∀ (t : Reference.Trans N) (p : N), NoInputRead t → Build t ≠ some (msgInputRead t p)) ∧
        ∀ (t : Reference.Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)),
          ¬ReadArc t p → on fun M M' => Q t M δ e M', shall fun x x_1 => δ.reads p = []
-/
#guard_msgs in #print EXEC_012

/-! ### The lines, one by one -/

section Lines

variable {N T : Type} [DecidableEq N]

/-- Line 1 of EXEC-012 for the relation `Q`. -/
def exec012_line1 (Q : QFireRel N T) : Prop :=
  ∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
    ReadArc t p → on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      (δ.reads p).head? = Head M p ∧ (∀ y ∈ δ.reads p, Head M p = some y) ∧
        (t.core.reads.count p = 1 → (δ.reads p).length ≤ 1))

/-- Line 2 of EXEC-012 for the relation `Q`. -/
def exec012_line2 (Q : QFireRel N T) : Prop :=
  ∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
    ReadArc t p → ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' => AppendedAtTail M M' e p)

/-- Lines 3 to 6 of EXEC-012 (the build rule of ruling D15) for the builder `Build`. -/
def exec012_buildLines [ToString N] (Build : Trans N → Option String) : Prop :=
  (∀ t : Trans N, ¬ NoInputRead t → Build t ≠ none) ∧
  (∀ (t : Trans N) (p : N), InputsDistinct t → InputCountsPositive t →
    firstInputRead t = some p → Build t = some (msgInputRead t p)) ∧
  (∀ (t : Trans N) (p : N), ¬ InputsDistinct t ∨ ¬ InputCountsPositive t →
    Build t ≠ some (msgInputRead t p)) ∧
  (∀ (t : Trans N) (p : N), NoInputRead t → Build t ≠ some (msgInputRead t p))

/-- Line 7 of EXEC-012 for the relation `Q`: no read token from a place that is not a read
place. -/
def exec012_line7 (Q : QFireRel N T) : Prop :=
  ∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), ¬ ReadArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun _ _ => δ.reads p = [])

/-- EXEC-012 is its four parts. -/
theorem exec012_iff [ToString N] (Build : Trans N → Option String) (Q : QFireRel N T) :
    EXEC_012 Build Q ↔
      exec012_line1 Q ∧ exec012_line2 Q ∧ exec012_buildLines Build ∧ exec012_line7 Q :=
  Iff.rfl

/-- Line 7 holds of every relation that delivers the reference reads, or the reference reads
repeated: the reference delivers no read token off the read places (`qDelivered_reads_off`). -/
theorem exec012_line7_of {Q : QFireRel N T}
    (hQ : ∀ t M δ e M', Q t M δ e M' → ∀ p, ¬ ReadArc t p → δ.reads p = []) :
    exec012_line7 Q :=
  fun t p δ e hp M M' h => hQ t M δ e M' h p hp

omit [DecidableEq N] in
/-- One head per read arc, as the reference delivers it: the first is the head, every token is
the head, and one read arc delivers at most one token. -/
theorem exec012_replicate_head (n : Nat) (hn : 0 < n) (o : Option T) :
    ((List.replicate n o.toList).flatten).head? = o ∧
      (∀ y ∈ (List.replicate n o.toList).flatten, o = some y) ∧
      (n = 1 → ((List.replicate n o.toList).flatten).length ≤ 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, fun h1 => ?_⟩
  · cases o with
    | none => simp
    | some a => simp [List.replicate_succ]
  · intro y hy
    cases o with
    | none => simp at hy
    | some a =>
      simp only [Option.toList_some, List.mem_flatten, List.mem_replicate] at hy
      obtain ⟨l, ⟨-, rfl⟩, hy⟩ := hy
      simp only [List.mem_singleton] at hy
      rw [hy]
  · obtain rfl : k = 0 := by omega
    cases o <;> simp

/-- **Read after consumption is read before.** On a transition with no input arc and read arc
on one place, input consumption leaves a read place's queue as it was, so the head the reference
peeks after consumption ([EXEC-013] AC4) is the head before the firing. -/
theorem exec012_head_postInput {t : Trans N} (hw : NoInputRead t) {p : N} (hp : ReadArc t p)
    (M : QueueMarking N T) : qPostInput M t p = M p := by
  apply qPostInput_of_none
  unfold nspecAt
  rw [List.find?_eq_none]
  intro s hs he
  have : s.place = p := by simpa using he
  exact hw s hs (this ▸ hp)

/-- Line 1 holds of every relation that delivers what the reference delivers. -/
theorem exec012_line1_of {Q : QFireRel N T}
    (hQ : ∀ t M δ e M', Q t M δ e M' → δ = qDelivered M t) : exec012_line1 Q := by
  intro t p δ e hw hp M M' h
  rw [hQ _ _ _ _ _ h]
  show (qReads M t p).head? = Head M p ∧ (∀ y ∈ qReads M t p, Head M p = some y) ∧
    (t.core.reads.count p = 1 → (qReads M t p).length ≤ 1)
  rw [qReads_noInputRead hw]
  exact exec012_replicate_head _ (List.count_pos_iff.mpr hp) _

/-- The reference builder, which runs the count checks and the D15 check, satisfies lines 3
to 6. -/
theorem refBuild_lines [ToString N] : exec012_buildLines (refBuild (N := N)) := by
  refine ⟨fun t hw h => hw ((refBuild_eq_none_iff t).1 h).1.2.2, fun t p hi hc hf => ?_,
    fun t p hn => ?_, fun t p hw => ?_⟩
  · unfold refBuild
    rw [if_neg (not_not.mpr hi), if_neg (not_not.mpr hc), hf]
  · unfold refBuild
    by_cases hi : InputsDistinct t
    · have hc : ¬ InputCountsPositive t := hn.resolve_left (not_not.mpr hi)
      rw [if_neg (not_not.mpr hi), if_pos hc]
      intro h
      exact msgCount_ne_msgInputRead t p (Option.some.inj h)
    · rw [if_pos hi]
      intro h
      exact core030_msg_ne_msgInputRead t p (Option.some.inj h)
  · by_cases hi : InputsDistinct t
    · by_cases hc : InputCountsPositive t
      · rw [refBuild_of_pre ⟨hi, hc, hw⟩]
        split
        · simp
        · exact checkOut_ne_msgInputRead t _ _ p
      · unfold refBuild
        rw [if_neg (not_not.mpr hi), if_pos hc]
        intro h
        exact msgCount_ne_msgInputRead t p (Option.some.inj h)
    · unfold refBuild
      rw [if_pos hi]
      intro h
      exact core030_msg_ne_msgInputRead t p (Option.some.inj h)

end Lines

/-- ✓ The reference pair satisfies EXEC-012: `RefQFire` delivers at a read place the head of the
queue after input consumption (`qReads`), which on a transition with no input arc and read arc on
one place is the head before the firing (`exec012_head_postInput`), one copy per read arc (line
1); it drains only reset places and appends the emitted tokens at the tail, so a read place that
is not a reset place keeps its queue (line 2, `refQFire_read_kept`); and `refBuild` rejects
every transition with an input arc and a read arc on one place, with the D15 message after the
[CORE-030] and count checks and before the output-spec checks, and never with that message
otherwise (lines 3 to 6); it delivers no read token off the read places
(`qDelivered_reads_off`, line 7). -/
@[evidence holds EXEC_012]
theorem EXEC_012_reference {N T : Type} [DecidableEq N] [ToString N] :
    EXEC_012 refBuild (RefQFire (N := N) (T := T)) :=
  ⟨exec012_line1_of (fun _ _ _ _ _ h => h.2.2.1),
    fun _ _ _ _ hw hp hr _ _ h => refQFire_read_kept hw h hp hr, refBuild_lines,
    exec012_line7_of fun t M δ e M' h p hp => by
      obtain ⟨-, -, rfl, -⟩ := h
      exact qDelivered_reads_off M t hp⟩

/-! ### Examples -/

/-- The transition of AC1: one `one()` input arc on place `0`, one read arc on place `1`, and
output place `1`, so the firing deposits into its read place. -/
def exec012_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := some (.place 1) }

/-- The queue marking of the examples: place `0` holds `10, 11`, place `1` holds `20, 21`
(added in that order), every other place nothing. -/
def exec012_M : QueueMarking Nat Nat :=
  fun p => if p = 0 then [10, 11] else if p = 1 then [20, 21] else []

/-- The emission of the examples: one token `30` to place `1`. -/
def exec012_e : List (Nat × Nat) := [(1, 30)]

/-- ✓ AC1 under the reference: `exec012_t` fires from `exec012_M`, delivers `20` (the head of
place `1`) as its read token and `10` as its input token, and leaves `20, 21` in place `1`,
followed by the emitted `30`, and `11` in place `0`. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_nonvacuous :
    NoInputRead exec012_t ∧ ReadArc exec012_t 1 ∧ ¬ ResetArc exec012_t 1 ∧
      RefQFire exec012_t exec012_M (qDelivered exec012_M exec012_t) exec012_e
        (qFire exec012_M exec012_t exec012_e) ∧
      (qDelivered exec012_M exec012_t).reads 1 = [20] ∧
      (qDelivered exec012_M exec012_t).inputs 0 = [10] ∧
      qFire exec012_M exec012_t exec012_e 1 = [20, 21, 30] ∧
      qFire exec012_M exec012_t exec012_e 0 = [11] ∧
      refBuild exec012_t = none :=
  ⟨by decide, by decide, by decide, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide,
    by decide, by decide, by decide, rfl⟩

/-- A transition named `t` with input arcs `ins`, read arcs `rs`, reset arcs `zs` and output
spec `o`. -/
def exec012_mk (ins : List (NInSpec Nat)) (rs zs : List Nat) (o : Option (Out Nat)) :
    Trans Nat :=
  { core := { name := "t", inputs := ins, inhibitors := [], reads := rs, resets := zs }, out := o }

/-- AC2's transition: an input arc of cardinality `c` and a read arc, both on place `0`. -/
def exec012_ir (c : Card) : Trans Nat := exec012_mk [⟨0, c⟩] [0] [] none

set_option maxRecDepth 8000 in
/-- The message pinned against the spec's fenced block, for `<t>` = `t` and `<p>` = `0`. -/
theorem exec012_msg :
    msgInputRead (exec012_ir .one) 0 = "Transition 't' declares an input arc and a read arc on place '0'. A read of a place the same firing consumes from has no coherent semantics and is rejected (EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the action." := by
  decide

/-- ✓ AC2: an input arc and a read arc on place `0` are rejected with the message naming `0`,
whether the input arc is `one()`, `all()`, `exactly(2)` or `atLeast(1)`. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_ac2 :
    refBuild (exec012_ir .one) = some (msgInputRead (exec012_ir .one) 0) ∧
      refBuild (exec012_ir .all) = some (msgInputRead (exec012_ir .all) 0) ∧
      refBuild (exec012_ir (.exactly 2)) = some (msgInputRead (exec012_ir (.exactly 2)) 0) ∧
      refBuild (exec012_ir (.atLeast 1)) = some (msgInputRead (exec012_ir (.atLeast 1)) 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- AC3's first transition: input arcs on `a = 0` and `b = 1`, read arcs declared on `b`, then
`a`. -/
def exec012_ab : Trans Nat := exec012_mk [⟨0, .one⟩, ⟨1, .one⟩] [1, 0] [] none

/-- AC3's second transition: two input arcs on place `0` and a read arc on `0`. -/
def exec012_dup : Trans Nat := exec012_mk [⟨0, .one⟩, ⟨0, .one⟩] [0] [] none

/-- ✓ AC3: the message names `b`, the first read arc in declaration order whose place is an
input place; and two input arcs on `p` with a read arc on `p` fail with the [CORE-030] message
(the reference builder's stand-in), not this one, for any place. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_ac3 :
    refBuild exec012_ab = some (msgInputRead exec012_ab 1) ∧
      refBuild exec012_dup = some "CORE-030" ∧
      ∀ p, refBuild exec012_dup ≠ some (msgInputRead exec012_dup p) :=
  ⟨rfl, rfl, fun p h => core030_msg_ne_msgInputRead exec012_dup p (Option.some.inj h)⟩

/-- ✓ AC4: an input arc on `a = 0` with a read arc on `b = 1` builds, and so does a read arc and
a reset arc on one place. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_ac4 :
    refBuild (exec012_mk [⟨0, .one⟩] [1] [] none) = none ∧
      refBuild (exec012_mk [] [0] [0] none) = none :=
  ⟨rfl, rfl⟩

/-- A transition with an input arc and a read arc on place `0` and an output spec that names
place `2` twice in one branch ([IO-011]). -/
def exec012_irDup : Trans Nat :=
  exec012_mk [⟨0, .one⟩] [0] [] (some (.and (.place 2) (.place 2)))

/-- ✓ The D15 check runs before the output-spec checks: a transition that breaks both fails with
this message, where the builder without the check fails with [IO-011]'s. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_before_output :
    refBuild exec012_irDup = some (msgInputRead exec012_irDup 0) ∧
      exec012_buildNoCheck exec012_irDup = some (msgDup exec012_irDup 2) :=
  ⟨rfl, rfl⟩

/-! ### Builders the build lines forbid -/

/-- ✗ The reference builder without the D15 check violates line 3: it builds AC2's transition. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_noCheck :
    ¬ EXEC_012 exec012_buildNoCheck (RefQFire (N := Nat) (T := Nat)) :=
  fun h => h.2.2.1.1 (exec012_ir .one) (by decide) rfl

/-- A builder that names the place of the **last** read arc on an input place. -/
def exec012_buildLast (t : Trans Nat) : Option String :=
  if InputsDistinct t then
    match (t.core.reads.reverse.find? (fun p => decide (p ∈ inPlaces t))) with
    | some p => some (msgInputRead t p)
    | none => refBuild t
  else refBuild t

/-- ✗ A builder that names the last read arc on an input place violates line 4: on AC3's
transition it names `a`, not `b`. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_last : ¬ EXEC_012 exec012_buildLast (RefQFire (N := Nat) (T := Nat)) := by
  intro h
  have := h.2.2.1.2.1 exec012_ab 1 (by decide) (by decide) rfl
  revert this
  decide

/-- A builder that runs the D15 check **before** [CORE-030]'s. -/
def exec012_buildEarly (t : Trans Nat) : Option String :=
  match firstInputRead t with
  | some p => some (msgInputRead t p)
  | none => refBuild t

/-- ✗ A builder that runs the D15 check before the [CORE-030] check violates line 5: on AC3's
second transition it fails with this message instead of [CORE-030]'s. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_early :
    ¬ EXEC_012 exec012_buildEarly (RefQFire (N := Nat) (T := Nat)) :=
  fun h => h.2.2.1.2.2.1 exec012_dup 0 (.inl (by decide)) rfl

/-- A builder that runs the D15 check **before** the [IO-002]/[IO-004] count checks. -/
def exec012_buildBeforeCounts (t : Trans Nat) : Option String :=
  if InputsDistinct t then
    match firstInputRead t with
    | some p => some (msgInputRead t p)
    | none => refBuild t
  else refBuild t

/-- ✗ A builder that runs the D15 check before the count checks violates line 5: an
`exactly(0)` input arc and a read arc on place `0` fail with this message instead of the count
check's. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_beforeCounts :
    ¬ EXEC_012 exec012_buildBeforeCounts (RefQFire (N := Nat) (T := Nat)) :=
  fun h => h.2.2.1.2.2.1 (exec012_ir (.exactly 0)) 0 (.inr (by decide)) rfl

/-- A transition with a read arc and a reset arc on place `0` and no input arc (AC4). -/
def exec012_rr : Trans Nat := exec012_mk [] [0] [0] none

/-- A builder that also rejects, with this message, the first read arc whose place is a reset
place, on a transition with no input arc and read arc on one place. -/
def exec012_buildReadReset (t : Trans Nat) : Option String :=
  match firstInputRead t with
  | some _ => refBuild t
  | none =>
    match t.core.reads.find? (fun p => decide (p ∈ t.core.resets)) with
    | some p => some (msgInputRead t p)
    | none => refBuild t

/-- ✗ A builder that rejects a read and a reset on one place with this message violates line 6:
AC4's second transition has no input arc and read arc on one place. Lines 3 to 5 alone allow
it. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_readReset :
    ¬ EXEC_012 exec012_buildReadReset (RefQFire (N := Nat) (T := Nat)) :=
  fun h => h.2.2.1.2.2.2 exec012_rr 0 (by decide) rfl

/-! ### Mutants: each changes one reading, and a pair tells it apart from EXEC-012 -/

section Mutants

variable {N T : Type} [DecidableEq N]

/-- A queue firing that peeks its read places **before** input consumption, on every
transition: the reference, with the read bag taken from the queue marking before the firing. -/
def exec012_preFixQ : QFireRel N T := fun t M δ e M' =>
  enabledNA (qCount M) t.core = true ∧
    (∃ ch, deposit (nconsumed (qCount M) t.core) t.out ch = some (e.map Prod.fst)) ∧
    δ = ⟨qInputs M t, qReadsBag M t.core.reads⟩ ∧ M' = qFire M t e

/-- Mutant reading of EXEC-012 without ruling D15: a read on an input place peeks the queue
before the firing's consumption, on every transition, and the builder accepts every transition
the reference builder accepts, the pair of an input arc and a read arc on one place among them. -/
def EXEC_012_mutant_preFixReads [ToString N] (Build : Trans N → Option String)
    (Q : QFireRel N T) : Prop :=
  (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), ReadArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      (δ.reads p).head? = Head M p ∧ (∀ y ∈ δ.reads p, Head M p = some y) ∧
        (t.core.reads.count p = 1 → (δ.reads p).length ≤ 1))) ∧
  exec012_line2 Q ∧ (∀ t, exec012_buildNoCheck t = none → Build t = none)

/-- The pre-consumption peek with the builder without the D15 check kills the mutant: it
satisfies it, but EXEC-012 rejects AC2's transition, which that builder builds. -/
@[evidence mutant EXEC_012]
theorem EXEC_012_mutant_preFixReads_killed :
    EXEC_012_mutant_preFixReads exec012_buildNoCheck (exec012_preFixQ (N := Nat) (T := Nat)) ∧
      ¬ EXEC_012 exec012_buildNoCheck (exec012_preFixQ (N := Nat) (T := Nat)) := by
  refine ⟨⟨fun t p δ e hp M M' h => ?_, fun t p δ e hw hp hr M M' h => ?_, fun _ h => h⟩,
    fun h => h.2.2.1.1 (exec012_ir .one) (by decide) rfl⟩
  · rw [h.2.2.1]
    show (qReadsBag M t.core.reads p).head? = Head M p ∧
      (∀ y ∈ qReadsBag M t.core.reads p, Head M p = some y) ∧
      (t.core.reads.count p = 1 → (qReadsBag M t.core.reads p).length ≤ 1)
    rw [qReadsBag_apply]
    exact exec012_replicate_head _ (List.count_pos_iff.mpr hp) _
  · exact refQFire_read_kept hw ⟨h.1, h.2.1, rfl, h.2.2.2⟩ hp hr

/-- A queue firing whose read **consumes** the head: the reference, except that each read place
that is not a reset place also loses its head. -/
def exec012_consumeQ : QFireRel N T := fun t M δ e M' =>
  enabledNA (qCount M) t.core = true ∧
    (∃ ch, deposit (nconsumed (qCount M) t.core) t.out ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧
    M' = qAppend (fun q => if q ∈ t.core.reads ∧ q ∉ t.core.resets then (qConsume M t q).drop 1
      else qConsume M t q) e

/-- Mutant reading of EXEC-012 in which a read consumes the token it delivers: a read place that
is not a reset place ends the firing without its head, followed by the deposited tokens. -/
def EXEC_012_mutant_readConsumes [ToString N] (Build : Trans N → Option String)
    (Q : QFireRel N T) : Prop :=
  exec012_line1 Q ∧
  (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
    ReadArc t p → ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' => M' p = (M p).drop 1 ++ EmittedTo e p)) ∧
  exec012_buildLines Build ∧ exec012_line7 Q

/-- The consuming read kills the mutant: it satisfies it, but `exec012_t` fired from
`exec012_M` leaves only `21` of the read place's `20, 21`, where EXEC-012 keeps both. -/
@[evidence mutant EXEC_012]
theorem EXEC_012_mutant_readConsumes_killed :
    EXEC_012_mutant_readConsumes refBuild (exec012_consumeQ (N := Nat) (T := Nat)) ∧
      ¬ EXEC_012 refBuild (exec012_consumeQ (N := Nat) (T := Nat)) := by
  refine ⟨⟨exec012_line1_of (fun _ _ _ _ _ h => h.2.2.1),
    fun t p δ e hw hp hr M M' h => ?_, refBuild_lines,
    exec012_line7_of fun _ M _ _ _ h p hp => by
      rw [h.2.2.1]; exact qDelivered_reads_off M _ hp⟩, fun h => ?_⟩
  · dsimp only at h ⊢
    rw [h.2.2.2, qAppend_apply]
    have hc : qConsume M t p = M p := by
      unfold qConsume
      rw [if_neg hr]
      exact exec012_head_postInput hw hp M
    simp only [if_pos (And.intro hp hr), hc]
  · have := h.2.1 exec012_t 1 _ exec012_e (by decide) (by decide) (by decide) exec012_M _
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
    dsimp only [AppendedAtTail] at this
    revert this
    decide

/-- A queue firing that keeps the tokens of a read place but **reverses** their order: the
reference, except that each read place that is not a reset place is reversed. -/
def exec012_reverseQ : QFireRel N T := fun t M δ e M' =>
  enabledNA (qCount M) t.core = true ∧
    (∃ ch, deposit (nconsumed (qCount M) t.core) t.out ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧
    M' = qAppend (fun q => if q ∈ t.core.reads ∧ q ∉ t.core.resets then (qConsume M t q).reverse
      else qConsume M t q) e

/-- Mutant reading of EXEC-012 that keeps only the count of a read place: it ends the firing
holding as many tokens as before plus the deposited ones, in any order. -/
def EXEC_012_mutant_countOnly [ToString N] (Build : Trans N → Option String)
    (Q : QFireRel N T) : Prop :=
  exec012_line1 Q ∧
  (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
    ReadArc t p → ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      (M' p).length = (M p).length + (EmittedTo e p).length)) ∧
  exec012_buildLines Build ∧ exec012_line7 Q

/-- The reversing firing kills the count-only mutant: it keeps every count, but `exec012_t` fired
from `exec012_M` leaves `21, 20` in the read place, where EXEC-012 keeps the queue order
`20, 21`. -/
@[evidence mutant EXEC_012]
theorem EXEC_012_mutant_countOnly_killed :
    EXEC_012_mutant_countOnly refBuild (exec012_reverseQ (N := Nat) (T := Nat)) ∧
      ¬ EXEC_012 refBuild (exec012_reverseQ (N := Nat) (T := Nat)) := by
  refine ⟨⟨exec012_line1_of (fun _ _ _ _ _ h => h.2.2.1),
    fun t p δ e hw hp hr M M' h => ?_, refBuild_lines,
    exec012_line7_of fun _ M _ _ _ h p hp => by
      rw [h.2.2.1]; exact qDelivered_reads_off M _ hp⟩, fun h => ?_⟩
  · dsimp only at h ⊢
    rw [h.2.2.2, qAppend_apply]
    have hc : qConsume M t p = M p := by
      unfold qConsume
      rw [if_neg hr]
      exact exec012_head_postInput hw hp M
    simp only [if_pos (And.intro hp hr), hc, List.length_append, List.length_reverse]
  · have := h.2.1 exec012_t 1 _ exec012_e (by decide) (by decide) (by decide) exec012_M _
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
    dsimp only [AppendedAtTail] at this
    revert this
    decide

/-- A queue firing that hands each read token over **twice**: the reference, with every read
place's delivery doubled. -/
def exec012_doubleQ : QFireRel N T := fun t M δ e M' =>
  enabledNA (qCount M) t.core = true ∧
    (∃ ch, deposit (nconsumed (qCount M) t.core) t.out ch = some (e.map Prod.fst)) ∧
    δ = ⟨qInputs M t, fun p => qReads M t p ++ qReads M t p⟩ ∧ M' = qFire M t e

/-- Mutant reading of EXEC-012 that fixes which token a read delivers but not how many: line 1
without its count clause. -/
def EXEC_012_mutant_noCount [ToString N] (Build : Trans N → Option String)
    (Q : QFireRel N T) : Prop :=
  (∀ (t : Trans N) (p : N) (δ : Delivered N T) (e : List (N × T)), NoInputRead t →
    ReadArc t p → on (fun M M' => Q t M δ e M'), shall (fun M _ =>
      (δ.reads p).head? = Head M p ∧ ∀ y ∈ δ.reads p, Head M p = some y)) ∧
  exec012_line2 Q ∧ exec012_buildLines Build ∧ exec012_line7 Q

/-- The doubling firing kills the mutant: every token it delivers is the head, but `exec012_t`,
with one read arc on place `1`, gets `20, 20` from `exec012_M` where EXEC-012 hands over one
`20`. -/
@[evidence mutant EXEC_012]
theorem EXEC_012_mutant_noCount_killed :
    EXEC_012_mutant_noCount refBuild (exec012_doubleQ (N := Nat) (T := Nat)) ∧
      ¬ EXEC_012 refBuild (exec012_doubleQ (N := Nat) (T := Nat)) := by
  refine ⟨⟨fun t p δ e hw hp M M' h => ?_, fun t p δ e hw hp hr M M' h => ?_,
    refBuild_lines, exec012_line7_of fun _ M _ _ _ h p hp => by
      rw [h.2.2.1]
      show qReads M _ p ++ qReads M _ p = []
      rw [show qReads M _ p = [] from qDelivered_reads_off M _ hp]; rfl⟩, fun h => ?_⟩
  · rw [h.2.2.1]
    show (qReads M t p ++ qReads M t p).head? = Head M p ∧
      ∀ y ∈ qReads M t p ++ qReads M t p, Head M p = some y
    rw [qReads_noInputRead hw]
    obtain ⟨h1, h2, -⟩ := exec012_replicate_head (t.core.reads.count p)
      (List.count_pos_iff.mpr hp) (M p).head?
    refine ⟨?_, fun y hy => ?_⟩
    · rw [List.head?_append, h1]
      show _ = (M p).head?
      cases (M p).head? <;> rfl
    · rcases List.mem_append.mp hy with hy | hy <;> exact h2 y hy
  · exact refQFire_read_kept hw ⟨h.1, h.2.1, rfl, h.2.2.2⟩ hp hr
  · have := (h.1 exec012_t 1 _ exec012_e (by decide) (by decide) exec012_M _
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩).2.2 (by decide)
    revert this
    decide

end Mutants

/-! ### Line 7: read tokens only from read places -/

/-- An executor that hands the consumed tokens over as read tokens too: the reference firing, with
the consumed tokens added to the read ones at every place (Java's and TypeScript's shared
`rawInput` without the read gate). -/
def exec012_mergedReads : QFireRel Nat Nat := fun t M δ e M' =>
  ∃ δ₀, RefQFire t M δ₀ e M' ∧ δ = ⟨δ₀.inputs, fun p => δ₀.reads p ++ δ₀.inputs p⟩

/-- ✗ Handing the consumed tokens over as read tokens violates EXEC-012 (line 7): firing
`exec012_t` from `exec012_M` delivers `10` as a read token from the input place `0`, which is not
a read place. -/
@[evidence forbids EXEC_012]
theorem EXEC_012_forbids_mergedReads : ¬ EXEC_012 refBuild exec012_mergedReads := by
  intro h
  have := h.2.2.2 exec012_t 0 _ exec012_e (by decide) exec012_M
    (qFire exec012_M exec012_t exec012_e) ⟨_, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl⟩
  revert this
  decide

/-- Line 7 on the reference: firing `exec012_t` from `exec012_M` delivers the read token `20` at
the read place `1` and no read token at the input place `0`, from which it consumes `10`. -/
@[evidence nonvacuous EXEC_012]
theorem EXEC_012_nonvacuous_offReads :
    ¬ ReadArc exec012_t 0 ∧ (qDelivered exec012_M exec012_t).reads 0 = [] ∧
      (qDelivered exec012_M exec012_t).inputs 0 = [10] ∧
      (qDelivered exec012_M exec012_t).reads 1 = [20] ∧
      RefQFire exec012_t exec012_M (qDelivered exec012_M exec012_t) exec012_e
        (qFire exec012_M exec012_t exec012_e) :=
  ⟨by decide, by decide, by decide, by decide, ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩⟩

end Libpetri.Spec
