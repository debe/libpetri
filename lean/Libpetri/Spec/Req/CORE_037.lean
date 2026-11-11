import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# CORE-037: Dead arc warning (`spec/01-core-model.md`)

CORE-037 has two parts. What a dead arc is, the order in which dead arcs are listed and the text
of one warning are a pure function of the net, its initial marking and its environment places:
this block (kind F). That the executors log one event per dead arc when they are constructed
and that the verifier writes one report line per dead arc, changing no verdict, needs the event
model and the verifier pipeline; it is the second block of this ID (kind B, wave W11).

The requirement is a predicate over a pair `(Rep, Msg)`, on nets whose places are their names
(ruling D10):

* `Rep : DeadArcReport String`, the dead-arc report: from a net, its environment places (as a
  predicate on places) and its initial marking (as token counts) to the list of dead arcs;
* `Msg : DeadArc String → String`, the warning text of one arc entry.

The witness pair is `refDeadArcs` (every read, inhibitor and reset arc of the net in report
order, `deadArcCandidates`, kept when its place is dead) and `refDeadArcMsg`. The statement is
checked against the witness pair; against reports that ignore the initial marking, ignore the
environment places, count producers only, read only a top-level output place, skip the
`Timeout` child, skip the `ForwardInput` target, count a reset arc as consuming or keep one entry
per place; against reports in kind order across transitions, in another kind order within a
transition or in reverse arc order within a kind; and against texts that swap two effects,
change the reset effect, swap the transition and the place or print a place record instead of
the place name. Every pair that satisfies the first two lines lists exactly the reference report
(`CORE_037_unique`).

The justification sentence of the section ("No firing ever puts a token on such a place, …") is
proved of the reference firing semantics: a dead place is empty in every reachable marking
(`core037_dead_stays_empty`), so a dead read arc's transition is never enabled, a dead inhibitor
never blocks and a dead reset clears nothing.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model -/

/-- The three arc kinds a dead-arc warning can name. -/
inductive DeadArcKind where
  /-- A read arc ([CORE-032]). -/
  | read
  /-- An inhibitor arc ([CORE-031]). -/
  | inhibitor
  /-- A reset arc ([CORE-034]). -/
  | reset
  deriving DecidableEq, Repr

/-- One entry of the dead-arc report: the arc's kind, the name of the transition that declares
it and its place. -/
structure DeadArc (N : Type) where
  /-- The arc's kind. -/
  kind : DeadArcKind
  /-- The name of the transition that declares the arc. -/
  transition : String
  /-- The arc's place. -/
  place : N
  deriving DecidableEq, Repr

/-- A dead-arc report: the net, its environment places as a predicate (`true`: an environment
place) and its initial marking as token counts, to the list of dead arcs. -/
abbrev DeadArcReport (N : Type) : Type :=
  Reference.Net N → (N → Bool) → (N → Nat) → List (DeadArc N)

variable {N : Type}

/-- A place some transition of the net consumes from or produces into: an input arc of some
transition is on it, or some transition's output spec names it anywhere in its tree (every `And`
and `Xor` branch, the `Timeout` child and the `ForwardInput` target included: `outPlaces`). -/
def ConnectedPlace (X : Reference.Net N) (p : N) : Prop :=
  ∃ t ∈ X.transitions, p ∈ inPlaces t ∨ OutputArc t p

/-- **Dead place** ([CORE-037]): no transition consumes from or produces into it, it is not an
environment place, and the initial marking holds no token on it. -/
def DeadPlace (X : Reference.Net N) (env : N → Bool) (m0 : N → Nat) (p : N) : Prop :=
  ¬ ConnectedPlace X p ∧ env p = false ∧ m0 p = 0

/-- Every read, inhibitor and reset arc of the net, one entry per arc, in report order: the
transitions in the order the net holds them, within a transition its read arcs, then its
inhibitor arcs, then its reset arcs, each kind in the order the transition lists them. -/
def deadArcCandidates (X : Reference.Net N) : List (DeadArc N) :=
  X.transitions.flatMap fun t =>
    t.core.reads.map (⟨.read, t.core.name, ·⟩) ++
      t.core.inhibitors.map (⟨.inhibitor, t.core.name, ·⟩) ++
      t.core.resets.map (⟨.reset, t.core.name, ·⟩)

/-- `ConnectedPlace`, computed: one pass over the input places and the output-spec places. -/
def connectedB [DecidableEq N] (X : Reference.Net N) (p : N) : Bool :=
  X.transitions.any fun t =>
    decide (p ∈ inPlaces t) || (match t.out with | some o => decide (p ∈ outPlaces o) | none => false)

/-- `DeadPlace`, computed. -/
def deadB [DecidableEq N] (X : Reference.Net N) (env : N → Bool) (m0 : N → Nat) (p : N) : Bool :=
  !connectedB X p && !env p && decide (m0 p = 0)

/-- The reference report: the arcs of `deadArcCandidates` whose place is dead (the shape of
`dead_arcs` in the Rust core crate's dead_arcs module, `typescript/src/core/internal/dead-arcs.ts`
`findDeadArcs` and `ArcDiagnostics.deadArcs` in Java). -/
def refDeadArcs [DecidableEq N] : DeadArcReport N :=
  fun X env m0 => (deadArcCandidates X).filter fun a => deadB X env m0 a.place

/-- The reference warning text of one arc entry (`DeadArc::message` in Rust, which writes
`place.name()`): the place is its name. -/
def refDeadArcMsg : DeadArc String → String
  | ⟨.read, t, p⟩ => "read arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the transition can never be enabled."
  | ⟨.inhibitor, t, p⟩ => "inhibitor arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the arc never blocks."
  | ⟨.reset, t, p⟩ => "reset arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the arc has no effect."

#spec_witness refDeadArcs
#spec_witness refDeadArcMsg

/-! ## CORE-037: Dead arc warning -/

requirement CORE_037
  id "CORE-037"
  title "Dead Arc Warning"
  kind F
  scope "the dead-arc report of every executor backend and of the SMT verifier; the events and report lines are the second block of this ID"
  source verbatim "spec/01-core-model.md"
  quote "The dead-arc report *shall* contain a read, inhibitor or reset arc of a transition of the net exactly when no transition has an input arc on the arc's place, no transition's output spec names that place anywhere in its tree (every `And` and `Xor` branch, the `Timeout` child and the `ForwardInput` target included), the place is not an environment place and the initial marking holds no token on it, and *shall* contain nothing else."
        "The dead-arc report *shall* list each dead arc once, as its own entry (two dead arcs on one place are two entries), in the order the net holds its transitions (the order they were added to the builder) and, within a transition, its read arcs, then its inhibitor arcs, then its reset arcs, each kind in the order the transition declares those arcs."
        "The warning text of a read, inhibitor or reset arc of a transition *shall* be `<kind> arc of '<transition>' on '<place>': no transition produces into or consumes from it and it starts empty; <effect>.` with `<kind>` the arc's kind (`read`, `inhibitor` or `reset`), `<transition>` the name of the transition that declares the arc, `<place>` the name of its place, and `<effect>` `the transition can never be enabled` for a read arc, `the arc never blocks` for an inhibitor arc and `the arc has no effect` for a reset arc."
  reading "For every dead-arc report Rep and warning text Msg on nets whose places are their names:"
          "for every net X, environment places env and initial marking m0, an entry is in Rep X env m0 exactly when some transition t of X carries the entry's transition name and has an arc of the entry's kind on the entry's place, and that place is dead: no transition of X has an input arc on it or names it anywhere in its output spec (outPlaces: both children of an And, both branches of an Xor, the Timeout child, the target of a ForwardInput), env does not hold it and m0 puts no token on it;"
          "Rep X env m0 is the list of every read, inhibitor and reset arc of X in report order (deadArcCandidates: the transitions in the order X holds them, within a transition its read, then inhibitor, then reset arcs, each kind in the transition's own order), keeping exactly the entries Rep X env m0 holds, each as often as X lists it;"
          "the warning text of a read arc entry (t, p) is the template with kind `read`, the transition name t, the place name p and effect `the transition can never be enabled`;"
          "the warning text of an inhibitor arc entry is the template with kind `inhibitor` and effect `the arc never blocks`;"
          "the warning text of a reset arc entry is the template with kind `reset` and effect `the arc has no effect`."
  assumes "The model is a pair: a dead-arc report Rep from a net (Reference.Net String: its transitions, in order), its environment places (a predicate on places) and its initial marking (token counts) to a list of entries (kind, name of the declaring transition, place), and a warning text Msg of one entry. The environment places and the initial marking are parameters, as in all three runtimes (`dead_arcs` in the dead_arcs module of the Rust core crate, `findDeadArcs` in typescript/src/core/internal/dead-arcs.ts, `ArcDiagnostics.deadArcs` in Java): an executor passes the environment places registered for the run and the initial marking it was given, the verifier its own initial marking and environment places ([VER-001]). 'Starts empty' and 'the initial marking holds no token' are m0 p = 0."
          "Places and transitions are identified by name (ruling D10), so a place of the model is its name and `<place>` in the text is that string, written as is. A text that prints some other rendering of the place, such as a Java Place record, is killed (CORE_037_forbids_recordMsg). Java tests whether a place is fed on its Place record (name and token type, the divergence MOD-024 records), Rust and TypeScript on its name; a net with two same-named places of different token types is that divergence and is not encoded. Lines 1 and 2 hold of refDeadArcs at every place type (core037_line1_ref, core037_line2_ref)."
          "Transition order is the order of the net's transition list. That this list is the order in which the transitions were added to the builder is CORE-040's line under ruling D32 (wave W2, RefNetBuild); the W2 integrator may then add a [CORE-040] link to the second sentence. Within one kind the order is the transition's own arc list (NTransition.reads, inhibitors, resets), which is the order the transition declares the arcs in all three runtimes. A transition that lists one place twice under one arc kind declares two arcs, and line 2 lists both, which is the sentence's 'each dead arc once, as its own entry'; whether a builder accepts such a transition is not this block's subject."
          "The text lines fix Msg on every read, inhibitor and reset arc entry, dead or not, as the third sentence says: the text is a pure template of the entry, and an implementation uses it only for the entries of the report."
          "The output-spec clause of line 1 is outPlaces: the place of a Place node, both children of an And, both branches of an Xor, the child of a Timeout and the target of a ForwardInput. The source of a ForwardInput is not named by the output spec; IO-014 requires it to be an input place of the transition, so the input-arc clause covers it."
          "The section's definition is its bullets (ruling D20, clash core-b#1): the lead-in ends at 'is dead when:', because 'nothing can ever put a token on P' is not equivalent: a place with an input arc but no producer, no initial token and no injection also stays empty for the whole run, yet its read arc is not dead, so the report holds nothing for it (core037_gap_nonvacuous). The sentence 'No firing ever puts a token on such a place, …' is a consequence on the reference firing semantics: a dead place is empty in every reachable marking (core037_dead_stays_empty), so a dead read arc's transition is never enabled (core037_deadRead_never_enabled), a dead inhibitor never blocks (core037_deadInhibitor_never_blocks) and a dead reset clears nothing (core037_deadReset_clears_nothing). Reach has no injection step: an environment place is not dead by line 1, and the sentence's 'a host injects tokens only into environment places' is ENV-001's; that the Rust and Python executors accept an injection into a place that is not registered, under a host assumption (ruling D89, clash env-a), is the environment requirements' subject, not this block's."
          "The executor bullet (one log-message event per dead arc when the executor is constructed, through the CORE-072 AC4 mechanism: logger `libpetri.runtime`, level `WARN`, the declaring transition's name, emitted only where events are recorded and never changing execution) and the verifier bullet (one report line per dead arc, the warning text prefixed with `WARNING: `, no result field and no verdict depending on it) are SHOULD sentences over the event model and the verifier pipeline. They are the second block of this ID (kind B, wave W11: RefEvents for EVT-013, RefVerifier for VER-001) and are not encoded here. Their text 'One message per dead arc, not per place: two dead arcs on one place are two messages.' and 'Arcs are reported in transition order and, within a transition, read, inhibitor, then reset.' is lines 1 and 2 of this block: a report with one entry per place loses an entry line 1 requires (CORE_037_forbids_perPlace), a report in kind order across transitions breaks line 2 (CORE_037_forbids_kindMajor), and so do a report with the kinds in another order within a transition (CORE_037_forbids_resetFirst) and a report with one kind's arcs in reverse order (CORE_037_forbids_reverseWithinKind)."
          "AC1 (a reset arc on a place no transition consumes from or produces into, not an environment place and empty in the initial marking, gives exactly one warning naming the transition and the place) is line 1 and the reset text; CORE_037_nonvacuous checks the test derivation's net (`hub_kill` resets `answer/IN`) and the message bytes of AC1's example; a report that counts a reset arc as consuming its place drops AC1's arc (CORE_037_forbids_resetConsumes), and a text with another reset effect (CORE_037_forbids_resetMsg) or with the transition and the place swapped (CORE_037_forbids_swapNames) is killed. That the warning is one WARN log-message event and one `WARNING:` report line is the B block (W11)."
          "AC2 (the same for a read arc and an inhibitor arc, with their effects) is line 1 and the read and inhibitor texts, checked by CORE_037_nonvacuous; a text that swaps the read and inhibitor effects is killed (CORE_037_forbids_swapMsg)."
          "AC3 (no warning when the initial marking puts a token on the place, when it is an environment place, when any transition has an input arc on it, or when any transition's output spec contains it in any branch) is line 1, the clauses of DeadPlace; CORE_037_nonvacuous checks a seeded place, an environment place, a consumed place and a place only a Timeout child inside an Xor names, and core037_outSpec_nonvacuous a place only an And child names and a place only a ForwardInput target names. Reports that ignore the initial marking (CORE_037_forbids_ignoreInit), ignore the environment places (CORE_037_forbids_ignoreEnv), count producers only (CORE_037_forbids_producersOnly), read only a top-level output place (CORE_037_forbids_topOnly), skip the Timeout child (CORE_037_forbids_noTimeout) or skip the ForwardInput target (CORE_037_forbids_noForward) are killed."
          "AC4 (the warning never rejects a net and never changes execution, a verdict or a result field): the report is a total function with no failure value, and no line of this block constrains a builder, a firing or a verdict; that a dead arc never makes a builder reject is CORE-040's (W2), and that execution, verdicts and result fields do not depend on the warning is the B block (W11)."
          "The SHOULD priority applies to the requirement: an implementation that reports dead arcs follows the three shall sentences."
          "The test derivation (a transition `kill` that resets `x`, nothing else touching `x`, one warning naming `kill` and `x` with an empty initial marking and none with `x` seeded; the same with a read and an inhibitor arc, and with `x` produced by another transition's Xor branch) is CORE_037_nonvacuous on the reference report: `kill` with a read, an inhibitor and a reset arc on untouched places, a seeded place, and a place only an Xor branch of `use` names. The event, the report line and their counts are the B block's."
  signoff "pending"
  statement : DeadArcReport String → (DeadArc String → String) → Prop :=
    fun Rep Msg =>
      (∀ X env m0 a, a ∈ Rep X env m0 ↔
        ∃ t ∈ X.transitions, a.transition = t.core.name ∧
          ((a.kind = .read ∧ ReadArc t a.place) ∨ (a.kind = .inhibitor ∧ InhibitorArc t a.place) ∨
            (a.kind = .reset ∧ ResetArc t a.place)) ∧
          DeadPlace X env m0 a.place) ∧
      (∀ X env m0, Rep X env m0 = (deadArcCandidates X).filter fun a => decide (a ∈ Rep X env m0)) ∧
      (∀ t p, Msg ⟨.read, t, p⟩ = "read arc of '" ++ t ++ "' on '" ++ p ++
        "': no transition produces into or consumes from it and it starts empty; the transition can never be enabled.") ∧
      (∀ t p, Msg ⟨.inhibitor, t, p⟩ = "inhibitor arc of '" ++ t ++ "' on '" ++ p ++
        "': no transition produces into or consumes from it and it starts empty; the arc never blocks.") ∧
      (∀ t p, Msg ⟨.reset, t, p⟩ = "reset arc of '" ++ t ++ "' on '" ++ p ++
        "': no transition produces into or consumes from it and it starts empty; the arc has no effect.")

/- The pinned readable form of CORE-037: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_037 : DeadArcReport String → (DeadArc String → String) → Prop :=
fun Rep Msg =>
  (∀ (X : Reference.Net String) (env : String → Bool) (m0 : String → ℕ) (a : DeadArc String),
      a ∈ Rep X env m0 ↔
        ∃ t ∈ X.transitions,
          a.transition = t.core.name ∧
            (a.kind = DeadArcKind.read ∧ ReadArc t a.place ∨
                a.kind = DeadArcKind.inhibitor ∧ InhibitorArc t a.place ∨
                  a.kind = DeadArcKind.reset ∧ ResetArc t a.place) ∧
              DeadPlace X env m0 a.place) ∧
    (∀ (X : Reference.Net String) (env : String → Bool) (m0 : String → ℕ),
        Rep X env m0 = List.filter (fun a => decide (a ∈ Rep X env m0)) (deadArcCandidates X)) ∧
      (∀ (t p : String),
          Msg { kind := DeadArcKind.read, transition := t, place := p } =
            "read arc of '" ++ t ++ "' on '" ++ p ++
              "': no transition produces into or consumes from it and it starts empty; the transition can never be enabled.") ∧
        (∀ (t p : String),
            Msg { kind := DeadArcKind.inhibitor, transition := t, place := p } =
              "inhibitor arc of '" ++ t ++ "' on '" ++ p ++
                "': no transition produces into or consumes from it and it starts empty; the arc never blocks.") ∧
          ∀ (t p : String),
            Msg { kind := DeadArcKind.reset, transition := t, place := p } =
              "reset arc of '" ++ t ++ "' on '" ++ p ++
                "': no transition produces into or consumes from it and it starts empty; the arc has no effect."
-/
#guard_msgs in #print CORE_037

/-! ### The reference -/

section Reference

variable [DecidableEq N]

theorem connectedB_iff (X : Reference.Net N) (p : N) :
    connectedB X p = true ↔ ConnectedPlace X p := by
  simp only [connectedB, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, ConnectedPlace,
    OutputArc]
  constructor
  · rintro ⟨t, ht, h | h⟩
    · exact ⟨t, ht, Or.inl h⟩
    · cases ho : t.out with
      | none => simp [ho] at h
      | some o => rw [ho] at h; exact ⟨t, ht, Or.inr ⟨o, ho, by simpa using h⟩⟩
  · rintro ⟨t, ht, h | ⟨o, ho, h⟩⟩
    · exact ⟨t, ht, Or.inl h⟩
    · exact ⟨t, ht, Or.inr (by rw [ho]; simpa using h)⟩

theorem deadB_iff (X : Reference.Net N) (env : N → Bool) (m0 : N → Nat) (p : N) :
    deadB X env m0 p = true ↔ DeadPlace X env m0 p := by
  simp only [deadB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, DeadPlace]
  rw [← connectedB_iff]
  simp [and_assoc]

omit [DecidableEq N] in
/-- An entry is a candidate exactly when some transition of the net, under the entry's name,
has an arc of the entry's kind on the entry's place. -/
theorem mem_deadArcCandidates (X : Reference.Net N) (a : DeadArc N) :
    a ∈ deadArcCandidates X ↔
      ∃ t ∈ X.transitions, a.transition = t.core.name ∧
        ((a.kind = .read ∧ ReadArc t a.place) ∨ (a.kind = .inhibitor ∧ InhibitorArc t a.place) ∨
          (a.kind = .reset ∧ ResetArc t a.place)) := by
  obtain ⟨k, n, p⟩ := a
  simp only [deadArcCandidates, List.mem_flatMap, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨t, ht, (⟨q, hq, he⟩ | ⟨q, hq, he⟩) | ⟨q, hq, he⟩⟩ <;> cases he
    · exact ⟨t, ht, rfl, Or.inl ⟨rfl, hq⟩⟩
    · exact ⟨t, ht, rfl, Or.inr (Or.inl ⟨rfl, hq⟩)⟩
    · exact ⟨t, ht, rfl, Or.inr (Or.inr ⟨rfl, hq⟩)⟩
  · rintro ⟨t, ht, hn, (⟨hk, hp⟩ | ⟨hk, hp⟩ | ⟨hk, hp⟩)⟩
    · exact ⟨t, ht, Or.inl (Or.inl ⟨p, hp, by simp_all⟩)⟩
    · exact ⟨t, ht, Or.inl (Or.inr ⟨p, hp, by simp_all⟩)⟩
    · exact ⟨t, ht, Or.inr ⟨p, hp, by simp_all⟩⟩

/-- Line 1 on the reference report, at every place type. -/
theorem core037_line1_ref (X : Reference.Net N) (env : N → Bool) (m0 : N → Nat) (a : DeadArc N) :
    a ∈ refDeadArcs X env m0 ↔
      ∃ t ∈ X.transitions, a.transition = t.core.name ∧
        ((a.kind = .read ∧ ReadArc t a.place) ∨ (a.kind = .inhibitor ∧ InhibitorArc t a.place) ∨
          (a.kind = .reset ∧ ResetArc t a.place)) ∧
        DeadPlace X env m0 a.place := by
  simp only [refDeadArcs, List.mem_filter, mem_deadArcCandidates, deadB_iff]
  constructor
  · rintro ⟨⟨t, ht, hn, hk⟩, hd⟩; exact ⟨t, ht, hn, hk, hd⟩
  · rintro ⟨t, ht, hn, hk, hd⟩; exact ⟨⟨t, ht, hn, hk⟩, hd⟩

/-- Filtering a list by membership in a filter of it is that filter. -/
theorem core037_filter_mem_filter {α : Type} [DecidableEq α] (l : List α) (q : α → Bool) :
    l.filter (fun a => decide (a ∈ l.filter q)) = l.filter q := by
  apply List.filter_congr
  intro a ha
  simp [List.mem_filter, ha]

/-- Line 2 on the reference report, at every place type. -/
theorem core037_line2_ref (X : Reference.Net N) (env : N → Bool) (m0 : N → Nat) :
    refDeadArcs X env m0 =
      (deadArcCandidates X).filter fun a => decide (a ∈ refDeadArcs X env m0) :=
  (core037_filter_mem_filter _ _).symm

end Reference

/-- ✓ The reference pair satisfies CORE-037: `refDeadArcs` keeps exactly the candidates whose
place is dead, in candidate order (`core037_line1_ref`, `core037_line2_ref`), and
`refDeadArcMsg` is the template, kind by kind. -/
@[evidence holds CORE_037]
theorem CORE_037_reference : CORE_037 refDeadArcs refDeadArcMsg :=
  ⟨core037_line1_ref, core037_line2_ref, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Lines 1 and 2 fix the report exactly: every report that satisfies them is the reference
report, on every net, environment and initial marking, entry for entry and in the same order. -/
theorem CORE_037_unique (Rep : DeadArcReport String) (Msg : DeadArc String → String)
    (h : CORE_037 Rep Msg) : Rep = refDeadArcs := by
  funext X env m0
  rw [h.2.1 X env m0, core037_line2_ref X env m0]
  apply List.filter_congr
  intro a _
  simp only [decide_eq_decide]
  rw [h.1, core037_line1_ref]

/-! ### Consequences on the reference firing semantics -/

section Consequences

variable [DecidableEq N]

/-- A dead place is empty in every marking reachable from the initial marking by firings of the
net: no firing consumes from it, and no firing deposits into it. -/
@[evidence cites "CORE-037" "No firing ever puts a token on such a place: on the reference firing semantics a place no transition consumes from or produces into, empty in the initial marking, is empty in every reachable marking"]
theorem core037_dead_stays_empty {X : Reference.Net N} {env : N → Bool} {m0 : N → Nat} {p : N}
    (hd : DeadPlace X env m0 p) {m : N → Nat} (hr : Reach X m0 m) : m p = 0 := by
  induction hr with
  | refl => exact hd.2.2
  | tail _ hs ih =>
    obtain ⟨l, t, ht, -, d, hf⟩ := hs
    have hno : Deposits d p = 0 := by
      simp only [Deposits, depProd, List.count_eq_zero]
      intro hp
      exact hd.1 ⟨t, ht, Or.inr (refFire_outputs hf p hp)⟩
    rw [refFire_apply hf p]
    split
    · exact hno
    · omega

/-- A dead read arc's transition is never enabled in a reachable marking. -/
@[evidence cites "CORE-037" "a dead read arc means its transition can never be enabled"]
theorem core037_deadRead_never_enabled {X : Reference.Net N} {env : N → Bool} {m0 : N → Nat}
    {p : N} (hd : DeadPlace X env m0 p) {t : Trans N} (hrd : ReadArc t p) {m : N → Nat}
    (hr : Reach X m0 m) : ¬ Enabled t m := by
  have h0 := core037_dead_stays_empty hd hr
  intro he
  simp only [Enabled, enabledNA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at he
  have := he.2 p hrd
  omega

/-- A dead inhibitor arc never blocks: in a reachable marking its transition is enabled exactly
when it would be without the arc. -/
@[evidence cites "CORE-037" "a dead inhibitor never blocks"]
theorem core037_deadInhibitor_never_blocks {X : Reference.Net N} {env : N → Bool}
    {m0 : N → Nat} {p : N} (hd : DeadPlace X env m0 p) (t : Trans N) {m : N → Nat}
    (hr : Reach X m0 m) : Enabled t m ↔ Enabled (withoutInhibitor t p) m := by
  have h0 := core037_dead_stays_empty hd hr
  simp only [Enabled, enabledNA, withoutInhibitor, Bool.and_eq_true, List.all_eq_true,
    List.mem_filter, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun q hq => h2 q hq.1⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, fun q hq => ?_⟩, h3⟩
    by_cases hqp : q = p
    · subst hqp; exact h0
    · exact h2 q ⟨hq, by simpa using hqp⟩

/-- A dead reset arc clears nothing: a firing of a transition of the net from a reachable marking
leaves a dead place as it was. -/
@[evidence cites "CORE-037" "a dead reset clears nothing"]
theorem core037_deadReset_clears_nothing {X : Reference.Net N} {env : N → Bool} {m0 : N → Nat}
    {p : N} (hd : DeadPlace X env m0 p) {m : N → Nat} (hr : Reach X m0 m) {t : Trans N}
    (ht : t ∈ X.transitions) {d : List N} {m' : N → Nat} (hf : RefFire t m d m') :
    m' p = m p := by
  have h0 := core037_dead_stays_empty hd hr
  have hno : Deposits d p = 0 := by
    simp only [Deposits, depProd, List.count_eq_zero]
    intro hp
    exact hd.1 ⟨t, ht, Or.inr (refFire_outputs hf p hp)⟩
  rw [refFire_apply hf p]
  split <;> omega

end Consequences

/-! ### Examples -/

/-- A transition with the given name, read, inhibitor and reset arcs and no input arc or output
spec. -/
def core037_tr (n : String) (rd inh rs : List String) : Trans String :=
  { core := { name := n, inputs := [], inhibitors := inh, reads := rd, resets := rs }, out := none }

/-- The net of the examples. `kill` has a read arc on `r`, an inhibitor arc on `i` and a reset arc
on `x`; `kill2` has an inhibitor arc and a reset arc on `x`; `guard` reads `seeded` and `branch`,
is inhibited by `used` and resets `env`; `use` consumes from `used` and has the output spec
`Xor(a, Timeout(branch))`. Nothing touches `r`, `i` or `x` otherwise. -/
def core037_X : Reference.Net String :=
  { places := [],
    transitions :=
      [core037_tr "kill" ["r"] ["i"] ["x"],
       core037_tr "kill2" [] ["x"] ["x"],
       core037_tr "guard" ["seeded", "branch"] ["used"] ["env"],
       { core := { name := "use", inputs := [⟨"used", .one⟩], inhibitors := [], reads := [],
                   resets := [] },
         out := some (.xor (.place "a") (.timeout (.place "branch"))) }] }

/-- The environment places of the examples: `env` only. -/
def core037_env : String → Bool := fun p => p == "env"

/-- The initial marking of the examples: one token on `seeded`. -/
def core037_m0 : String → Nat := fun p => if p = "seeded" then 1 else 0

/-- The reference report on the example net. -/
def core037_expected : List (DeadArc String) :=
  [⟨.read, "kill", "r"⟩, ⟨.inhibitor, "kill", "i"⟩, ⟨.reset, "kill", "x"⟩,
   ⟨.inhibitor, "kill2", "x"⟩, ⟨.reset, "kill2", "x"⟩]

/-- The net of AC1's example: `hub_kill` resets `answer/IN`, which nothing else touches. -/
def core037_hub : Reference.Net String :=
  { places := [], transitions := [core037_tr "hub_kill" [] [] ["answer/IN"]] }

set_option maxRecDepth 20000 in
/-- Every line of CORE-037 is exercised by the reference pair. On the example net the report
holds the three arcs of `kill` in the order read, inhibitor, reset (AC1, AC2) and both dead arcs
of `kill2` on `x`, two entries on one place after the entry of `kill` on it; it holds nothing for
the seeded place `seeded`, the environment place `env`, the consumed place `used` and the place
`branch` that only a `Timeout` child inside an `Xor` names (AC3). On AC1's net it holds the reset
arc of `hub_kill`, and the warning texts are AC1's example and the read and inhibitor texts, byte
for byte. -/
@[evidence nonvacuous CORE_037]
theorem CORE_037_nonvacuous :
    refDeadArcs core037_X core037_env core037_m0 = core037_expected ∧
      refDeadArcs core037_hub (fun _ => false) (fun _ => 0) = [⟨.reset, "hub_kill", "answer/IN"⟩] ∧
      refDeadArcMsg ⟨.reset, "hub_kill", "answer/IN"⟩ =
        "reset arc of 'hub_kill' on 'answer/IN': no transition produces into or consumes from it and it starts empty; the arc has no effect." ∧
      refDeadArcMsg ⟨.read, "kill", "r"⟩ =
        "read arc of 'kill' on 'r': no transition produces into or consumes from it and it starts empty; the transition can never be enabled." ∧
      refDeadArcMsg ⟨.inhibitor, "kill", "i"⟩ =
        "inhibitor arc of 'kill' on 'i': no transition produces into or consumes from it and it starts empty; the arc never blocks." :=
  ⟨by decide, by decide, rfl, rfl, rfl⟩

/-- A net for the output-spec clause: `g` reads `andc`, `fwd` and `lone`; `o` consumes from
`src` and has the output spec `And(andc, ForwardInput(src, fwd))`. Only an `And` child names
`andc`, only a `ForwardInput` target names `fwd`, and nothing touches `lone`. -/
def core037_outNet : Reference.Net String :=
  { places := [],
    transitions :=
      [core037_tr "g" ["andc", "fwd", "lone"] [] [],
       { core := { name := "o", inputs := [⟨"src", .one⟩], inhibitors := [], reads := [],
                   resets := [] },
         out := some (.and (.place "andc") (.forward "src" "fwd")) }] }

/-- A net for the order within one kind: `k` reads `p`, then `q`, both untouched. -/
def core037_two : Reference.Net String :=
  { places := [], transitions := [core037_tr "k" ["p", "q"] [] []] }

set_option maxRecDepth 20000 in
/-- The output-spec clause and the order within one kind, on the reference report: on
`core037_outNet` it holds only the read arc on `lone` (a place only an `And` child names and a
place only a `ForwardInput` target names are fed); on `core037_two` it holds both read arcs of
`k`, `p` before `q`, the order `k` declares them. -/
@[evidence nonvacuous CORE_037]
theorem core037_outSpec_nonvacuous :
    refDeadArcs core037_outNet (fun _ => false) (fun _ => 0) = [⟨.read, "g", "lone"⟩] ∧
      refDeadArcs core037_two (fun _ => false) (fun _ => 0) =
        [⟨.read, "k", "p"⟩, ⟨.read, "k", "q"⟩] :=
  ⟨by decide, by decide⟩

/-- A net in which place `0` has a read arc (of `r`) and an input arc (of `c`), no producer, and
starts empty. -/
def core037_gapNet : Reference.Net Nat :=
  { places := [0],
    transitions :=
      [{ core := { name := "r", inputs := [], inhibitors := [], reads := [0], resets := [] },
         out := none },
       { core := { name := "c", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
         out := none }] }

/-- The definition is the bullets, not 'nothing can ever put a token on the place': in
`core037_gapNet` place `0` is empty in every reachable marking (no transition produces into
it), yet `c` consumes from it, so the read arc of `r` is not dead and the report is empty. -/
@[evidence nonvacuous CORE_037]
theorem core037_gap_nonvacuous :
    refDeadArcs core037_gapNet (fun _ => false) (fun _ => 0) = [] ∧
      ∀ m, Reach core037_gapNet (fun _ => 0) m → m 0 = 0 := by
  refine ⟨by decide, fun m hr => ?_⟩
  induction hr with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨l, t, ht, -, d, hf⟩ := hs
    have hno : Deposits d 0 = 0 := by
      simp only [Deposits, depProd, List.count_eq_zero]
      intro hp
      have := refFire_outputs hf 0 hp
      simp only [core037_gapNet, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [OutputArc] at this
    rw [refFire_apply hf 0]
    split
    · exact hno
    · omega

/-! ### Wrong reports: which places count as dead -/

/-- A report that ignores the initial marking: the reference report as if the net started empty. -/
def core037_ignoreInit : DeadArcReport String :=
  fun X env _ => refDeadArcs X env fun _ => 0

/-- ✗ Ignoring the initial marking violates CORE-037 (line 1, AC3): the read arc of `guard` on
the seeded place `seeded` is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_ignoreInit : ¬ CORE_037 core037_ignoreInit refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ := (h.1 core037_X core037_env core037_m0 ⟨.read, "guard", "seeded"⟩).1
    (by decide)
  exact absurd hd.2.2 (by decide)

/-- A report that ignores the environment places. -/
def core037_ignoreEnv : DeadArcReport String :=
  fun X _ m0 => refDeadArcs X (fun _ => false) m0

/-- ✗ Ignoring the environment places violates CORE-037 (line 1, AC3): the reset arc of `guard`
on the environment place `env` is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_ignoreEnv : ¬ CORE_037 core037_ignoreEnv refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ := (h.1 core037_X core037_env core037_m0 ⟨.reset, "guard", "env"⟩).1
    (by decide)
  exact absurd hd.2.1 (by decide)

/-- A report that counts producers only: a place is fed when an output spec names it, and an
input arc of another transition does not count. -/
def core037_producersOnly : DeadArcReport String :=
  fun X env m0 => refDeadArcs
    { X with transitions := X.transitions.map fun t => { t with core := { t.core with inputs := [] } } }
    env m0

/-- ✗ Counting producers only violates CORE-037 (line 1, AC3): the inhibitor arc of `guard` on
`used`, which `use` consumes from, is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_producersOnly : ¬ CORE_037 core037_producersOnly refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ :=
    (h.1 core037_X core037_env core037_m0 ⟨.inhibitor, "guard", "used"⟩).1 (by decide)
  exact hd.1 ((connectedB_iff _ _).1 (by decide))

/-- The reference report with the output-spec places read by `f` instead of `outPlaces`. -/
def core037_reportWith (f : Out String → List String) : DeadArcReport String :=
  fun X env m0 => (deadArcCandidates X).filter fun a =>
    !(X.transitions.any fun t => decide (a.place ∈ inPlaces t) ||
        (match t.out with | some o => decide (a.place ∈ f o) | none => false)) &&
      !env a.place && decide (m0 a.place = 0)

/-- Only a `Place` node at the root of the output spec names a place. -/
def core037_topPlaces : Out String → List String
  | .place p => [p]
  | _ => []

/-- `outPlaces` without the child of a `Timeout`. -/
def core037_noTimeoutPlaces : Out String → List String
  | .place p => [p]
  | .forward _ dst => [dst]
  | .and l r => core037_noTimeoutPlaces l ++ core037_noTimeoutPlaces r
  | .xor l r => core037_noTimeoutPlaces l ++ core037_noTimeoutPlaces r
  | .timeout _ => []

/-- `outPlaces` without the target of a `ForwardInput`. -/
def core037_noForwardPlaces : Out String → List String
  | .place p => [p]
  | .forward _ _ => []
  | .and l r => core037_noForwardPlaces l ++ core037_noForwardPlaces r
  | .xor l r => core037_noForwardPlaces l ++ core037_noForwardPlaces r
  | .timeout c => core037_noForwardPlaces c

/-- ✗ A report that reads only a top-level output place violates CORE-037 (line 1, AC3): the
read arc of `g` on `andc`, which an `And` child of `o` names, is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_topOnly :
    ¬ CORE_037 (core037_reportWith core037_topPlaces) refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ :=
    (h.1 core037_outNet (fun _ => false) (fun _ => 0) ⟨.read, "g", "andc"⟩).1 (by decide)
  exact hd.1 ((connectedB_iff _ _).1 (by decide))

/-- ✗ A report that skips the `Timeout` child violates CORE-037 (line 1, AC3): the read arc of
`guard` on `branch`, which only the `Timeout` child of `use` names, is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_noTimeout :
    ¬ CORE_037 (core037_reportWith core037_noTimeoutPlaces) refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ :=
    (h.1 core037_X core037_env core037_m0 ⟨.read, "guard", "branch"⟩).1 (by decide)
  exact hd.1 ((connectedB_iff _ _).1 (by decide))

/-- ✗ A report that skips the `ForwardInput` target violates CORE-037 (line 1, AC3): the read
arc of `g` on `fwd`, which `o` forwards into, is reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_noForward :
    ¬ CORE_037 (core037_reportWith core037_noForwardPlaces) refDeadArcMsg := by
  intro h
  obtain ⟨_, _, _, _, hd⟩ :=
    (h.1 core037_outNet (fun _ => false) (fun _ => 0) ⟨.read, "g", "fwd"⟩).1 (by decide)
  exact hd.1 ((connectedB_iff _ _).1 (by decide))

/-- A report that counts a reset arc as consuming its place. -/
def core037_resetConsumes : DeadArcReport String :=
  fun X env m0 => (refDeadArcs X env m0).filter fun a =>
    !(X.transitions.any fun t => decide (a.place ∈ t.core.resets))

/-- ✗ Counting a reset arc as consuming violates CORE-037 (line 1, AC1): AC1's reset arc of
`hub_kill` on `answer/IN` is not reported. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_resetConsumes : ¬ CORE_037 core037_resetConsumes refDeadArcMsg := by
  intro h
  have := (h.1 core037_hub (fun _ => false) (fun _ => 0) ⟨.reset, "hub_kill", "answer/IN"⟩).2
    ⟨_, List.mem_cons_self, rfl, Or.inr (Or.inr ⟨rfl, by decide⟩),
      (deadB_iff _ _ _ _).1 (by decide)⟩
  revert this
  decide

/-- Keep the first entry on each place and drop the later ones. -/
def core037_firstPerPlace (l : List (DeadArc String)) : List (DeadArc String) :=
  l.foldl (fun acc a => if acc.any (fun b => decide (b.place = a.place)) then acc else acc ++ [a]) []

/-- A report with one entry per place instead of one per arc. -/
def core037_perPlace : DeadArcReport String :=
  fun X env m0 => core037_firstPerPlace (refDeadArcs X env m0)

/-- ✗ One entry per place violates CORE-037 (line 1; 'two dead arcs on one place are two
entries'): of the three dead arcs on `x` only the reset arc of `kill` is kept, and the inhibitor
arc of `kill2` on `x` is missing. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_perPlace : ¬ CORE_037 core037_perPlace refDeadArcMsg := by
  intro h
  have := (h.1 core037_X core037_env core037_m0 ⟨.inhibitor, "kill2", "x"⟩).2
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, Or.inr (Or.inl ⟨rfl, by decide⟩),
      (deadB_iff _ _ _ _).1 (by decide)⟩
  revert this
  decide

/-! ### Wrong reports: order -/

/-- The candidates in kind order across the net: every read arc of every transition, then every
inhibitor arc, then every reset arc. -/
def core037_kindMajorCandidates {N : Type} (X : Reference.Net N) : List (DeadArc N) :=
  X.transitions.flatMap (fun t => t.core.reads.map (⟨.read, t.core.name, ·⟩)) ++
    X.transitions.flatMap (fun t => t.core.inhibitors.map (⟨.inhibitor, t.core.name, ·⟩)) ++
    X.transitions.flatMap (fun t => t.core.resets.map (⟨.reset, t.core.name, ·⟩))

/-- A report in kind order across transitions instead of transition order. -/
def core037_kindMajor : DeadArcReport String :=
  fun X env m0 => (core037_kindMajorCandidates X).filter fun a => deadB X env m0 a.place

theorem core037_mem_kindMajorCandidates {N : Type} (X : Reference.Net N) (a : DeadArc N) :
    a ∈ core037_kindMajorCandidates X ↔ a ∈ deadArcCandidates X := by
  simp only [core037_kindMajorCandidates, deadArcCandidates, List.mem_append, List.mem_flatMap]
  constructor
  · rintro ((⟨t, ht, h⟩ | ⟨t, ht, h⟩) | ⟨t, ht, h⟩)
    · exact ⟨t, ht, Or.inl (Or.inl h)⟩
    · exact ⟨t, ht, Or.inl (Or.inr h)⟩
    · exact ⟨t, ht, Or.inr h⟩
  · rintro ⟨t, ht, (h | h) | h⟩
    · exact Or.inl (Or.inl ⟨t, ht, h⟩)
    · exact Or.inl (Or.inr ⟨t, ht, h⟩)
    · exact Or.inr ⟨t, ht, h⟩

/-- ✗ Kind order across transitions violates CORE-037 (line 2): the inhibitor arc of `kill2` on
`x` comes before the reset arc of `kill` on `x`. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_kindMajor : ¬ CORE_037 core037_kindMajor refDeadArcMsg := by
  intro h
  have := h.2.1 core037_X core037_env core037_m0
  revert this
  decide

/-- A report in transition order with each transition's arcs in the kind order reset, inhibitor,
read. -/
def core037_resetFirst : DeadArcReport String :=
  fun X env m0 => (X.transitions.flatMap fun t =>
      t.core.resets.map (⟨.reset, t.core.name, ·⟩) ++
        t.core.inhibitors.map (⟨.inhibitor, t.core.name, ·⟩) ++
        t.core.reads.map (⟨.read, t.core.name, ·⟩)).filter fun a => deadB X env m0 a.place

/-- ✗ Another kind order within a transition violates CORE-037 (line 2): the reset arc of `kill`
on `x` comes before its read arc on `r`. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_resetFirst : ¬ CORE_037 core037_resetFirst refDeadArcMsg := by
  intro h
  have := h.2.1 core037_X core037_env core037_m0
  revert this
  decide

/-- A report in transition and kind order with each kind's arcs in reverse declaration order. -/
def core037_reverseWithinKind : DeadArcReport String :=
  fun X env m0 => (X.transitions.flatMap fun t =>
      t.core.reads.reverse.map (⟨.read, t.core.name, ·⟩) ++
        t.core.inhibitors.reverse.map (⟨.inhibitor, t.core.name, ·⟩) ++
        t.core.resets.reverse.map (⟨.reset, t.core.name, ·⟩)).filter fun a => deadB X env m0 a.place

/-- ✗ Reverse order within one kind violates CORE-037 (line 2): the read arc of `k` on `q` comes
before its read arc on `p`. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_reverseWithinKind :
    ¬ CORE_037 core037_reverseWithinKind refDeadArcMsg := by
  intro h
  have := h.2.1 core037_two (fun _ => false) (fun _ => 0)
  revert this
  decide

/-- Mutant reading of CORE-037 that drops line 2: the report holds the right entries, in any
order and with any repetition. -/
def CORE_037_mutant_membersOnly (Rep : DeadArcReport String)
    (Msg : DeadArc String → String) : Prop :=
  (∀ X env m0 a, a ∈ Rep X env m0 ↔
    ∃ t ∈ X.transitions, a.transition = t.core.name ∧
      ((a.kind = .read ∧ ReadArc t a.place) ∨ (a.kind = .inhibitor ∧ InhibitorArc t a.place) ∨
        (a.kind = .reset ∧ ResetArc t a.place)) ∧
      DeadPlace X env m0 a.place) ∧
  (∀ t p, Msg ⟨.read, t, p⟩ = "read arc of '" ++ t ++ "' on '" ++ p ++
    "': no transition produces into or consumes from it and it starts empty; the transition can never be enabled.") ∧
  (∀ t p, Msg ⟨.inhibitor, t, p⟩ = "inhibitor arc of '" ++ t ++ "' on '" ++ p ++
    "': no transition produces into or consumes from it and it starts empty; the arc never blocks.") ∧
  (∀ t p, Msg ⟨.reset, t, p⟩ = "reset arc of '" ++ t ++ "' on '" ++ p ++
    "': no transition produces into or consumes from it and it starts empty; the arc has no effect.")

/-- The kind-order report kills the mutant reading without line 2: it holds exactly the dead
arcs, but not in report order. -/
@[evidence mutant CORE_037]
theorem CORE_037_mutant_membersOnly_killed :
    CORE_037_mutant_membersOnly core037_kindMajor refDeadArcMsg ∧
      ¬ CORE_037 core037_kindMajor refDeadArcMsg := by
  refine ⟨⟨fun X env m0 a => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    CORE_037_forbids_kindMajor⟩
  rw [← core037_line1_ref]
  simp only [core037_kindMajor, refDeadArcs, List.mem_filter, core037_mem_kindMajorCandidates]

/-! ### Wrong warning texts -/

/-- A warning text with the effects of the read and the inhibitor arc swapped. -/
def core037_swapMsg : DeadArc String → String
  | ⟨.read, t, p⟩ => "read arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the arc never blocks."
  | ⟨.inhibitor, t, p⟩ => "inhibitor arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the transition can never be enabled."
  | a => refDeadArcMsg a

set_option maxRecDepth 20000 in
/-- ✗ Swapping the effects violates CORE-037 (read text, AC2): the read arc of `kill` on `r`
says the arc never blocks. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_swapMsg : ¬ CORE_037 refDeadArcs core037_swapMsg := by
  intro h
  have := h.2.2.1 "kill" "r"
  revert this
  decide

/-- A warning text whose reset effect is the inhibitor's. -/
def core037_resetMsg : DeadArc String → String
  | ⟨.reset, t, p⟩ => "reset arc of '" ++ t ++ "' on '" ++ p ++
      "': no transition produces into or consumes from it and it starts empty; the arc never blocks."
  | a => refDeadArcMsg a

set_option maxRecDepth 20000 in
/-- ✗ Another reset effect violates CORE-037 (reset text, AC1): AC1's reset arc of `hub_kill`
says the arc never blocks. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_resetMsg : ¬ CORE_037 refDeadArcs core037_resetMsg := by
  intro h
  have := h.2.2.2.2 "hub_kill" "answer/IN"
  revert this
  decide

/-- A warning text with the transition and the place swapped in the template. -/
def core037_swapNamesMsg : DeadArc String → String
  | ⟨k, t, p⟩ => refDeadArcMsg ⟨k, p, t⟩

set_option maxRecDepth 20000 in
/-- ✗ Swapping the transition and the place violates CORE-037 (reset text, AC1): AC1's arc
reads "reset arc of 'answer/IN' on 'hub_kill'". -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_swapNames : ¬ CORE_037 refDeadArcs core037_swapNamesMsg := by
  intro h
  have := h.2.2.2.2 "hub_kill" "answer/IN"
  revert this
  decide

/-- A warning text that prints the place as a Java Place record (name and token type) instead of
its name: the bug of writing the record where `place.name()` belongs. -/
def core037_recordMsg : DeadArc String → String
  | ⟨k, t, p⟩ => refDeadArcMsg ⟨k, t, "Place[name=" ++ p ++ ", tokenType=String]"⟩

set_option maxRecDepth 20000 in
/-- ✗ Printing the place record violates CORE-037 (reset text, AC1): AC1's arc names
`Place[name=answer/IN, tokenType=String]` instead of `answer/IN`. -/
@[evidence forbids CORE_037]
theorem CORE_037_forbids_recordMsg : ¬ CORE_037 refDeadArcs core037_recordMsg := by
  intro h
  have := h.2.2.2.2 "hub_kill" "answer/IN"
  revert this
  decide

/-- Mutant reading of CORE-037 that drops the warning text: lines 1 and 2 only. -/
def CORE_037_mutant_noText (Rep : DeadArcReport String) (_Msg : DeadArc String → String) : Prop :=
  (∀ X env m0 a, a ∈ Rep X env m0 ↔
    ∃ t ∈ X.transitions, a.transition = t.core.name ∧
      ((a.kind = .read ∧ ReadArc t a.place) ∨ (a.kind = .inhibitor ∧ InhibitorArc t a.place) ∨
        (a.kind = .reset ∧ ResetArc t a.place)) ∧
      DeadPlace X env m0 a.place) ∧
  (∀ X env m0, Rep X env m0 = (deadArcCandidates X).filter fun a => decide (a ∈ Rep X env m0))

/-- The swapped text kills the mutant reading without the text lines: the report is the
reference one, the text is not. -/
@[evidence mutant CORE_037]
theorem CORE_037_mutant_noText_killed :
    CORE_037_mutant_noText refDeadArcs core037_swapMsg ∧
      ¬ CORE_037 refDeadArcs core037_swapMsg :=
  ⟨⟨core037_line1_ref, core037_line2_ref⟩, CORE_037_forbids_swapMsg⟩

end Libpetri.Spec
