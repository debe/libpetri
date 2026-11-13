import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# CORE-072: Initial marking (`spec/01-core-model.md`)

The requirement is a predicate over three abstract models: an initialiser `I : Init N` (the
state an executor starts from, glossary `GlossaryTime.lean`), a timed step relation `R : TRel N`
and a queue firing relation `Q : QFireRel N T` (glossary `GlossaryQueue.lean`). The evidence
theorems check it against the reference initialiser (`TSt.init`), the timed reference step
(`RefTStep`) and the reference queue firing (`RefQFire`), and against wrong models: an
initialiser that starts from the empty marking, one that arms nothing, one that stamps the
initially armed transitions with a stale reading, a step relation whose storage keeps only the
places the net lists (on every step, on a reap only, on a firing only), one that inflates an
unknown place on a delay, and queue firings that
drop, reverse or rotate the queue of a place they do not touch. Mutant readings (the
declared-only marking, arming without the stamp, retention as counts and sublists, and order
as a count) are each told apart from the statement.

Line 2 states the stamp of an initially armed transition, the first half of TIME-010's quoted
sentence on being newly armed that TIME_010.lean leaves outside its step relation; with line 1
it gives the glossary predicate `InitArms` in full (`core072_initArms`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## CORE-072: Initial marking -/

requirement CORE_072
  id "CORE-072"
  title "Initial Marking"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "An executor can be initialized with an initial marking that pre-populates places with tokens before execution begins."
        "*When* an executor is initialized with an initial marking, its marking *shall* hold, before execution begins, exactly the tokens the initial marking puts on each place, whether or not the net declares that place."
        "*When* execution begins, a transition of the net *shall* be armed exactly when its enablement check passes on the initial marking, with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 ([TIME-010])."
        "*While* a place is an unknown place, the executor *shall* retain its tokens in the marking, in their order and ahead of any token that reaches the place later, and *shall not* drop any of them."
        "*While* a place is an unknown place, the executor *shall not* change its tokens when the firing clock advances or when it reaps a transition ([TIME-013])."
  reading "For every initialiser I, timed step relation R and queue firing relation Q:"
          "for every timed net X, initial marking m0 and start reading now0, the state I X m0 now0 holds exactly m0, on every place, whether or not the net declares it;"
          "in the state I X m0 now0, every transition of the net that m0 enables holds the state's own clock reading as its stamp (with line 1: a transition of the net is armed there exactly when m0 enables it, and its elapsed time is 0);"
          "for an unknown place p of X, a delay of R and a reap of R leave p's token count as it is, and a firing of R leaves p with at least the tokens it had;"
          "every firing under Q of a transition of X leaves the queue an unknown place of X had before the firing as a prefix of its queue after it: every token kept, in its order, at the head."
  assumes "The initialiser I X m0 now0 is the state an executor starts from (glossary: Init): the marking, the reading of the firing clock and a stamp per transition name, for the timed net X, the initial marking m0 as token counts and the first clock reading now0. A step of R (glossary: TRel) is a delay of the clock, a reap or an atomic firing. A firing of Q (glossary: QFireRel) is one step Q t M δ e M' on queue markings, which carry token identity and order. Unknown place, Armed, Elapsed time and Enabled are the glossary terms."
          "The second quoted shall sentence speaks of the enablement check (glossary: Enablement check), read here as Enabled in the initial marking: for a transition that has no match specification the enablement check passes exactly when the transition is enabled (CONC-008, its fourth shall sentence), and the transitions of the model (Reference.Trans) carry no match specification, so every transition of the net is such a transition (ruling D30). For a transition with a match specification the check also needs a name of which every correlated input holds at least its required count of tokens (NU-020); that case is not encoded here."
          "Unknown place (glossary): no transition of the net has an arc on the place or names it in its output spec. A net of the model is its list of transitions and a place exists by use, so a place declared through the builder but touched by no arc (CORE-040 AC1) is an unknown place here, although AC3 speaks of 'places the net does not declare' and the runtimes warn only for a place the compiled net does not hold. Lines 3 and 4 therefore cover more places than AC3 names, never fewer, and line 1 is on every place. The places list of a Lean net plays no part in the statement; the mutant initialiser core072_dropInit uses it as the compiled place set."
          "Places are identified by name here, as transitions are under ruling D10: a place of the model is its name. Java identifies a place by its name and its token type together (the Place record, the divergence MOD-024 records), so in Java an initial token on a place with the net's name but another token type is on an unknown place there, retained, inert and warned about, while in TypeScript and Rust it is on the net's place and can enable a transition. Line 2 therefore arms differently across the runtimes for such a marking; the block does not encode that case, which is MOD-024's divergence, not CORE-072's."
          "Transitions are identified by name (ruling D10): line 2 ranges over the transitions the net holds under their own names (InNet), line 4 over the members of the transition list, and under pairwise distinct names (NamesDistinct) the two are the same set (inNet_iff_mem)."
          "Fusion sets (MOD-060, MOD-061) are not modelled: a Lean net has no fused members. Initial tokens on a non-canonical member of a fusion set stay on that name, which the built net no longer declares, in the runtimes: the built net keeps no fusion map (the Rust core rebuilds the fused `PetriNet` from its places, transitions, subnet membership and terminals only), no executor knows a fusion set, and Java tells the caller to concentrate initial tokens on the canonical place itself (the FusionSet class documentation, java/src/main/java/org/libpetri/core/FusionSet.java; clash mod-c#1). Whether MOD-061 AC2 is restated to match is ruling D54 (W8); line 1 states CORE-072's own text, which the runtimes follow, and does not depend on D54."
          "Line 1 is the body sentence and the first quoted shall sentence, on token counts: the initial state's marking is the initial marking, as a function on every place, so an initialiser that drops the tokens of an undeclared place (core072_dropInit, the declared-only mutant) or starts from the empty marking (core072_emptyInit) violates it. The quoted sentence says 'exactly the tokens'; the timed state of Phase 1 carries counts only, so token identity and order in the initial state are not visible here. A state with queues is the executor cycle relation's (RefExec, W5), and that a restored marking keeps identity and order is CORE-073's subject (W3)."
          "Line 2 is the second quoted shall sentence: every transition of the net that the initial marking enables holds the initial state's clock reading as its stamp. With line 1 it gives InitArms in full (core072_initArms): a transition of the net is armed in the initial state exactly when the initial marking enables it (the 'only when' half follows from line 1 alone, since Armed includes Enabled in the state's own marking), and its elapsed time is 0 (initArms_elapsed). This is the first case of TIME-010's quoted sentence on being newly armed ('A transition is newly armed when it is enabled in the initial marking'), which TIME_010.lean leaves outside its step relation. An initialiser that holds the marking but arms nothing (core072_noArmInit) violates line 2, and so does one that arms the right transitions with a stale stamp (core072_staleStampInit: the reading 0 while the clock reads now0, as a runtime that seeds its enable times from a zeroed buffer), which the arming-only mutant reading accepts; under it a Deadline(5) transition is expired before the first step (core072_staleStamp_expired) where the reference has it ready (core072_ref_ready). Line 2 does not fix the clock reading itself: elapsed times, which are all that timing reads, depend on the difference between the clock and the stamp, and the clock is TIME-010's and TIME-015's."
          "AC2 ('Execution begins with these tokens available') is read as line 2: the initial tokens are available to a transition when it is armed on them with elapsed time 0, so its earliest bound counts from the start of the run. No line ties I to R: lines 3 and 4 hold on every state, the initial one included, and that a run starts at I X m0 now0 and that an armed ready transition does fire are the executor cycle relation's (RefExec, W5) and the consistency witness's (Covers in ConsistencyTime.lean), not CORE-072's. The relation that never fires from the initial state is not forbidden here; CORE_072_nonvacuous shows the reference firing from it."
          "Line 2 does not cover a terminal place ([EXEC-042]): a run whose initial marking marks a terminal place ends before its first enablement update, so no transition is armed (the terminal_reached check that opens the loop of run_sync, rust/libpetri-runtime/src/executor_core/executor.rs). The Phase 1 state has no terminal places; the exception belongs to the executor cycle relation (RefExec, W5) and is not encoded."
          "Lines 3 and 4 are the third and fourth quoted shall sentences, which restate the first sentence of AC3 ('retained in the observable marking (inert ...) but never silently dropped'). Line 3 is on token counts: a delay or a reap leaves an unknown place's count as it is (the fourth sentence; neither is a seam, so 'inert' means unchanged there), and a firing leaves at least the count it had. Line 4 is on queues over every firing of a transition of the net: the old queue is a prefix of the new one, so every token stays, in its order, ahead of any token added later. The timed state has no order, so the order clause of the third sentence is line 4's alone."
          "A firing is held to retention, not to 'unchanged' (the test derivation's word), because AC3 lets tokens reach an unknown place through the production seam, which ruling D63 (W3) settles; any deposit appends at the tail (EXEC-020), so the prefix and count lines hold under every option of D63. On the reference the unknown place is in fact unchanged on every step (core072_ref_count, core072_ref_queue), as CORE-035 lines 1 and 3 and EXEC-020 say of a place a firing does not deposit into, so a firing that adds a token to an unknown place is CORE-035's to forbid, not this block's. The injection seam is not a label of R or Q (it waits for RefExec's injection label, W5); lines 3 and 4 name the delay, reap and firing labels and so do not constrain it."
          "Wrong models of lines 3 and 4: a step relation whose storage keeps only the places the net lists (core072_clearR, the shape of the pre-fix precompiled pool, whose produce_token dropped a token for a place the program does not know; Libpetri.unknown_place_drop cites CORE-072 AC3) one that doubles an unknown place on every delay, as a backend that merges its side map of uncompiled-place tokens into the marking each cycle without clearing it (core072_doubleMergeR, clash conc-b#8; the retention-only mutant reading accepts it), one that rebuilds the store from the listed places on a reap (core072_clearOnReapR, the reap clause) and one that does so on a firing (core072_clearOnFireR, the firing clause) violate line 3; CORE_072_nonvacuous_delayReap shows the reference keeping the unknown place's tokens across a delay and a reap. A queue firing that rebuilds the marking from the places it touches (core072_dropQ), one that reverses an untouched queue (core072_reverseQ; the count-only mutant reading accepts it) and one that rotates it with stale copies (core072_staleRingQ, a ring whose head index moved without clearing its slots; the retention-only mutant reading accepts it) violate line 4."
          "AC1 (initial marking distributes tokens to specified places) is line 1 (CORE_072_nonvacuous: places 1, 2 and the unknown place 9 hold 2, 1 and 4 tokens in the initial state)."
          "AC3 is lines 3 and 4 for its first sentence. Its second sentence, 'every backend regardless of its internal token storage', is the scope 'all executors': the Lean models are one store, and that the production backend's ring store agrees with it is CONC-022's and CONC-025's subject. Its seams are deferred as above: production into an uncompiled place through a raw output that bypasses the context waits for ruling D63 (CORE-063 errors on a context call naming an undeclared place, and CORE-035 line 1 and CONC-026 line 2 forbid a firing to deposit outside its output places, so no relation of the joint model can witness the seam today); injection into a registered environment place that no arc touches needs RefExec's injection label (W5, ENV-002 AC2 and AC3). The quoted sentences restate AC3's first sentence only and leave the seams to the markdown. Its last sentence, that verification models such a place as one with no arcs whose tokens stay, is VER-001's subject; the Lean side is Novel.Seam.inertNet, which appends an arc-less place per inert place and adds no transition (inertNet_transitions)."
          "AC4 (the SHOULD diagnostic: one WARN log-message event per distinct unknown place per executor, its logger, transition name and message) needs the event model (RefEvents, EVT-013, W7) and the events-wave rulings on payloads (D38) and wording (D20, clash evt-b#4 on the transition name); no quoted sentence states it and it is not encoded. Retention does not depend on it, as lines 3 and 4 show."
          "The test derivation is AC1 to AC3 on one net: CORE_072_nonvacuous starts from {1: 2 tokens, 2: 1 token, 9: 4 tokens} with 9 unknown, fires once, and keeps the unknown place's tokens unchanged, on counts and as the queue 90, 91, 92, 93; the WARN count is AC4's."
  signoff "2026-11-13 31b2fc4630cbe0e6 ai"
  statement : ∀ {N T : Type} [DecidableEq N], Init N → TRel N → QFireRel N T → Prop :=
    fun I R Q =>
      (∀ X m0 now0, (I X m0 now0).m = m0) ∧
      (∀ X m0 now0 u, InNet X u → Enabled u m0 →
          (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0))) ∧
      (∀ X p, UnknownPlace X p →
          (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' => s'.m p = s.m p)) ∧
          (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => s'.m p = s.m p)) ∧
          (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => s.m p ≤ s'.m p))) ∧
      (∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
          on (fun M M' => Q t M δ e M'), shall (fun M M' => M p <+: M' p))

/- The pinned readable form of CORE-072: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_072 : {N T : Type} → [DecidableEq N] → Init N → TRel N → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] I R Q =>
  (∀ (X : TimedNet N) (m0 : CountMarking N) (now0 : ℕ), (I X m0 now0).m = m0) ∧
    (∀ (X : TimedNet N) (m0 : CountMarking N) (now0 : ℕ) (u : Reference.Trans N),
        InNet X u → Enabled u m0 → (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0))) ∧
      (∀ (X : TimedNet N) (p : N),
          UnknownPlace X p →
            (∀ (δ : ℕ), on fun s s' => R X s (TLbl.delay δ) s', shall fun s s' => s'.m p = s.m p) ∧
              (∀ (u : Reference.Trans N), on fun s s' => R X s (TLbl.reap u) s', shall fun s s' => s'.m p = s.m p) ∧
                ∀ (t : Reference.Trans N) (d : List N),
                  on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' => s.m p ≤ s'.m p) ∧
        ∀ (X : TimedNet N) (p : N),
          UnknownPlace X p →
            ∀ t ∈ X.net.transitions,
              ∀ (δ : Delivered N T) (e : List (N × T)), on fun M M' => Q t M δ e M', shall fun M M' => M p <+: M' p
-/
#guard_msgs in #print CORE_072

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- With line 1, line 2 is the glossary predicate `InitArms` in full: a transition of the net is
armed in the initial state exactly when the initial marking enables it, with the state's clock
reading as its stamp. -/
theorem core072_initArms {I : Init N} {R : TRel N} {Q : QFireRel N T}
    (h : CORE_072 I R Q) : InitArms I := by
  intro X m0 now0 u hu
  have hm := h.1 X m0 now0
  have hs := h.2.1 X m0 now0 u hu
  refine ⟨⟨fun ha => ?_, fun he => ?_⟩, hs⟩
  · have := ha.1
    rw [hm] at this
    exact this
  · refine ⟨?_, ?_⟩
    · show Enabled u (I X m0 now0).m
      rw [hm]; exact he
    · rw [hs he]; rfl

/-- Under line 2, a transition of the net enabled in the initial marking starts with elapsed time
0. -/
theorem core072_elapsed {I : Init N} {R : TRel N} {Q : QFireRel N T}
    (h : CORE_072 I R Q) {X : TimedNet N} {m0 : CountMarking N} {now0 : Nat} {u : Trans N}
    (hu : InNet X u) (he : Enabled u m0) : Elapsed (I X m0 now0) u = 0 :=
  initArms_elapsed (core072_initArms h) hu he

/-- On the timed reference step an unknown place keeps its token count across every step: a
delay or a reap keeps the marking, and a firing neither consumes from, drains nor deposits into a
place on which its transition has no arc and which its output spec does not name. -/
theorem core072_ref_count {X : TimedNet N} {p : N} (hu : UnknownPlace X p) {s s' : TSt N}
    {l : TLbl N} (h : RefTStep X s l s') : s'.m p = s.m p := by
  cases l with
  | delay δ => rw [refTStep_framesMarking X s _ s' h (by simp)]
  | reap t => rw [refTStep_framesMarking X s _ s' h (by simp)]
  | fire t d =>
    have ht : t ∈ X.net.transitions := by cases h; assumption
    have hf : RefFire t s.m d s'.m := refTStep_projects h
    have hna := unknownPlace_not_arc hu ht
    have hno := unknownPlace_not_output hu ht
    have hnd : ¬ Produced d p := fun hp => hno (refFire_outputs hf p hp)
    have hni : p ∉ inPlaces t := fun hi => hna (Or.inl hi)
    have hnr : ¬ ResetArc t p := fun hr => hna (Or.inr (Or.inr (Or.inr hr)))
    have hn : nspecAt t.core p = none := by
      unfold nspecAt
      rw [List.find?_eq_none]
      intro x hx he
      have : x.place = p := by simpa using he
      exact hni (List.mem_map.mpr ⟨x, hx, this⟩)
    have hd : Deposits d p = 0 := by
      simp only [Deposits, depProd]
      exact List.count_eq_zero_of_not_mem hnd
    rw [refFire_apply hf p, if_neg hnr, hd]
    simp [Consumes, nconsumed, hn]

/-- On the reference queue firing a place on which the transition has no arc and which its
output spec does not name keeps its queue, tokens and order. -/
theorem core072_ref_queue {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} (h : RefQFire t M δ e M') {p : N} (hna : ¬ ArcPlace t p)
    (hno : ¬ OutputArc t p) : M' p = M p := by
  have hi : p ∉ inPlaces t := fun hi => hna (Or.inl hi)
  have hr : ¬ ResetArc t p := fun hr => hna (Or.inr (Or.inr (Or.inr hr)))
  have ha := refQFire_appendedAtTail h hi hr
  have hf : RefFire t (Counts M) (e.map Prod.fst) (Counts M') :=
    refQFire_projectsTo t M δ e M' h
  have hnp : p ∉ e.map Prod.fst := fun hp => hno (refFire_outputs hf p hp)
  have he : EmittedTo e p = [] := by
    simp only [EmittedTo, qEmittedTo, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro x hx hxp
    exact hnp (List.mem_map.mpr ⟨x, hx, by simpa using hxp⟩)
  rw [AppendedAtTail, he, List.append_nil] at ha
  exact ha

/-- Line 3 on the timed reference step. -/
theorem core072_line3_ref :
    ∀ X p, UnknownPlace X p →
      (∀ δ, on (fun s s' => RefTStep (N := N) X s (.delay δ) s'),
          shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ u, on (fun s s' => RefTStep (N := N) X s (.reap u) s'),
          shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ t d, on (fun s s' => RefTStep (N := N) X s (.fire t d) s'),
          shall (fun s s' => s.m p ≤ s'.m p)) :=
  fun _ _ hu => ⟨fun _ _ _ h => core072_ref_count hu h, fun _ _ _ h => core072_ref_count hu h,
    fun _ _ _ _ h => (core072_ref_count hu h).ge⟩

/-- Line 4 on the reference queue firing. -/
theorem core072_line4_ref :
    ∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
      on (fun M M' => RefQFire (N := N) (T := T) t M δ e M'), shall (fun M M' => M p <+: M' p) :=
  fun _ _ hu _ ht _ _ M M' h => by
    show M _ <+: M' _
    rw [core072_ref_queue h (unknownPlace_not_arc hu ht) (unknownPlace_not_output hu ht)]

end Reference

/-- The reference satisfies CORE-072: `TSt.init` holds the initial marking as given
(`init_marking`) and stamps every transition of the net the initial marking enables with its own
clock reading (`initArms_init`); the timed reference step and the reference queue firing leave
an unknown place as it is (`core072_ref_count`, `core072_ref_queue`). -/
@[evidence holds CORE_072]
theorem CORE_072_reference {N T : Type} [DecidableEq N] :
    CORE_072 (N := N) (T := T) TSt.init RefTStep RefQFire :=
  ⟨fun X m0 now0 => init_marking X m0 now0,
    fun X m0 now0 u hu he => (initArms_init X m0 now0 u hu).2 he,
    core072_line3_ref, core072_line4_ref⟩

/-- The reference initialiser stamps every transition of the net enabled in the initial marking
with the start reading of the firing clock. -/
@[evidence cites "TIME-010" "first case of the quoted sentence on being newly armed ('A transition is newly armed when it is enabled in the initial marking'): the reference initialiser TSt.init stamps every transition of the net enabled in the initial marking with the start reading now0, so its elapsed time starts at 0; TIME_010.lean leaves this case outside its step relation and CORE-072 line 2 states it"]
theorem core072_init_stamp {N : Type} [DecidableEq N] {X : TimedNet N} {m0 : CountMarking N}
    {now0 : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u m0) :
    (TSt.init X m0 now0).stamp u.core.name = some now0 :=
  (initArms_init X m0 now0 u hu).2 he

/-! ### Examples -/

/-- The transition of the examples: one input arc on place `1`, a read arc on place `2`, an
output on place `3`. -/
def core072_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨1, .one⟩], inhibitors := [], reads := [2], resets := [] },
    out := some (.place 3) }

/-- The timed net of the examples: `core072_t` alone, `Immediate`, tolerance 0; it lists the
places `1`, `2` and `3`. -/
def core072_X : TimedNet Nat :=
  { net := { places := [1, 2, 3], transitions := [core072_t] },
    timing := fun _ => .immediate, tol := 0 }

/-- The initial marking of the test derivation: two tokens in place `1`, one in place `2`, and
four in place `9`, which the net does not declare. -/
def core072_m0 : Nat → Nat := fun p =>
  if p = 1 then 2 else if p = 2 then 1 else if p = 9 then 4 else 0

/-- The same initial marking as queues (token values `10, 11`, `20`, `90..93`). -/
def core072_M : QueueMarking Nat Nat := fun p =>
  if p = 1 then [10, 11] else if p = 2 then [20] else if p = 9 then [90, 91, 92, 93] else []

theorem core072_t_inX : InNet core072_X core072_t := rfl

theorem core072_t_mem : core072_t ∈ core072_X.net.transitions := by simp [core072_X]

/-- Place `9` is an unknown place of the example net. -/
theorem core072_unknown9 : UnknownPlace core072_X 9 := by
  intro u hu
  simp only [core072_X, List.mem_singleton] at hu
  subst hu
  simp [ArcPlace, OutputArc, inPlaces, ReadArc, InhibitorArc, ResetArc, outPlaces, core072_t]

/-- The initial state of the examples, at reading `0`. -/
def core072_s0 : TSt Nat := TSt.init core072_X core072_m0 0

/-- The state after `core072_t` fires once from the initial state. -/
def core072_s1 : TSt Nat :=
  { m := fireNC core072_m0 core072_t.core (depProd [3]), now := 0,
    stamp := restampAll refPolicy core072_X core072_s0 core072_t [3]
      (fireNC core072_m0 core072_t.core (depProd [3])) }

/-- `core072_t` fires from the initial state on the timed reference step. -/
theorem core072_fires : RefTStep core072_X core072_s0 (.fire core072_t [3]) core072_s1 :=
  RefTStepW.fire _ _ _ _ _ core072_t_mem ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) (by decide) (by decide)

/-- `core072_t` fires from the queue form of the initial marking, emitting one token on `3`. -/
theorem core072_qfires :
    RefQFire core072_t core072_M (qDelivered core072_M core072_t) [(3, 30)]
      (qFire core072_M core072_t [(3, 30)]) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- Every line of CORE-072 is exercised by the reference, on the test derivation's marking with
the unknown place `9`: the initial state holds the four tokens of place `9` and the two of place
`1` (line 1); `core072_t` holds the initial reading `0` as its stamp, so it is armed there
(line 2), and fires, consuming a token of place `1`, while place `9` keeps its four tokens
(line 3); on queues the firing keeps place `9`'s queue `90, 91, 92, 93` (line 4). -/
@[evidence nonvacuous CORE_072]
theorem CORE_072_nonvacuous :
    core072_s0.m 9 = 4 ∧ core072_s0.m 1 = 2 ∧ core072_s0.m 2 = 1 ∧
      UnknownPlace core072_X 9 ∧
      core072_s0.stamp core072_t.core.name = some (ClockReading core072_s0) ∧
      Armed core072_s0 core072_t ∧
      RefTStep core072_X core072_s0 (.fire core072_t [3]) core072_s1 ∧
      core072_s1.m 1 = 1 ∧ core072_s1.m 9 = 4 ∧
      RefQFire core072_t core072_M (qDelivered core072_M core072_t) [(3, 30)]
        (qFire core072_M core072_t [(3, 30)]) ∧
      qFire core072_M core072_t [(3, 30)] 9 = [90, 91, 92, 93] := by
  refine ⟨by decide, by decide, by decide, core072_unknown9, by decide, by decide,
    core072_fires, by decide, by decide, core072_qfires, ?_⟩
  rw [core072_ref_queue core072_qfires
    (unknownPlace_not_arc core072_unknown9 core072_t_mem)
    (unknownPlace_not_output core072_unknown9 core072_t_mem)]
  rfl

/-! ### Wrong initialisers -/

/-- An initialiser that starts from the empty marking, whatever initial marking it is given. -/
def core072_emptyInit {N : Type} [DecidableEq N] : Init N :=
  fun X _ now0 => TSt.init X (fun _ => 0) now0

/-- ✗ Starting from the empty marking violates CORE-072 (line 1): the four tokens of place `9`
and the two of place `1` are missing. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_emptyInit :
    ¬ CORE_072 (N := Nat) (T := Nat) core072_emptyInit RefTStep RefQFire := by
  intro h
  have := congrFun (h.1 core072_X core072_m0 0) 1
  revert this
  decide

/-- An initialiser that holds the initial marking but arms no transition. -/
def core072_noArmInit {N : Type} : Init N :=
  fun _ m0 now0 => { m := m0, now := now0, stamp := fun _ => none }

/-- ✗ An initialiser that arms nothing violates CORE-072 (line 2): `core072_t` is enabled by the
initial marking but holds no stamp, so it is not armed. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_noArmInit :
    ¬ CORE_072 (N := Nat) (T := Nat) core072_noArmInit RefTStep RefQFire := by
  intro h
  have := h.2.1 core072_X core072_m0 0 core072_t core072_t_inX (by decide)
  revert this
  decide

/-- An initialiser that arms exactly the transitions the initial marking enables, but stamps
them with the reading `0` while the clock reads the start reading: a runtime that seeds its
per-transition enable times from a zeroed buffer instead of the firing clock. -/
def core072_staleStampInit {N : Type} [DecidableEq N] : Init N :=
  fun X m0 now0 => { TSt.init X m0 0 with now := now0 }

/-- ✗ A stale initial stamp violates CORE-072 (line 2): at the start reading `100`, `core072_t`
holds the stamp `0`, not `100`. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_staleStampInit :
    ¬ CORE_072 (N := Nat) (T := Nat) core072_staleStampInit RefTStep RefQFire := by
  intro h
  have := h.2.1 core072_X core072_m0 100 core072_t core072_t_inX (by decide)
  revert this
  decide

/-- The example net with `Deadline(5)` timing and tolerance 0. -/
def core072_dX : TimedNet Nat := { core072_X with timing := fun _ => .deadline 5 }

/-- Why the stale stamp matters: at the start reading `100` it makes `core072_t` expired before
the first step (elapsed time 100 > 5), so it can be reaped but not fire. -/
theorem core072_staleStamp_expired :
    Expired core072_dX (core072_staleStampInit core072_dX core072_m0 100) core072_t := by
  decide

/-- The reference initial state at the same reading has `core072_t` ready. -/
theorem core072_ref_ready : Ready core072_dX (TSt.init core072_dX core072_m0 100) core072_t := by
  decide

/-- Mutant reading of line 2 that asks only that a transition is armed in the initial state
exactly when the initial marking enables it, whatever its stamp. -/
def CORE_072_mutant_armedOnly {N T : Type} [DecidableEq N] (I : Init N) (R : TRel N)
    (Q : QFireRel N T) : Prop :=
  (∀ X m0 now0, (I X m0 now0).m = m0) ∧
  (∀ X m0 now0 u, InNet X u → (Armed (I X m0 now0) u ↔ Enabled u m0)) ∧
  (∀ X p, UnknownPlace X p →
      (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => s.m p ≤ s'.m p))) ∧
  (∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
      on (fun M M' => Q t M δ e M'), shall (fun M M' => M p <+: M' p))

/-- The stale-stamp initialiser kills the arming-only mutant: it arms the right transitions, but
not with the start reading. -/
@[evidence mutant CORE_072]
theorem CORE_072_mutant_armedOnly_killed :
    CORE_072_mutant_armedOnly (N := Nat) (T := Nat) core072_staleStampInit RefTStep RefQFire ∧
      ¬ CORE_072 (N := Nat) (T := Nat) core072_staleStampInit RefTStep RefQFire :=
  ⟨⟨fun _ _ _ => rfl, fun X m0 _ u hu => (initArms_init X m0 0 u hu).1,
    core072_line3_ref, core072_line4_ref⟩, CORE_072_forbids_staleStampInit⟩

/-- An initialiser that keeps the initial tokens only on the places the net lists, as a store
with a slot per compiled place and nowhere to put the rest. -/
def core072_dropInit {N : Type} [DecidableEq N] : Init N :=
  fun X m0 now0 => TSt.init X (fun p => if p ∈ X.net.places then m0 p else 0) now0

/-- Mutant reading of CORE-072 that holds the initial marking on the places the net lists only:
line 1 asks only for listed places, and line 2 stamps what the initial state's own marking
enables. Lines 3 and 4 are as in CORE-072. -/
def CORE_072_mutant_declaredOnly {N T : Type} [DecidableEq N] (I : Init N) (R : TRel N)
    (Q : QFireRel N T) : Prop :=
  (∀ X m0 now0 p, p ∈ X.net.places → (I X m0 now0).m p = m0 p) ∧
  (∀ X m0 now0 u, InNet X u → Enabled u (I X m0 now0).m →
      (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0))) ∧
  (∀ X p, UnknownPlace X p →
      (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => s.m p ≤ s'.m p))) ∧
  (∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
      on (fun M M' => Q t M δ e M'), shall (fun M M' => M p <+: M' p))

/-- The initialiser that drops undeclared places kills the mutant: it satisfies the declared-only
reading, but not CORE-072, since the four initial tokens of the unknown place `9` are gone. -/
@[evidence mutant CORE_072]
theorem CORE_072_mutant_declaredOnly_killed :
    CORE_072_mutant_declaredOnly (N := Nat) (T := Nat) core072_dropInit RefTStep RefQFire ∧
      ¬ CORE_072 (N := Nat) (T := Nat) core072_dropInit RefTStep RefQFire := by
  refine ⟨⟨fun X m0 now0 p hp => ?_, fun X m0 now0 u hu he => ?_,
      core072_line3_ref, core072_line4_ref⟩, fun h => ?_⟩
  · show (if p ∈ X.net.places then m0 p else 0) = m0 p
    rw [if_pos hp]
  · exact (initArms_init X _ now0 u hu).2 he
  · have := congrFun (h.1 core072_X core072_m0 0) 9
    revert this
    decide

/-! ### Wrong step relations -/

/-- A timed step relation whose storage keeps only the places the net lists: every step of the
reference, after which the tokens of every other place are gone. -/
def core072_clearR {N : Type} [DecidableEq N] : TRel N := fun X s l s' =>
  ∃ s'', RefTStep X s l s'' ∧
    s' = { s'' with m := fun p => if p ∈ X.net.places then s''.m p else 0 }

/-- ✗ A store that keeps only the listed places violates CORE-072 (line 3): a delay of `0` from
the initial state empties the unknown place `9`. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_clearR :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init core072_clearR RefQFire := by
  intro h
  have := (h.2.2.1 core072_X 9 core072_unknown9).1 0 core072_s0 _
    ⟨_, RefTStepW.delay _ _ 0, rfl⟩
  revert this
  decide

/-- A timed step relation that is the reference on reaps and firings, but on every delay (even
of `0`) doubles the count of every place the net does not list: a backend that merges its side
map of uncompiled-place tokens into the marking each cycle without clearing it. -/
def core072_doubleMergeR {N : Type} [DecidableEq N] : TRel N := fun X s l s' =>
  match l with
  | .delay δ => s' = { s with now := s.now + δ,
                              m := fun p => if p ∈ X.net.places then s.m p else 2 * s.m p }
  | l => RefTStep X s l s'

/-- ✗ Inflating an unknown place on a delay violates CORE-072 (line 3): a delay of `0` from the
initial state turns the four tokens of place `9` into eight. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_doubleMergeR :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init core072_doubleMergeR RefQFire := by
  intro h
  have := (h.2.2.1 core072_X 9 core072_unknown9).1 0 core072_s0 _ rfl
  revert this
  decide

/-- The marking `m` rebuilt from the places the net lists: every other place emptied. -/
def core072_listedOnly {N : Type} [DecidableEq N] (X : TimedNet N) (m : N → Nat) : N → Nat :=
  fun p => if p ∈ X.net.places then m p else 0

/-- A timed step relation that is the reference except that a reap rebuilds the marking from the
places the net lists: a backend whose deadline enforcement rewrites its store from the compiled
places and loses the tokens of every other place. -/
def core072_clearOnReapR {N : Type} [DecidableEq N] : TRel N := fun X s l s' =>
  match l with
  | .reap u => ∃ s'', RefTStep X s (.reap u) s'' ∧ s' = { s'' with m := core072_listedOnly X s''.m }
  | l => RefTStep X s l s'

/-- A timed step relation that is the reference except that a firing rebuilds the marking from
the places the net lists, as `core072_clearR` does on every step. -/
def core072_clearOnFireR {N : Type} [DecidableEq N] : TRel N := fun X s l s' =>
  match l with
  | .fire t d => ∃ s'', RefTStep X s (.fire t d) s'' ∧
      s' = { s'' with m := core072_listedOnly X s''.m }
  | l => RefTStep X s l s'

/-- The example net with `Deadline(5)` timing, from the reference initial state at reading `0`:
the initial state. -/
def core072_ds0 : TSt Nat := TSt.init core072_dX core072_m0 0

/-- The state after a delay of `6` from `core072_ds0`: `core072_t` has been enabled for 6 time
units, past its deadline of 5. -/
def core072_ds1 : TSt Nat := { core072_ds0 with now := core072_ds0.now + 6 }

/-- The state after the reap of `core072_t` from `core072_ds1`. -/
def core072_ds2 : TSt Nat :=
  { core072_ds1 with stamp := fun n =>
      if n = core072_t.core.name then none else core072_ds1.stamp n }

theorem core072_t_mem_d : core072_t ∈ core072_dX.net.transitions := core072_t_mem

/-- Place `9` is an unknown place of the `Deadline(5)` net, which has the transitions of
`core072_X`. -/
theorem core072_unknown9_d : UnknownPlace core072_dX 9 := core072_unknown9

/-- The reference delays `core072_ds0` by `6`. -/
theorem core072_delay_d : RefTStep core072_dX core072_ds0 (.delay 6) core072_ds1 :=
  RefTStepW.delay _ _ 6

/-- The reference reaps the expired `core072_t` from `core072_ds1`. -/
theorem core072_reap_d : RefTStep core072_dX core072_ds1 (.reap core072_t) core072_ds2 :=
  RefTStepW.reap _ _ _ core072_t_mem_d (by decide)

/-- ✗ A reap that rebuilds the store from the listed places violates CORE-072 (line 3, "*shall
not* change its tokens ... when it reaps a transition"): the reap of the expired `core072_t`
empties the unknown place `9`, which held four tokens. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_clearOnReapR :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init core072_clearOnReapR RefQFire := by
  intro h
  have := (h.2.2.1 core072_dX 9 core072_unknown9_d).2.1 core072_t core072_ds1 _
    ⟨_, core072_reap_d, rfl⟩
  revert this
  decide

/-- ✗ A firing that rebuilds the store from the listed places violates CORE-072 (line 3, "*shall
not* drop any of them"): the firing of `core072_t` from the initial state empties the unknown
place `9`, which held four tokens. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_clearOnFireR :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init core072_clearOnFireR RefQFire := by
  intro h
  have := (h.2.2.1 core072_X 9 core072_unknown9).2.2 core072_t [3] core072_s0 _
    ⟨_, core072_fires, rfl⟩
  revert this
  decide

/-- The delay and the reap of line 3 on the reference: from the `Deadline(5)` net's initial state
a delay of `6` and the reap of the expired `core072_t` keep the four tokens of the unknown place
`9`, the case `CORE_072_forbids_clearOnReapR` breaks. -/
@[evidence nonvacuous CORE_072]
theorem CORE_072_nonvacuous_delayReap :
    RefTStep core072_dX core072_ds0 (.delay 6) core072_ds1 ∧
      Expired core072_dX core072_ds1 core072_t ∧
      RefTStep core072_dX core072_ds1 (.reap core072_t) core072_ds2 ∧
      UnknownPlace core072_dX 9 ∧
      core072_ds0.m 9 = 4 ∧ core072_ds1.m 9 = 4 ∧ core072_ds2.m 9 = 4 ∧
      ¬ Armed core072_ds2 core072_t :=
  ⟨core072_delay_d, by decide, core072_reap_d, core072_unknown9_d, by decide, by decide,
    by decide, by decide⟩

/-! ### Wrong queue firings -/

/-- A queue firing that rebuilds the marking from the places it consumes from or deposits into:
the reference firing, after which every other place is empty. -/
def core072_dropQ {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  ∃ M'', RefQFire t M δ e M'' ∧
    M' = fun p => if p ∈ inPlaces t ∨ p ∈ e.map Prod.fst then M'' p else []

/-- ✗ A queue firing that drops the places it does not touch violates CORE-072 (line 4): the
firing of `core072_t` empties the queue of the unknown place `9`. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_dropQ :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init RefTStep core072_dropQ := by
  intro h
  have := h.2.2.2 core072_X 9 core072_unknown9 core072_t core072_t_mem _ [(3, 30)] core072_M _
    ⟨_, core072_qfires, rfl⟩
  revert this
  decide

/-- A queue firing that reverses the queue of every place it neither consumes from nor emits
into: every token kept, the order lost. -/
def core072_reverseQ {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  ∃ M'', RefQFire t M δ e M'' ∧
    M' = fun p => if p ∈ inPlaces t ∨ p ∈ e.map Prod.fst then M'' p else (M'' p).reverse

/-- ✗ Reordering an unknown place violates CORE-072 (line 4): the firing of `core072_t` turns
place `9`'s queue `90, 91, 92, 93` into `93, 92, 91, 90`. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_reverseQ :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init RefTStep core072_reverseQ := by
  intro h
  have := h.2.2.2 core072_X 9 core072_unknown9 core072_t core072_t_mem _ [(3, 30)] core072_M _
    ⟨_, core072_qfires, rfl⟩
  revert this
  decide

/-- Mutant reading of line 4 that asks only that an unknown place keeps at least as many tokens
on a firing, in any order. -/
def CORE_072_mutant_countOnlyQ {N T : Type} [DecidableEq N] (I : Init N) (R : TRel N)
    (Q : QFireRel N T) : Prop :=
  (∀ X m0 now0, (I X m0 now0).m = m0) ∧
  (∀ X m0 now0 u, InNet X u → Enabled u m0 →
      (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0))) ∧
  (∀ X p, UnknownPlace X p →
      (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => s'.m p = s.m p)) ∧
      (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' => s.m p ≤ s'.m p))) ∧
  (∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
      on (fun M M' => Q t M δ e M'), shall (fun M M' => (M p).length ≤ (M' p).length))

/-- The reversing firing kills the count-only mutant: it keeps every token, so the counts hold,
but not their order. -/
@[evidence mutant CORE_072]
theorem CORE_072_mutant_countOnlyQ_killed :
    CORE_072_mutant_countOnlyQ (N := Nat) (T := Nat) TSt.init RefTStep core072_reverseQ ∧
      ¬ CORE_072 (N := Nat) (T := Nat) TSt.init RefTStep core072_reverseQ := by
  refine ⟨⟨fun X m0 now0 => init_marking X m0 now0,
      fun X m0 now0 u hu he => (initArms_init X m0 now0 u hu).2 he, core072_line3_ref, ?_⟩,
    CORE_072_forbids_reverseQ⟩
  intro X p hu t ht δ e M M' h
  obtain ⟨M'', hq, rfl⟩ := h
  have hM := core072_ref_queue hq (unknownPlace_not_arc hu ht) (unknownPlace_not_output hu ht)
  show (M p).length ≤ (if p ∈ inPlaces t ∨ p ∈ e.map Prod.fst then M'' p
    else (M'' p).reverse).length
  split <;> simp [hM]

/-- A queue firing that rebuilds every place it neither consumes from nor emits into as its
queue's tail followed by the whole queue: a ring whose head index moved by one without clearing
its slots, then read back at its full slot count. -/
def core072_staleRingQ {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  ∃ M'', RefQFire t M δ e M'' ∧
    M' = fun p => if p ∈ inPlaces t ∨ p ∈ e.map Prod.fst then M'' p else (M'' p).tail ++ M'' p

/-- ✗ A stale ring rotation violates CORE-072 (line 4): the firing of `core072_t` turns place
`9`'s queue `90, 91, 92, 93` into `91, 92, 93, 90, 91, 92, 93`, whose head is no longer `90`. -/
@[evidence forbids CORE_072]
theorem CORE_072_forbids_staleRingQ :
    ¬ CORE_072 (N := Nat) (T := Nat) TSt.init RefTStep core072_staleRingQ := by
  intro h
  have := h.2.2.2 core072_X 9 core072_unknown9 core072_t core072_t_mem _ [(3, 30)] core072_M _
    ⟨_, core072_qfires, rfl⟩
  revert this
  decide

/-- Mutant reading of lines 3 and 4 as retention only: every step of R leaves an unknown place
at least its count, and every firing of Q leaves its old queue as a sublist of the new one. -/
def CORE_072_mutant_retainOnly {N T : Type} [DecidableEq N] (I : Init N) (R : TRel N)
    (Q : QFireRel N T) : Prop :=
  (∀ X m0 now0, (I X m0 now0).m = m0) ∧
  (∀ X m0 now0 u, InNet X u → Enabled u m0 →
      (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0))) ∧
  (∀ X p, UnknownPlace X p → ∀ l, on (fun s s' => R X s l s'), shall (fun s s' =>
      s.m p ≤ s'.m p)) ∧
  (∀ X p, UnknownPlace X p → ∀ t, t ∈ X.net.transitions → ∀ δ e,
      on (fun M M' => Q t M δ e M'), shall (fun M M' => List.Sublist (M p) (M' p)))

/-- The doubling step kills the retention-only mutant: a delay keeps every token of an unknown
place and adds copies, which retention allows and line 3 does not. -/
@[evidence mutant CORE_072]
theorem CORE_072_mutant_retainOnly_killed_doubleMergeR :
    CORE_072_mutant_retainOnly (N := Nat) (T := Nat) TSt.init core072_doubleMergeR RefQFire ∧
      ¬ CORE_072 (N := Nat) (T := Nat) TSt.init core072_doubleMergeR RefQFire := by
  refine ⟨⟨fun X m0 now0 => init_marking X m0 now0,
      fun X m0 now0 u hu he => (initArms_init X m0 now0 u hu).2 he, ?_,
      fun _ _ hu _ ht _ _ M M' h => by
        show List.Sublist (M _) (M' _)
        rw [core072_ref_queue h (unknownPlace_not_arc hu ht) (unknownPlace_not_output hu ht)]⟩,
    CORE_072_forbids_doubleMergeR⟩
  intro X p hu l s s' h
  cases l with
  | delay δ =>
    subst h
    show s.m p ≤ (if p ∈ X.net.places then s.m p else 2 * s.m p)
    split <;> omega
  | reap t => exact (core072_ref_count hu h).ge
  | fire t d => exact (core072_ref_count hu h).ge

/-- The stale ring kills the retention-only mutant: the old queue is a sublist of the rotated
one, but not a prefix. -/
@[evidence mutant CORE_072]
theorem CORE_072_mutant_retainOnly_killed_staleRingQ :
    CORE_072_mutant_retainOnly (N := Nat) (T := Nat) TSt.init RefTStep core072_staleRingQ ∧
      ¬ CORE_072 (N := Nat) (T := Nat) TSt.init RefTStep core072_staleRingQ := by
  refine ⟨⟨fun X m0 now0 => init_marking X m0 now0,
      fun X m0 now0 u hu he => (initArms_init X m0 now0 u hu).2 he,
      fun _ _ hu _ _ _ h => (core072_ref_count hu h).ge, ?_⟩,
    CORE_072_forbids_staleRingQ⟩
  intro X p hu t ht δ e M M' h
  obtain ⟨M'', hq, rfl⟩ := h
  have hM := core072_ref_queue hq (unknownPlace_not_arc hu ht) (unknownPlace_not_output hu ht)
  show List.Sublist (M p) (if p ∈ inPlaces t ∨ p ∈ e.map Prod.fst then M'' p
    else (M'' p).tail ++ M'' p)
  split
  · rw [hM]
  · rw [hM]; exact List.sublist_append_right _ _

end Libpetri.Spec
