import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryAction
import Libpetri.Spec.Text.CORE_050

set_option linter.missingDocs true

/-!
# CORE-050: Transition action (`spec/01-core-model.md`)

CORE-050 says what an action receives and what a firing that ends with it deposits. The model is
a pair. `Q : QFireRel N T` is every queue firing: `t` fires from the queue marking `M`, delivers
`δ` to its action, emits `e` and leaves `M'`. `AF : ActFireRel N T` gives, for every action `a`
(`ActionRel`, `Spec/GlossaryAction.lean`), the queue firings that end with the completion of `a`.
A plain `QFireRel` cannot carry the second relation: it does not record how a firing ended, and a
firing that ends with the timeout outcome deposits tokens no action produced ([IO-013]), so the
executor whose action firings are all its queue firings is wrong (`CORE_050_forbids_timeout`).

The three lines: an action firing is a firing of `Q` with the same delivery (the action receives
what the firing delivers); its emission is one the action completes with on that delivery (the
firing deposits what the action completed with); and a firing of `Q` whose emission fills one
output branch and that the action completes with is an action firing (cover). The witness pair is
`RefQFire` and `refActionFire`. One wrong executor per line is killed: one that hands the action
every token of each input place, one that deposits tokens of its own in the places the action
wrote, and one whose firings never end with their action.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-050: Transition Action -/

requirement CORE_050
  id "CORE-050"
  title "Transition Action"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_050.s1, CORE_050.s2, CORE_050.s3
  reading "Let Q be the queue firings (Q t M δ e M': t fires from the queue marking M, delivers δ to its action, emits e and leaves M') and AF the action firings (AF a t M δ e M': such a firing under the action a that ends with the completion of a, which emitted e)."
          "For every action a, transition t, delivery δ and emission e: every firing in AF a is a firing in Q with the same delivery, emission and markings, so the action receives exactly what the firing delivers."
          "For every action a, transition t, delivery δ and emission e: if AF a has a firing of t delivering δ and emitting e, then a completes with e on t and δ."
          "For every action a, transition t, delivery δ and emission e whose places, in emission order, are one output branch of t and that a completes with on t and δ: every firing of t in Q delivering δ and emitting e is a firing in AF a."
  assumes "The model is the pair (Q, AF). Q is the queue firing relation (QFireRel, Spec/GlossaryQueue.lean; glossary: Queue order): Q t M δ e M' says that t fires from the queue marking M, delivers δ to its action (the tokens it consumed from each input place and the tokens its read arcs read, Delivered), emits e (places and tokens, in emission order) and leaves M'. AF is the action firing relation (ActFireRel, Spec/GlossaryAction.lean): AF a t M δ e M' is a firing of t under the action a that ends with the completion of a, which emitted e. A plain QFireRel cannot carry AF: it does not record how a firing ended, and a firing that ends with the timeout outcome deposits tokens no action produced (IO-013). The witness pair is RefQFire and refActionFire, the reference queue firings whose emission fills one output branch and that the action completes with."
          "An action (glossary: Action; ActionRel in Spec/GlossaryAction.lean) is a relation from a transition and the delivery to how the action ends: completing with an emission or failing with a message (EXEC-030). It is a relation, not a function, because an action may read the world. The transition context is read as the delivery δ; its accessors (input, inputs, inputToken, read, output) are CORE-060 to CORE-063's, stated over the same delivery."
          "Line 1 reads the first sentence as 'the action receives what the firing delivers': the delivery of a firing in AF is that of a firing in Q. Which tokens Q delivers is EXEC-010's second line (from each input place, its consumed oldest tokens) and EXEC-012 (one head per read arc), stated over the same Q in the joint model; CORE-050 does not restate them. An executor that hands the action every token of each input place violates line 1 against the reference Q (CORE_050_mutant_wholePlaces_killed)."
          "Line 2 reads the second sentence: the emission of a firing in AF a is one a completes with on that delivery, and the firing in Q (line 1) deposits exactly that emission; 'exactly' is Q's effect rule (EXEC-020: appended at the tail, in emission order; CORE-035). An executor that deposits tokens of its own in the places the action wrote violates it (CORE_050_mutant_placesOnly_killed), and so does one that counts a timed-out firing as a firing that ends with an action that never completes (CORE_050_forbids_timeout). Whether the action wrote its tokens through the context or returned them, they reach the firing as the emission it completes with; the context's output buffer is CORE-062's."
          "Line 3 reads the third sentence. The model has no stop, no immediate termination and no Timeout budget, so 'the executor admits the completion' is read as 'the action completes': an admitted completion is never that of a firing that ended with its timeout outcome or that a stop on a terminal place or an immediate termination abandoned (glossary: Admitted completion; EXEC-020), and which completions the executor admits is the executor model's (RefExec). A transition of the model has no match specification (Trans, ruling D16), which is the sentence's scope: on a correlated join the relay check of NU-054 may reject a completion that fills a branch (EXEC-021). An executor whose firings never end with their action violates the line (CORE_050_mutant_soundOnly_killed: the first draft, lines 1 and 2 alone, held of it)."
          "Line 3 is stated on the granularity of the reference: the places of the emission, in emission order, are one output branch as Out.branches lists it (glossary: Output branch, one token per place, the IO-016 convention). RefQFire compares the emitted places with an offered deposit as a list, so a completion that fills a branch with its places in another order, or that puts more than one token in a place of a branch, is no firing of RefQFire, and line 3 says nothing of it. That such a completion passes validation and deposits in the order the action produced its tokens is IO-015's set comparison and EXEC-020, stated at count level."
          "Line 3 is relative to Q, so CORE-050 alone holds of the empty pair. In the joint model Q covers every reference firing (QCovers) and delivers the reference delivery (EXEC-010, EXEC-012), so every completion with an output branch of an enabled transition is a firing in AF (core050_fires), every firing in AF, counted, is a firing of the count semantics (core050_projects), and every firing in Q ends with the completion of an action or with IO-013's timeout outcome (core050_endsBy)."
          "Ruling D17: 'ends with the completion of its action' is the admitted completion (glossary: Admitted completion). A completion that is not admitted (after the timeout outcome, a stop on a terminal place, an immediate termination) is not one line 2 speaks of. AF a holds a tuple only if a completes with its emission on its delivery (line 2), so an action that fails ends no firing in AF (EXEC-030), and an executor that counts a failed action as completing with no token violates line 2 (CORE_050_forbids_failAsEmpty). A tuple does not record how the firing ended: the child of a Timeout node is also an action branch, so the tuple of a firing that ended with the timeout outcome is in AF a whenever a can complete with the same emission (core050_timeout_overlap), and EndsByActionOrTimeout is a cover, not a partition; CORE_050_forbids_timeout therefore uses an action that never completes. Tokens an action publishes before it completes (the IO-015 flush, Rust and Python) are not in the atomic model, as in EXEC-020. The ν-correlated inputs of NU-020 are not modelled: RefQFire consumes oldest first from every input place (ruling D16)."
          "Q models an executor with output validation enabled, the default (CONC-026), as RefQFire does: a completion whose emission fills no output branch ends no firing (EXEC-021). The deposit of the action's write under the validation skip is CONC-026's."
          "A built transition carries its action as an identity tag (Act, CORE-020); the action a tag names is Act.interp I, the passthrough tag naming the action that completes with no token (CORE-051). By line 2 a firing under the passthrough tag deposits nothing (core050_passthrough_nil), the firing-level fact CORE-043 rests on (passthrough_never_offered)."
          "AC1 (the action receives a context with consumed input tokens and read token values) is line 1 together with EXEC-010 and EXEC-012 on the same Q; the context's accessors are CORE-060 and CORE-061."
          "AC2 (the action produces output tokens via the context or a return value) is line 2: through either channel the tokens are the emission the action completes with. That both channels exist is API shape."
          "AC3 (the action is asynchronous: it returns a future, a promise or a completion stage) is API shape, a Q-kind test, not encoded. That an action starts at one step and completes at a later one is CONC-002's, over the executor model (RefExec)."
          "The test derivation (an action that reads its input, transforms it and produces output) is CORE_050_nonvacuous: an action that doubles the value it is handed, fired on a place holding 7 then 8, receives the oldest token 7 and the firing deposits 14."
  signoff "2026-11-13 0e01354c5393cdc4 ai"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → ActFireRel N T → Prop :=
    fun Q AF =>
      (∀ a t δ e, on (fun M M' => AF a t M δ e M'), shall (fun M M' => Q t M δ e M')) ∧
      (∀ a t δ e, on (fun M M' => AF a t M δ e M'), shall (fun _ _ => a t δ (.ok e))) ∧
      (∀ a t δ e, OutputBranch t (e.map Prod.fst) → a t δ (.ok e) →
        on (fun M M' => Q t M δ e M'), shall (fun M M' => AF a t M δ e M'))

/- The pinned readable form of CORE-050: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_050 : {N T : Type} → [DecidableEq N] → QFireRel N T → ActFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q AF =>
  (∀ (a : ActionRel N T) (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
      on fun M M' => AF a t M δ e M', shall fun M M' => Q t M δ e M') ∧
    (∀ (a : ActionRel N T) (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
        on fun M M' => AF a t M δ e M', shall fun x x_1 => a t δ (Except.ok e)) ∧
      ∀ (a : ActionRel N T) (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
        OutputBranch t (List.map Prod.fst e) →
          a t δ (Except.ok e) → on fun M M' => Q t M δ e M', shall fun M M' => AF a t M δ e M'
-/
#guard_msgs in #print CORE_050

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N T : Type} [DecidableEq N]

/-- Line 1 of CORE-050: a firing that ends with its action is a firing, with the same delivery. -/
def core050_line1 (Q : QFireRel N T) (AF : ActFireRel N T) : Prop :=
  ∀ a t δ e, on (fun M M' => AF a t M δ e M'), shall (fun M M' => Q t M δ e M')

/-- Line 2 of CORE-050: the emission is one the action completes with on that delivery. -/
def core050_line2 (_Q : QFireRel N T) (AF : ActFireRel N T) : Prop :=
  ∀ a t δ e, on (fun M M' => AF a t M δ e M'), shall (fun _ _ => a t δ (.ok e))

/-- Line 3 of CORE-050: a firing whose emission fills an output branch and that the action
completes with ends with that completion. -/
def core050_line3 (Q : QFireRel N T) (AF : ActFireRel N T) : Prop :=
  ∀ a t δ e, OutputBranch t (e.map Prod.fst) → a t δ (.ok e) →
    on (fun M M' => Q t M δ e M'), shall (fun M M' => AF a t M δ e M')

/-- CORE-050 is its three lines. -/
theorem core050_iff (Q : QFireRel N T) (AF : ActFireRel N T) :
    CORE_050 Q AF ↔ core050_line1 Q AF ∧ core050_line2 Q AF ∧ core050_line3 Q AF :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference pair satisfies CORE-050: a reference action firing is a reference queue
firing whose emission fills an output branch and that the action completes with, and every such
queue firing is one. -/
@[evidence holds CORE_050]
theorem CORE_050_reference {N T : Type} [DecidableEq N] :
    CORE_050 (RefQFire (N := N) (T := T)) refActionFire :=
  ⟨fun _ _ _ _ _ _ h => h.1, fun _ _ _ _ _ _ h => h.2.2,
    fun _ _ _ _ hb ha _ _ h => ⟨h, hb, ha⟩⟩

/-! ### Consequences in the joint model -/

section Joint

variable {N T A : Type} [DecidableEq N]

/-- Counted, every firing that ends with its action is a firing of the count semantics `F` that
`Q` projects to (with `Q := RefQFire`, the reference firing `RefFire`). -/
theorem core050_projects {Q : QFireRel N T} {AF : ActFireRel N T} {F : FireRel N}
    (h : CORE_050 Q AF) (hp : QProjectsTo Q F) {a : ActionRel N T} {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : AF a t M δ e M') : F t (Counts M) (e.map Prod.fst) (Counts M') :=
  hp t M δ e M' (h.1 a t δ e M M' hf)

/-- **Agreement with IO-013**: with the count guard `QProjectsTo Q RefFire` of the queue blocks,
CORE-050 alone makes every queue firing end with the completion of an action or with IO-013's
timeout outcome (`refTimeoutOutcomeFire`). So `EndsByActionOrTimeout` is derived in the joint
model, not a separate conjunct: a firing whose deposit is an `action` choice is an action firing
under the action that completes with its emission (line 3), and every other is timed out. -/
theorem core050_endsBy {Q : QFireRel N T} {AF : ActFireRel N T} (h : CORE_050 Q AF)
    (hp : QProjectsTo Q RefFire) : EndsByActionOrTimeout Q AF refTimeoutOutcomeFire := by
  intro t M δ e M' hq
  obtain ⟨hen, ⟨ch, hch⟩, hM⟩ := hp t M δ e M' hq
  cases ch with
  | action i =>
    exact .inl ⟨fun _ _ r => r = .ok e,
      h.2.2 _ t δ e ((outputBranch_iff_action t _ _).2 ⟨i, hch⟩) rfl M M' hq⟩
  | timedOut j => exact .inr ⟨hen, ⟨j, hch⟩, hM⟩

/-- In the joint model the empty action firing relation is excluded: when `Q` covers every
reference firing and delivers the reference delivery, every completion of an enabled transition
whose emission fills an output branch ends a firing in `AF`. -/
theorem core050_fires {Q : QFireRel N T} {AF : ActFireRel N T} (h : CORE_050 Q AF)
    (hc : QCovers Q RefFire) (hδ : ∀ t M δ e M', Q t M δ e M' → δ = qDelivered M t)
    {a : ActionRel N T} {t : Trans N} {M : QueueMarking N T} {e : List (N × T)}
    (hen : Enabled t (Counts M)) (hb : OutputBranch t (e.map Prod.fst))
    (ha : a t (qDelivered M t) (.ok e)) : ∃ M', AF a t M (qDelivered M t) e M' := by
  obtain ⟨i, hi⟩ := (outputBranch_iff_action t (Consumes t (Counts M)) _).1 hb
  have hF : RefFire t (Counts M) (e.map Prod.fst)
      (fireNC (Counts M) t.core (depProd (e.map Prod.fst))) := ⟨hen, ⟨.action i, hi⟩, rfl⟩
  obtain ⟨δ, M', hq, -⟩ := hc t M e _ hF
  have hd := hδ t M δ e M' hq
  subst hd
  exact ⟨M', h.2.2 a t _ e hb ha M M' hq⟩

/-- By line 2, a firing that ends with the passthrough action deposits nothing, whatever the
table of other actions. -/
theorem core050_passthrough_nil {Q : QFireRel N T} {AF : ActFireRel N T} (h : CORE_050 Q AF)
    (I : A → ActionRel N T) {t : Trans N} {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} (hf : AF (Act.interp I .passthrough) t M δ e M') : e = [] :=
  (Except.ok.inj ((interp_passthrough I t δ _).1 (h.2.1 _ t δ e M M' hf))).symm ▸ rfl

/-- A built transition whose tag is passthrough deposits nothing when a firing ends with its
action. -/
theorem core050_tag_passthrough_nil {Q : QFireRel N T} {AF : ActFireRel N T}
    (h : CORE_050 Q AF) (I : A → ActionRel N T) {d : TransDef N A}
    (hd : IsPassthrough d.action) {M M' : QueueMarking N T} {δ : Delivered N T}
    {e : List (N × T)} (hf : TagFire AF I d M δ e M') : e = [] := by
  unfold TagFire at hf
  rw [show d.action = .passthrough from hd] at hf
  exact core050_passthrough_nil h I hf

end Joint

/-! ### Examples -/

/-- `u`: one input arc on place 0 (one token), output `Place 1`. -/
def core050_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `tTO`: one input arc on place 0, output `Timeout(Place 1)`. -/
def core050_tTO : Trans Nat :=
  { core := { name := "tTO", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.timeout (.place 1)) }

/-- Place 0 holds 7, then 8; every other place is empty. -/
def core050_M : QueueMarking Nat Nat := fun p => if p = 0 then [7, 8] else []

/-- The test derivation's action: it reads the tokens delivered from place 0, doubles each, and
completes with the results in place 1. -/
def core050_double : ActionFn Nat Nat := fun _ δ => .ok ((δ.inputs 0).map fun x => (1, 2 * x))

/-- An action that never completes: it only fails. -/
def core050_hangs : ActionRel Nat Nat := fun _ _ r => r = .error "hangs"

/-- An action that completes with one token 5 in place 1, whatever it is handed. -/
def core050_five : ActionRel Nat Nat := fun _ _ r => r = .ok [(1, 5)]

/-- `u` fires from `core050_M` with the emission `e`, a reference queue firing by the `action`
choice, whatever the token value. -/
theorem core050_u_fires (x : Nat) :
    RefQFire core050_u core050_M (qDelivered core050_M core050_u) [(1, x)]
      (qFire core050_M core050_u [(1, x)]) :=
  ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩

/-- Its emission fills the one output branch of `u`. -/
theorem core050_u_branch (x : Nat) : OutputBranch core050_u ([(1, x)].map Prod.fst) :=
  show ([1] : List Nat) ∈ [[1]] from List.mem_singleton.2 rfl

/-- ✓ CORE-050 is not vacuous. The test derivation: on `u` from a place 0 holding 7 then 8, the
doubling action receives the oldest token 7, and the reference action firing deposits 14 in
place 1 and leaves 8 in place 0. And on `Timeout(Place 1)` the reference has a queue firing that
deposits a token 99 in place 1 (the timeout outcome), which is not a firing that ends with an
action that never completes. -/
@[evidence nonvacuous CORE_050]
theorem CORE_050_nonvacuous :
    (qDelivered core050_M core050_u).inputs 0 = [7] ∧
    refActionFire core050_double.rel core050_u core050_M (qDelivered core050_M core050_u)
      [(1, 14)] (qFire core050_M core050_u [(1, 14)]) ∧
    qFire core050_M core050_u [(1, 14)] 0 = [8] ∧
    qFire core050_M core050_u [(1, 14)] 1 = [14] ∧
    RefQFire core050_tTO core050_M (qDelivered core050_M core050_tTO) [(1, 99)]
      (qFire core050_M core050_tTO [(1, 99)]) ∧
    ¬ refActionFire core050_hangs core050_tTO core050_M (qDelivered core050_M core050_tTO)
      [(1, 99)] (qFire core050_M core050_tTO [(1, 99)]) := by
  refine ⟨by decide, ⟨core050_u_fires 14, core050_u_branch 14, rfl⟩, by decide, by decide,
    ⟨by decide, ⟨.timedOut 0, rfl⟩, rfl, rfl⟩, ?_⟩
  rintro ⟨-, -, h⟩
  cases h

/-! ### A wrong executor: every queue firing ends with the action -/

/-- An executor that counts every queue firing as a firing that ends with every action, the
timed-out firings included, where the executor, not the action, makes the deposit. -/
def core050_allFire {N T : Type} [DecidableEq N] : ActFireRel N T :=
  fun _ t M δ e M' => RefQFire t M δ e M'

/-- ✗ It violates line 2: on `Timeout(Place 1)` under an action that never completes, its
timed-out firing deposits a token 99 the action did not produce. -/
@[evidence forbids CORE_050]
theorem CORE_050_forbids_timeout :
    ¬ CORE_050 (RefQFire (N := Nat) (T := Nat)) core050_allFire := by
  intro h
  have := h.2.1 core050_hangs core050_tTO _ [(1, 99)] _ _
    (⟨by decide, ⟨.timedOut 0, rfl⟩, rfl, rfl⟩ :
      RefQFire core050_tTO core050_M (qDelivered core050_M core050_tTO) [(1, 99)]
        (qFire core050_M core050_tTO [(1, 99)]))
  cases this

/-- **A tuple does not record how the firing ended**: on `Timeout(Place 1)`, the same tuple is a
firing that ends with the timeout outcome (IO-013's `refTimeoutOutcomeFire`, counted) and a
reference action firing under the action that completes with a token 5 in place 1, since the
child of a Timeout node is also an action branch. So `EndsByActionOrTimeout` is a cover, not a
partition, and `CORE_050_forbids_timeout` uses an action that never completes. -/
theorem core050_timeout_overlap :
    refActionFire core050_five core050_tTO core050_M (qDelivered core050_M core050_tTO)
      [(1, 5)] (qFire core050_M core050_tTO [(1, 5)]) ∧
    refTimeoutOutcomeFire core050_tTO (Counts core050_M) [1]
      (Counts (qFire core050_M core050_tTO [(1, 5)])) := by
  refine ⟨⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, List.mem_singleton.2 rfl, rfl⟩, ?_⟩
  have hf : RefQFire core050_tTO core050_M (qDelivered core050_M core050_tTO) [(1, 5)]
      (qFire core050_M core050_tTO [(1, 5)]) := ⟨by decide, ⟨.timedOut 0, rfl⟩, rfl, rfl⟩
  exact ⟨hf.1, ⟨0, rfl⟩, hf.fires.2.2⟩

/-! ### A wrong executor: a failed action counted as completing with no token -/

/-- `s`: one input arc on place 0, no output specification (a sink). -/
def core050_s : Trans Nat :=
  { core := { name := "s", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- An executor that counts a failed action ([EXEC-030]) as a firing that ends with the action
and deposits nothing. -/
def core050_failAsEmpty {N T : Type} [DecidableEq N] : ActFireRel N T := fun a t M δ e M' =>
  RefQFire t M δ e M' ∧ OutputBranch t (e.map Prod.fst) ∧
    (a t δ (.ok e) ∨ (e = [] ∧ ∃ m, a t δ (.error m)))

/-- Lines 1 and 3 hold of it: only line 2 excludes it. -/
theorem core050_failAsEmpty_lines13 :
    core050_line1 (RefQFire (N := Nat) (T := Nat)) core050_failAsEmpty ∧
      core050_line3 (RefQFire (N := Nat) (T := Nat)) core050_failAsEmpty :=
  ⟨fun _ _ _ _ _ _ h => h.1, fun _ _ _ _ hb ha _ _ h => ⟨h, hb, .inl ha⟩⟩

/-- ✗ It violates line 2: on the sink `s` under an action that only fails, it counts the firing
that deposits nothing as one that ends with the action, which never completed. -/
@[evidence forbids CORE_050]
theorem CORE_050_forbids_failAsEmpty :
    ¬ CORE_050 (RefQFire (N := Nat) (T := Nat)) core050_failAsEmpty := by
  intro h
  have hf : core050_failAsEmpty core050_hangs core050_s core050_M
      (qDelivered core050_M core050_s) [] (qFire core050_M core050_s []) :=
    ⟨⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, rfl, .inr ⟨rfl, "hangs", rfl⟩⟩
  have := h.2.1 _ _ _ _ _ _ hf
  cases this

/-! ### Mutant: line 1 with every token of each input place delivered -/

section MutantWhole

variable {N T : Type} [DecidableEq N]

/-- Mutant reading of line 1 ("receives a context with the input tokens" read as "the tokens of
its input places"): the action of a firing that ends with it is handed every token of each input
place. Line 2 is as in CORE-050. -/
def CORE_050_mutant_wholePlaces (Q : QFireRel N T) (AF : ActFireRel N T) : Prop :=
  (∀ a t M δ e M', AF a t M δ e M' → ∀ p ∈ inPlaces t, δ.inputs p = M p) ∧
    core050_line2 Q AF

/-- The delivery of every token of each input place, with the reference reads. -/
def core050_wholeDelivery (M : QueueMarking N T) (t : Trans N) : Delivered N T :=
  ⟨fun p => if p ∈ inPlaces t then M p else [], (qDelivered M t).reads⟩

/-- An executor that consumes and deposits as the reference does but hands the action every token
of each input place. -/
def core050_wholeAF : ActFireRel N T := fun a t M δ e M' =>
  RefQFire t M (qDelivered M t) e M' ∧ OutputBranch t (e.map Prod.fst) ∧
    δ = core050_wholeDelivery M t ∧ a t δ (.ok e)

end MutantWhole

/-- ✗ The whole-place executor kills the mutant: it meets the wrong reading, but on `u` from a
place 0 holding 7 then 8 the firing consumes only 7 while the action is handed 7 and 8, so its
delivery is not the firing's (line 1). -/
@[evidence mutant CORE_050]
theorem CORE_050_mutant_wholePlaces_killed :
    CORE_050_mutant_wholePlaces (RefQFire (N := Nat) (T := Nat)) core050_wholeAF ∧
      ¬ CORE_050 (RefQFire (N := Nat) (T := Nat)) core050_wholeAF := by
  refine ⟨⟨fun a t M δ e M' h p hp => ?_, fun a t δ e M M' h => h.2.2.2⟩, fun h => ?_⟩
  · rw [h.2.2.1]
    simp [core050_wholeDelivery, hp]
  · have hw : core050_wholeAF core050_five core050_u core050_M
        (core050_wholeDelivery core050_M core050_u) [(1, 5)]
        (qFire core050_M core050_u [(1, 5)]) :=
      ⟨core050_u_fires 5, core050_u_branch 5, rfl, rfl⟩
    have hq := h.1 _ _ _ _ _ _ hw
    have hi := congrArg (fun δ : Delivered Nat Nat => δ.inputs 0) hq.2.2.1
    exact absurd hi (by decide)

/-! ### Mutant: line 2 with the action choosing places only -/

section MutantPlaces

variable {N T : Type} [DecidableEq N]

/-- Mutant reading of line 2 ("produces output tokens" read as "chooses the places"): the
emission of a firing that ends with the action has the places of a completion of the action,
and its tokens may be the executor's own. Lines 1 and 3 are as in CORE-050. -/
def CORE_050_mutant_placesOnly (Q : QFireRel N T) (AF : ActFireRel N T) : Prop :=
  core050_line1 Q AF ∧
    (∀ a t M δ e M', AF a t M δ e M' →
      ∃ e', a t δ (.ok e') ∧ e'.map Prod.fst = e.map Prod.fst) ∧
    core050_line3 Q AF

/-- An executor that deposits, in the places the action wrote, tokens of its own. -/
def core050_mintAF : ActFireRel N T := fun a t M δ e M' =>
  RefQFire t M δ e M' ∧ OutputBranch t (e.map Prod.fst) ∧
    ∃ e', a t δ (.ok e') ∧ e'.map Prod.fst = e.map Prod.fst

end MutantPlaces

/-- ✗ The minting executor kills the mutant: it meets the wrong reading, but on `u` under the
action that completes with a token 5 in place 1 it deposits a token 6 there (line 2). -/
@[evidence mutant CORE_050]
theorem CORE_050_mutant_placesOnly_killed :
    CORE_050_mutant_placesOnly (RefQFire (N := Nat) (T := Nat)) core050_mintAF ∧
      ¬ CORE_050 (RefQFire (N := Nat) (T := Nat)) core050_mintAF := by
  refine ⟨⟨fun _ _ _ _ _ _ h => h.1, fun _ _ _ _ _ _ h => h.2.2,
    fun _ _ _ e hb ha _ _ h => ⟨h, hb, e, ha, rfl⟩⟩, fun h => ?_⟩
  have hm : core050_mintAF core050_five core050_u core050_M (qDelivered core050_M core050_u)
      [(1, 6)] (qFire core050_M core050_u [(1, 6)]) :=
    ⟨core050_u_fires 6, core050_u_branch 6, [(1, 5)], rfl, rfl⟩
  have h2 := h.2.1 _ _ _ _ _ _ hm
  have := Except.ok.inj h2
  exact absurd this (by decide)

/-! ### Mutant: lines 1 and 2 alone (the first draft) -/

/-- Mutant reading (the first draft of the block): lines 1 and 2 alone, without the cover line.
It holds of the executor whose firings never end with their action. -/
def CORE_050_mutant_soundOnly {N T : Type} [DecidableEq N] (Q : QFireRel N T)
    (AF : ActFireRel N T) : Prop :=
  core050_line1 Q AF ∧ core050_line2 Q AF

/-- An executor whose firings never end with their action. -/
def core050_neverAF {N T : Type} : ActFireRel N T := fun _ _ _ _ _ _ => False

/-- ✗ The never-ending executor kills the mutant: it meets lines 1 and 2, but `u` fires from
`core050_M` with an emission that fills its output branch and that the action completes with,
and that firing is not one that ends with the action (line 3). -/
@[evidence mutant CORE_050]
theorem CORE_050_mutant_soundOnly_killed :
    CORE_050_mutant_soundOnly (RefQFire (N := Nat) (T := Nat)) core050_neverAF ∧
      ¬ CORE_050 (RefQFire (N := Nat) (T := Nat)) core050_neverAF :=
  ⟨⟨fun _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim⟩,
    fun h => h.2.2 core050_five core050_u _ [(1, 5)] (core050_u_branch 5) rfl _ _
      (core050_u_fires 5)⟩

end Libpetri.Spec
