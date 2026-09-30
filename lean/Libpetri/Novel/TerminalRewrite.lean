import Libpetri.Strengthening

/-!
# The terminal-place rewrite ([EXEC-042])

[EXEC-042]: a terminal place ends the run once it holds a token — no transition starts after
the deposit that marks it (strict stop), and an external event queued behind it is refused
([ENV-004]). The verifier applies terminals with no restatement by the caller: it verifies the
net in which every terminal inhibits every transition, is a sink, and is a conditional-sink
marker for every place ([VER-014]). For atomic firings the rewrite is exact
(`terminal_rewrite_exact`); with actions in flight see **In-flight actions** below.

The Rust behaviour:
* `inhibit_on_terminals` (`rust/libpetri-verification/src/terminal_places.rs`) returns `None`
  when the net declares no terminal — the caller keeps the original net — and otherwise
  `net.map_transitions(|t| t.with_added_inhibitors(terminals))`.
  `Transition::with_added_inhibitors` (`rust/libpetri-core/src/transition.rs`) appends each
  terminal in declaration order unless the growing list already holds it. `addInhibitors` is
  that fold; `inhibitOnTerminals` the `Option`; `verifiedNet` the caller's `match`
  (`SmtVerifier::verify_terminals_split`, `smt_verifier.rs`). `SmtVerifier::verify_terminals`
  now runs it after the in-flight split (`with_in_flight`, `in_flight::split_in_flight`,
  `InFlight.lean`): the net rewritten here is the split net, so every transition of it, each
  completion step `complete:t` included, gets the terminal inhibitors. A terminal counts as a
  non-monotone test, so every transition that can mark a terminal is split.
* `flatten` (`net_flattener.rs`) copies a transition's `inhibitor_places` into every one of
  its flat branches, so rewriting before flattening is rewriting each flat transition's
  `Transition` — which is how the rewrite acts on a `FlatNet` here.
* `SmtVerifier::with_net_terminals` makes each terminal a sink and
  `sink_places_when(P, all places)`: a marked terminal excuses every place. So the `Bad` of the
  two arms that read sinks and excuses implies `NoTerminal`: `DeadlockFree` (a stranded place
  needs every excusing marker, the terminal included, unmarked) and `TerminatesAtSink` (every
  sink, the terminal included, unmarked). `QuiescentCount` and `JoinedOrDeadLettered` read
  neither, so their `Bad` can hold with a terminal marked.
* The executor's strict stop (`run_sync`, `executor_core/executor.rs`): the loop breaks at
  the top of a cycle once `terminal_reached()`, and inside the firing pass right after the
  deposit that marks one. At atomic-firing granularity a firing happens only from a marking
  with no terminal marked — `StepStopRel`. `run_sync` has no injection; the refusal of a
  queued external event is the async path's: `run_async` re-reads `terminal_reached()` before
  each completion, flush and signal it admits, and `handle_signal` stops an `EventBatch` at
  the first token behind a terminal deposit (`executor_core/executor.rs`). `StepStopInjRel`
  models both.

Results:
* `mem_addInhibitors`, `addInhibitors_idem`: the fold adds exactly the terminals, and the
  rewrite is idempotent (the doc comment's claim).
* `enabledA_rewrite`, `fireA_rewrite`: a rewritten transition is enabled iff the original is
  and no terminal is marked; its firing effect is unchanged.
* `terminal_rewrite_exact` — env-free: `ReachA` of the verified net is exactly the strict-stop
  reachable set, for every terminal list including `[]` (the `None` branch). Hence
  `terminal_bad_transfer`: `Proven` on the verified net ⟺ no strict-stop run reaches `Bad`,
  for every `Bad`.
* With environment places the rewrite is **not** exact. The encoder's injection rule carries no
  terminal guard, so the model may inject after a terminal is marked, which the runtime refuses.
  `terminal_rewrite_sound_inj` is the inclusion that holds; `terminal_rewrite_inj_not_exact` is
  a witness (`Unreachable {e, P}` holds under strict stop, the rewritten model reaches it: a
  spurious `Violated`, never a false `Proven`); `terminal_rewrite_inj_extra` characterises the
  surplus (a strict-stop marking with a terminal marked, plus env tokens); and
  `terminal_bad_transfer_excused` restores exactness for every `Bad` a marked terminal excuses
  — after `with_net_terminals`, the `DeadlockFree` and `TerminatesAtSink` arms (not
  `QuiescentCount` or `JoinedOrDeadLettered`).
* `deadlock_bad_transfer`: the rewritten net's DeadlockFree violation with the terminal excuse
  is exactly the original net's violation with no terminal marked. It is stated for the
  reap-aware quiescence the shipped `encode_quiescent` emits (`DeadA rp`: every row that is
  not reapable is disabled; `rp` is `flatten_with_reapable`'s mark, `fun _ => false` under
  `assume_no_reaping`). The rewrite keeps each transition's name and timing, so the mark is
  the same on both nets (`hrp`, which a name-based mark meets by `rewriteT_name`).
* `strict_stop_simulated`: `proposition_one` for the strict-stop concrete semantics.

Row multiplicity: the flat semantics here is `fireA` and the concrete step `StepCRel`
(`UnitOutput`), so `strict_stop_simulated` and every `ReachA` statement cover duplicate-free rows
only, not a timeout forward row with `post[to] = k ≥ 2` (`ForwardDeposit.lean`). The rewrite
touches inhibitors alone and `fireAD` does not read them, so the argument carries over; it is
not restated.

**In-flight actions.** The model is atomic, and the Rust applies it to the split net, whose
completion steps are ordinary transitions here. With the completions inhibited too, the strict
stop refuses a completion once a terminal is marked, which is [EXEC-042]'s abandoned in-flight
action: its deposit never lands. `InFlight.lean` carries that strict stop (`live`, gating every
step of the executor and of the split net) and proves the split net covers the executor
(`split_covers_executor`); `terminal_rewrite_exact` over the split net then describes the split
net's runs, so together they over-approximate the executor.
An action the stop abandons is harmless to a property whose `Bad` only more tokens can make
true (`split_safety_sound`), and to `DeadlockFree` and `TerminatesAtSink`, whose `Bad` a marked
terminal excuses. It can break a `QuiescentCount` lower bound, whose count an abandoned
deposit leaves short: `quiescent_count_demand` splits every depositor into a counted or waiver
place for it, and `quiescent_count_stop_sound` proves the stop is then covered
(`terminal_stop_witness` is the net the plain split gets wrong). The in-flight places are
excused wherever a token could rest there: a marked terminal excuses every place, and otherwise
`complete:t` is enabled and immediate, so a marked `inflight:t` never rests. TypeScript's
completion-phase deposit is out of scope.
-/

namespace Libpetri.Novel.TerminalRewrite

open Libpetri

/-! ## The rewrite -/

/-- `Transition::with_added_inhibitors`: append each extra place unless the list holds it. -/
def addInhibitors (inh terms : List PlaceId) : List PlaceId :=
  terms.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) inh

/-- One transition with every terminal inhibiting it. -/
def rewriteT (terms : List PlaceId) (t : Transition) : Transition :=
  { t with inhibitors := addInhibitors t.inhibitors terms }

/-- The rewrite applied to each flat transition (see the module note on `flatten`). -/
def rewriteNet (terms : List PlaceId) (net : FlatNet) : FlatNet :=
  net.map fun ft => (rewriteT terms ft.1, ft.2)

/-- `inhibit_on_terminals`: `None` without terminals. -/
def inhibitOnTerminals (terms : List PlaceId) (net : FlatNet) : Option FlatNet :=
  if terms.isEmpty then none else some (rewriteNet terms net)

/-- The net the verifier flattens: the rewrite, or the original net on `None`. -/
def verifiedNet (terms : List PlaceId) (net : FlatNet) : FlatNet :=
  (inhibitOnTerminals terms net).getD net

theorem mem_addInhibitors {p : PlaceId} :
    ∀ {inh : List PlaceId} {terms : List PlaceId},
      p ∈ addInhibitors inh terms ↔ p ∈ inh ∨ p ∈ terms
  | inh, [] => by simp [addInhibitors]
  | inh, q :: rest => by
    show p ∈ addInhibitors (if inh.contains q then inh else inh ++ [q]) rest ↔ _
    rw [mem_addInhibitors]
    by_cases hq : inh.contains q = true
    · rw [if_pos hq]
      have : q ∈ inh := by simpa using hq
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl this
          · exact Or.inr h
    · rw [if_neg hq]
      simp only [List.mem_append, List.mem_cons]
      tauto

/-- A fold over places the list already holds is the identity. -/
theorem addInhibitors_of_subset :
    ∀ {inh terms : List PlaceId}, (∀ p ∈ terms, p ∈ inh) → addInhibitors inh terms = inh
  | _, [], _ => rfl
  | inh, q :: rest, h => by
    show addInhibitors (if inh.contains q then inh else inh ++ [q]) rest = inh
    have hq : inh.contains q = true := by simpa using h q (by simp)
    rw [if_pos hq]
    exact addInhibitors_of_subset fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- **Idempotence** (the doc comment of `inhibit_on_terminals`). -/
theorem addInhibitors_idem (inh terms : List PlaceId) :
    addInhibitors (addInhibitors inh terms) terms = addInhibitors inh terms :=
  addInhibitors_of_subset fun _ hp => mem_addInhibitors.mpr (Or.inr hp)

/-! ## Effect on enablement and firing -/

/-- No terminal holds a token. -/
def NoTerminal (terms : List PlaceId) (a : AMarking) : Prop :=
  ∀ p ∈ terms, a p = 0

theorem enabledA_rewrite (terms : List PlaceId) (t : Transition) (a : AMarking) :
    enabledA a (rewriteT terms t) = true ↔ enabledA a t = true ∧ NoTerminal terms a := by
  unfold enabledA rewriteT NoTerminal
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hi, hinh⟩, hr⟩
    exact ⟨⟨⟨hi, fun p hp => hinh p (mem_addInhibitors.mpr (Or.inl hp))⟩, hr⟩,
      fun p hp => hinh p (mem_addInhibitors.mpr (Or.inr hp))⟩
  · rintro ⟨⟨⟨hi, hinh⟩, hr⟩, ht⟩
    refine ⟨⟨hi, fun p hp => ?_⟩, hr⟩
    rcases mem_addInhibitors.mp hp with h | h
    · exact hinh p h
    · exact ht p h

theorem fireA_rewrite (terms : List PlaceId) (t : Transition) (a : AMarking)
    (br : List PlaceId) : fireA a (rewriteT terms t) br = fireA a t br := rfl

/-! ## Strict-stop semantics and exactness -/

/-- One step of the strict-stop runtime at atomic-firing granularity: a firing happens only
while no terminal is marked. -/
def StepStopRel (net : FlatNet) (terms : List PlaceId) (a a' : AMarking) : Prop :=
  NoTerminal terms a ∧ StepARel net a a'

/-- Markings a strict-stop run reaches. -/
def ReachStop (net : FlatNet) (terms : List PlaceId) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepStopRel net terms) a0

/-- The rewritten net's step relation is the strict-stop relation. -/
theorem step_rewrite_iff (net : FlatNet) (terms : List PlaceId) (a a' : AMarking) :
    StepARel (rewriteNet terms net) a a' ↔ StepStopRel net terms a a' := by
  unfold StepARel StepStopRel rewriteNet
  constructor
  · rintro ⟨ft', hmem, hen, rfl⟩
    obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨hen', hnt⟩ := (enabledA_rewrite terms ft.1 a).mp hen
    exact ⟨hnt, ft, hft, hen', rfl⟩
  · rintro ⟨hnt, ft, hft, hen, rfl⟩
    exact ⟨(rewriteT terms ft.1, ft.2), List.mem_map.mpr ⟨ft, hft, rfl⟩,
      (enabledA_rewrite terms ft.1 a).mpr ⟨hen, hnt⟩, rfl⟩

theorem verifiedNet_nil (net : FlatNet) : verifiedNet [] net = net := rfl

theorem verifiedNet_cons (net : FlatNet) (p : PlaceId) (ps : List PlaceId) :
    verifiedNet (p :: ps) net = rewriteNet (p :: ps) net := rfl

/-- **[EXEC-042] exactness, env-free.** The verified net reaches exactly the strict-stop
markings — for any terminal list, the `None` branch (no terminals) included. -/
theorem terminal_rewrite_exact (net : FlatNet) (terms : List PlaceId) (a0 a : AMarking) :
    ReachA (verifiedNet terms net) a0 a ↔ ReachStop net terms a0 a := by
  cases terms with
  | nil =>
    rw [verifiedNet_nil]
    unfold ReachA ReachStop
    have : StepStopRel net [] = StepARel net := by
      funext a a'; simp [StepStopRel, NoTerminal]
    rw [this]
  | cons p ps =>
    rw [verifiedNet_cons]
    unfold ReachA ReachStop
    have : StepARel (rewriteNet (p :: ps) net) = StepStopRel net (p :: ps) := by
      funext a a'; exact propext (step_rewrite_iff net _ a a')
    rw [this]

/-- **Bad transfer, env-free**: a `Proven` on the verified net is a `Proven` for the strict-stop
runtime and conversely, for every violation predicate. -/
theorem terminal_bad_transfer (net : FlatNet) (terms : List PlaceId) (a0 : AMarking)
    (Bad : AMarking → Prop) :
    ProvenFor (ReachA (verifiedNet terms net) a0) Bad ↔ ProvenFor (ReachStop net terms a0) Bad :=
  ⟨fun h a hr => h a ((terminal_rewrite_exact net terms a0 a).mpr hr),
   fun h a hr => h a ((terminal_rewrite_exact net terms a0 a).mp hr)⟩

/-! ## The quiescence arm -/

/-- `encode_quiescent` on an env-free net, as shipped: every flat transition that is not
reapable is disabled (`encode_quiescent` skips the rows `flatten_with_reapable` marked
`ft.reapable`; `ReapAware.lean` proves that reading sound for the executor's rests). With
`rp = fun _ => false` (`assume_no_reaping`, or no `Deadline` / `Window` transition) it is the
strict "no flat transition is enabled". -/
def DeadA (rp : Transition → Bool) (net : FlatNet) (a : AMarking) : Prop :=
  ∀ ft ∈ net, rp ft.1 = false → enabledA a ft.1 = false

/-- The rewrite keeps the name, so a mark read off the name is kept. -/
theorem rewriteT_name (terms : List PlaceId) (t : Transition) : (rewriteT terms t).name = t.name :=
  rfl

theorem deadA_rewrite {rp : Transition → Bool} (net : FlatNet) (terms : List PlaceId)
    (hrp : ∀ t, rp (rewriteT terms t) = rp t) (a : AMarking) :
    DeadA rp (rewriteNet terms net) a ↔ (NoTerminal terms a → DeadA rp net a) := by
  unfold DeadA rewriteNet
  constructor
  · intro h hnt ft hft hrf
    have := h _ (List.mem_map.mpr ⟨ft, hft, rfl⟩) (by simpa [hrp] using hrf)
    cases hen : enabledA a ft.1
    · rfl
    · exact absurd ((enabledA_rewrite terms ft.1 a).mpr ⟨hen, hnt⟩) (by simp [this])
  · intro h ft' hmem hrf
    obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp hmem
    cases hen : enabledA a (rewriteT terms ft.1)
    · rfl
    · obtain ⟨hen', hnt⟩ := (enabledA_rewrite terms ft.1 a).mp hen
      simp [h hnt ft hft (by simpa [hrp] using hrf)] at hen'

/-- **DeadlockFree transfer.** `strand` is the stranding disjunction over the caller's sinks
(`stranded_conditions`, unmodelled); `with_net_terminals` adds the terminal excuse, i.e. the
conjunct `NoTerminal`. The verified net's violation is then exactly the original net's
quiescent stranding with no terminal marked — the strict-stop runtime resting `quiescent`
rather than `terminal` with a token stranded. -/
theorem deadlock_bad_transfer {rp : Transition → Bool} (net : FlatNet) (terms : List PlaceId)
    (hrp : ∀ terms t, rp (rewriteT terms t) = rp t)
    (strand : AMarking → Prop) (a : AMarking) :
    (DeadA rp (verifiedNet terms net) a ∧ strand a ∧ NoTerminal terms a)
      ↔ (DeadA rp net a ∧ strand a ∧ NoTerminal terms a) := by
  cases terms with
  | nil => rfl
  | cons p ps =>
    rw [verifiedNet_cons, deadA_rewrite net _ (hrp _)]
    constructor
    · rintro ⟨hd, hs, hnt⟩; exact ⟨hd hnt, hs, hnt⟩
    · rintro ⟨hd, hs, hnt⟩; exact ⟨fun _ => hd, hs, hnt⟩

/-! ## Environment places: sound, not exact -/

/-- The strict-stop runtime with injection: neither a firing nor an injection is admitted once
a terminal is marked ([EXEC-042] "queued external events are refused": `run_async`'s admission
loops and `handle_signal`'s batch check, not `run_sync`, which injects nothing). -/
def StepStopInjRel (net : FlatNet) (envs terms : List PlaceId) (a a' : AMarking) : Prop :=
  NoTerminal terms a ∧ StepAInjRel net envs a a'

def ReachStopInj (net : FlatNet) (envs terms : List PlaceId) (a0 : AMarking) :
    AMarking → Prop :=
  Relation.ReflTransGen (StepStopInjRel net envs terms) a0

/-- **Soundness with injection**: every strict-stop marking is reachable in the verified net's
injected relation (`encode_injection_rule`, no terminal guard). -/
theorem terminal_rewrite_sound_inj (net : FlatNet) (envs terms : List PlaceId)
    {a0 a : AMarking} (h : ReachStopInj net envs terms a0 a) :
    ReachAInj (verifiedNet terms net) envs a0 a := by
  induction h with
  | refl => exact ReachAInj.init
  | tail _ hs ih =>
    obtain ⟨hnt, hst⟩ := hs
    refine Relation.ReflTransGen.tail ih ?_
    rcases hst with hstep | hinj
    · left
      cases terms with
      | nil => exact hstep
      | cons p ps => exact (step_rewrite_iff net (p :: ps) _ _).mpr ⟨hnt, hstep⟩
    · exact Or.inr hinj

/-- **The surplus is post-terminal injection.** A marking of the verified net's injected
relation is a strict-stop marking, or a strict-stop marking `b` with a terminal marked plus
tokens on environment places only. -/
theorem terminal_rewrite_inj_extra (net : FlatNet) (envs terms : List PlaceId)
    {a0 a : AMarking} (h : ReachAInj (verifiedNet terms net) envs a0 a) :
    ReachStopInj net envs terms a0 a
      ∨ ∃ b, ReachStopInj net envs terms a0 b ∧ ¬ NoTerminal terms b
          ∧ (∀ q, q ∉ envs → a q = b q) ∧ (∀ q, b q ≤ a q) := by
  induction h with
  | init => exact Or.inl Relation.ReflTransGen.refl
  | @step a1 ft _ hmem hen ih =>
    have hstop : StepStopRel net terms a1 (fireA a1 ft.1 ft.2) := by
      cases terms with
      | nil => exact ⟨fun _ h => by simp at h, ft, hmem, hen, rfl⟩
      | cons p ps => exact (step_rewrite_iff net (p :: ps) _ _).mp ⟨ft, hmem, hen, rfl⟩
    rcases ih with hr | ⟨b, _, hbt, hoff, hle⟩
    · exact Or.inl (Relation.ReflTransGen.tail hr ⟨hstop.1, Or.inl hstop.2⟩)
    · exfalso
      apply hbt
      intro p hp
      have := hstop.1 p hp
      have := hle p
      omega
  | @inject a1 p _ hp ih =>
    rcases ih with hr | ⟨b, hb, hbt, hoff, hle⟩
    · by_cases hnt : NoTerminal terms a1
      · exact Or.inl (Relation.ReflTransGen.tail hr ⟨hnt, Or.inr ⟨p, hp, rfl⟩⟩)
      · refine Or.inr ⟨a1, hr, hnt, fun q hq => ?_, fun q => ?_⟩
        · have : (q == p) = false := by
            simp only [beq_eq_false_iff_ne]; rintro rfl; exact hq hp
          simp [this]
        · show a1 q ≤ (if q == p then a1 q + 1 else a1 q)
          split <;> omega
    · refine Or.inr ⟨b, hb, hbt, fun q hq => ?_, fun q => ?_⟩
      · have : (q == p) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hq hp
        simp only [this]; exact hoff q hq
      · have := hle q
        show b q ≤ (if q == p then a1 q + 1 else a1 q)
        split <;> omega

/-- **Bad transfer with injection, for excused properties.** When every violation has no
terminal marked — after `with_net_terminals`, the `DeadlockFree` and `TerminatesAtSink` arms —
the verified net's verdict is exact for the strict-stop runtime even with environment places. -/
theorem terminal_bad_transfer_excused (net : FlatNet) (envs terms : List PlaceId)
    (a0 : AMarking) (Bad : AMarking → Prop) (hex : ∀ a, Bad a → NoTerminal terms a) :
    ProvenFor (ReachAInj (verifiedNet terms net) envs a0) Bad
      ↔ ProvenFor (ReachStopInj net envs terms a0) Bad := by
  constructor
  · exact fun h a hr => h a (terminal_rewrite_sound_inj net envs terms hr)
  · intro h a hr hbad
    rcases terminal_rewrite_inj_extra net envs terms hr with hs | ⟨b, _, hbt, _, hle⟩
    · exact h a hs hbad
    · apply hbt
      intro p hp
      have := hex a hbad p hp
      have := hle p
      omega

/-- Environment place `e = 0` drained by `In::All` into terminal `P = 1`. -/
def tFinish : Transition :=
  { name := "finish"
  , inputs := [{ place := 0, card := .all, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def netFinish : FlatNet := [(tFinish, [1])]

def a0Finish : AMarking := fun _ => 0

/-- `e = 0` whenever `P = 1` holds a token, on every strict-stop run. -/
theorem finish_stop_inv {a : AMarking} (h : ReachStopInj netFinish [0] [1] a0Finish a) :
    1 ≤ a 1 → a 0 = 0 := by
  induction h with
  | refl => intro h; simp [a0Finish] at h
  | tail _ hs ih =>
    rename_i a1 a2 _
    obtain ⟨hnt, hst⟩ := hs
    have h1 : a1 1 = 0 := hnt 1 (by simp)
    rcases hst with ⟨ft, hmem, _, rfl⟩ | ⟨p, hp, rfl⟩
    · have : ft = (tFinish, [1]) := by simpa [netFinish] using hmem
      subst this
      intro _
      rfl
    · have : p = 0 := by simpa using hp
      subst this
      intro h
      simp [h1] at h

/-- **Not exact with injection.** `Unreachable {e, P}` holds on every strict-stop run (the
runtime refuses the injection after `P` is marked), yet the verified net's injected relation
reaches `e = 1 ∧ P = 1` by injecting after the terminal: a spurious `Violated`. -/
theorem terminal_rewrite_inj_not_exact :
    ProvenFor (ReachStopInj netFinish [0] [1] a0Finish) (fun a => 1 ≤ a 0 ∧ 1 ≤ a 1)
    ∧ ∃ a, ReachAInj (verifiedNet [1] netFinish) [0] a0Finish a ∧ 1 ≤ a 0 ∧ 1 ≤ a 1 := by
  refine ⟨fun a hr ⟨h0, h1⟩ => by have := finish_stop_inv hr h1; omega, ?_⟩
  have hm : ((rewriteT [1] tFinish, [1]) : FlatTransition) ∈ verifiedNet [1] netFinish := by
    simp [verifiedNet_cons, rewriteNet, netFinish]
  have r1 : ReachAInj (verifiedNet [1] netFinish) [0] a0Finish
      (fun q => if q == 0 then a0Finish q + 1 else a0Finish q) :=
    ReachAInj.inject ReachAInj.init (by simp)
  have r2 := ReachAInj.step r1 hm (by decide)
  have r3 := ReachAInj.inject (p := 0) r2 (by simp)
  exact ⟨_, r3, by decide, by decide⟩

/-! ## The concrete strict-stop runtime -/

/-- A concrete firing admitted by the strict stop: no terminal queue holds a token. -/
def StepCStopRel (net : FlatNet) (terms : List PlaceId) (m m' : CMarking) : Prop :=
  (∀ p ∈ terms, (m p).length = 0) ∧ StepCRel net m m'

def ReachCStop (net : FlatNet) (terms : List PlaceId) (m0 : CMarking) : CMarking → Prop :=
  Relation.ReflTransGen (StepCStopRel net terms) m0

/-- **Proposition 1 for the strict stop**: every marking of the concrete strict-stop runtime is,
under `alpha`, reachable in the verified net. -/
theorem strict_stop_simulated {net : FlatNet} {terms : List PlaceId} {m0 m : CMarking}
    (hWF : WellFormed net) (h : ReachCStop net terms m0 m) :
    ReachA (verifiedNet terms net) (alpha m0) (alpha m) := by
  rw [terminal_rewrite_exact]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    rename_i m1 m2 _
    obtain ⟨hnt, ft, hmem, prod, hst⟩ := hs
    obtain ⟨_, hGuard⟩ := hWF ft hmem
    obtain ⟨hEn, hUnit, hEff⟩ := hst
    obtain ⟨hEnA, hFire⟩ := prop1_step m1 ft.1 prod ft.2 hGuard hUnit hEn
    refine Relation.ReflTransGen.tail ih ⟨fun p hp => hnt p hp, ft, hmem, hEnA, ?_⟩
    rw [hEff, hFire]

end Libpetri.Novel.TerminalRewrite
