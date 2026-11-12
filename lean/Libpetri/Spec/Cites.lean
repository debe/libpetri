import Libpetri.Spec.Registry
import Libpetri.Refinement
import Libpetri.Reference.Exec
import Libpetri.Spec.GlossaryContext
import Libpetri.Spec.Req.CORE_050
import Libpetri.Spec.Req.CONC_001
import Libpetri.Spec.Req.CONC_005
import Libpetri.Spec.Req.CONC_021
import Libpetri.Spec.Req.CONC_022
import Libpetri.Spec.Req.CONC_023
import Libpetri.Spec.Req.CONC_024
import Libpetri.Spec.Req.PERF_042
import Libpetri.Spec.Req.EXEC_003
import Libpetri.Spec.Req.EXEC_020
import Libpetri.Spec.Req.EVT_022
import Libpetri.Spec.Req.EXP_012
import Libpetri.Spec.Req.EXP_013

set_option linter.missingDocs true

/-!
# Citations for the requirements without a block (`spec/10-performance.md` and others)

Some active requirements get no requirement block (plan section 7, ruling D21): they state a cost,
a thread placement, a data-structure property or a repository property, which no step relation
can express, or they are a definition or an umbrella over other requirements. Their spec section
carries a one-letter `**Kind:**` line (mostly Q, tested and not proven), and the coverage matrix
shows that kind next to the Lean form ("block", "cites" or none).

Where Lean does prove the behaviour such a requirement rests on, this file links it with
`@[evidence cites "ID" "fragment"]`. The registry only accepts the tag on a theorem of the
module that declares it, so every citation here is a small theorem that restates a proved result
(a `holds` theorem of another block, a refinement theorem or a lemma of a reference model) or
decides a concrete run of the reference executor. The fragment names exactly what is proved and
says what is not; the rest of each requirement (costs, locks, threads, memory, benchmarks) stays
with the tests.

Requirements with no citation here, because no Lean result carries any of their behaviour:
EXP-010 (an interchange format no runtime implements), EXP-011 (build-tool integration; its AC2
holds by the type of an exporter, which takes no marking), PERF-021 (timing targets), PERF-022
(a CI process) and MOD-002 (open and closed nets are distinct types). They are kind Q.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-071: Marking Thread Safety -/

/-- An action reaches the marking only through what it completes with. Take a transition `t`
whose action, in a reference firing, writes the tokens `e` through its context. If the context
accepts output calls on output places only, every place named in `e` is an output place of
`t`: the action cannot write to any other place of the marking. -/
@[evidence cites "CORE-071" "AC2: token production from actions goes through the context/output mechanism: an action that writes through a context accepting output calls on output places only deposits, in a reference action firing, on output places of its transition only (thread confinement and the absence of locks are not stated)"]
theorem cites_core071_ctx {N T V : Type} [DecidableEq N] {C : Ctx N T V} {val : T → V}
    {a : ActionRel N T} (hC : OutputsOnlyDeclared C) (ha : ThroughCtx C val a) {t : Trans N}
    {M M' : QueueMarking N T} {δ : Delivered N T} {e : List (N × T)}
    (hf : refActionFire a t M δ e M') : ∀ p ∈ e.map Prod.fst, OutputArc t p :=
  ctx_deposits_outputs hC ha hf

/-- The marking changes only by the firing's deposit. In the reference model a firing that ends
with its action's completion deposits exactly the tokens the action completed with, and hands
the action the tokens it consumed and read: if an action completes with one token for place
`out`, the firing adds that one token and nothing else. -/
@[evidence cites "CORE-071" "AC2 on the reference firing: a firing that ends with its action's completion deposits exactly the output tokens the action completed with (CORE-050 line 2), so an action changes the marking only through its outputs"]
theorem cites_core071_completion {N T : Type} [DecidableEq N] :
    CORE_050 (RefQFire (N := N) (T := T)) refActionFire :=
  CORE_050_reference

/-! ## CONC-006 and PERF-004: completion hand-off -/

/-- What the hand-off between an action and the orchestrator must preserve, on the reference
executor. Suppose an action writes the tokens `a` then `b` to place `p` and returns. The
orchestrator deposits nothing before the action has returned (CONC-001), and then adds `a` and
`b` at the tail of `p`'s queue in that order (EXEC-020). How the completion reaches the
orchestrator (a queue, a channel, with or without a lock) is not part of the statement. -/
@[evidence cites "CONC-006" "the behaviour the completion hand-off carries: the orchestrator deposits a firing's produced tokens only after its action has returned (CONC-001, on the reference executor), at the tail of each place's queue in the order the action produced them (EXEC-020); lock-freedom and the O(1) cost per completion are not stated", evidence cites "PERF-004" "the behaviour the completion signaling path carries: a completion is deposited only after the action has returned (CONC-001, on the reference executor), its tokens in production order at the queue tails (EXEC-020); that the path takes no lock is not stated"]
theorem cites_completion_handoff {N T : Type} [DecidableEq N] :
    CONC_001 (RefExec (N := N) (T := T)) ∧ EXEC_020 (RefQFire (N := N) (T := T)) :=
  ⟨CONC_001_reference, EXEC_020_reference⟩

/-! ## CONC-011 and PERF-011: inline synchronous execution -/

/-- The observable side of running a synchronous action inline. In a firing pass of the
reference executor, a token that a synchronous action deposits during the pass is not part of
the marking the pass sees: a second transition of the same pass cannot consume it, and an
`all()` or reset arc of a later start in the pass leaves it in place. Which thread runs the
action, and whether a task is spawned, is not part of the statement. -/
@[evidence cites "CONC-011" "the observable consequence of inline execution: a token a synchronous action deposits during a firing pass is not part of the pass-visible marking, so no later start of the same pass consumes or drains it (EXEC-003, on the reference executor); which thread runs the action and the absence of task dispatch are not stated", evidence cites "PERF-011" "AC1's observable half: a synchronous action that completes inside a firing pass deposits tokens the same pass does not see (EXEC-003, on the reference executor); task spawning and its cost are not stated"]
theorem cites_inline_sync {N T : Type} [DecidableEq N] :
    EXEC_003 (RefExec (N := N) (T := T)) :=
  EXEC_003_reference

/-! ## CONC-020, PERF-040 and PERF-041: the precompiled executor -/

/-- The precompiled executor computes what the bitmap reference computes. Start both backends
from related states (the precompiled pool materializes to the reference marking and the control
bits agree) and run any number `k` of executor cycles on a net of Immediate transitions with
synchronous actions: after every cycle the two states are still related, so both fire the same
transitions in the same order and show the same marking. -/
@[evidence cites "CONC-020" "the precompiled net computes what the net it is compiled from computes: on the untimed immediate synchronous fragment, any number of precompiled executor cycles keeps the materialized marking and the control bits equal to the bitmap reference's (array layout and the absence of hash lookups are not stated)", evidence cites "PERF-040" "computes what the reference computes: on the untimed immediate synchronous fragment the precompiled backend's materialized marking and control bits equal the bitmap backend's after every cycle; the flat-array layout and the absence of hash map lookups are not stated", evidence cites "PERF-041" "the two executors the speedup compares compute the same result: on the untimed immediate synchronous fragment they fire the same transitions in the same order and show the same marking after every cycle; the speedup itself is a benchmark"]
theorem cites_precompiled_refines {n : Nat} {net : Net} {emit : Emit} {st₀ : PBState}
    {bb₀ : BBState} (hrel : Rel n st₀ bb₀) (hok : NetOK net n) (hemit : EmitOK emit n) :
    ∀ k, Rel n (iterate (pcCycle net emit) k st₀) (iterate (bbCycle net emit) k bb₀) :=
  precompiled_refines_bitmap_immediate hrel hok hemit

/-- Each part of the precompiled layout meets its own requirement on its reference model: the
opcode consume operations (CONC-021), the token storage with one queue per place (CONC-022), the
ready order by priority level then stamp (CONC-023), the timing arrays (CONC-024) and the sparse
enablement masks at every word size (PERF-042). For example, a transition with `One` from `a`
and a reset on `b` hands its action the oldest token of `a` and leaves `b` empty. -/
@[evidence cites "CONC-020" "the parts of the precompiled representation, each on its reference model: opcode consume operations (CONC-021), one token queue per place (CONC-022), priority-partitioned ready order (CONC-023), precomputed timing arrays (CONC-024) and sparse enablement masks (PERF-042); that the parts live in flat arrays and that the net is immutable after compile() are not stated"]
theorem cites_conc020_parts :
    CONC_021 refRingStore refConsume ∧ CONC_022 refRingStore ∧ CONC_023 refReadyOrder ∧
      CONC_024 refTimingQ refTimingCompile ∧ ∀ w, PERF_042 w refSparse :=
  ⟨CONC_021_reference, CONC_022_reference, CONC_023_reference, CONC_024_reference,
    PERF_042_reference⟩

/-! ## PERF-001 and PERF-003: the dirty set -/

/-- Only transitions next to a written place are re-evaluated. On the timed reference step, a
transition's enablement check is re-run when a firing or an injection writes one of its arc
places, and only then or when the transition itself fires (CONC-005). In a net of 500
transitions where one firing writes the arc places of 3 others, only those 3 and the fired
transition are checked again. -/
@[evidence cites "PERF-001" "AC2's behaviour: a cycle re-evaluates only the transitions whose arc places a firing or an injection wrote, or that fired (CONC-005 on the timed reference step); the linear time bound is a benchmark", evidence cites "PERF-003" "only transitions affected by token changes are re-evaluated: the enablement check of a transition is re-run only when one of its arc places is written or it fires (CONC-005 on the timed reference step); the O(D) cost is a benchmark"]
theorem cites_dirty_set {N : Type} [DecidableEq N] : CONC_005 (RefTStep (N := N)) :=
  CONC_005_reference

/-- A firing that writes none of a transition's arc places leaves that transition's enablement
as it was, under any re-arming policy. If firing `t` writes only place `c`, a transition `u`
that reads `a` and consumes from `b` is enabled after the firing exactly when it was before, so
re-evaluating it would change nothing. -/
@[evidence cites "PERF-003" "AC2: transitions connected to unchanged places need no re-evaluation: a firing that writes none of a transition's arc places leaves the transition's enablement unchanged (CONC-005 line 3, for every policy of the timed step)"]
theorem cites_perf003_unwritten {N : Type} [DecidableEq N] {P : Policy N} {X : TimedNet N}
    {s s' : TSt N} {t : Trans N} {d : List N} (h : RefTStepW P X s (.fire t d) s')
    (u : Trans N) (hw : ∀ p, ArcPlace u p → ¬ Writes t d p) :
    enabledNA s'.m u.core = enabledNA s.m u.core :=
  conc005_frame h u hw

/-! ## PERF-010: the noop event store -/

/-- The observable half of a zero-cost noop store. The noop event store reports itself as not
enabled, and whatever is appended to it, `events()` stays empty: append three events and the
store still returns none. Whether the executor skips building the event objects is an
allocation property and not part of the statement. -/
@[evidence cites "PERF-010" "the observable half: the noop event store reports itself as not enabled and keeps nothing that is appended to it (EVT-022 on the reference noop store); that the executor allocates no event object is not stated"]
theorem cites_perf010_noop {E : Type} : EVT_022 (refNoopStore (E := E)) :=
  EVT_022_reference

/-! ## PERF-031: token storage -/

/-- The storage shape the efficiency claim is about. The reference ring store keeps one FIFO
queue per place: adding a token appends it at the tail, removing takes the head, and the count
of a place is the length of its queue. A place with tokens `x`, `y` hands out `x` first. Memory
use is not part of the statement. -/
@[evidence cites "PERF-031" "AC2's storage shape as behaviour: each place keeps its tokens in one sequential FIFO queue of its own, appended at the tail and taken from the head (CONC-022 on the reference ring store); memory use and pre-allocation are not stated"]
theorem cites_perf031_store : CONC_022 refRingStore :=
  CONC_022_reference

/-! ## EXP-015: doc generator parity -/

/-- What every doc generator embeds when it delegates to the mapper. The reference mapper draws
one junction node for each `XOR` or `AND` group with two or more children (EXP-012), so a net
with `XOR(A, B)` gets one diamond junction between the transition and `A` and `B`; and it
combines an output edge and a reset edge into one place into the single edge EXP-013 describes.
That each generator embeds exactly the mapper's DOT is tested per generator. -/
@[evidence cites "EXP-015" "the mapper the doc generators delegate to draws one junction node per XOR or AND group of two or more children (EXP-012) and the combined reset and output edges (EXP-013), on the reference exporter; that javadoc, cargo doc and the TypeDoc plugin embed that mapper's DOT is tested per generator"]
theorem cites_exp015_mapper : EXP_012 refEmit ∧ EXP_013 refExport :=
  ⟨EXP_012_reference, EXP_013_reference⟩

/-! ## Decided runs of the reference executor -/

/-- Read a decided fact off a run: if the check `p` of the state `o` evaluates to `true`, the
state exists and satisfies the check. -/
theorem cites_state_of_check {N T : Type} {o : Option (XSt N T)} {p : XSt N T → Bool}
    (h : o.map p = some true) : ∃ s, o = some s ∧ p s = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s => simp only [ho, Option.map_some, Option.some.injEq] at h; exact ⟨s, rfl, h⟩

/-- The steps of a cycle with nothing to settle, up to the termination test: completions,
publications and events end, the enablement update, and a deadline step that reaps nothing. -/
def citesToTest {N T : Type} : List (XLbl N T) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-! ### PERF-020: the linear chain scenario -/

/-- The names of the five transitions of the chain. -/
def perf020Names : List String := ["c0", "c1", "c2", "c3", "c4"]

/-- Transition `c<i>`: one token from place `i`, output spec `Out.place (i + 1)`. -/
def perf020T (i : Nat) : Trans Nat :=
  { core := { name := perf020Names.getD i "", inputs := [⟨i, .one⟩], inhibitors := [], reads := [],
              resets := [] },
    out := some (.place (i + 1)) }

/-- The linear chain of five Immediate transitions over places `0` to `5`, with no environment
place and no terminal place. -/
def perf020Cfg : Cfg Nat Nat :=
  { X := { net := { places := List.range 6, transitions := (List.range 5).map perf020T },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial marking: one token `7` in place `0`. -/
def perf020M0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- One hop: a pass that starts `c<i>` (firing `i`), its passthrough action writes the token to
place `i + 1` and returns, and the completion is committed. -/
def perf020Hop (i : Nat) : List (XLbl Nat Nat) :=
  [.begin, .start (perf020Names.getD i "") false, .endPass, .write i (i + 1) 7, .ret i true,
    .commit i] ++ citesToTest

/-- The whole run: five hops; at the termination test after the fifth, nothing is armed or in
flight and no environment place is registered, so the executor ends quiescent. -/
def perf020Run : List (XLbl Nat Nat) :=
  citesToTest ++ (List.range 5).flatMap perf020Hop ++ [.finish .quiescent]

set_option maxRecDepth 100000 in
/-- The Linear chain benchmark scenario with N = 5, decided on the reference executor. A token
starts in place `0`; the five transitions fire one after another, one per firing pass, each
passing the token on; after five firings the token is in place `5`, every other place is
empty, and the executor ends quiescent. This is the outcome a correct run of the scenario has;
how long it takes is what the benchmark measures. -/
@[evidence cites "PERF-020" "the Linear chain scenario (N = 5) on one decided run of the reference executor: the five transitions fire in turn, one per firing pass, the token ends in the last place, every other place is empty and the run ends quiescent; that each implementation ships the benchmark suite, and its timings, are not stated"]
theorem cites_perf020_chain :
    ∃ s, xrun perf020Cfg (xinit perf020M0 0) perf020Run = some s ∧
      s.phase = .done .quiescent ∧ s.nextId = 5 ∧ s.M 5 = [7] ∧ ∀ i, i < 5 → s.M i = [] := by
  obtain ⟨s, hs, hp⟩ := cites_state_of_check (o := xrun perf020Cfg (xinit perf020M0 0) perf020Run)
    (p := fun s => decide (s.phase = .done .quiescent) && s.nextId == 5 && s.M 5 == [7] &&
      (List.range 5).all fun i => (s.M i).isEmpty) (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.isEmpty_iff] at hp
  exact ⟨s, hs, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

end Libpetri.Spec
