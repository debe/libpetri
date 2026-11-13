import Libpetri.Spec.Req.CORE_011
import Libpetri.Spec.Req.EXEC_022
import Libpetri.Spec.Text.CORE_011

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# CORE-011 block B: the tokens the executor creates (`spec/01-core-model.md`)

The second block of CORE-011, beside the F block `CORE_011` (`CORE_011.lean`) on the host token
factories. Ruling D64 (a): a token the executor creates is not made by a host factory; it is
stamped from the executor's epoch clock ([TIME-015] AC13), and a forwarded token keeps its
timestamp ([IO-014]). CORE-035 AC2, TIME-015 AC13 and IO-014 AC5 cite this block.

**The epoch slice** (block local, on the executor model `RefExec`). The executor's tokens are the
F block's factory tokens (`FacTok V`: an optional value and an integer creation timestamp), and
the executor state carries, next to the firing clock of `XSt`, the readings of the two clocks of
the F block (`ClockReadings`: the host's wall clock and the executor's epoch clock). The labels
are every executor step (`step l`, its tokens as given), an action writing a value
(`writeVal`), a caller injecting a raw value (`requestVal`), and an outside step that moves the
clocks (`tick`, which may set them anywhere: an injected clock is the host's, and a wall clock
may be set back). The witness `RefEpochExec` is `RefExec` with two additions: the choice of
tokens, and a guard on the expiry. A value write is the executor's write of the token
`⟨some v, epoch⟩`, the explicit-timestamp factory applied to the epoch reading
(`core011b_ref_writeVal`), and a raw-value injection is its request of that token
(`core011b_ref_requestVal`). An expiry is taken only with the timeout outcome the slice mints from
the `Timeout` child, as Rust's `collect_timeout_outputs` does (a unit token at the epoch reading
for each `Place`, the consumed tokens themselves for each `ForwardInput`); `RefExec` itself takes
any outcome its configuration accepts (`C.timeoutOut`). Every executor step of the slice is a
`RefExec` step (`core011b_ref_step`).

The six lines: a value write adds only the token holding the value at the epoch reading of the
write, and only to its firing's buffer; a raw-value injection queues only the token holding the
value at the epoch reading of the call; the timeout outcome of an expiry mints at the epoch
reading of the expiry and forwards the consumed tokens unchanged; a token an action built itself
and writes, and a token a host built and injects, are kept as given; and the readings the lines
read are the clocks': a tick to `r` leaves the state reading `r`, and no other step moves them.

Wrong executors, one per line: one that mints a value write with the host's wall clock (the
default factory, the slip TIME-015 AC13 names), one that stamps a raw injection with the firing
clock, one that also deposits an injected raw value straight into the marking, one that mints the
timeout's unit token as the canonical unit token with the timestamp 0, one that re-stamps
forwarded tokens, one that re-stamps host-built tokens, and two that keep their own copy of the
epoch reading (one copies the wall clock into it, one freezes it while a firing is in flight).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The epoch slice (block local) -/

/-- The state of the epoch slice: the executor state, whose tokens are factory tokens, and the
readings of the host's wall clock and of the executor's epoch clock. -/
structure EpochSt (N V : Type) where
  /-- The executor state ([EXEC-001]); its tokens hold an optional value and a timestamp. -/
  x  : XSt N (FacTok V)
  /-- The present readings of the host's wall clock and of the executor's epoch clock. -/
  rd : ClockReadings

/-- The labels of the epoch slice. -/
inductive EpochLbl (N V : Type) where
  /-- An executor step with its tokens as given: a `write` or a `request` here carries a token
  the action or the host built itself (Java `output(Place, Token)`, TypeScript `outputToken`,
  `inject(place, token)` in Java, TypeScript and Rust). -/
  | step (l : XLbl N (FacTok V))
  /-- Outside: the action of firing `i` writes the value `v` to place `p` (`ctx.output`); the
  executor creates the token. -/
  | writeVal (i : Nat) (p : N) (v : V)
  /-- Outside: a caller asks to inject the raw value `v` into `p` (`injectValue`, Java
  `inject(place, value)`, Python `inject`); the executor creates the token and answers `r`. -/
  | requestVal (p : N) (v : V) (r : Reply)
  /-- Outside: the clocks now read `r` (time passes on the host's clocks, or the host moves its
  injected epoch clock, or sets its wall clock back). -/
  | tick (r : ClockReadings)

/-- An executor with an epoch clock: `E C s l s'` says that under configuration `C` the step
labelled `l` leads from `s` to `s'`. -/
abbrev EpochRel (N V : Type) :=
  Cfg N (FacTok V) → EpochSt N V → EpochLbl N V → EpochSt N V → Prop

/-- The token choices of an epoch slice, each read at the clock readings of the step (and the
firing-clock reading `now` of the executor state). A plausible wrong executor is a one-field
change of `refEpochPol`. -/
structure EpochPol (V : Type) where
  /-- The token a value write of `v` creates. -/
  mintWrite  : ClockReadings → Nat → V → FacTok V
  /-- The token a raw-value injection of `v` creates. -/
  mintInject : ClockReadings → Nat → V → FacTok V
  /-- The token a `Place` node of a `Timeout` child mints. -/
  mintUnit   : ClockReadings → FacTok V
  /-- What a `ForwardInput` node deposits for a consumed token. -/
  forward    : ClockReadings → FacTok V → FacTok V
  /-- What becomes of a token the action or the host built itself. -/
  keepHost   : ClockReadings → FacTok V → FacTok V

/-- **The reference token choices**: a value write and a raw-value injection create the token
holding the value at the epoch reading (Rust `Context::output` and `epoch_now`, TypeScript
`TokenOutput.add` and `injectValue`, Java `TokenOutput` over `environment::now` and
`inject(place, value)`); a `Place` node of a `Timeout` child mints a unit token at the epoch
reading (Rust `Token::at((), epoch_ms)`, Java and TypeScript `outputToHarvest`); a forward
deposits the consumed token itself; a token built by the action or the host is kept. -/
def refEpochPol {V : Type} : EpochPol V where
  mintWrite r _ v  := ⟨some v, r.epoch⟩
  mintInject r _ v := ⟨some v, r.epoch⟩
  mintUnit r       := ⟨none, r.epoch⟩
  forward _ y      := y
  keepHost _ y     := y

section Slice

variable {N V : Type}

/-- **The timeout outcome the executor mints** from the `Timeout` child, at the clock readings
`r`, for a firing that delivered `δ` (Rust `collect_timeout_outputs`, Java and TypeScript
`produceTimeoutOutput`): a minted token for each `Place`, every consumed token of `src` for each
`ForwardInput(src, dst)`, in consumption order, the children of an `And` one after the other. A
`Xor` inside a `Timeout` child does not build ([IO-013]); its first branch is read. -/
def core011b_mint (P : EpochPol V) (r : ClockReadings) (δ : QDelivered N (FacTok V)) :
    Out N → List (N × FacTok V)
  | .place p => [(p, P.mintUnit r)]
  | .forward src dst => (δ.inputs src).map fun y => (dst, P.forward r y)
  | .and l q => core011b_mint P r δ l ++ core011b_mint P r δ q
  | .xor l _ => core011b_mint P r δ l
  | .timeout c => core011b_mint P r δ c

variable [DecidableEq N] [DecidableEq V]

/-- The expiry of firing `i` announces the outcome `e` the executor mints at the readings `r`:
`i` is in flight, its output spec has a `Timeout` node, and `e` is that node's minted outcome. -/
def core011b_expireOk (P : EpochPol V) (r : ClockReadings) (x : XSt N (FacTok V)) (i : Nat)
    (e : List (N × FacTok V)) : Bool :=
  match x.fl.find? (·.id == i) with
  | some f =>
    match f.t.out.bind Out.findTimeout with
    | some c => decide (e = core011b_mint P r f.deliv c)
    | none => false
  | none => false

/-- An executor step of the slice with token choices `P`: a token write and a token request
keep or change the given token as `P.keepHost` says, an expiry needs the minted outcome, every
other step is the reference executor's. -/
def core011b_stepX (P : EpochPol V) (C : Cfg N (FacTok V)) (s : EpochSt N V) :
    XLbl N (FacTok V) → Option (XSt N (FacTok V))
  | .write i p y => xstep C s.x (.write i p (P.keepHost s.rd y))
  | .request p y r => xstep C s.x (.request p (P.keepHost s.rd y) r)
  | .expire i e =>
    if core011b_expireOk P s.rd s.x i e then xstep C s.x (.expire i e) else none
  | l => xstep C s.x l

/-- One step of the epoch slice with token choices `P`. Only `tick` moves the clocks. -/
def core011b_stepW (P : EpochPol V) (C : Cfg N (FacTok V)) (s : EpochSt N V) :
    EpochLbl N V → Option (EpochSt N V)
  | .step l => (core011b_stepX P C s l).map fun x' => ⟨x', s.rd⟩
  | .writeVal i p v =>
    (xstep C s.x (.write i p (P.mintWrite s.rd s.x.now v))).map fun x' => ⟨x', s.rd⟩
  | .requestVal p v r =>
    (xstep C s.x (.request p (P.mintInject s.rd s.x.now v) r)).map fun x' => ⟨x', s.rd⟩
  | .tick r => some ⟨s.x, r⟩

/-- The epoch slice with token choices `P`, as a relation. -/
def core011b_exec (P : EpochPol V) : EpochRel N V :=
  fun C s l s' => core011b_stepW P C s l = some s'

/-- **The reference epoch slice**: the reference executor with the reference token choices. -/
def RefEpochExec : EpochRel N V := core011b_exec refEpochPol

end Slice

/- The reference epoch slice is the witness model of CORE-011's executor block. -/
#spec_witness RefEpochExec

/-! ## Observations -/

section Observations

variable {N T : Type}

/-- The step puts no new token in the marking or the publication queue, and changes no firing's
outcome: every token in a place after the step was in that place before it, every queued batch
was queued before it, and every firing after it was in flight before it with the same outcome. -/
def core011b_keepsRest (x x' : XSt N T) : Prop :=
  (∀ p z, z ∈ x'.M p → z ∈ x.M p) ∧ (∀ b ∈ x'.pq, b ∈ x.pq) ∧
    ∀ f' ∈ x'.fl, ∃ f ∈ x.fl, f.id = f'.id ∧ f'.out = f.out

/-- The step adds to the buffers of the firings no entry but `py`, and that one only to the
buffer of firing `i`: every entry in a firing's buffer after the step was in the buffer of the
firing with the same identity before it, or is `py` in the buffer of firing `i`. -/
def core011b_bufsAdd (i : Nat) (py : N × T) (x x' : XSt N T) : Prop :=
  ∀ f' ∈ x'.fl, ∀ z ∈ f'.buf, ∃ f ∈ x.fl, f.id = f'.id ∧ (z ∈ f.buf ∨ (f'.id = i ∧ z = py))

/-- The step adds no entry to any firing's buffer. -/
def core011b_bufsKept (x x' : XSt N T) : Prop :=
  ∀ f' ∈ x'.fl, ∀ z ∈ f'.buf, ∃ f ∈ x.fl, f.id = f'.id ∧ z ∈ f.buf

/-- The step queues no injection but one carrying `py` (its place and token). -/
def core011b_eqAdd (py : N × T) (x x' : XSt N T) : Prop :=
  ∀ q ∈ x'.eq, q ∈ x.eq ∨ q.2 = py

/-- The step queues no injection. -/
def core011b_eqKept (x x' : XSt N T) : Prop :=
  ∀ q ∈ x'.eq, q ∈ x.eq

/-- **The step creates no token but `py`, buffered for firing `i`**: it adds `py` to the buffer
of firing `i` and nothing else to any buffer, queues no injection, puts nothing in the marking or
the publication queue and changes no firing's outcome. -/
def core011b_buffers (i : Nat) (py : N × T) (x x' : XSt N T) : Prop :=
  core011b_bufsAdd i py x x' ∧ core011b_eqKept x x' ∧ core011b_keepsRest x x'

/-- **The step creates no token but `py`, queued as an injection**: it queues no injection but
one carrying `py`, adds nothing to any buffer, puts nothing in the marking or the publication
queue and changes no firing's outcome. -/
def core011b_queues (py : N × T) (x x' : XSt N T) : Prop :=
  core011b_bufsKept x x' ∧ core011b_eqAdd py x x' ∧ core011b_keepsRest x x'

instance [DecidableEq N] [DecidableEq T] (i : Nat) (py : N × T) (x x' : XSt N T) :
    Decidable (core011b_bufsAdd i py x x') := by
  unfold core011b_bufsAdd; infer_instance

instance [DecidableEq N] [DecidableEq T] (py : N × T) (x x' : XSt N T) :
    Decidable (core011b_eqAdd py x x') := by
  unfold core011b_eqAdd; infer_instance

/-- The clock readings a step of the epoch slice leaves: a tick to `r` leaves `r`, every other
step leaves the readings it found. -/
def core011b_rdAfter {V : Type} (l : EpochLbl N V) (rd : ClockReadings) : ClockReadings :=
  match l with
  | .tick r => r
  | _ => rd

end Observations

section Stamped

variable {N V : Type}

/-- **The tokens of a `Timeout` child stamped at `ep`**, for a firing that delivered `δ`: a
`Place` node gives one token whose timestamp is `ep` (its value is [IO-013]'s), a
`ForwardInput(src, dst)` gives every token the firing consumed from `src`, in consumption order,
each the same token (value and timestamp), an `And` gives its children's tokens one after the
other. The stamped form of EXEC-022's `exec022_Emits`. -/
def core011b_Stamped (ep : Int) (δ : QDelivered N (FacTok V)) :
    Out N → List (N × FacTok V) → Prop
  | .place p, e => ∃ y, e = [(p, y)] ∧ y.stamp = ep
  | .forward src dst, e => e = (δ.inputs src).map fun y => (dst, y)
  | .and l r, e => ∃ e₁ e₂, e = e₁ ++ e₂ ∧ core011b_Stamped ep δ l e₁ ∧
      core011b_Stamped ep δ r e₂
  | .xor l r, e => core011b_Stamped ep δ l e ∨ core011b_Stamped ep δ r e
  | .timeout c, e => core011b_Stamped ep δ c e

/-- **A timeout outcome stamped at `ep`**: `t`'s output spec has a `Timeout` node, and `e` puts
in every place the same tokens, in the same order, as the stamped tokens of that node's child
(places compared one by one, as in `exec022_QOutcome`). -/
def core011b_QStamped [DecidableEq N] (ep : Int) (t : Trans N) (δ : QDelivered N (FacTok V))
    (e : List (N × FacTok V)) : Prop :=
  ∃ o c e₀, t.out = some o ∧ o.findTimeout = some c ∧ core011b_Stamped ep δ c e₀ ∧
    ∀ p, qEmittedTo e p = qEmittedTo e₀ p

end Stamped

/-! ## CORE-011 block B: Token Creation (tokens the executor creates) -/

requirement CORE_011_B
  id "CORE-011"
  title "Token Creation (tokens the executor creates)"
  kind B
  scope "the tokens the executors of Java, TypeScript, Rust and Python create: action outputs written as values, raw-value injections, minted timeout outcomes"
  source verbatim "spec/01-core-model.md"
  covers CORE_011.s4, CORE_011.s5, CORE_011.s6, CORE_011.s7
  reading "For every executor with an epoch clock E (EpochRel: executor states with the readings of the host's wall clock and of the executor's epoch clock), every configuration C, and every step of E from s to s', s.rd.epoch being the epoch clock's reading at the step:"
          "a value write of v to p by firing i creates no token but (p, the token holding v and carrying s.rd.epoch), and puts it only in the buffer of firing i (core011b_buffers: nothing else enters a buffer, the event queue, the marking or the publication queue, and no firing's outcome changes);"
          "a raw-value injection request of v into p creates no token but one queued as an event carrying (p, the token holding v and carrying s.rd.epoch) (core011b_queues: nothing else enters the event queue, a buffer, the marking or the publication queue, and no firing's outcome changes);"
          "an expiry of firing i with timeout outcome e is the expiry of a firing i in flight for which e is the timeout outcome stamped at s.rd.epoch (core011b_QStamped: each minted token carries s.rd.epoch, each forwarded token is the consumed token itself);"
          "a write of a token y to p by firing i creates no token but (p, y), buffered for firing i;"
          "an injection request of a token y into p creates no token but one queued as an event carrying (p, y);"
          "the readings a step leaves are the clocks': a tick to r leaves r, and every other step leaves s.rd (core011b_rdAfter), so the epoch reading the lines read is the epoch clock's and not a copy the executor keeps."
  assumes "The model is an executor with an epoch clock E : EpochRel N V (block local): the executor relation of GlossaryExec.lean over tokens FacTok V (an optional value and an integer timestamp, CORE-011's F block), with the readings of the host's wall clock and of the executor's epoch clock (ClockReadings) in the state. The labels are every executor step with its tokens as given (step), an action writing a value (writeVal), a caller injecting a raw value (requestVal), and tick, an outside step that sets the clock readings to any values: an injected epoch clock is the host's to move (TIME-015), and a wall clock may be set back. The witness is RefEpochExec: RefExec with the reference token choices refEpochPol and one guard. Its executor steps are RefExec steps (core011b_ref_step), a value write is RefExec's write of the token the explicit-timestamp factory gives at the epoch reading (core011b_ref_writeVal), and a raw-value injection is RefExec's request of that token (core011b_ref_requestVal). The guard (core011b_expireOk) takes an expiry only with the timeout outcome the slice mints from the Timeout child (core011b_mint, after Rust's collect_timeout_outputs); RefExec takes any outcome its configuration accepts (C.timeoutOut), and EXEC-022 line 1 pins that outcome only under exec022_OutcomeSound C. So lines 1, 2, 4 and 5 hold of the witness by its token choices and line 3 by its guard. The Rust items Context::output, output_raw, epoch_now, timeout_outputs and collect_timeout_outputs are pinned to this block in lean/fidelity.toml, so a change to them forces a re-read of refEpochPol and core011b_mint; the Java and TypeScript sites are not pinned."
          "The epoch reading is part of the slice's state, so an executor could keep its own copy of it. Line 6 rules that out: a tick to r leaves the readings r and no other step moves them, so the s.rd.epoch that lines 1 to 3 read is the clock's reading at the step. An executor that never consults the injected clock and copies the wall reading into its epoch reading meets lines 1 to 5 and breaks line 6 (CORE_011_B_mutant_ownClock_killed: the clocks move to wall 6 and epoch 120, the executor's epoch reading is 6, and the value 50 written next is buffered as created at 6); so does one that freezes the epoch reading while a firing is in flight, the slip of capturing the clock's value where its source is expected (CORE_011_B_forbids_snapshotEpoch). How the host's clock moves is TIME-015's subject; line 6 says only that the executor stamps with what the clock reads."
          "'While the firing is in flight' is the step at which the token is created: a write and an expiry are steps of a firing in flight whose outcome is not set (the guards of RefExec's write and expire rules, CONC-003 and EXEC-022), and the line reads the epoch clock at that step. Rust reads it in Context::output and at the instant the timeout fired (executor_core/output.rs timeout_outputs), TypeScript in TokenOutput.add and in the harvest collector of produceTimeoutOutput, Java in TokenOutput over environment::now and in outputToHarvest. Rust's output_many stamps several tokens with one reading: a run of value writes with no tick between them. A Python action's ctx.output only buffers the raw value (rust/libpetri-py/src/action.rs output); the token is created when the action returns, by flush_outputs calling Rust output_raw, which reads epoch_now then, or when the action calls ctx.flush(), which stamps the buffered values with one reading. So a Python write is the writeVal step at the return or the flush, and a run of them is a run of value writes; the plain sentence after the first EARS sentence says so, and it is no runtime defect. A raw-value injection is read at the call, the request step (TypeScript injectValue and injectNoAwait, Java inject(place, value), Python inject): the token is queued and injected later unchanged (ENV-003)."
          "Each line constrains the step that creates a token: it says which token the step creates and where that step puts it, the buffer of the writing firing or the event queue, with every other part of the state that holds tokens (the other buffers, the event queue or the buffers, the marking, the publication queue and the firings' outcomes) getting nothing new from it. An executor that also deposits an injected raw value straight into the marking, stamped by the wall clock, breaks line 2 (CORE_011_B_forbids_directInject). Where the token goes next is not these lines' subject: that a buffered token is deposited unchanged, a queued token is injected unchanged and a recorded timeout outcome is deposited as recorded are EXEC-020, ENV-003 and EXEC-022 line 3 (tokens are identities in the queue model). Lines 1 and 2 do not check that p is an output place or an environment place: a write to an undeclared place or an injection into another place is refused or, where a runtime accepts it, still creates only the stated token, so the lines hold of it (ENV-002 decides the answer)."
          "The lines are safety lines. That the executor offers a value write, an injection or an expiry at all is not stated in this block. For RefExec the injection and the expiry are offered by ENV-002's and EXEC-022's coverage clauses in ExecCoversW5 (Env002Covers, Exec022Covers), over requests and expiries of any token; they reach the slice's requestVal through core011b_ref_requestVal and its expiries through core011b_ref_step, but no theorem states that carried-over clause for the slice. No coverage clause states that a write step is offered (CONC-002's conc002Covers is about the begin, start and lose steps). Both are open items for the consistency theorem."
          "Line 1 is the first sentence. 'Holds that value and carries the reading of its epoch clock at the write' is the token (some v, s.rd.epoch), which is the F block's explicit-timestamp factory applied to the epoch reading, not its default factory (core011b_ref_writeVal). An executor that mints a value write with the host's wall clock, the default factory, violates it under an injected clock (CORE_011_B_mutant_defaultFactory_killed: wall reading 5, epoch reading 100, the written token carries 5); this is the slip TIME-015 AC13 names, a collector built without the clock (Java new TokenOutput(), TypeScript tokenOf)."
          "Line 2 is the second sentence. An executor that stamps a raw-value injection with the firing clock, conflating the two time bases TIME-015 keeps apart, violates it (CORE_011_B_forbids_firingClockInject: firing clock 40, epoch reading 100, the queued token carries 40). A refused request queues nothing, so the line holds of it whatever token the call made (Java mints the token before the executor answers)."
          "Line 3 is the third sentence (ruling D64 (a): the timeout's unit token is not the canonical unit token, whose timestamp 0 is the F block's line 3). An executor that mints the timeout's unit token as the canonical unit token, Token.unit() with the timestamp 0, violates it (CORE_011_B_mutant_anyMinted_killed: the reading with EXEC-022's free minted token held of it), and so does one that re-stamps the forwarded tokens at the epoch reading (CORE_011_B_forbids_restampForward: the consumed token stamped 3 is deposited stamped 100). A forwarded token is the consumed token itself, so it keeps its value and timestamp (IO-014 AC5). To tell the minted tokens from the forwarded ones, line 3 reads the outcome's shape: the firing is in flight, its spec has a Timeout node, each Place node gives one token, each ForwardInput(src, dst) gives every token consumed from src in consumption order. That shape is EXEC-022 line 1's and IO-013's (a stamped outcome is a token-level timeout outcome, core011b_QStamped_exec022), so an executor whose outcome has another shape also breaks EXEC-022 line 1 under a sound configuration; what line 3 adds to them is the stamps."
          "Lines 4 and 5 are the fourth sentence. A token an action builds itself through a factory and outputs as a token (Java output(Place, Token), TypeScript outputToken) and a token a host builds and injects (inject(place, token) in Java, TypeScript and Rust) keep the factory's stamp, which the F block's lines 1 and 2 fix; the executor does not re-stamp host-supplied tokens (TIME-015, token stamping boundary). 'Keep that token as it is' is the whole token (p, y), value and timestamp. An executor that re-stamps them at the epoch reading violates line 4 (CORE_011_B_mutant_noKeep_killed: the reading without lines 4 and 5 held of it), and one that re-stamps only the token a host injects violates line 5 alone (CORE_011_B_mutant_noKeepHost_killed: the reading without line 5 held of it). Rust's actions output values only, and Python has no token object, so line 4 is vacuous there."
          "Tokens of the initial marking and of a restored snapshot are not created by an executor step: the initial state holds them as given (xinit), CORE-072's and CORE-073's subject. Python's legacy initial marking, given as raw values, is stamped by the binding when the run starts, from the clock's epoch under a host clock and from the wall clock without one (the Python binding's marking_from_python_at; TIME-015's prose on Python says the same); no line of this block reads it, and whether CORE-072 or CORE-073 states it is an open item."
          "AC1 to AC5 of CORE-011 are the F block's (CORE_011.lean): the host factories. AC6 (under an injected clock, a token the executor creates for a value write, a raw-value injection or a minted timeout output carries the epoch clock's reading at that moment, not the wall clock's; a forwarded token, a token the action built and a token the host built keep their timestamps) is lines 1 to 5 with line 6: CORE_011_B_nonvacuous runs all of them on RefEpochExec, and core011b_ref_wall_blind shows the reference's written token does not depend on the wall reading. TIME-015 AC13 (under an injected clock, tokens produced by ctx.output, by a raw-value injection and by a minted action-timeout recovery output carry the injected epoch clock's timestamps, not wall time; a forwarded recovery token keeps the created_at of the token it forwards) is lines 1 to 3 with line 6. CORE-035 AC2 (output tokens are created with the current timestamp of the epoch clock; a forwarded token keeps its created_at) is lines 1 and 3 (core011b_output_stamp). IO-014 AC5 (a forwarded token's created_at equals the original's, a minted recovery token in the same branch is stamped from the epoch clock) is line 3 (core011b_QStamped_forward). Each of them cites this block."
          "The test derivation of AC6 and of TIME-015 AC13 (a value write, a token write, a raw-value injection, a token injection and a timeout outcome with a forward, under an injected clock) is CORE_011_B_nonvacuous on RefEpochExec: wall reading 5 and injected epoch reading 100 at the value write, then 6 and 120; the written value carries 100, the token the action built at -7 stays at -7, the injected raw value carries 120, the token the host built at -3 stays at -3, the minted unit token carries 120, and the forwarded seed token keeps 3."
  signoff "2026-11-13 08776b8cad7bb709 ai"
  statement : ∀ {N V : Type} [DecidableEq N], EpochRel N V → Prop :=
    fun {N V} _ E =>
      (∀ C i (p : N) (v : V), on (fun s s' => E C s (.writeVal i p v) s'), shall (fun s s' =>
        core011b_buffers i (p, (⟨some v, s.rd.epoch⟩ : FacTok V)) s.x s'.x)) ∧
      (∀ C (p : N) (v : V) r, on (fun s s' => E C s (.requestVal p v r) s'), shall (fun s s' =>
        core011b_queues (p, (⟨some v, s.rd.epoch⟩ : FacTok V)) s.x s'.x)) ∧
      (∀ C i e, on (fun s s' => E C s (.step (.expire i e)) s'), shall (fun s _ =>
        ∃ f ∈ s.x.fl, f.id = i ∧ core011b_QStamped s.rd.epoch f.t f.deliv e)) ∧
      (∀ C i p y, on (fun s s' => E C s (.step (.write i p y)) s'), shall (fun s s' =>
        core011b_buffers i (p, y) s.x s'.x)) ∧
      (∀ C p y r, on (fun s s' => E C s (.step (.request p y r)) s'), shall (fun s s' =>
        core011b_queues (p, y) s.x s'.x)) ∧
      (∀ C l, on (fun s s' => E C s l s'), shall (fun s s' => s'.rd = core011b_rdAfter l s.rd))


/- The pinned readable form of CORE-011 block B: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_011_B : {N V : Type} → [DecidableEq N] → EpochRel N V → Prop :=
fun {N V} x E =>
  (∀ (C : Cfg N (FacTok V)) (i : ℕ) (p : N) (v : V),
      on fun s s' => E C s (EpochLbl.writeVal i p v) s', shall fun s s' =>
        core011b_buffers i (p, { val := some v, stamp := s.rd.epoch }) s.x s'.x) ∧
    (∀ (C : Cfg N (FacTok V)) (p : N) (v : V) (r : Reply),
        on fun s s' => E C s (EpochLbl.requestVal p v r) s', shall fun s s' =>
          core011b_queues (p, { val := some v, stamp := s.rd.epoch }) s.x s'.x) ∧
      (∀ (C : Cfg N (FacTok V)) (i : ℕ) (e : List (N × FacTok V)),
          on fun s s' => E C s (EpochLbl.step (XLbl.expire i e)) s', shall fun s x_1 =>
            ∃ f ∈ s.x.fl, f.id = i ∧ core011b_QStamped s.rd.epoch f.t f.deliv e) ∧
        (∀ (C : Cfg N (FacTok V)) (i : ℕ) (p : N) (y : FacTok V),
            on fun s s' => E C s (EpochLbl.step (XLbl.write i p y)) s', shall fun s s' =>
              core011b_buffers i (p, y) s.x s'.x) ∧
          (∀ (C : Cfg N (FacTok V)) (p : N) (y : FacTok V) (r : Reply),
              on fun s s' => E C s (EpochLbl.step (XLbl.request p y r)) s', shall fun s s' =>
                core011b_queues (p, y) s.x s'.x) ∧
            ∀ (C : Cfg N (FacTok V)) (l : EpochLbl N V),
              on fun s s' => E C s l s', shall fun s s' => s'.rd = core011b_rdAfter l s.rd
-/
#guard_msgs in #print CORE_011_B

/-! ### The five lines, named (for the mutants) -/

section Lines

variable {N V : Type} [DecidableEq N]

/-- Line 1: a value write adds only the token holding the value at the epoch reading. -/
def core011b_line1 (E : EpochRel N V) : Prop :=
  ∀ C i (p : N) (v : V), on (fun s s' => E C s (.writeVal i p v) s'), shall (fun s s' =>
    core011b_buffers i (p, (⟨some v, s.rd.epoch⟩ : FacTok V)) s.x s'.x)

/-- Line 2: a raw-value injection queues only the token holding the value at the epoch
reading. -/
def core011b_line2 (E : EpochRel N V) : Prop :=
  ∀ C (p : N) (v : V) r, on (fun s s' => E C s (.requestVal p v r) s'), shall (fun s s' =>
    core011b_queues (p, (⟨some v, s.rd.epoch⟩ : FacTok V)) s.x s'.x)

/-- Line 3: an expiry's timeout outcome is stamped at the epoch reading. -/
def core011b_line3 (E : EpochRel N V) : Prop :=
  ∀ C i e, on (fun s s' => E C s (.step (.expire i e)) s'), shall (fun s _ =>
    ∃ f ∈ s.x.fl, f.id = i ∧ core011b_QStamped s.rd.epoch f.t f.deliv e)

/-- Line 4: a token the action built itself is written as given. -/
def core011b_line4 (E : EpochRel N V) : Prop :=
  ∀ C i p y, on (fun s s' => E C s (.step (.write i p y)) s'), shall (fun s s' =>
    core011b_buffers i (p, y) s.x s'.x)

/-- Line 5: a token the host built itself is queued as given. -/
def core011b_line5 (E : EpochRel N V) : Prop :=
  ∀ C p y r, on (fun s s' => E C s (.step (.request p y r)) s'), shall (fun s s' =>
    core011b_queues (p, y) s.x s'.x)

/-- Line 6: the readings a step leaves are the clocks': a tick to `r` leaves `r`, every other
step keeps them. -/
def core011b_line6 (E : EpochRel N V) : Prop :=
  ∀ C l, on (fun s s' => E C s l s'), shall (fun s s' => s'.rd = core011b_rdAfter l s.rd)

/-- CORE-011 block B is its six lines. -/
theorem core011b_iff (E : EpochRel N V) :
    CORE_011_B E ↔ core011b_line1 E ∧ core011b_line2 E ∧ core011b_line3 E ∧
      core011b_line4 E ∧ core011b_line5 E ∧ core011b_line6 E :=
  Iff.rfl

end Lines

/-! ### The steps of the slice -/

section Steps

variable {N V : Type} [DecidableEq N]

omit [DecidableEq N] in
/-- A step that changes only the event queue, the ticket supply and the parked flag keeps the
buffers, the marking, the publication queue and the outcomes. -/
theorem core011b_kept_of_eq {T : Type} {x : XSt N T} {q : List (Nat × N × T)} {n : Nat}
    {b : Bool} :
    core011b_bufsKept x { x with eq := q, nextId := n, parked := b } ∧
      core011b_keepsRest x { x with eq := q, nextId := n, parked := b } :=
  ⟨fun f' hf' _ hz => ⟨f', hf', rfl, hz⟩,
    fun _ _ hz => hz, fun _ hb => hb, fun f' hf' => ⟨f', hf', rfl, rfl⟩⟩

/-- A write of `y` to `p` by firing `i` creates only `(p, y)`, in the buffer of firing `i`. -/
theorem core011b_buffers_write {T : Type} {C : Cfg N T} {x x' : XSt N T} {i : Nat} {p : N}
    {y : T} (h : xstep C x (.write i p y) = some x') : core011b_buffers i (p, y) x x' := by
  obtain ⟨-, -, -, rfl⟩ := writeStep_some (show writeStep x i p y = some x' from h)
  refine ⟨fun f' hf' z hz => ?_, fun _ hq => hq, fun _ _ hz => hz, fun _ hb => hb,
    fun f' hf' => ?_⟩
  · obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨hgi, rfl⟩⟩ := exec022_mem_upd hf'
    · exact ⟨g, hg, rfl, Or.inl hz⟩
    · refine ⟨g, hg, rfl, ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hz
      exact hz.imp_right fun hz => ⟨hgi, hz⟩
  · obtain ⟨g, hg, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := exec022_mem_upd hf'
    · exact ⟨g, hg, rfl, rfl⟩
    · exact ⟨g, hg, rfl, rfl⟩

/-- A request to inject `y` into `p` creates only an event carrying `(p, y)`. -/
theorem core011b_queues_request {T : Type} {C : Cfg N T} {x x' : XSt N T} {p : N} {y : T}
    {r : Reply} (h : xstep C x (.request p y r) = some x') : core011b_queues (p, y) x x' := by
  obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some (show requestStep C x p y r = some x' from h)
  · refine ⟨core011b_kept_of_eq.1, fun q hq => ?_, core011b_kept_of_eq.2⟩
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact Or.inl hq
    · exact Or.inr rfl
  · exact ⟨fun f' hf' _ hz => ⟨f', hf', rfl, hz⟩, fun q hq => Or.inl hq, fun _ _ hz => hz,
      fun _ hb => hb, fun f' hf' => ⟨f', hf', rfl, rfl⟩⟩

omit [DecidableEq N] in
/-- The minted outcome is stamped at the epoch reading when the minted token carries it and a
forward keeps the consumed token. -/
theorem core011b_mint_stamped {P : EpochPol V} {r : ClockReadings}
    (hu : (P.mintUnit r).stamp = r.epoch) (hf : ∀ y, P.forward r y = y)
    (δ : QDelivered N (FacTok V)) :
    ∀ c, core011b_Stamped r.epoch δ c (core011b_mint P r δ c)
  | .place _ => ⟨_, rfl, hu⟩
  | .forward src dst => by
    show (δ.inputs src).map (fun y => (dst, P.forward r y)) = (δ.inputs src).map fun y => (dst, y)
    simp only [hf]
  | .and l q => ⟨_, _, rfl, core011b_mint_stamped hu hf δ l, core011b_mint_stamped hu hf δ q⟩
  | .xor l _ => Or.inl (core011b_mint_stamped hu hf δ l)
  | .timeout c => core011b_mint_stamped hu hf δ c

omit [DecidableEq N] in
/-- Whatever token a `Place` node mints, the minted outcome is EXEC-022's token-level emission
when a forward keeps the consumed token. -/
theorem core011b_mint_emits {P : EpochPol V} {r : ClockReadings} (hf : ∀ y, P.forward r y = y)
    (δ : QDelivered N (FacTok V)) : ∀ c, exec022_Emits δ c (core011b_mint P r δ c)
  | .place _ => ⟨_, rfl⟩
  | .forward src dst => by
    show (δ.inputs src).map (fun y => (dst, P.forward r y)) = (δ.inputs src).map fun y => (dst, y)
    simp only [hf]
  | .and l q => ⟨_, _, rfl, core011b_mint_emits hf δ l, core011b_mint_emits hf δ q⟩
  | .xor l _ => Or.inl (core011b_mint_emits hf δ l)
  | .timeout c => core011b_mint_emits hf δ c

omit [DecidableEq N] in
/-- A stamped `Timeout` child emission is an EXEC-022 emission. -/
theorem core011b_stamped_emits {ep : Int} {δ : QDelivered N (FacTok V)} :
    ∀ c e, core011b_Stamped ep δ c e → exec022_Emits δ c e
  | .place _, _, ⟨y, he, _⟩ => ⟨y, he⟩
  | .forward _ _, _, h => h
  | .and l q, _, ⟨e₁, e₂, he, h₁, h₂⟩ =>
    ⟨e₁, e₂, he, core011b_stamped_emits l e₁ h₁, core011b_stamped_emits q e₂ h₂⟩
  | .xor l q, e, h => h.elim (fun h => Or.inl (core011b_stamped_emits l e h))
      (fun h => Or.inr (core011b_stamped_emits q e h))
  | .timeout c, e, h => core011b_stamped_emits c e h

variable [DecidableEq V]

/-- An expiry of the slice announces the outcome the executor mints at the step's readings. -/
theorem core011b_expire_of {P : EpochPol V} {C : Cfg N (FacTok V)} {s : EpochSt N V} {i : Nat}
    {e : List (N × FacTok V)} {x' : XSt N (FacTok V)}
    (h : core011b_stepX P C s (.expire i e) = some x') :
    xstep C s.x (.expire i e) = some x' ∧ ∃ f ∈ s.x.fl, f.id = i ∧
      ∃ o c, f.t.out = some o ∧ o.findTimeout = some c ∧ e = core011b_mint P s.rd f.deliv c := by
  simp only [core011b_stepX] at h
  split at h
  · rename_i hok
    refine ⟨h, ?_⟩
    unfold core011b_expireOk at hok
    split at hok
    · rename_i f hf
      split at hok
      · rename_i c hc
        obtain ⟨o, ho, hoc⟩ := Option.bind_eq_some_iff.mp hc
        exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf,
          o, c, ho, hoc, of_decide_eq_true hok⟩
      · exact absurd hok Bool.false_ne_true
    · exact absurd hok Bool.false_ne_true
  · exact absurd h (by simp)

/-- The steps of the slice with token choices `P` meet the five lines with `P`'s tokens. -/
theorem core011b_stepW_lines (P : EpochPol V) (C : Cfg N (FacTok V)) (s s' : EpochSt N V) :
    (∀ i p v, core011b_stepW P C s (.writeVal i p v) = some s' →
      core011b_buffers i (p, P.mintWrite s.rd s.x.now v) s.x s'.x) ∧
    (∀ p v r, core011b_stepW P C s (.requestVal p v r) = some s' →
      core011b_queues (p, P.mintInject s.rd s.x.now v) s.x s'.x) ∧
    (∀ i e, core011b_stepW P C s (.step (.expire i e)) = some s' →
      ∃ f ∈ s.x.fl, f.id = i ∧
        ∃ o c, f.t.out = some o ∧ o.findTimeout = some c ∧ e = core011b_mint P s.rd f.deliv c) ∧
    (∀ i p y, core011b_stepW P C s (.step (.write i p y)) = some s' →
      core011b_buffers i (p, P.keepHost s.rd y) s.x s'.x) ∧
    (∀ p y r, core011b_stepW P C s (.step (.request p y r)) = some s' →
      core011b_queues (p, P.keepHost s.rd y) s.x s'.x) := by
  refine ⟨fun i p v h => ?_, fun p v r h => ?_, fun i e h => ?_, fun i p y h => ?_,
    fun p y r h => ?_⟩
  · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact core011b_buffers_write hx
  · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact core011b_queues_request hx
  · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (core011b_expire_of hx).2
  · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact core011b_buffers_write hx
  · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact core011b_queues_request hx

/-- Line 1 holds of the slice whose value write mints the token at the epoch reading. -/
theorem core011b_exec_line1 {P : EpochPol V} (hw : ∀ r n v, P.mintWrite r n v = ⟨some v, r.epoch⟩) :
    core011b_line1 (core011b_exec (N := N) P) := fun C i p v s s' h => by
  have := (core011b_stepW_lines P C s s').1 i p v h
  rwa [hw] at this

/-- Line 2 holds of the slice whose raw-value injection mints the token at the epoch reading. -/
theorem core011b_exec_line2 {P : EpochPol V}
    (hi : ∀ r n v, P.mintInject r n v = ⟨some v, r.epoch⟩) :
    core011b_line2 (core011b_exec (N := N) P) := fun C p v r s s' h => by
  have := (core011b_stepW_lines P C s s').2.1 p v r h
  rwa [hi] at this

/-- Line 3 holds of the slice whose timeout outcome mints at the epoch reading and forwards the
consumed tokens. -/
theorem core011b_exec_line3 {P : EpochPol V} (hu : ∀ r, (P.mintUnit r).stamp = r.epoch)
    (hf : ∀ r y, P.forward r y = y) : core011b_line3 (core011b_exec (N := N) P) :=
  fun C i e s s' h => by
    obtain ⟨f, hf', hid, o, c, ho, hc, rfl⟩ := (core011b_stepW_lines P C s s').2.2.1 i e h
    exact ⟨f, hf', hid, o, c, _, ho, hc, core011b_mint_stamped (hu s.rd) (hf s.rd) f.deliv c,
      fun _ => rfl⟩

/-- Line 4 holds of the slice that keeps a token the action built. -/
theorem core011b_exec_line4 {P : EpochPol V} (hk : ∀ r y, P.keepHost r y = y) :
    core011b_line4 (core011b_exec (N := N) P) := fun C i p y s s' h => by
  have := (core011b_stepW_lines P C s s').2.2.2.1 i p y h
  rwa [hk] at this

/-- Line 5 holds of the slice that keeps a token the host built. -/
theorem core011b_exec_line5 {P : EpochPol V} (hk : ∀ r y, P.keepHost r y = y) :
    core011b_line5 (core011b_exec (N := N) P) := fun C p y r s s' h => by
  have := (core011b_stepW_lines P C s s').2.2.2.2 p y r h
  rwa [hk] at this

/-- Line 6 holds of the slice whatever its token choices: only a tick moves the readings, and it
sets them to the clocks'. -/
theorem core011b_exec_line6 (P : EpochPol V) : core011b_line6 (core011b_exec (N := N) P) :=
  fun C l s s' h => by
    cases l with
    | tick r => exact (Option.some.inj h).symm ▸ rfl
    | step l => obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    | writeVal i p v => obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    | requestVal p v r => obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

/-- The slice meets the block when its token choices are the reference's on the five points the
lines read. -/
theorem core011b_exec_of {P : EpochPol V}
    (hw : ∀ r n v, P.mintWrite r n v = ⟨some v, r.epoch⟩)
    (hi : ∀ r n v, P.mintInject r n v = ⟨some v, r.epoch⟩)
    (hu : ∀ r, (P.mintUnit r).stamp = r.epoch) (hf : ∀ r y, P.forward r y = y)
    (hk : ∀ r y, P.keepHost r y = y) : CORE_011_B (core011b_exec (N := N) P) :=
  ⟨core011b_exec_line1 hw, core011b_exec_line2 hi, core011b_exec_line3 hu hf,
    core011b_exec_line4 hk, core011b_exec_line5 hk, core011b_exec_line6 P⟩

end Steps

/-! ### The reference -/

/-- ✓ The reference epoch slice satisfies CORE-011's executor block, at every place and value
type: a value write and a raw-value injection create only the token holding the value at the
epoch reading, the timeout outcome mints at the epoch reading and forwards the consumed tokens,
tokens built by the action or the host are kept, and the epoch reading it stamps with is always
the clock's. -/
@[evidence holds CORE_011_B]
theorem CORE_011_B_reference {N V : Type} [DecidableEq N] [DecidableEq V] :
    CORE_011_B (RefEpochExec (N := N) (V := V)) :=
  core011b_exec_of (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)


/-! ### The slice and the executor model -/

section Links

variable {N V : Type} [DecidableEq N] [DecidableEq V]

/-- Every executor step of the reference slice is a step of the reference executor with the same
label, and keeps the clocks, so every requirement over the executor model holds of the slice's
executor steps. -/
theorem core011b_ref_step {C : Cfg N (FacTok V)} {s s' : EpochSt N V} {l : XLbl N (FacTok V)}
    (h : RefEpochExec C s (.step l) s') : RefExec C s.x l s'.x ∧ s'.rd = s.rd := by
  obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨?_, rfl⟩
  show xstep C s.x l = some x'
  cases l with
  | expire i e => exact (core011b_expire_of hx).1
  | _ => exact hx

/-- A value write of the reference slice is the reference executor's write of the token the
explicit-timestamp factory of CORE-011's F block gives at the epoch reading. -/
theorem core011b_ref_writeVal {C : Cfg N (FacTok V)} {s s' : EpochSt N V} {i : Nat} {p : N}
    {v : V} :
    RefEpochExec C s (.writeVal i p v) s' ↔
      RefExec C s.x (.write i p (refTokenFactory.makeAt s.rd s.rd.epoch v)) s'.x ∧
        s'.rd = s.rd := by
  constructor
  · intro h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hx, rfl⟩
  · rintro ⟨h, hr⟩
    show Option.map _ (xstep C s.x (.write i p (refEpochPol.mintWrite s.rd s.x.now v))) = some s'
    rw [show xstep C s.x (.write i p (refEpochPol.mintWrite s.rd s.x.now v)) = some s'.x from h]
    obtain ⟨x', rd'⟩ := s'
    simp only at hr
    subst hr
    rfl

/-- A raw-value injection request of the reference slice is the reference executor's request of
the token the explicit-timestamp factory gives at the epoch reading. -/
theorem core011b_ref_requestVal {C : Cfg N (FacTok V)} {s s' : EpochSt N V} {p : N} {v : V}
    {r : Reply} :
    RefEpochExec C s (.requestVal p v r) s' ↔
      RefExec C s.x (.request p (refTokenFactory.makeAt s.rd s.rd.epoch v) r) s'.x ∧
        s'.rd = s.rd := by
  constructor
  · intro h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hx, rfl⟩
  · rintro ⟨h, hr⟩
    show Option.map _ (xstep C s.x (.request p (refEpochPol.mintInject s.rd s.x.now v) r)) =
      some s'
    rw [show xstep C s.x (.request p (refEpochPol.mintInject s.rd s.x.now v) r) = some s'.x
      from h]
    obtain ⟨x', rd'⟩ := s'
    simp only at hr
    subst hr
    rfl

/-- **The wall clock does not reach executor-created tokens.** From one executor state and one
epoch reading, a value write of the reference slice leads to the same executor state whether the
host's wall clock reads 5 or 1000: the written token carries the epoch reading in both. -/
@[evidence cites "TIME-015" "Under an injected clock, tokens produced by `ctx.output`, by a raw-value injection, and by a minted action-timeout recovery output all carry timestamps from the injected epoch clock, not from wall time."]
theorem core011b_ref_wall_blind {C : Cfg N (FacTok V)} {x : XSt N (FacTok V)} {w₁ w₂ ep : Int}
    {i : Nat} {p : N} {v : V} {s₁ s₂ : EpochSt N V}
    (h₁ : RefEpochExec C ⟨x, ⟨w₁, ep⟩⟩ (.writeVal i p v) s₁)
    (h₂ : RefEpochExec C ⟨x, ⟨w₂, ep⟩⟩ (.writeVal i p v) s₂) : s₁.x = s₂.x := by
  obtain ⟨x₁, hx₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨x₂, hx₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  exact Option.some.inj (hx₁.symm.trans hx₂)

end Links

/-! ### Consequences of the block -/

section Consequences

variable {N V : Type} [DecidableEq N]

/-- A timeout outcome stamped at any reading is a token-level timeout outcome of EXEC-022: this
block and EXEC-022's line 1 agree on which tokens the outcome holds. -/
theorem core011b_QStamped_exec022 {ep : Int} {t : Trans N} {δ : QDelivered N (FacTok V)}
    {e : List (N × FacTok V)} (h : core011b_QStamped ep t δ e) : exec022_QOutcome t δ e := by
  obtain ⟨o, c, e₀, ho, hc, hS, hq⟩ := h
  exact ⟨o, c, e₀, ho, hc, core011b_stamped_emits c e₀ hS, hq⟩

/-- **A forward keeps the consumed tokens.** When the `Timeout` child of `t` is one
`ForwardInput(src, dst)`, a timeout outcome stamped at any reading puts in `dst` exactly the
tokens the firing consumed from `src`, in consumption order: a seed token created at 3 is
deposited with the timestamp 3, whatever the epoch clock reads. -/
@[evidence cites "IO-014" "A forwarded token's `created_at` equals the original's and is **not** re-stamped from the epoch clock, while a minted recovery token in the same branch *is*, in every implementation."]
theorem core011b_QStamped_forward {ep : Int} {t : Trans N} {δ : QDelivered N (FacTok V)}
    {e : List (N × FacTok V)} {o : Out N} {src dst : N} (ho : t.out = some o)
    (hc : o.findTimeout = some (.forward src dst)) (h : core011b_QStamped ep t δ e) :
    qEmittedTo e dst = δ.inputs src := by
  obtain ⟨o', c, e₀, ho', hc', hS, hq⟩ := h
  rw [ho] at ho'
  obtain rfl := Option.some.inj ho'
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  rw [hq dst]
  change e₀ = (δ.inputs src).map (fun y => (dst, y)) at hS
  subst hS
  simp [qEmittedTo, List.filter_map, Function.comp_def]

/-- **Output tokens follow the epoch clock.** Under the block, a token a value write adds to its
firing's buffer, one that was in no buffer of that firing before, holds the value and carries the
epoch reading of the write. -/
@[evidence cites "CORE-035" "Output tokens are created with the current timestamp of the epoch clock ([TIME-015]); a token a `ForwardInput` forwards keeps its original `created_at` ([IO-014])."]
theorem core011b_output_stamp {E : EpochRel N V} (h : CORE_011_B E) {C : Cfg N (FacTok V)}
    {s s' : EpochSt N V} {i : Nat} {p : N} {v : V} (hs : E C s (.writeVal i p v) s')
    {f' : Firing N (FacTok V)} (hf' : f' ∈ s'.x.fl) (hid : f'.id = i) {z : N × FacTok V}
    (hz : z ∈ f'.buf) (hnew : ∀ f ∈ s.x.fl, f.id = i → z ∉ f.buf) :
    z = (p, ⟨some v, s.rd.epoch⟩) := by
  obtain ⟨f, hf, hfi, hb⟩ := (h.1 C i p v s s' hs).1 f' hf' z hz
  exact (hb.resolve_left (hnew f hf (hfi.trans hid))).2

end Consequences

/-! ### Examples

The transition `t` takes one token from place `0`; its output spec is
`Xor(Place(1), Timeout(d, And(Place(3), ForwardInput(0, 2))))`: the action writes place `1`, or
the budget runs out, a unit token is minted in place `3` and the consumed token is forwarded to
place `2`. Place `4` is an environment place. The seed token in place `0` holds 7 and was created
by the host at 3. The host's wall clock reads 5 and the executor's injected epoch clock 100. -/

/-- `Xor(Place(1), Timeout(d, And(Place(3), ForwardInput(0, 2))))`. -/
def core011b_spec : Out Nat := .xor (.place 1) (.timeout (.and (.place 3) (.forward 0 2)))

/-- The transition of the examples, named `t`: one token from place `0`. -/
def core011b_t : Trans Nat :=
  { core := { name := "t", inputs := [{ place := 0, card := .exactly 1 }], inhibitors := [],
              reads := [], resets := [] },
    out := some core011b_spec }

/-- The configuration of the examples: no validation, every timeout outcome accepted (the
slice's own guard pins the minted one), place `4` an environment place. -/
def core011b_C : Cfg Nat (FacTok Nat) :=
  { X := { net := { places := [0, 1, 2, 3, 4], transitions := [core011b_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [4], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => true,
    res := 0 }

/-- The seed token: it holds 7 and the host created it at 3. -/
def core011b_tok7 : FacTok Nat := ⟨some 7, 3⟩

/-- The initial marking: the seed token in place `0`. -/
def core011b_m0 : QMarking Nat (FacTok Nat) := fun p => if p = 0 then [core011b_tok7] else []

/-- The initial state: the wall clock reads 5, the injected epoch clock 100. -/
def core011b_s0 : EpochSt Nat Nat := ⟨xinit core011b_m0 0, ⟨5, 100⟩⟩

/-- A run of the reference slice, as a fold. -/
def core011b_run {N V : Type} [DecidableEq N] [DecidableEq V] (C : Cfg N (FacTok V))
    (s : EpochSt N V) : List (EpochLbl N V) → Option (EpochSt N V)
  | [] => some s
  | l :: ls => (core011b_stepW refEpochPol C s l).bind fun s' => core011b_run C s' ls

/-- A decided step of the reference slice from the end of a run. -/
theorem core011b_step_of_check {N V : Type} [DecidableEq N] [DecidableEq V]
    {C : Cfg N (FacTok V)} {o : Option (EpochSt N V)} {l : EpochLbl N V}
    {p : EpochSt N V → EpochSt N V → Bool}
    (h : (o.bind fun s => (core011b_stepW refEpochPol C s l).map (p s)) = some true) :
    ∃ s s', o = some s ∧ RefEpochExec C s l s' ∧ p s s' = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some s =>
    cases hg : core011b_stepW refEpochPol C s l with
    | none => simp [ho, hg] at h
    | some s' =>
      simp only [ho, hg, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨s, s', rfl, hg, h⟩

/-- One cycle up to the asynchronous start of `t`. -/
def core011b_pre : List (EpochLbl Nat Nat) :=
  [.step .endCompletions, .step .endPublications, .step .endEvents, .step .update,
   .step (.deadline []), .step .begin, .step (.start "t" false)]

/-- The timeout outcome the executor mints at the epoch reading 120: a unit token in place `3`
stamped 120, and the seed token forwarded to place `2` with its own timestamp 3. -/
def core011b_out : List (Nat × FacTok Nat) := [(3, ⟨none, 120⟩), (2, core011b_tok7)]

/-- After the value write: the clocks move (wall 6, epoch 120), and the action outputs a token it
built itself (51, created at -7). -/
def core011b_mid : List (EpochLbl Nat Nat) :=
  [.tick ⟨6, 120⟩, .step (.write 0 1 ⟨some 51, -7⟩)]

/-- Then a raw value 9 and a host-built token (11, created at -3) are injected, the budget runs
out, and the timeout outcome and both injections land in the marking. -/
def core011b_rest : List (EpochLbl Nat Nat) :=
  [.requestVal 4 9 .accepted, .step (.request 4 ⟨some 11, -3⟩ .accepted),
   .step (.expire 0 core011b_out), .step .endPass, .step (.tdeposit 0), .step .endCompletions,
   .step .endPublications, .step (.inject 1), .step (.inject 2), .step .endEvents]

/-- ✓ CORE-011's executor block is not vacuous. While the host's wall clock reads 5 and the
executor's injected epoch clock reads 100, the action of `t` writes the value 50, and the
executor buffers the token (50, created at 100), not at 5. The clocks then move to 6 and 120,
and the action outputs a token it built at -7: it is buffered as it is. A raw value 9 injected
into place `4` lands as (9, created at 120); a token the host built at -3 lands as it is. The
budget runs out: place `3` gets a unit token created at 120, place `2` gets the seed token with
its own timestamp 3, and the action's written tokens are dropped. -/
@[evidence nonvacuous CORE_011_B]
theorem CORE_011_B_nonvacuous :
    ∃ s s', core011b_run core011b_C core011b_s0 core011b_pre = some s ∧
      RefEpochExec core011b_C s (.writeVal 0 1 50) s' ∧
      s'.x.fl.map (·.buf) = [[(1, ⟨some 50, 100⟩)]] ∧
      ∃ s₁, core011b_run core011b_C s' core011b_mid = some s₁ ∧
        s₁.x.fl.map (·.buf) = [[(1, ⟨some 50, 100⟩), (1, ⟨some 51, -7⟩)]] ∧
      ∃ s'', core011b_run core011b_C s₁ core011b_rest = some s'' ∧
        s''.rd = ⟨6, 120⟩ ∧ s''.x.M 1 = [] ∧ s''.x.M 2 = [core011b_tok7] ∧
        s''.x.M 3 = [⟨none, 120⟩] ∧ s''.x.M 4 = [⟨some 9, 120⟩, ⟨some 11, -3⟩] := by
  obtain ⟨s, s', hs, hstep, hp⟩ := core011b_step_of_check (C := core011b_C)
    (o := core011b_run core011b_C core011b_s0 core011b_pre) (l := .writeVal 0 1 50)
    (p := fun _ s' => s'.x.fl.map (·.buf) == [[(1, ⟨some 50, 100⟩)]] &&
      (core011b_run core011b_C s' core011b_mid).any fun s₁ =>
        s₁.x.fl.map (·.buf) == [[(1, ⟨some 50, 100⟩), (1, ⟨some 51, -7⟩)]] &&
        (core011b_run core011b_C s₁ core011b_rest).any fun s'' =>
          s''.rd == ⟨6, 120⟩ && s''.x.M 1 == [] && s''.x.M 2 == [core011b_tok7] &&
            s''.x.M 3 == [⟨none, 120⟩] && s''.x.M 4 == [⟨some 9, 120⟩, ⟨some 11, -3⟩])
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hb, hr⟩ := hp
  refine ⟨s, s', hs, hstep, hb, ?_⟩
  cases h₁ : core011b_run core011b_C s' core011b_mid with
  | none => simp [h₁] at hr
  | some s₁ =>
    simp only [h₁, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨hb₁, hr⟩ := hr
    refine ⟨s₁, rfl, hb₁, ?_⟩
    cases h : core011b_run core011b_C s₁ core011b_rest with
    | none => simp [h] at hr
    | some s'' =>
      simp only [h, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hr
      exact ⟨s'', rfl, h1, h2, h3, h4, h5⟩


/-! ### Wrong executors

Each is the reference slice with one token choice changed, run from the state `core011b_sIn` in
which the asynchronous firing `0` of `t` is in flight, having consumed the seed token, while the
host's wall clock reads 5, the injected epoch clock 100 and the firing clock 40. -/

/-- The firing in flight in `core011b_sIn`: identity `0`, transition `t`, the seed token
consumed from place `0`, asynchronous, nothing written yet. -/
def core011b_f0 : Firing Nat (FacTok Nat) :=
  { id := 0, t := core011b_t,
    deliv := ⟨fun p => if p = 0 then [core011b_tok7] else [], fun _ => []⟩,
    start := 40, sync := false, buf := [], pub := [], relayBad := false, out := none }

/-- The state of the wrong-executor examples: firing `0` in flight inside the firing pass, the
wall clock at 5, the injected epoch clock at 100, the firing clock at 40. -/
def core011b_sIn : EpochSt Nat Nat :=
  { x := { M := fun _ => [], now := 40, cyc := 40, st := fun _ => .off, fl := [core011b_f0],
           nextId := 1, cq := [], pq := [], eq := [], mode := .open, phase := .pass, order := [],
           delta := fun _ => 0, started := true, parked := false },
    rd := ⟨5, 100⟩ }

/-- What a timeout outcome stamped at `ep` holds for firing `0` of the examples: one token in
place `3`, stamped `ep`, and the seed token itself in place `2`. -/
theorem core011b_stamped_f0 {ep : Int} {e : List (Nat × FacTok Nat)}
    (h : core011b_QStamped ep core011b_t core011b_f0.deliv e) :
    (∃ y : FacTok Nat, y.stamp = ep ∧ qEmittedTo e 3 = [y]) ∧
      qEmittedTo e 2 = [core011b_tok7] := by
  obtain ⟨o, c, e₀, ho, hc, hS, hq⟩ := h
  obtain rfl : core011b_spec = o := Option.some.inj ho
  obtain rfl : (.and (.place 3) (.forward 0 2) : Out Nat) = c := Option.some.inj hc
  obtain ⟨e₁, e₂, rfl, ⟨y, rfl, hy⟩, he₂⟩ := hS
  change e₂ = (core011b_f0.deliv.inputs 0).map (fun y => (2, y)) at he₂
  subst he₂
  refine ⟨⟨y, hy, ?_⟩, ?_⟩
  · rw [hq 3]
    simp [qEmittedTo, core011b_f0]
  · rw [hq 2]
    simp [qEmittedTo, core011b_f0]

/-! #### Line 1: the default factory in place of the epoch clock -/

section MutantDefault

variable {N V : Type} [DecidableEq N]

/-- Mutant reading of line 1 (the text before D64, "a factory that captures the current time",
read as the default factory): a value write adds only the token the default factory gives, which
carries the host's wall-clock reading. Lines 2 to 6 are as in the block. -/
def CORE_011_B_mutant_defaultFactory (E : EpochRel N V) : Prop :=
  (∀ C i (p : N) (v : V), on (fun s s' => E C s (.writeVal i p v) s'), shall (fun s s' =>
    core011b_buffers i (p, refTokenFactory.make s.rd v) s.x s'.x)) ∧
  core011b_line2 E ∧ core011b_line3 E ∧ core011b_line4 E ∧ core011b_line5 E ∧ core011b_line6 E

end MutantDefault

/-- An executor whose value write mints with the host's wall clock (a collector built without
the clock: Java `new TokenOutput()`, TypeScript `tokenOf`). The other choices are the
reference's. -/
def core011b_wallPol {V : Type} : EpochPol V :=
  { refEpochPol with mintWrite := fun r _ v => ⟨some v, r.wall⟩ }

/-- ✗ The wall-clock executor kills the mutant: it meets the default-factory reading, but under
the injected clock (wall 5, epoch 100) the value 50 it writes is buffered as (50, created at 5),
not at 100 (line 1, TIME-015 AC13). -/
@[evidence mutant CORE_011_B]
theorem CORE_011_B_mutant_defaultFactory_killed :
    CORE_011_B_mutant_defaultFactory (core011b_exec (N := Nat) (V := Nat) core011b_wallPol) ∧
      ¬ CORE_011_B (core011b_exec (N := Nat) (V := Nat) core011b_wallPol) := by
  refine ⟨⟨fun C i p v s s' h => (core011b_stepW_lines _ C s s').1 i p v h,
    core011b_exec_line2 (fun _ _ _ => rfl), core011b_exec_line3 (fun _ => rfl) (fun _ _ => rfl),
    core011b_exec_line4 (fun _ _ => rfl), core011b_exec_line5 (fun _ _ => rfl),
    core011b_exec_line6 _⟩, fun h => ?_⟩
  have := (h.1 core011b_C 0 1 50 core011b_sIn _ rfl).1
  revert this
  decide

/-! #### Line 2: the firing clock in place of the epoch clock -/

/-- An executor that stamps a raw-value injection with the firing clock, conflating the two time
bases TIME-015 keeps apart. The other choices are the reference's. -/
def core011b_clockInjectPol {V : Type} : EpochPol V :=
  { refEpochPol with mintInject := fun _ n v => ⟨some v, n⟩ }

/-- ✗ It violates line 2: with the firing clock at 40 and the epoch clock at 100, the raw value
9 injected into place `4` is queued as (9, created at 40). -/
@[evidence forbids CORE_011_B]
theorem CORE_011_B_forbids_firingClockInject :
    ¬ CORE_011_B (core011b_exec (N := Nat) (V := Nat) core011b_clockInjectPol) := by
  intro h
  have := (h.2.1 core011b_C 4 9 .accepted core011b_sIn _ rfl).2.1
  revert this
  decide

/-! #### Line 3: the canonical unit token, and a re-stamped forward -/

section MutantMinted

variable {N V : Type} [DecidableEq N]

/-- Mutant reading of line 3 (EXEC-022's timeout outcome alone, whose minted token is free): an
expiry announces a token-level timeout outcome of a firing in flight. Lines 1, 2, 4, 5 and 6 are
as in the block. -/
def CORE_011_B_mutant_anyMinted (E : EpochRel N V) : Prop :=
  core011b_line1 E ∧ core011b_line2 E ∧
  (∀ C i e, on (fun s s' => E C s (.step (.expire i e)) s'), shall (fun s _ =>
    ∃ f ∈ s.x.fl, f.id = i ∧ exec022_QOutcome f.t f.deliv e)) ∧
  core011b_line4 E ∧ core011b_line5 E ∧ core011b_line6 E

end MutantMinted

/-- An executor that mints the timeout's unit token as the canonical unit token (Java
`Token.unit()` deposited as it is), whose timestamp is 0. The other choices are the
reference's. -/
def core011b_unitZeroPol {V : Type} : EpochPol V :=
  { refEpochPol with mintUnit := fun _ => ⟨none, 0⟩ }

/-- ✗ The canonical-unit executor kills the mutant: its timeout outcome is a token-level outcome,
but with the epoch clock at 100 the unit token it mints in place `3` carries 0 (line 3, ruling
D64 (a)). -/
@[evidence mutant CORE_011_B]
theorem CORE_011_B_mutant_anyMinted_killed :
    CORE_011_B_mutant_anyMinted (core011b_exec (N := Nat) (V := Nat) core011b_unitZeroPol) ∧
      ¬ CORE_011_B (core011b_exec (N := Nat) (V := Nat) core011b_unitZeroPol) := by
  refine ⟨⟨core011b_exec_line1 (fun _ _ _ => rfl), core011b_exec_line2 (fun _ _ _ => rfl),
    fun C i e s s' h => ?_, core011b_exec_line4 (fun _ _ => rfl),
    core011b_exec_line5 (fun _ _ => rfl), core011b_exec_line6 _⟩, fun h => ?_⟩
  · obtain ⟨f, hf, hid, o, c, ho, hc, rfl⟩ := (core011b_stepW_lines _ C s s').2.2.1 i e h
    exact ⟨f, hf, hid, o, c, _, ho, hc, core011b_mint_emits (fun _ => rfl) f.deliv c,
      fun _ => rfl⟩
  · obtain ⟨f, hf, -, hQ⟩ := h.2.2.1 core011b_C 0 [(3, ⟨none, 0⟩), (2, core011b_tok7)]
      core011b_sIn _ rfl
    obtain rfl : f = core011b_f0 := List.mem_singleton.mp hf
    obtain ⟨⟨y, hy, h3⟩, -⟩ := core011b_stamped_f0 hQ
    have he : qEmittedTo ([(3, ⟨none, 0⟩), (2, core011b_tok7)] : List (Nat × FacTok Nat)) 3 =
        [⟨none, 0⟩] := by decide
    rw [he] at h3
    obtain rfl := (List.cons.inj h3).1
    exact absurd hy (by decide)

/-- An executor that re-stamps every forwarded token at the epoch reading. The other choices are
the reference's. -/
def core011b_restampFwdPol {V : Type} : EpochPol V :=
  { refEpochPol with forward := fun r y => ⟨y.val, r.epoch⟩ }

/-- ✗ It violates line 3: the seed token created at 3 is forwarded to place `2` as (7, created
at 100), so a restored or replayed token loses its timestamp (IO-014 AC5). -/
@[evidence forbids CORE_011_B]
theorem CORE_011_B_forbids_restampForward :
    ¬ CORE_011_B (core011b_exec (N := Nat) (V := Nat) core011b_restampFwdPol) := by
  intro h
  obtain ⟨f, hf, -, hQ⟩ := h.2.2.1 core011b_C 0 [(3, ⟨none, 100⟩), (2, ⟨some 7, 100⟩)]
    core011b_sIn _ rfl
  obtain rfl : f = core011b_f0 := List.mem_singleton.mp hf
  obtain ⟨-, h2⟩ := core011b_stamped_f0 hQ
  revert h2
  decide

/-! #### Lines 4 and 5: re-stamping what the host built -/

section MutantKeep

variable {N V : Type} [DecidableEq N]

/-- Mutant reading (the executor lines without the fourth sentence): lines 1 to 3 and 6. -/
def CORE_011_B_mutant_noKeep (E : EpochRel N V) : Prop :=
  core011b_line1 E ∧ core011b_line2 E ∧ core011b_line3 E ∧ core011b_line6 E

end MutantKeep

/-- An executor that re-stamps every token the action or the host built at the epoch reading.
The other choices are the reference's. -/
def core011b_restampHostPol {V : Type} : EpochPol V :=
  { refEpochPol with keepHost := fun r y => ⟨y.val, r.epoch⟩ }

/-- ✗ The re-stamping executor kills the mutant: it meets lines 1 to 3 and 6, but a token holding 50
that the action built at -3 is buffered as (50, created at 100) (line 4; TIME-015: the executor
does not re-stamp host-supplied tokens). -/
@[evidence mutant CORE_011_B]
theorem CORE_011_B_mutant_noKeep_killed :
    CORE_011_B_mutant_noKeep (core011b_exec (N := Nat) (V := Nat) core011b_restampHostPol) ∧
      ¬ CORE_011_B (core011b_exec (N := Nat) (V := Nat) core011b_restampHostPol) := by
  refine ⟨⟨core011b_exec_line1 (fun _ _ _ => rfl), core011b_exec_line2 (fun _ _ _ => rfl),
    core011b_exec_line3 (fun _ => rfl) (fun _ _ => rfl), core011b_exec_line6 _⟩, fun h => ?_⟩
  have := (h.2.2.2.1 core011b_C 0 1 ⟨some 50, -3⟩ core011b_sIn _ rfl).1
  revert this
  decide

/-- Mutant reading (the executor lines without line 5): lines 1 to 4 and 6. -/
def CORE_011_B_mutant_noKeepHost {N V : Type} [DecidableEq N] (E : EpochRel N V) : Prop :=
  core011b_line1 E ∧ core011b_line2 E ∧ core011b_line3 E ∧ core011b_line4 E ∧ core011b_line6 E

/-- Whether a step is a host's injection request of a token it built. -/
def core011b_isTokRequest {N V : Type} : EpochLbl N V → Bool
  | .step (.request _ _ _) => true
  | _ => false

/-- An executor that re-stamps a token the host built and injects at the epoch reading, and keeps
a token the action built as given. Every other choice is the reference's. -/
def core011b_restampInjected {N V : Type} [DecidableEq N] [DecidableEq V] : EpochRel N V :=
  fun C s l s' => core011b_stepW
    (bif core011b_isTokRequest l then core011b_restampHostPol else refEpochPol) C s l = some s'

/-- ✗ The executor that re-stamps only an injected token kills the mutant: it meets lines 1 to 4
and 6, and keeps a token the action built, but a token holding 9 that the host built at -3 and
injects into the environment place `4` is queued as (9, created at 100), with the epoch clock at
100 (line 5; TIME-015: the executor does not re-stamp host-supplied tokens). -/
@[evidence mutant CORE_011_B]
theorem CORE_011_B_mutant_noKeepHost_killed :
    CORE_011_B_mutant_noKeepHost (core011b_restampInjected (N := Nat) (V := Nat)) ∧
      ¬ CORE_011_B (core011b_restampInjected (N := Nat) (V := Nat)) := by
  refine ⟨⟨fun C i p v s s' h => core011b_exec_line1 (P := refEpochPol) (fun _ _ _ => rfl)
      C i p v s s' h,
    fun C p v r s s' h => core011b_exec_line2 (P := refEpochPol) (fun _ _ _ => rfl) C p v r s s' h,
    fun C i e s s' h => core011b_exec_line3 (P := refEpochPol) (fun _ => rfl) (fun _ _ => rfl)
      C i e s s' h,
    fun C i p y s s' h => core011b_exec_line4 (P := refEpochPol) (fun _ _ => rfl) C i p y s s' h,
    fun C l s s' h => core011b_exec_line6
      (bif core011b_isTokRequest l then core011b_restampHostPol else refEpochPol) C l s s' h⟩,
    fun h => ?_⟩
  have := (h.2.2.2.2.1 core011b_C 4 ⟨some 9, -3⟩ .accepted core011b_sIn _ rfl).2.1
  revert this
  decide

/-! #### Line 2: a raw value deposited past the queue -/

section MutantDirect

variable {N V : Type} [DecidableEq N] [DecidableEq V]

/-- An executor that queues an accepted raw value as the reference does and also deposits it
straight into the marking, stamped by the host's wall clock (a fast path that skips the event
queue). Every other step is the reference's. -/
def core011b_directStep (C : Cfg N (FacTok V)) (s : EpochSt N V) :
    EpochLbl N V → Option (EpochSt N V)
  | .requestVal p v r =>
    (core011b_stepW refEpochPol C s (.requestVal p v r)).map fun s' =>
      if r = .accepted then
        ⟨{ s'.x with M := fun q => if q = p then s'.x.M q ++ [⟨some v, s.rd.wall⟩] else s'.x.M q },
          s'.rd⟩
      else s'
  | l => core011b_stepW refEpochPol C s l

/-- The direct-deposit executor as a relation. -/
def core011b_direct : EpochRel N V := fun C s l s' => core011b_directStep C s l = some s'

end MutantDirect

/-- ✗ It violates line 2: the raw value 9 injected into place `4` is queued as (9, created at
100), and a second token (9, created at 5) appears in place `4` at once, a token the injection
creates beside the one it queues. -/
@[evidence forbids CORE_011_B]
theorem CORE_011_B_forbids_directInject :
    ¬ CORE_011_B (core011b_direct (N := Nat) (V := Nat)) := by
  intro h
  have := (h.2.1 core011b_C 4 9 .accepted core011b_sIn _ rfl).2.2.1 4 ⟨some 9, 5⟩ (by decide)
  revert this
  decide

/-! #### Line 6: an epoch reading of the executor's own -/

section MutantClock

variable {N V : Type} [DecidableEq N] [DecidableEq V]

/-- An executor that never consults the injected epoch clock: when the clocks move, it stores the
wall reading as its epoch reading (a clock seam dropped on the way into the executor, so every
stamp falls back to the wall clock: Rust `Context::epoch_now` and the timeout path read
`now_millis()` when no clock is set). Every other step is the reference's. -/
def core011b_ownClockStep (C : Cfg N (FacTok V)) (s : EpochSt N V) :
    EpochLbl N V → Option (EpochSt N V)
  | .tick r => some ⟨s.x, ⟨r.wall, r.wall⟩⟩
  | l => core011b_stepW refEpochPol C s l

/-- The wall-copying executor as a relation. -/
def core011b_ownClock : EpochRel N V := fun C s l s' => core011b_ownClockStep C s l = some s'

/-- An executor that freezes its epoch reading while a firing is in flight: the reading taken
when the firing started stamps its writes and its timeout outcome (the slip of capturing the
clock's value where its source is expected, as in Rust's timeout path capturing `epoch_fn()`
before the action is spawned instead of the function itself). Every other step is the
reference's. -/
def core011b_snapshotStep (C : Cfg N (FacTok V)) (s : EpochSt N V) :
    EpochLbl N V → Option (EpochSt N V)
  | .tick r => some ⟨s.x, if s.x.fl.isEmpty then r else ⟨r.wall, s.rd.epoch⟩⟩
  | l => core011b_stepW refEpochPol C s l

/-- The snapshot executor as a relation. -/
def core011b_snapshot : EpochRel N V := fun C s l s' => core011b_snapshotStep C s l = some s'

end MutantClock

section MutantOwnClock

variable {N V : Type} [DecidableEq N]

/-- Mutant reading (the block before line 6): lines 1 to 5 alone, which read the epoch reading
the executor's state holds, whoever set it. -/
def CORE_011_B_mutant_ownClock (E : EpochRel N V) : Prop :=
  core011b_line1 E ∧ core011b_line2 E ∧ core011b_line3 E ∧ core011b_line4 E ∧ core011b_line5 E

end MutantOwnClock

/-- ✗ The wall-copying executor kills the mutant: on every label lines 1 to 5 read it steps as
the reference, so it meets them; but when the clocks move to wall 6 and injected epoch 120, its
epoch reading becomes 6, not 120 (line 6). -/
@[evidence mutant CORE_011_B]
theorem CORE_011_B_mutant_ownClock_killed :
    CORE_011_B_mutant_ownClock (core011b_ownClock (N := Nat) (V := Nat)) ∧
      ¬ CORE_011_B (core011b_ownClock (N := Nat) (V := Nat)) := by
  refine ⟨⟨fun C i p v s s' h => (CORE_011_B_reference (N := Nat) (V := Nat)).1 C i p v s s' h,
    fun C p v r s s' h => (CORE_011_B_reference (N := Nat) (V := Nat)).2.1 C p v r s s' h,
    fun C i e s s' h => (CORE_011_B_reference (N := Nat) (V := Nat)).2.2.1 C i e s s' h,
    fun C i p y s s' h => (CORE_011_B_reference (N := Nat) (V := Nat)).2.2.2.1 C i p y s s' h,
    fun C p y r s s' h => (CORE_011_B_reference (N := Nat) (V := Nat)).2.2.2.2.1 C p y r s s' h⟩,
    fun h => ?_⟩
  have := h.2.2.2.2.2 core011b_C (.tick ⟨6, 120⟩) core011b_sIn _ rfl
  revert this
  decide

/-- What the wall-copying executor does to a run: with firing `0` in flight and the clocks moving
to wall 6 and injected epoch 120, the value 50 written next is buffered as (50, created at 6),
wall time, where the reference buffers (50, created at 120). -/
theorem core011b_ownClock_stamps_wall :
    ((core011b_ownClockStep core011b_C core011b_sIn (.tick ⟨6, 120⟩)).bind fun s₁ =>
      (core011b_ownClockStep core011b_C s₁ (.writeVal 0 1 50)).map fun s₂ => s₂.x.fl.map (·.buf))
      = some [[(1, ⟨some 50, 6⟩)]] ∧
    ((core011b_stepW refEpochPol core011b_C core011b_sIn (.tick ⟨6, 120⟩)).bind fun s₁ =>
      (core011b_stepW refEpochPol core011b_C s₁ (.writeVal 0 1 50)).map
        fun s₂ => s₂.x.fl.map (·.buf))
      = some [[(1, ⟨some 50, 120⟩)]] := by
  decide

/-- ✗ The snapshot executor violates line 6: firing `0` started while the epoch clock read 100;
the clocks move to wall 6 and injected epoch 120 while it is in flight, and the executor's epoch
reading stays at 100, so the value it writes next would be stamped 100. -/
@[evidence forbids CORE_011_B]
theorem CORE_011_B_forbids_snapshotEpoch :
    ¬ CORE_011_B (core011b_snapshot (N := Nat) (V := Nat)) := by
  intro h
  have := h.2.2.2.2.2 core011b_C (.tick ⟨6, 120⟩) core011b_sIn _ rfl
  revert this
  decide

end Libpetri.Spec
