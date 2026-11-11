import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryAction

set_option linter.missingDocs true

/-!
# CORE-011: Token creation (`spec/01-core-model.md`)

CORE-011 says how a host creates a token and which timestamp the token carries (ruling D64 (a)).
The model is a token factory `K : TokenFactory V`, three functions a host calls: the default
factory `make`, the explicit-timestamp factory `makeAt` and the canonical unit-token constructor
`unit`. Each is called at the readings of two clocks (`ClockReadings`): the host's wall clock and
the epoch clock of an executor the host runs, which differs from the wall clock when that
executor runs on an injected clock ([TIME-015]). A token (`FacTok V`) is an optional value (none
for the unit token, glossary: Unit token) and a timestamp, an integer count of the
implementation's unit since the start of the epoch, so a timestamp before the epoch or finer than
a millisecond is in the model.

The three lines: the default factory keeps the value and stamps the reading of the host's wall
clock, never the epoch clock's; the explicit-timestamp factory keeps the value and the timestamp
it is given, unclamped and unrounded; the canonical unit token has no value and the timestamp 0.
The witness is the block local `refTokenFactory`, which is what `Token.of`, `Token::new`,
`tokenOf` (default), the record constructor, `Token::at`, `tokenAt` (explicit) and `Token.unit()`,
`unit_token()`, `unitToken()` do. The statement pins the factory exactly (`core011_unique`). AC2
(sequential tokens have non-decreasing timestamps) is derived from line 1 under the kind A
assumption that the wall clock does not go back (`core011_monotone`); when it does go back, so do
the stamps (`core011_wall_back`).

Wrong factories are killed against plausible wrong readings: the old AC2 alone, which a factory
stamping a later reading meets, and the executor's epoch clock (line 1); the old text with one
factory, which a factory that re-stamps an explicit timestamp meets, and the explicit factory over
non-negative timestamps only, which a factory clamping at 0 meets (line 2); and a unit token of
unspecified timestamp, which a unit constructor stamping the wall clock (ruling D64 (b)) meets
(line 3). A factory with state is read at every state a host reaches: a high-water-mark clamp is
killed at the state it reaches after one call (`CORE_011_forbids_clamp`).

The executor line (a token the executor creates is stamped from its epoch clock while the firing
is in flight; a forwarded token keeps its timestamp) is CORE-011's second block, over the executor
model, in wave W11.
-/

namespace Libpetri.Spec

/-! ## The model (block-local) -/

/-- The readings of the two clocks when a host calls a factory: `wall`, the host's wall clock,
and `epoch`, the epoch clock of an executor the host runs ([TIME-015]: it equals the wall clock
unless that executor runs on an injected clock). Both count the implementation's unit since the
start of the epoch. -/
structure ClockReadings where
  /-- The reading of the host's wall clock at the call. -/
  wall : Int
  /-- The reading of an executor's epoch clock at the call. -/
  epoch : Int
  deriving DecidableEq, Repr

/-- A token as a factory returns it: its value, absent for the unit token ([CORE-012]), and its
creation timestamp. Immutability is CORE-010's. -/
structure FacTok (V : Type) where
  /-- The value; `none` for a token without a value (glossary: Unit token). -/
  val : Option V
  /-- The creation timestamp: an integer count of the implementation's unit since the start of
  the epoch, negative before it. -/
  stamp : Int
  deriving DecidableEq, Repr

/-- A host's token factories: the default factory, the explicit-timestamp factory and the
canonical unit-token constructor, each called at the readings of the clocks. -/
structure TokenFactory (V : Type) where
  /-- The default factory: the token for value `v`, created when the clocks read `r`. -/
  make : ClockReadings → V → FacTok V
  /-- The explicit-timestamp factory: the token for value `v` at timestamp `s`, created when the
  clocks read `r`. -/
  makeAt : ClockReadings → Int → V → FacTok V
  /-- The canonical unit-token constructor, called when the clocks read `r`. -/
  unit : ClockReadings → FacTok V

/-- **The reference token factory** (block-local witness): the default factory stamps the
host's wall-clock reading (`Token.of` with `Instant.now()`, `Token::new` with `now_millis()`,
`tokenOf` with `Date.now()`), the explicit-timestamp factory keeps the timestamp as given (the
`Token` record constructor, `Token::at`, `tokenAt`), and the canonical unit token has no value and
the timestamp 0 (`Instant.EPOCH`, `created_at: 0`, `createdAt: 0`). -/
def refTokenFactory {V : Type} : TokenFactory V where
  make r v := ⟨some v, r.wall⟩
  makeAt _ s v := ⟨some v, s⟩
  unit _ := ⟨none, 0⟩

#spec_witness refTokenFactory

/-! ## CORE-011: Token Creation -/

requirement CORE_011
  id "CORE-011"
  title "Token Creation"
  kind F
  scope "the host token factories of Java, TypeScript and Rust"
  source verbatim "spec/01-core-model.md"
  quote "*When* a host creates a token from a value through the default factory, the token *shall* hold that value and carry the reading of the host's wall clock at the call as its creation timestamp, whatever clock an executor runs on ([TIME-015])."
        "*When* a host creates a token from a value and a timestamp through the explicit-timestamp factory, the token *shall* hold that value and carry that timestamp, whatever the clocks read at the call."
        "*When* a host creates the canonical unit token, the token *shall* hold no value and carry the timestamp 0, whatever the clocks read at the call."
  reading "For the token factory K (make the default factory, makeAt the explicit-timestamp factory, unit the canonical unit-token constructor, each called when the host's wall clock reads r.wall and an executor's epoch clock reads r.epoch, timestamps being integers):"
          "for all readings r and every value v, the default factory's token holds v and carries the timestamp r.wall;"
          "for all readings r, every timestamp s (negative ones included) and every value v, the explicit-timestamp factory's token holds v and carries the timestamp s;"
          "for all readings r, the canonical unit token is a unit token (it holds no value) and carries the timestamp 0."
  assumes "The model is a token factory K : TokenFactory V (block-local): three functions a host calls, the default factory make, the explicit-timestamp factory makeAt and the canonical unit-token constructor unit. Each takes the readings at the call (ClockReadings): wall, of the host's wall clock, and epoch, of the epoch clock of an executor the host runs, which differs from wall when that executor runs on an injected clock (TIME-015). A token (FacTok V) is an optional value, none for a token without a value (glossary: Unit token, IsUnitToken; CORE-012), and a timestamp. The model takes the readings as given: which reading a call sees, and the clocks themselves, are not modelled. The witness is refTokenFactory, and CORE-011 holds of no other factory (core011_unique)."
          "A timestamp is an integer count of the implementation's unit since the start of the epoch, negative before it: nanoseconds for a Java Instant, milliseconds in Rust, and for TypeScript a unit fine enough that the number given is a whole count of it (every finite number is a whole count of 2 to the power -1074). So a timestamp before the epoch, or finer than a millisecond, is in scope. Rust's timestamp is a u64, so its explicit-timestamp factory takes only s at least 0, and line 2 applies to those."
          "A factory with state (a cache, a high-water mark) is read as the family of its states: CORE-011 holds of it when it holds at every state a host can reach. A default factory that clamps its stamp to the last stamp it handed out, so that AC2 holds while the wall clock goes back, violates line 1 at the state it reaches after a call at the wall reading 10 (CORE_011_forbids_clamp: called next at the wall reading 5, it stamps 10)."
          "Line 1 is the first sentence (ruling D64 (a)). 'The reading of the host's wall clock at the call' is r.wall; 'whatever clock an executor runs on' is that the stamp does not depend on r.epoch: the factory is called from host code, which no executor's clock reaches (core011_make_epoch_blind). A factory that always stamps 0 (CORE_011_forbids_zero), one that stamps a later reading (CORE_011_forbids_later) and one that stamps the epoch clock (CORE_011_mutant_epochClock_killed) violate it. The later reading stands in for any reading other than the one at the call: a test cannot see when inside the call the clock is read, so it checks that the stamp lies between wall readings taken just before and just after the call (core011_make_between)."
          "Line 2 is the second sentence: the explicit-timestamp construction TIME-015 requires (spec/03-timing.md, token stamping boundary), and what a snapshot restore (CORE-073) and a seed token (a seed-token helper is this factory applied to a clock's reading) use. A factory that re-stamps the given timestamp with the wall clock violates it (CORE_011_mutant_noExplicit_killed: the text before D64, with one factory, held of it). So do a factory that clamps a timestamp before the epoch to 0 (CORE_011_mutant_nonnegStamps_killed: the reading over non-negative timestamps only held of it) and one that rounds a timestamp to a coarser unit, as a Java Instant truncated to milliseconds (CORE_011_forbids_truncate)."
          "Line 3 is the third sentence (ruling D64 (a): stamp 0 only for the canonical unit constructor). That the canonical unit token is shared (a cached singleton in Java and TypeScript) and recognised by identity there, and how a runtime tells a unit token from a token holding a value, are CORE-012's and not modelled. A unit token the executor creates on a timeout outcome is not this constructor's: it is stamped from the epoch clock, which is the executor line. A unit constructor that stamps the wall clock (ruling D64 (b)) violates line 3 (CORE_011_mutant_unitUnspecified_killed: the reading with the unit token's timestamp left open held of it)."
          "AC1 (creating a token through the default factory yields a token that holds the given value and records the current reading of the host's wall clock) is line 1."
          "AC2 (while the host's wall clock does not go back, two tokens created one after the other through the default factory have non-decreasing timestamps) is core011_monotone, derived from line 1 under the kind A assumption that the wall clock does not go back between the two calls (r1.wall ≤ r2.wall). Without it AC2 has no basis (clash K6): a wall clock may be set back, and then the second stamp is the lower one (core011_wall_back). AC2 does not hold of a default-factory token followed by an explicit-timestamp or a unit token, and the old AC2 alone does not pin the stamp (CORE_011_mutant_monotoneOnly_killed)."
          "AC3 (a token created at an explicit timestamp holds the given value and carries that timestamp unchanged, also before the epoch or finer than a millisecond where the timestamp type holds it) is line 2."
          "AC4 (the canonical unit token holds no value and carries the timestamp 0) is line 3."
          "AC5 (while an executor runs on an injected clock, a token created through the default factory carries the reading of the host's wall clock, not the injected clock's) is line 1 at readings whose epoch differs from wall: core011_make_epoch_blind, and CORE_011_mutant_epochClock_killed at a wall reading of 5 while the injected clock reads 100."
          "The test derivation (a default token between two wall readings; two default tokens in sequence, the second timestamp at least the first; the same under an injected clock; tokens at explicit timestamps before the epoch and finer than a millisecond; the unit token; each holding its value) is CORE_011_nonvacuous on refTokenFactory, at wall readings 5 then 8 while an executor's injected epoch clock reads 100, with explicit timestamps -3 and 1500."
          "Deferred to CORE-011's second block (wave W11, ruling D64 (a)): a token the executor creates (an action output written as a value, a token injected as a raw value, the unit token of a timeout outcome) carries a reading of the executor's epoch clock taken while the firing is in flight, and a forwarded token keeps its timestamp (IO-014). A token an action builds itself through a factory and outputs as a token (Java's output(Place, Token), TypeScript's outputToken) keeps that factory's stamp, which lines 1 and 2 already fix. CORE-035 AC2 and TIME-015 AC13 cite that line. It needs the executor model (RefExec) with an epoch clock next to the firing clock."
          "Python has no token object and no token factory: a Python host passes values, and the Rust runtime it binds creates their tokens (ruling R5). Immutability of the token is CORE-010's."
  signoff "pending"
  statement : ∀ {V : Type}, TokenFactory V → Prop :=
    fun K =>
      (∀ r v, K.make r v = ⟨some v, r.wall⟩) ∧
      (∀ r s v, K.makeAt r s v = ⟨some v, s⟩) ∧
      (∀ r, IsUnitToken FacTok.val (K.unit r) ∧ (K.unit r).stamp = 0)

/- The pinned readable form of CORE-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_011 : {V : Type} → TokenFactory V → Prop :=
fun {V} K =>
  (∀ (r : ClockReadings) (v : V), K.make r v = { val := some v, stamp := r.wall }) ∧
    (∀ (r : ClockReadings) (s : ℤ) (v : V), K.makeAt r s v = { val := some v, stamp := s }) ∧
      ∀ (r : ClockReadings), IsUnitToken FacTok.val (K.unit r) ∧ (K.unit r).stamp = 0
-/
#guard_msgs in #print CORE_011

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {V : Type}

/-- Line 1 of CORE-011: the default factory keeps the value and stamps the wall-clock reading. -/
def core011_line1 (K : TokenFactory V) : Prop := ∀ r v, K.make r v = ⟨some v, r.wall⟩

/-- Line 2 of CORE-011: the explicit-timestamp factory keeps the value and the timestamp. -/
def core011_line2 (K : TokenFactory V) : Prop := ∀ r s v, K.makeAt r s v = ⟨some v, s⟩

/-- Line 3 of CORE-011: the canonical unit token has no value and the timestamp 0. -/
def core011_line3 (K : TokenFactory V) : Prop :=
  ∀ r, IsUnitToken FacTok.val (K.unit r) ∧ (K.unit r).stamp = 0

/-- CORE-011 is its three lines. -/
theorem core011_iff (K : TokenFactory V) :
    CORE_011 K ↔ core011_line1 K ∧ core011_line2 K ∧ core011_line3 K :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference token factory satisfies CORE-011, at every value type. -/
@[evidence holds CORE_011]
theorem CORE_011_reference {V : Type} : CORE_011 (refTokenFactory (V := V)) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

/-! ### Consequences -/

section Consequences

variable {V : Type} {K : TokenFactory V}

/-- CORE-011 pins the factory: the reference is the only factory it holds of, so a wrong factory
without state is killed by the statement itself. -/
theorem core011_unique (h : CORE_011 K) : K = refTokenFactory := by
  obtain ⟨mk, mkAt, un⟩ := K
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : mk = refTokenFactory.make := funext fun r => funext fun v => h1 r v
  have e2 : mkAt = refTokenFactory.makeAt :=
    funext fun r => funext fun s => funext fun v => h2 r s v
  have e3 : un = refTokenFactory.unit := funext fun r => by
    obtain ⟨hv, hs⟩ := h3 r
    simp only [IsUnitToken] at hv hs
    show un r = ⟨none, 0⟩
    cases hu : un r with
    | mk a b =>
      rw [hu] at hv hs
      simp only at hv hs
      subst hv; subst hs; rfl
  subst e1; subst e2; subst e3; rfl

/-- **AC2**: while the host's wall clock does not go back between two calls of the default
factory (the kind A assumption `r₁.wall ≤ r₂.wall`), the second token's timestamp is at least the
first's. -/
theorem core011_monotone (h : CORE_011 K) {r₁ r₂ : ClockReadings} (hr : r₁.wall ≤ r₂.wall)
    (v₁ v₂ : V) : (K.make r₁ v₁).stamp ≤ (K.make r₂ v₂).stamp := by
  rw [h.1 r₁ v₁, h.1 r₂ v₂]
  exact hr

/-- AC2 needs its precondition: when the wall clock is set back from 10 to 5 between two calls of
the default factory, the second token's timestamp is the lower one, 5. -/
theorem core011_wall_back (h : CORE_011 K) (e₁ e₂ : Int) (v₁ v₂ : V) :
    (K.make ⟨10, e₁⟩ v₁).stamp = 10 ∧ (K.make ⟨5, e₂⟩ v₂).stamp = 5 := by
  rw [h.1, h.1]
  exact ⟨rfl, rfl⟩

/-- **AC1 as a test checks it**: when wall readings `b` before the call and `a` after it bound
the reading at the call, the default token's timestamp lies between them. -/
theorem core011_make_between (h : CORE_011 K) {b a : Int} (r : ClockReadings)
    (hb : b ≤ r.wall) (ha : r.wall ≤ a) (v : V) :
    b ≤ (K.make r v).stamp ∧ (K.make r v).stamp ≤ a := by
  rw [h.1 r v]
  exact ⟨hb, ha⟩

/-- **AC5**: the default factory does not read an executor's epoch clock: at one wall-clock
reading, the token is the same whatever the epoch clock reads. -/
theorem core011_make_epoch_blind (h : CORE_011 K) (w e₁ e₂ : Int) (v : V) :
    K.make ⟨w, e₁⟩ v = K.make ⟨w, e₂⟩ v := by
  rw [h.1, h.1]

/-- The explicit-timestamp factory keeps the timestamp it is given, whatever the clocks read:
the construction at an explicit timestamp that TIME-015 requires a host to have. -/
@[evidence cites "TIME-015" "an implementation MUST therefore offer construction of a token at an explicit timestamp ([CORE-011]) so a host can keep those replay-safe without one"]
theorem core011_explicit (h : CORE_011 K) (r : ClockReadings) (s : Int) (v : V) :
    (K.makeAt r s v).stamp = s ∧ (K.makeAt r s v).val = some v := by
  rw [h.2.1 r s v]
  exact ⟨rfl, rfl⟩

/-- The canonical unit token is a unit token: it holds no value. -/
@[evidence cites "CORE-012" "A unit token is a special token with no meaningful payload value, used for pure control flow signaling. The engine provides a canonical way to create unit tokens."]
theorem core011_unit_isUnit (h : CORE_011 K) (r : ClockReadings) :
    IsUnitToken FacTok.val (K.unit r) :=
  (h.2.2 r).1

end Consequences

/-! ### The test derivation -/

/-- The clocks at the first call: the host's wall clock reads 5, an executor's injected epoch
clock reads 100. -/
def core011_r₁ : ClockReadings := ⟨5, 100⟩

/-- The clocks at the second call: the wall clock reads 8, the epoch clock still 100. -/
def core011_r₂ : ClockReadings := ⟨8, 100⟩

/-- ✓ CORE-011 is not vacuous. The test derivation on the reference: two tokens created in
sequence through the default factory, at wall readings 5 then 8 while an executor's injected epoch
clock reads 100, hold their values and carry the timestamps 5 and 8 (not 100), so the second is at
least the first; a token created at the explicit timestamp -3 (before the epoch) carries -3, and
one at 1500 (finer than the unit a truncation would keep) carries 1500; the canonical unit token
holds no value and carries 0. -/
@[evidence nonvacuous CORE_011]
theorem CORE_011_nonvacuous :
    (refTokenFactory (V := Nat)).make core011_r₁ 7 = ⟨some 7, 5⟩ ∧
    (refTokenFactory (V := Nat)).make core011_r₂ 9 = ⟨some 9, 8⟩ ∧
    ((refTokenFactory (V := Nat)).make core011_r₁ 7).stamp ≤
      ((refTokenFactory (V := Nat)).make core011_r₂ 9).stamp ∧
    (refTokenFactory (V := Nat)).makeAt core011_r₂ (-3) 7 = ⟨some 7, -3⟩ ∧
    (refTokenFactory (V := Nat)).makeAt core011_r₂ 1500 7 = ⟨some 7, 1500⟩ ∧
    (refTokenFactory (V := Nat)).unit core011_r₂ = ⟨none, 0⟩ := by
  decide

/-! ### Wrong factories -/

/-- A factory whose default factory stamps every token 0, the canonical unit token's timestamp.
The other two factories are the reference's. -/
def core011_zero {V : Type} : TokenFactory V :=
  { refTokenFactory with make := fun _ v => ⟨some v, 0⟩ }

/-- ✗ It violates line 1: at a wall reading of 5 its default token carries 0. -/
@[evidence forbids CORE_011]
theorem CORE_011_forbids_zero : ¬ CORE_011 (core011_zero (V := Nat)) := by
  intro h
  have := h.1 core011_r₁ 7
  revert this
  decide

/-- A factory whose default factory stamps a later reading than the one at the call (one unit
after the wall clock). The other two factories are the reference's. -/
def core011_later {V : Type} : TokenFactory V :=
  { refTokenFactory with make := fun r v => ⟨some v, r.wall + 1⟩ }

/-- ✗ It violates line 1: at a wall reading of 5 its default token carries 6. -/
@[evidence forbids CORE_011]
theorem CORE_011_forbids_later : ¬ CORE_011 (core011_later (V := Nat)) := by
  intro h
  have := h.1 core011_r₁ 7
  revert this
  decide

/-! ### A factory with state: the high-water-mark clamp -/

section Clamp

variable {V : Type}

/-- One call of a default factory that keeps a high-water mark `last` and stamps
`max last wall`, so that its stamps never go back (a module-level `Math.max(last, Date.now())`,
an `AtomicLong` mark in Java, an `AtomicU64::fetch_max` in Rust): the token and the next state. -/
def core011_clampStep (last : Int) (r : ClockReadings) (v : V) : FacTok V × Int :=
  (⟨some v, max last r.wall⟩, max last r.wall)

/-- The clamping factory in state `last`. The other two factories are the reference's. -/
def core011_clamp (last : Int) : TokenFactory V :=
  { refTokenFactory with make := fun r v => (core011_clampStep last r v).1 }

end Clamp

/-- ✗ The clamping factory violates line 1 at the state it reaches from state 0 after one call
at the wall reading 10: called next at the wall reading 5, it stamps 10. -/
@[evidence forbids CORE_011]
theorem CORE_011_forbids_clamp :
    ¬ CORE_011 (core011_clamp (V := Nat) (core011_clampStep (V := Nat) 0 ⟨10, 10⟩ 7).2) := by
  intro h
  have := h.1 ⟨5, 5⟩ 8
  revert this
  decide

/-! ### Mutant: line 1 as the old AC2 alone -/

section MutantMonotone

variable {V : Type}

/-- Mutant reading of line 1 (the text before D64: AC2 alone): the default factory keeps the
value and two tokens created at non-decreasing wall readings carry non-decreasing timestamps.
Lines 2 and 3 are as in CORE-011. -/
def CORE_011_mutant_monotoneOnly (K : TokenFactory V) : Prop :=
  (∀ r v, (K.make r v).val = some v) ∧
    (∀ r₁ r₂ v₁ v₂, r₁.wall ≤ r₂.wall → (K.make r₁ v₁).stamp ≤ (K.make r₂ v₂).stamp) ∧
    core011_line2 K ∧ core011_line3 K

end MutantMonotone

/-- ✗ The later-reading factory kills the mutant: its stamps are monotone in the wall reading, but
it does not stamp the reading at the call (line 1). -/
@[evidence mutant CORE_011]
theorem CORE_011_mutant_monotoneOnly_killed :
    CORE_011_mutant_monotoneOnly (core011_later (V := Nat)) ∧
      ¬ CORE_011 (core011_later (V := Nat)) :=
  ⟨⟨fun _ _ => rfl, fun _ _ _ _ h => Int.add_le_add_right h 1, fun _ _ _ => rfl,
    fun _ => ⟨rfl, rfl⟩⟩, CORE_011_forbids_later⟩

/-! ### Mutant: line 1 with the epoch clock -/

section MutantEpoch

variable {V : Type}

/-- Mutant reading of line 1 ("captures the current time" read as the executor's epoch clock):
the default factory stamps the epoch clock's reading. Lines 2 and 3 are as in CORE-011. -/
def CORE_011_mutant_epochClock (K : TokenFactory V) : Prop :=
  (∀ r v, K.make r v = ⟨some v, r.epoch⟩) ∧ core011_line2 K ∧ core011_line3 K

/-- A factory whose default factory stamps the epoch clock of an executor the host runs, so an
injected clock reaches it. The other two factories are the reference's. -/
def core011_epoch : TokenFactory V :=
  { refTokenFactory with make := fun r v => ⟨some v, r.epoch⟩ }

end MutantEpoch

/-- ✗ The epoch-clock factory kills the mutant: it meets the wrong reading, but at a wall reading
of 5 while an injected epoch clock reads 100 its default token carries 100 (line 1, AC5). -/
@[evidence mutant CORE_011]
theorem CORE_011_mutant_epochClock_killed :
    CORE_011_mutant_epochClock (core011_epoch (V := Nat)) ∧
      ¬ CORE_011 (core011_epoch (V := Nat)) := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩, fun h => ?_⟩
  have := h.1 core011_r₁ 7
  revert this
  decide

/-! ### Mutant: no explicit-timestamp line (one factory) -/

section MutantNoExplicit

variable {V : Type}

/-- Mutant reading (the text before D64, which names one factory): lines 1 and 3 alone. -/
def CORE_011_mutant_noExplicit (K : TokenFactory V) : Prop :=
  core011_line1 K ∧ core011_line3 K

/-- A factory whose explicit-timestamp factory re-stamps the token with the wall clock and drops
the timestamp it is given. The other two factories are the reference's. -/
def core011_restamp : TokenFactory V :=
  { refTokenFactory with makeAt := fun r _ v => ⟨some v, r.wall⟩ }

end MutantNoExplicit

/-- ✗ The re-stamping factory kills the mutant: it meets lines 1 and 3, but a token created at the
explicit timestamp 3 while the wall clock reads 5 carries 5 (line 2). -/
@[evidence mutant CORE_011]
theorem CORE_011_mutant_noExplicit_killed :
    CORE_011_mutant_noExplicit (core011_restamp (V := Nat)) ∧
      ¬ CORE_011 (core011_restamp (V := Nat)) := by
  refine ⟨⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩, fun h => ?_⟩
  have := h.2.1 core011_r₁ 3 7
  revert this
  decide

/-! ### Mutant: line 2 over non-negative timestamps only -/

section MutantNonneg

variable {V : Type}

/-- Mutant reading of line 2 (timestamps as natural numbers, before this block's integer
domain): the explicit-timestamp factory keeps a timestamp at or after the start of the epoch.
Lines 1 and 3 are as in CORE-011. -/
def CORE_011_mutant_nonnegStamps (K : TokenFactory V) : Prop :=
  core011_line1 K ∧ (∀ r s v, 0 ≤ s → K.makeAt r s v = ⟨some v, s⟩) ∧ core011_line3 K

/-- A factory whose explicit-timestamp factory clamps the timestamp at 0, the start of the epoch
(a TypeScript `tokenAt` storing `Math.max(0, t)` to "validate" it). The other two factories are
the reference's. -/
def core011_clampAt0 : TokenFactory V :=
  { refTokenFactory with makeAt := fun _ s v => ⟨some v, max 0 s⟩ }

end MutantNonneg

/-- ✗ The clamping-at-0 factory kills the mutant: it keeps every timestamp at or after the epoch,
but a token restored at the timestamp -3, before the epoch, carries 0 (line 2). -/
@[evidence mutant CORE_011]
theorem CORE_011_mutant_nonnegStamps_killed :
    CORE_011_mutant_nonnegStamps (core011_clampAt0 (V := Nat)) ∧
      ¬ CORE_011 (core011_clampAt0 (V := Nat)) := by
  refine ⟨⟨fun _ _ => rfl, fun _ s _ hs => ?_, fun _ => ⟨rfl, rfl⟩⟩, fun h => ?_⟩
  · show (⟨_, max 0 s⟩ : FacTok Nat) = ⟨_, s⟩
    rw [Int.max_eq_right hs]
  · have := h.2.1 core011_r₁ (-3) 7
    revert this
    decide

/-- A factory whose explicit-timestamp factory truncates the timestamp to a unit 1000000 times
coarser (a Java compact constructor `createdAt.truncatedTo(ChronoUnit.MILLIS)` over an `Instant`
counted in nanoseconds, or a TypeScript `Math.trunc` of fractional milliseconds). The other two
factories are the reference's. -/
def core011_truncate {V : Type} : TokenFactory V :=
  { refTokenFactory with makeAt := fun _ s v => ⟨some v, s / 1000000 * 1000000⟩ }

/-- ✗ It violates line 2: a token restored at the timestamp 1500 carries 0. -/
@[evidence forbids CORE_011]
theorem CORE_011_forbids_truncate : ¬ CORE_011 (core011_truncate (V := Nat)) := by
  intro h
  have := h.2.1 core011_r₁ 1500 7
  revert this
  decide

/-! ### Mutant: the unit token's timestamp left open -/

section MutantUnit

variable {V : Type}

/-- Mutant reading of line 3 (the draft of ruling R3, before D64: the canonical unit token's
timestamp unspecified): the canonical unit token is a unit token. Lines 1 and 2 are as in
CORE-011. -/
def CORE_011_mutant_unitUnspecified (K : TokenFactory V) : Prop :=
  core011_line1 K ∧ core011_line2 K ∧ ∀ r, IsUnitToken FacTok.val (K.unit r)

/-- A factory whose unit constructor takes a reading too (ruling D64 (b)): the canonical unit
token carries the wall-clock reading at the call. The other two factories are the reference's. -/
def core011_unitNow : TokenFactory V :=
  { refTokenFactory with unit := fun r => ⟨none, r.wall⟩ }

end MutantUnit

/-- ✗ The stamped-unit factory kills the mutant: its unit token holds no value, but created while
the wall clock reads 5 it carries 5, not 0 (line 3). -/
@[evidence mutant CORE_011]
theorem CORE_011_mutant_unitUnspecified_killed :
    CORE_011_mutant_unitUnspecified (core011_unitNow (V := Nat)) ∧
      ¬ CORE_011 (core011_unitNow (V := Nat)) := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  have := (h.2.2 core011_r₁).2
  revert this
  decide

end Libpetri.Spec
