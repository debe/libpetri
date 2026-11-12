import Libpetri.Spec.Verifier.Pipeline

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-013: Solver Transport (`spec/07-verification.md`)

The solver transport has four parts, each a block of its own:

* `VER_013_order` (F): names are ordered by Unicode code point, never by UTF-16 code unit. The
  witness is `refNameLt`, the lexicographic order of the code-point lists.
* `VER_013_args` (F): the timeouts of one `z3` process, `-t`, `-T` and the watchdog, from its
  budget of `t ≥ 1` milliseconds (ruling D90 (a)), and the clamp a total budget applies before a
  process starts. The witnesses are `refBudgets` (`z3_process.rs` `args_for`,
  `hard_timeout_secs`, `watchdog_ms`) and `refClamp` (`total_budget.rs` `clamp`).
* `VER_013_classify` (F): how a reply is read, the first trimmed verdict line wherever it
  appears, and without one the failure reason in the order the transport fixes. The witness is
  `refClassify` (`z3_process.rs` `classify_first_line`, `failure_reason`).
* `VER_013_stop` (B): the pipeline under a solver and a stop, over an abstract runner `RP` and a
  finisher `Fin`. A decision is something the deciding step's program can return when every
  solver call gets the solver's reply or a refusal to start; a stop found on entering a step is
  charged to the step that was running; after a stop nothing starts and nothing is decided; a
  `Proven` or `Violated` stands and an `Unknown` takes the stop's reason; without a stop none is
  recorded. The witness is `runPipeline` and `finishVerdict` of `Spec/Verifier/Pipeline.lean`.
-/

namespace Libpetri.Spec

open Libpetri.Spec.Verifier

namespace Ver013

/-! ## Name order -/

/-- A strict order on names, as a comparator. -/
abbrev NameLt : Type := String → String → Bool

/-- The Unicode code points of a name. -/
def codePoints (s : String) : List Nat := s.toList.map Char.toNat

/-- **The reference name order**: lexicographic on code points. -/
def refNameLt : NameLt := fun a b => decide (codePoints a < codePoints b)

/-- The UTF-16 code units of one character. -/
def utf16Units (c : Char) : List Nat :=
  if c.toNat < 0x10000 then [c.toNat]
  else [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400]

/-- Lexicographic on UTF-16 code units (JavaScript `<`, Java `String.compareTo`). -/
def utf16NameLt : NameLt := fun a b =>
  decide (a.toList.flatMap utf16Units < b.toList.flatMap utf16Units)

/-- A one-character name. -/
def cp (n : Nat) : String := String.singleton (Char.ofNat n)

/-- The AC7 vector, in the order every implementation must sort it into. -/
def ac7 : List String :=
  ["", "Z", "a", "ab", "Ä", "中", cp 0xE000, "Ａ", cp 0x1D400, cp 0x1F600]

/-! ## The timeouts of one process -/

/-- The `-t` value, the `-T` value and the watchdog of one process, from its budget in ms. -/
abbrev Budgets : Type := Nat → Nat × Nat × Nat

/-- **The reference formula**: `-t` is the budget, `-T` the budget plus one second rounded up to
whole seconds, the watchdog the budget plus two seconds. -/
def refBudgets : Budgets := fun t => (t, (t + 1000 + 999) / 1000, t + 2000)

/-- The `-T` value rounded down instead of up. -/
def floorBudgets : Budgets := fun t => (t, (t + 1000) / 1000, t + 2000)

/-- The budget a process gets: from its normal budget and, when a total budget is set, the whole
milliseconds that remain; `none` when no process may start. -/
abbrev Clamp : Type := Nat → Option Nat → Option Nat

/-- **The reference clamp** (`total_budget.rs` `clamp`): without a total budget the normal budget;
with one, nothing when no millisecond remains, else the smaller of the two. -/
def refClamp : Clamp
  | n, none => some n
  | n, some r => if r = 0 then none else some (min n r)

/-! ## Reply classification -/

/-- **A raw reply**: the stdout and stderr lines, each trimmed, and whether the watchdog killed
the process. -/
structure RawReply where
  /-- The stdout lines, trimmed. -/
  out : List String
  /-- The stderr lines, trimmed. -/
  err : List String
  /-- The watchdog killed the process. -/
  killed : Bool := false

/-- The verdict a trimmed line spells, if any. -/
def answerOf (l : String) : Option Verifier.SolverAnswer :=
  if l = "sat" then some .sat else if l = "unsat" then some .unsat
  else if l = "unknown" then some .unknown else none

/-- The first verdict line of a list of lines. -/
def firstAnswer (ls : List String) : Option Verifier.SolverAnswer := ls.findSome? answerOf

/-- An `(error …)` line: one that starts with `(error`. -/
def isErrorLine (l : String) : Bool := "(error".toList.isPrefixOf l.toList

/-- The first `(error …)` line of a list of lines. -/
def firstError (ls : List String) : Option String := ls.find? isErrorLine

/-- Some stderr line has text. -/
def hasText (ls : List String) : Bool := ls.any fun l => l != ""

/-- A classifier: a raw reply to a verdict line or a failure with its reason. -/
abbrev Classify : Type := RawReply → Verifier.SolverReply

/-- **The reference classifier**: the first verdict line wherever it appears; without one, the
`timeout` line of the `-T` backstop, then the watchdog kill, then the first `(error …)` line on
stdout and then on stderr, then any other stderr text, then the stdout itself. -/
def refClassify : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "z3 hard timeout"
    else if r.killed then .failure .killed "z3 did not exit and was killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none =>
        if hasText r.err then .failure .stderrText (String.intercalate "\n" r.err)
        else .failure .unexpected (String.intercalate "\n" r.out)

/-! ## The pipeline under a solver and a stop -/

/-- **A pipeline runner**: from the solver, the stop, the options, the query, the steps and a
trail, the decision (the route and what the deciding step returned) and the trail after it. -/
abbrev Runner (Q : Type) : Type :=
  Verifier.Oracle → Verifier.Stop → Verifier.Options → Q → List (Verifier.GStep Q) →
    Verifier.Trail → Option (Verifier.Route × Verifier.PhaseOut) × Verifier.Trail

/-- **A finisher**: the verdict a call returns, from the trail of its run and the verdict the run
reached. -/
abbrev Finisher : Type := Verifier.Trail → Verifier.Verdict → Verifier.Verdict

/-- The reason an `Unknown` gets: the stop's, when a stop is recorded. -/
def stopOrWhy (t : Verifier.Trail) (why : String) : String :=
  match t.stopped with
  | some (k, n) => Verifier.stopReason k n
  | none => why

end Ver013

open Ver013

#spec_witness refNameLt
#spec_witness refBudgets
#spec_witness refClamp
#spec_witness refClassify
#spec_witness Verifier.runPipeline
#spec_witness Verifier.finishVerdict

/-! ## VER-013 (F): the name order -/

requirement VER_013_order
  id "VER-013"
  title "Solver Transport: name order"
  kind F
  scope "every ordering of place or transition names that reaches a script, a flat index, a report, a witness or a violation list, all implementations"
  source verbatim "spec/07-verification.md"
  quote "Every ordering of place or transition names that reaches a script, a flat index, a report, a witness or a violation list MUST compare names by Unicode code point, never by host locale or UTF-16 code unit: the flat place index above, the canonical clock order of a state class ([VER-010]), and the markings and violation lists of an open-net report ([VER-022])."
  reading "For every name order lt and all names a and b: lt a b holds exactly when the code points of a are lexicographically smaller than those of b."
  assumes "Names are Lean strings, sequences of Unicode scalar values; codePoints reads them as numbers. Where the order is used (the flat place index of the scripts, the clock order of a state class of VER-010, the markings and violation lists of an open-net report of VER-022) is those requirements' and the encoders'; the block fixes the comparison. The runtimes: Rust compares str, which is code-point order; Java and TypeScript compare with a code-point comparator (TypeScript compareCodePoints, the ICU fix-up on the first differing UTF-16 unit pair). A UTF-16 code-unit order, JavaScript's < and Java's String.compareTo, is killed (VER_013_order_forbids_utf16): it puts U+1D400 before U+E000."
          "AC7 (the names \"\", Z, a, ab, Ä, 中, U+E000, Ａ, U+1D400 and U+1F600 sort in exactly that order, and a UTF-16 sort puts U+1D400 and U+1F600 before U+E000) is the line, checked on that vector (VER_013_order_nonvacuous). AC1 (byte-identical HORN and certificate scripts in every implementation, the goldens under spec/verification-fixtures/scripts/) and the Script determinism paragraph are kind Q: they are checked by the script-parity tests of every language against the goldens Rust writes, and the order of places in a script is this line."
  signoff "pending"
  statement : NameLt → Prop :=
    fun lt => ∀ a b, lt a b = true ↔ codePoints a < codePoints b

/-- ✓ **The reference compares code points.** Example: `"ab"` comes before `"b"` because `a`
(97) is below `b` (98), and U+E000 comes before U+1D400 because 57344 is below 119808. -/
@[evidence holds VER_013_order]
theorem VER_013_order_reference : VER_013_order refNameLt := by
  intro a b
  simp [refNameLt]

/-- ✓ **The AC7 vector is in code-point order.** Example: `""`, `Z`, `a`, `ab`, `Ä`, `中`,
U+E000, `Ａ`, U+1D400 and U+1F600: each comes before every later one. -/
@[evidence nonvacuous VER_013_order]
theorem VER_013_order_nonvacuous :
    ac7.Pairwise (fun a b => refNameLt a b = true) := by
  decide

/-- ✗ **A UTF-16 code-unit order is not code-point order.** Example: U+1D400 is the surrogate
pair D835 DC00 in UTF-16, which sorts before U+E000; by code point U+1D400 (119808) comes after
U+E000 (57344). -/
@[evidence forbids VER_013_order]
theorem VER_013_order_forbids_utf16 : ¬ VER_013_order utf16NameLt := by
  intro h
  have h1 : utf16NameLt (cp 0x1D400) (cp 0xE000) = true := by decide
  have h2 : ¬ codePoints (cp 0x1D400) < codePoints (cp 0xE000) := by decide
  exact h2 ((h _ _).mp h1)

/-! ## VER-013 (F): the timeouts of one process -/

requirement VER_013_args
  id "VER-013"
  title "Solver Transport: timeouts of one process"
  kind F
  scope "every z3 process the verifier starts, all implementations"
  source verbatim "spec/07-verification.md"
  quote "*When* the verifier starts a `z3` process with a timeout of `t` milliseconds, `t` at least 1, it *shall* pass `-t:t` and, as `-T`, the smallest whole number of seconds that is at least `(t + 1000) / 1000`, and *shall* kill the process at `t + 2000` milliseconds if it has not exited."
        "*While* a total budget is set, the verifier *shall* give each `z3` process the smaller of its normal timeout and the whole milliseconds that remain, and *shall* start no process when none remain."
  reading "For every timeout formula B and clamp Cl, and every budget t of at least 1 millisecond: the -t value of B t is t;"
          "the -T value of B t is the smallest number of seconds whose milliseconds reach t + 1000;"
          "the watchdog of B t is t + 2000;"
          "and for every normal budget n: without a total budget, Cl gives n;"
          "with r milliseconds remaining and r at least 1, Cl gives the smaller of n and r;"
          "with no millisecond remaining, Cl starts no process."
  assumes "Ruling D90 (a): the formula is stated for a budget of at least 1 ms. At 0 the runtimes differ (Java and TypeScript raise the budget to 1 ms, Z3Solver.java timeoutMs and z3-process.ts timeoutBudget, so that -t:0, no limit to z3, never reaches the solver; Rust passes -t:0, z3_process.rs args_for), and the markdown says so. The -T value is z3_process.rs hard_timeout_secs ((t + 1000) rounded up to seconds, at least 1, which at t >= 1 is never the floor), and the watchdog watchdog_ms; Java and TypeScript have the same functions. A -T rounded down is killed (VER_013_args_forbids_floor): at 1 ms it would give -T:1."
          "The clamp is total_budget.rs clamp: the remaining time is whole milliseconds rounded down, and a remainder of 0 (or a cancellation, which the model reads as nothing remaining) starts no process; the stop it records is VER_013_stop's. Every process passes this one choke point per implementation (Java Z3Solver.run, TypeScript runZ3Text, Rust Z3Solver::run), and the -t, -T and watchdog of the clamped budget are line 1 to 3 at that budget. A clamp that ignores the remaining time, one that starts a process with nothing left, and one that gives a budget without a total budget set are killed (VER_013_args_forbids_noClamp, VER_013_args_forbids_startAtZero, VER_013_args_forbids_clampUnset). The HORN query, the certificate script and its detail re-run each get the full per-call budget without a total budget: that is the normal budget n, set by the caller (kind N)."
          "The argument list (-smt2 -in, fp.engine=spacer for the HORN query), the single write of the script on stdin followed by end-of-file, the concurrent draining of both streams, the kill and reap on every exit path, the executable on PATH or LIBPETRI_Z3, the probe of --version against 4.8.0, and the LIBPETRI_SMT_DUMP file names are process handling, kind Q and N, as is AC6 (the report carries '  Solver: z3 <version>' in its solver phase, or '  Solver: z3 unavailable (<reason>)' followed by the UNKNOWN result line naming the same reason), which is report text; the runtimes' stub-solver tests (the stub_z3 tests of libpetri-verification) check them. AC9 (with a total budget of N ms, verify() returns within N ms plus one watchdog slack and one polling interval) is wall-clock time, kind Q; its reason text and 'no z3 process starts once the budget is spent' are VER_013_stop's lines 5 and 3 with line 6 here."
  signoff "pending"
  statement : Budgets → Clamp → Prop :=
    fun B Cl =>
      (∀ t, 1 ≤ t →
        (B t).1 = t ∧
        ((B t).2.1 * 1000 ≥ t + 1000 ∧ (B t).2.1 * 1000 < t + 2000) ∧
        (B t).2.2 = t + 2000) ∧
      (∀ n, Cl n none = some n) ∧
      (∀ n r, 1 ≤ r → Cl n (some r) = some (min n r)) ∧
      (∀ n, Cl n (some 0) = none)

/-- ✓ **The reference timeouts.** Example: a budget of 30 000 ms gives `-t:30000`, `-T:31` and a
watchdog at 32 000 ms; with a total budget and 200 ms left, a process whose normal budget is
30 000 ms gets 200 ms; with nothing left none starts. -/
@[evidence holds VER_013_args]
theorem VER_013_args_reference : VER_013_args refBudgets refClamp := by
  refine ⟨fun t _ => ⟨rfl, ⟨?_, ?_⟩, rfl⟩, fun _ => rfl, fun n r hr => ?_, fun _ => rfl⟩
  · show (t + 1000 + 999) / 1000 * 1000 ≥ t + 1000
    omega
  · show (t + 1000 + 999) / 1000 * 1000 < t + 2000
    omega
  · have : r ≠ 0 := by omega
    simp [refClamp, this]

/-- ✓ **The worked numbers.** Example: 30 000 ms gives `(30000, 31, 32000)`; 1 ms gives `-T:2`,
since 1001 ms round up to 2 s; 200 ms left clamp a normal 30 000 ms to 200 ms. -/
@[evidence nonvacuous VER_013_args]
theorem VER_013_args_nonvacuous :
    refBudgets 30000 = (30000, 31, 32000) ∧ (refBudgets 1).2.1 = 2 ∧
    refClamp 30000 (some 200) = some 200 ∧ refClamp 30000 (some 0) = none ∧
    refClamp 30000 none = some 30000 := by
  decide

/-- ✗ **`-T` rounds up.** Example: at a budget of 1 ms, rounding `1001 ms` down gives `-T:1`, a
backstop that can fire before the soft timeout's second of grace has passed. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_floor : ¬ VER_013_args floorBudgets refClamp := by
  intro h
  have := (h.1 1 (by omega)).2.1.1
  simp [floorBudgets] at this

/-- A clamp that ignores the remaining time. -/
def noClamp : Clamp := fun n r => match r with
  | some 0 => none
  | _ => some n

/-- ✗ **A total budget clamps the process.** Example: with 200 ms left, a process that still gets
its normal 30 000 ms can run far past the total budget. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_noClamp : ¬ VER_013_args refBudgets noClamp := by
  intro h
  have := h.2.2.1 30000 200 (by omega)
  revert this
  decide

/-- A clamp that starts a process with nothing left, at a budget of 0. -/
def startAtZero : Clamp := fun n r => match r with
  | none => some n
  | some r => some (min n r)

/-- ✗ **Nothing left, no process.** Example: with 0 ms left, a process at budget 0 would be passed
`-t:0`, which `z3` reads as no limit. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_startAtZero : ¬ VER_013_args refBudgets startAtZero := by
  intro h
  have := h.2.2.2 30000
  simp [startAtZero] at this

/-- A clamp that reads an unset total budget as no time at all. -/
def clampUnset : Clamp := fun n r => match r with
  | none => none
  | some r => if r = 0 then none else some (min n r)

/-- ✗ **Without a total budget, the normal budget.** Example: with no total budget set, a clamp
that starts no process would make every verification `Unknown`, against AC8. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_clampUnset : ¬ VER_013_args refBudgets clampUnset := by
  intro h
  have := h.2.1 30000
  simp [clampUnset] at this

/-! ## VER-013 (F): reply classification -/

requirement VER_013_classify
  id "VER-013"
  title "Solver Transport: reply classification"
  kind F
  scope "every z3 reply the verifier reads, all implementations"
  source verbatim "spec/07-verification.md"
  quote "The verifier *shall* read the verdict of a reply off the first stdout line that, trimmed, equals `sat`, `unsat` or `unknown`, wherever that line appears."
        "*If* no stdout line of a reply is a verdict line, *then* the verifier *shall* give as the reason of the failure the first of these that applies: a `timeout` line on stdout, the watchdog kill, the first `(error …)` line on stdout and then on stderr, any other stderr text, the stdout itself."
        "A verdict line decides whatever else the reply carries, an `(error …)` line or a non-zero exit included."
  reading "For every classifier C and raw reply r (trimmed stdout lines, trimmed stderr lines, whether the watchdog killed the process): if the first verdict line of r's stdout spells a, C r is the answer a;"
          "otherwise, if some stdout line is timeout, C r is a timeout-line failure;"
          "otherwise, if the watchdog killed the process, C r is a kill failure;"
          "otherwise, if some line of stdout and then stderr is an (error …) line, C r is an error-line failure whose reason is the first such line;"
          "otherwise, if some stderr line has text, C r is a stderr failure;"
          "otherwise C r is an unexpected-output failure."
  assumes "The raw reply holds the lines trimmed, as every runtime trims them (z3_process.rs classify_first_line, timeout_line, error_line; TypeScript smt-text.ts; Java SmtText), and the kill flag; the exit code is not read here, since a verdict line decides whatever the exit (ruling D90 (a): AC4 is reworded from this paragraph, and the markdown now says that a verdict line decides with an (error …) line or a non-zero exit beside it). The order is Rust failure_reason, Java Z3Process.failureReason and TypeScript failureReason, the same in all three; TypeScript checks a cancellation kill first, which is VER_013_stop's stop. The reason texts ('z3 hard timeout after <s>s', 'Z3 error: <line>', 'Unexpected Z3 output: <stdout>') are kind Q; the error line itself is the reason here, as it is the substance of Rust's text. Under the HORN query sat is Proven and unsat Violated: that is the fixpoint query's reading of the answer, the phase's (VER-001)."
          "A classifier that lets an (error …) line win over a verdict line, the literal reading of the old AC4, is killed (VER_013_classify_forbids_errorFirst): the HORN script's paired (get-proof) and (get-model) always yield one (error …) line beside the verdict. Killed for the failure order: one without the timeout line (VER_013_classify_forbids_noTimeout), one without the kill (VER_013_classify_forbids_noKill), one that reads stderr's error line before stdout's (VER_013_classify_forbids_stderrFirst), one that ignores other stderr text (VER_013_classify_forbids_noStderr) and one that reports empty stderr as stderr text (VER_013_classify_forbids_stderrAlways)."
          "AC4 (a reply without a verdict line yields Unknown with a distinct reason per cause, a verdict line decides even with an (error …) line or a non-zero exit) is lines 1 to 6, with the Unknown itself VER_013_stop's line 1: a failure is no answer. 'No solver process is left behind' is process handling, kind Q. AC5 (a banner of arbitrary size before the verdict line, on either stream) is line 1: the banner lines are not verdict lines, and stderr is not read when a verdict line is there (VER_013_classify_nonvacuous). The certificate check's own reading (exactly three positional answers; an (error …) line on either stream, a timeout line, a kill or a non-zero exit making it inconclusive) is the certificate check's; that an inconclusive check withholds Proven is the hand-over of VER-018 (ver018_refWrap_aside: a proof whose check did not pass steps aside)."
  signoff "pending"
  statement : Classify → Prop :=
    fun C => ∀ r : RawReply,
      (∀ a, firstAnswer r.out = some a → C r = .answer a) ∧
      (firstAnswer r.out = none → "timeout" ∈ r.out → ∃ why, C r = .failure .timeoutLine why) ∧
      (firstAnswer r.out = none → "timeout" ∉ r.out → r.killed = true →
        ∃ why, C r = .failure .killed why) ∧
      (firstAnswer r.out = none → "timeout" ∉ r.out → r.killed = false →
        ∀ e, firstError (r.out ++ r.err) = some e → C r = .failure .errorLine e) ∧
      (firstAnswer r.out = none → "timeout" ∉ r.out → r.killed = false →
        firstError (r.out ++ r.err) = none → hasText r.err = true →
        ∃ why, C r = .failure .stderrText why) ∧
      (firstAnswer r.out = none → "timeout" ∉ r.out → r.killed = false →
        firstError (r.out ++ r.err) = none → hasText r.err = false →
        ∃ why, C r = .failure .unexpected why)

/-- ✓ **The reference classifier.** Example: a reply whose stdout is a warning, then `unsat`,
then `(error "proof is not available")` is `unsat`; a reply with only `timeout` on stdout is the
`-T` backstop; a killed process with nothing printed is the watchdog kill. -/
@[evidence holds VER_013_classify]
theorem VER_013_classify_reference : VER_013_classify refClassify := by
  intro r
  refine ⟨fun a ha => by simp [refClassify, ha], fun h1 h2 => ?_, fun h1 h2 h3 => ?_,
    fun h1 h2 h3 e he => ?_, fun h1 h2 h3 h4 h5 => ?_, fun h1 h2 h3 h4 h5 => ?_⟩
  · exact ⟨"z3 hard timeout", by simp [refClassify, h1, h2]⟩
  · exact ⟨"z3 did not exit and was killed", by simp [refClassify, h1, h2, h3]⟩
  · simp [refClassify, h1, h2, h3, he]
  · exact ⟨String.intercalate "\n" r.err, by simp [refClassify, h1, h2, h3, h4, h5]⟩
  · exact ⟨String.intercalate "\n" r.out, by simp [refClassify, h1, h2, h3, h4, h5]⟩

/-- ✓ **Banners and error lines around the verdict.** Example: stdout `WARNING: banner`,
`unsat`, `(error "proof is not available")` with stderr `noise` reads `unsat` (AC5: the banner and
the stderr text do not matter once a verdict line is there); stdout `(error "x")` with nothing else
is an error-line failure naming that line; stdout `garbage` alone is unexpected output. -/
@[evidence nonvacuous VER_013_classify]
theorem VER_013_classify_nonvacuous :
    refClassify ⟨["WARNING: banner", "unsat", "(error \"proof is not available\")"], ["noise"],
      false⟩ = .answer .unsat ∧
    refClassify ⟨["(error \"x\")"], [], false⟩ = .failure .errorLine "(error \"x\")" ∧
    (∃ why, refClassify ⟨["garbage"], [], false⟩ = .failure .unexpected why) ∧
    (∃ why, refClassify ⟨["timeout"], [], true⟩ = .failure .timeoutLine why) := by
  refine ⟨by decide, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- An error line wins over a verdict line: the literal reading of the old AC4. -/
def errorFirst : Classify := fun r =>
  match firstError (r.out ++ r.err) with
  | some e => .failure .errorLine e
  | none => refClassify r

/-- ✗ **A verdict line wins over an error line.** Example: the HORN query's reply `sat`, then
`(error "model is not available")` from the paired `(get-model)`, is `sat`; reading it as an
error would turn every proof into `Unknown`. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_errorFirst : ¬ VER_013_classify errorFirst := by
  intro h
  have := (h ⟨["sat", "(error \"model is not available\")"], [], false⟩).1 .sat (by decide)
  revert this
  decide

/-- No timeout line: the backstop's `timeout` read as unexpected output. -/
def noTimeout : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if r.killed then .failure .killed "killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none => if hasText r.err then .failure .stderrText "stderr" else .failure .unexpected "out"

/-- ✗ **The `-T` backstop is named.** Example: stdout `timeout` alone is the hard timeout, not
unexpected output. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_noTimeout : ¬ VER_013_classify noTimeout := by
  intro h
  obtain ⟨why, hw⟩ := (h ⟨["timeout"], [], false⟩).2.1 (by decide) (by decide)
  have hm : noTimeout ⟨["timeout"], [], false⟩ = .failure .unexpected "out" := by decide
  rw [hm] at hw
  cases hw

/-- No kill: the watchdog's kill read as unexpected output. -/
def noKill : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "timeout"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none => if hasText r.err then .failure .stderrText "stderr" else .failure .unexpected "out"

/-- ✗ **The watchdog kill is named.** Example: a process killed with nothing printed is a kill,
not unexpected (empty) output. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_noKill : ¬ VER_013_classify noKill := by
  intro h
  obtain ⟨why, hw⟩ := (h ⟨[], [], true⟩).2.2.1 (by decide) (by decide) rfl
  have hm : noKill ⟨[], [], true⟩ = .failure .unexpected "out" := by decide
  rw [hm] at hw
  cases hw

/-- The error line of stderr read before the one of stdout. -/
def stderrFirst : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "timeout"
    else if r.killed then .failure .killed "killed"
    else match firstError (r.err ++ r.out) with
      | some e => .failure .errorLine e
      | none => if hasText r.err then .failure .stderrText "stderr" else .failure .unexpected "out"

/-- ✗ **Stdout's error line first.** Example: `(error "a")` on stdout and `(error "b")` on stderr
give the reason `(error "a")`. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_stderrFirst : ¬ VER_013_classify stderrFirst := by
  intro h
  have := (h ⟨["(error \"a\")"], ["(error \"b\")"], false⟩).2.2.2.1 (by decide) (by decide) rfl
    "(error \"a\")" (by decide)
  revert this
  decide

/-- Other stderr text ignored. -/
def noStderr : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "timeout"
    else if r.killed then .failure .killed "killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none => .failure .unexpected "out"

/-- ✗ **Stderr text is the reason.** Example: a crash that prints `Segmentation fault` on stderr
and nothing on stdout is reported with that text, not as unexpected output. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_noStderr : ¬ VER_013_classify noStderr := by
  intro h
  obtain ⟨why, hw⟩ := (h ⟨[], ["Segmentation fault"], false⟩).2.2.2.2.1 (by decide) (by decide)
    rfl (by decide) (by decide)
  have hm : noStderr ⟨[], ["Segmentation fault"], false⟩ = .failure .unexpected "out" := by decide
  rw [hm] at hw
  cases hw

/-- Empty stderr reported as stderr text. -/
def stderrAlways : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "timeout"
    else if r.killed then .failure .killed "killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none => .failure .stderrText "stderr"

/-- ✗ **Without stderr text, the stdout itself.** Example: stdout `garbage` with an empty stderr is
unexpected output naming `garbage`, not a stderr failure with nothing to show. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_stderrAlways : ¬ VER_013_classify stderrAlways := by
  intro h
  obtain ⟨why, hw⟩ := (h ⟨["garbage"], [], false⟩).2.2.2.2.2 (by decide) (by decide) rfl
    (by decide) (by decide)
  have hm : stderrAlways ⟨["garbage"], [], false⟩ = .failure .stderrText "stderr" := by decide
  rw [hm] at hw
  cases hw

/-! ## VER-013 (B): the pipeline under a solver and a stop -/

requirement VER_013_stop
  id "VER-013"
  title "Solver Transport: solver failures, total budget and cancellation"
  kind B
  scope "the verifier pipeline of every implementation that offers a total budget or cancellation (SHOULD), and every solver call"
  source verbatim "spec/07-verification.md"
  quote "*If* a `z3` process gives no verdict line, or no process is started, *then* the step that asked for it *shall* read the failure as no answer, so a step that proves a property only on a solver answer *shall not* return `Proven` from it."
        "*When* the poll made on entering a step finds the total budget spent or the call cancelled, the verifier *shall* charge the stop to the step that was running before, *shall* not enter the new step, and *shall* end the pipeline without a verdict."
        "*While* a stop is recorded, the verifier *shall* start no `z3` process, enter no step and reach no verdict."
        "*When* a stop is recorded, the verifier *shall* keep a `Proven` or `Violated` reached before it, and *shall* give an `Unknown` the reason `total verification budget of <N> ms exhausted during <phase>` or `verification cancelled during <phase>`, `<phase>` the step the stop was charged to."
        "*While* no total budget is set and the caller does not cancel, the verifier *shall* record no stop."
  reading "For every runner RP and finisher Fin, every solver O, stop, options o, query q, step list and trail t:"
          "if RP decides with route r and outcome out, some applicable step of the list has route r, out is not an aside, and the step's program can return out when every solver call gets O's reply or a refusal to start;"
          "if t records no stop, step s applies and the stop answers k at t's poll count, then RP on s followed by any steps decides nothing, records the stop k charged to t's running step, and enters no step;"
          "if t records a stop x, RP decides nothing, keeps x and starts no script;"
          "Fin keeps every verdict that is not Unknown;"
          "Fin gives an Unknown the stop's reason when t records a stop, and keeps its reason otherwise;"
          "with no stop at all, RP from a trail without a stop records none."
  assumes "The model is Spec/Verifier/Pipeline.lean: a solver is a pure function from scripts to replies (Oracle; no solver state survives a query), a reply is a verdict line or a failure with a reason (the classification is VER_013_classify), a phase is a program that asks the solver and polls the stop (PhaseProg), a stop is what the i-th poll sees (Stop: the total budget or a cancellation, which share one stop), and the trail records the polls, the running step, the first stop with the step it was charged to, the steps entered and the scripts started. RP and Fin are abstract; the witness is runPipeline and finishVerdict, and the decider pipeVerify (entry poll, unresolved place, verified net, runPipeline, finishVerdict through packResult) meets VER-003 under every solver and every stop (pipeVerify_VER_003)."
          "Line 1 is 'a solver crash is a verdict, never a crashed host' and the first quoted sentence: a decision is what the deciding step's program returns for the replies it got, a failure being a failure and never an answer. A step that proves only on an answer therefore proves nothing from a failing solver (VER_013_stop_failing; demoQuery_failing is the shape). A runner that reads every call as sat is killed (VER_013_stop_forbids_ignoreSolver). 'Never an escaping exception' is the totality of the functions, which no line states. AC2 (a missing executable) and AC3 (a version below 4.8.0, or none reported) are failures of this kind, missing and tooOld, and give Unknown by line 1; the reason naming the command and LIBPETRI_Z3, or both versions, is report text, kind Q."
          "Line 2 is the entry poll (Rust's step! and total_budget::step, Java SmtVerifier.enter, TypeScript this.enter): the poll is made before the new step is recorded, so the stop is charged to the step that just ended. A runner that records the new step first is killed (VER_013_stop_forbids_blameNext); demo_blame shows the three cases on a two-step pipeline. A stop seen at a poll inside a step (a graph build, a long loop, before or after a solver call, Rust note_if_expired) is charged to that step, the running one; that is the poll of Pipeline.lean (pollStop), and execProg_after_stop shows that no process starts after it inside the step."
          "Line 3 is 'When nothing remains, no process is started' and 'A cancelled call starts no further process', read on the trail: from a stopped trail nothing is entered, decided or started (runPipeline_after_stop). A runner that forgets a recorded stop is killed (VER_013_stop_forbids_forget). The clamp before each process is VER_013_args. 'A verdict reached before the deadline stands' and 'whichever stop comes first names the reason' are lines 4 and 5 with the stickiness of the first stop (runPipeline_keeps). A finisher that lets a stop overwrite a Proven and one that keeps the inner reason are killed (VER_013_stop_forbids_overwrite, VER_013_stop_forbids_innerReason)."
          "Line 6 with line 5 is AC8 (with no total budget set, verdicts, reports and solver arguments are those of the requirement without it): no stop is recorded, so Fin keeps every verdict, and the reference pipeline without a stop is refVerify (pipeVerify_noStop, cited by ver013_ac8). A runner that records a stop on its own is killed (VER_013_stop_forbids_selfStop). The total budget being off by default, and the per-language mechanism (TypeScript AbortSignal, Rust and Python CancelToken, Java thread interruption with the interrupt flag set again when verify() returns), are kind N."
          "AC9 (verify() returns within N ms plus one watchdog slack and one polling interval; the exhaustion reason; no process once the budget is spent) is wall-clock time, kind Q, for its bound, and lines 3 and 5 for the rest. AC10 and AC12 (a build stopped by the total budget or by cancellation leaves a state-space cache as it found it, and stops at its next poll) are VER-017's: the cache block keeps the entry after a stopped build (VER_017_cache, VER_017_forbids_storeStopped) and the route reads nothing off a stopped build (VER_017, line 9); Route B's build is VER_012_build. AC11 (a running process is killed at once on cancellation and the call returns long before its timeout; a call cancelled before it starts returns the same Unknown without a process; Java's interrupt flag) is process handling, kind Q, for the kill and the time, line 3 for no further process, and the entry poll of pipeVerify for a call cancelled before it starts (demo_ac11: verification cancelled during net preparation). The total budget's start before the terminal rewrite, the solver-free loops that poll, the colour-slot bound as its own step and the HORN query's share are the pipeline's structure (rtStepNames, the order lines of VER-015, VER-018, VER-019 and NU-053); SubnetDef.verify (MOD-051) and open-net verification (VER-022) reaching the budget only per query is kind N."
          "Ruling D22 (a): VER-013 is SHOULD, and its shall sentences bind an implementation that offers verification; the total budget and cancellation are each a SHOULD offer."
  signoff "pending"
  statement : ∀ {Q : Type}, Runner Q → Finisher → Prop :=
    fun RP Fin =>
      (∀ O stop o q steps t r out, (RP O stop o q steps t).1 = some (r, out) →
        ∃ s ∈ steps, s.route = r ∧ s.applies o q = true ∧ Yields (byOracle O) (s.run o q) out ∧
          ∀ n, out ≠ .aside n) ∧
      (∀ O stop o q (s : GStep _) ss (t : Trail) k, t.stopped = none → s.applies o q = true →
        stop t.polls = some k →
        (RP O stop o q (s :: ss) t).1 = none ∧
        (RP O stop o q (s :: ss) t).2.stopped = some (k, t.running) ∧
        (RP O stop o q (s :: ss) t).2.entered = t.entered) ∧
      (∀ O stop o q steps (t : Trail) x, t.stopped = some x →
        (RP O stop o q steps t).1 = none ∧ (RP O stop o q steps t).2.stopped = some x ∧
        (RP O stop o q steps t).2.started = t.started) ∧
      (∀ t v, (∀ why, v ≠ .unknown why) → Fin t v = v) ∧
      (∀ t why, Fin t (.unknown why) = .unknown (stopOrWhy t why)) ∧
      (∀ O o q steps (t : Trail), t.stopped = none → (RP O noStop o q steps t).2.stopped = none)

namespace Ver013

open Verifier

variable {Q : Type}

/-- A program run without a stop records none. -/
theorem execProg_noStop {α : Type} {O : Oracle} : ∀ (P : PhaseProg α) (t : Trail),
    t.stopped = none → (execProg O noStop P t).2.stopped = none
  | .done _, _, h => h
  | .ask s k, t, h => by
    simp only [execProg, pollStop_noStop h, Bool.false_eq_true, if_false]
    apply execProg_noStop
    have h1 : ({ (({ t with polls := t.polls + 1 } : Trail)) with
        started := t.started ++ [s] } : Trail).stopped = none := h
    rw [pollStop_noStop h1]
    exact h
  | .poll k, t, h => by
    simp only [execProg, pollStop_noStop h]
    exact execProg_noStop _ _ h

/-- A pipeline run without a stop records none. -/
theorem runPipeline_noStop' {O : Oracle} {o : Options} {q : Q} : ∀ (steps : List (GStep Q))
    (t : Trail), t.stopped = none → (runPipeline O noStop o q steps t).2.stopped = none
  | [], _, h => h
  | s :: ss, t, h => by
    simp only [runPipeline, pollStop_noStop h, Bool.false_eq_true, if_false]
    split
    · have he : (({ t with polls := t.polls + 1 } : Trail).enter s).stopped = none := h
      have hx := execProg_noStop (O := O) (s.run o q) _ he
      split
      · rename_i n t' hrun
        rw [hrun] at hx
        exact runPipeline_noStop' ss t' hx
      · rename_i v tr c t' hrun
        rw [hrun] at hx
        exact hx
    · exact runPipeline_noStop' ss t h

end Ver013

/-- ✓ **The reference pipeline meets VER-013's stop lines.** Example: on the pipeline `linear
bound` (which steps aside) then `IC3/PDR query`, a cancellation seen on entering the query is
charged to `linear bound`, the query is not entered and no `z3` process starts; a 100 ms budget
spent just before the query's process refuses the process, and the query's `Unknown` becomes
`total verification budget of 100 ms exhausted during IC3/PDR query`; a `sat` reached before a
cancellation stays `Proven`. -/
@[evidence holds VER_013_stop]
theorem VER_013_stop_reference {Q : Type} :
    VER_013_stop (Q := Q) Verifier.runPipeline Verifier.finishVerdict := by
  refine ⟨fun O stop o q steps t r out h => Verifier.runPipeline_step h, ?_,
    fun O stop o q steps t x h => Verifier.runPipeline_after_stop steps t h, ?_, ?_,
    fun O o q steps t h => Ver013.runPipeline_noStop' steps t h⟩
  · intro O stop o q s ss t k h0 ha hk
    have hp : Verifier.pollStop stop t =
        (true, { t with polls := t.polls + 1, stopped := some (k, t.running) }) := by
      simp [Verifier.pollStop, h0, hk]
    simp [Verifier.runPipeline, ha, hp]
  · intro t v hv
    cases v with
    | unknown why => exact absurd rfl (hv why)
    | proven m => rfl
    | violated => rfl
  · intro t why
    unfold Verifier.finishVerdict stopOrWhy
    cases t.stopped with
    | none => rfl
    | some x => obtain ⟨k, n⟩ := x; rfl

/-- ✓ **The stop lines on the demo pipeline.** Example: a cancellation from poll 1, seen on
entering `IC3/PDR query`, is charged to `linear bound`, and only `linear bound` was entered; a
budget of 100 ms spent from poll 2 starts no process, and the finished `Unknown` names
`IC3/PDR query`; a `Proven` reached before a cancellation at poll 3 stands. -/
@[evidence nonvacuous VER_013_stop]
theorem VER_013_stop_nonvacuous :
    (Verifier.runPipeline Verifier.satOracle (Verifier.stopFrom 1 .cancelled) {} ()
        Verifier.demoSteps {}).2.stopped = some (.cancelled, "linear bound") ∧
    (Verifier.runPipeline Verifier.satOracle (Verifier.stopFrom 1 .cancelled) {} ()
        Verifier.demoSteps {}).2.entered = ["linear bound"] ∧
    (Verifier.runPipeline Verifier.satOracle (Verifier.stopFrom 2 (.budget 100)) {} ()
        Verifier.demoSteps {}).2.started = [] ∧
    Verifier.finishVerdict (Verifier.runPipeline Verifier.satOracle
        (Verifier.stopFrom 2 (.budget 100)) {} () Verifier.demoSteps {}).2 (.unknown "refused") =
      .unknown "total verification budget of 100 ms exhausted during IC3/PDR query" ∧
    Verifier.finishVerdict (Verifier.runPipeline Verifier.satOracle
        (Verifier.stopFrom 3 .cancelled) {} () Verifier.demoSteps {}).2 (.proven "IC3/PDR") =
      .proven "IC3/PDR" := by
  decide

namespace Ver013

open Verifier

variable {Q : Type}

/-- More allowed replies, more possible returns. -/
theorem Yields.mono {α : Type} {R R' : String → SolverReply → Prop}
    (hR : ∀ s r, R s r → R' s r) : ∀ {P : PhaseProg α} {a : α}, Yields R P a → Yields R' P a
  | _, _, .done a => .done a
  | _, _, .ask hr hk => .ask (hR _ _ hr) (Yields.mono hR hk)
  | _, _, .poll b hk => .poll b (Yields.mono hR hk)

/-- A solver whose every reply is a failure. -/
def FailingOracle (O : Oracle) : Prop := ∀ s, ∃ f why, O s = .failure f why

/-- **A failing solver proves nothing**, for every runner that meets VER-013's stop lines:
when every step's program proves only on an answer (it never returns `Proven` while every
reply is a failure), no decision of the run is `Proven`. Example: the demo query decides
`Proven` on `sat` only, so under a solver that is never found it answers `Unknown`. -/
@[evidence cites "VER-013" "AC2"]
theorem VER_013_stop_failing {Q : Type} {RP : Runner Q} {Fin : Finisher}
    (h : VER_013_stop RP Fin) {O : Oracle} (hO : FailingOracle O) {stop : Stop} {o : Options}
    {q : Q} {steps : List (GStep Q)} {t : Trail}
    (hP : ∀ s ∈ steps, ∀ meth tr c, ¬ Yields failing (s.run o q) (.decided (.proven meth) tr c))
    {r : Route} {meth : String} {tr : List String} {c : Option Bool} :
    (RP O stop o q steps t).1 ≠ some (r, .decided (.proven meth) tr c) := by
  intro hd
  obtain ⟨s, hs, -, -, hy, -⟩ := h.1 O stop o q steps t r _ hd
  refine hP s hs meth tr c (Yields.mono ?_ hy)
  rintro s' r' (rfl | ⟨why, rfl⟩)
  · exact hO s'
  · exact ⟨_, _, rfl⟩

/-- **With no stop, the reference pipeline is the verifier without one** ([VER-013] AC8).
Example: on the AC11 net `p0 → t → p1`, `DeadlockFree([p1])` from `{p0: 1}` is `Violated` with
the empty trace, whatever the solver, exactly as `refVerify` answers. -/
@[evidence cites "VER-013" "AC8"]
theorem ver013_ac8 {K : Type} [LinearOrder K] [Hashable K] (abs : Abs K) (O : Oracle) :
    pipeVerify abs inertInvariants rtPipeline O noStop = refVerify abs :=
  pipeVerify_noStop abs O

/-- A runner that answers every solver call with `sat`, whatever the solver says. -/
def ignoreSolver : Runner Q := fun _ stop o q steps t => runPipeline satOracle stop o q steps t

/-- A solver that is never found. -/
def missingOracle : Oracle := fun _ => .failure .missing "z3 binary not found"

/-- A runner that records the new step before its entry poll. -/
def blameNext : Runner Q := fun O stop o q steps t =>
  match steps with
  | [] => (none, t)
  | s :: ss => runPipeline O stop o q (s :: ss)
      (if s.applies o q then { t with running := s.name } else t)

/-- A runner that forgets a recorded stop. -/
def forgetStop : Runner Q := fun O stop o q steps t =>
  runPipeline O stop o q steps { t with stopped := none }

/-- A runner that records a 0 ms budget at its first poll on its own. -/
def selfStop : Runner Q := fun O stop o q steps t =>
  runPipeline O (fun i => if i = 0 then some (.budget 0) else stop i) o q steps t

/-- A finisher that lets a stop overwrite every verdict. -/
def overwrite : Finisher := fun t v =>
  match t.stopped with
  | some (k, n) => .unknown (stopReason k n)
  | none => v

/-- A finisher that keeps the inner reason of an `Unknown`. -/
def innerReason : Finisher := fun _ v => v

/-- The query step of the demo pipeline. -/
def queryStep : GStep Unit := { name := "IC3/PDR query", route := .smt, run := fun _ _ => demoQuery "horn" }

end Ver013

open Verifier Ver013

/-- ✗ **A failure is no answer** (line 1). Example: with `z3` missing, a runner that reads the
query's reply as `sat` proves the property; the query proves only on `sat`, so no step of the
demo pipeline can return that `Proven` from a missing solver. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_ignoreSolver :
    ¬ VER_013_stop (Q := Unit) ignoreSolver finishVerdict := by
  intro h
  have hd : (ignoreSolver missingOracle noStop {} () demoSteps {}).1 =
      some (.smt, .decided (.proven "IC3/PDR") [] none) := rfl
  obtain ⟨s, hs, -, -, hy, -⟩ := h.1 _ _ _ _ _ _ _ _ hd
  simp [Verifier.demoSteps] at hs
  rcases hs with rfl | rfl
  · have := Yields.done_iff.mp hy
    cases this
  · obtain ⟨why, hw, -⟩ := demoQuery_failing (Yields.mono (fun s' r' hr => by
      rcases hr with rfl | ⟨w, rfl⟩
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩) hy)
    cases hw

/-- ✗ **A stop found on entry blames the step that just ended** (line 2). Example: a cancellation
seen on entering `IC3/PDR query` from the start of the run is charged to `net preparation`, the
step that was running; a runner that records the query first blames the query. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_blameNext :
    ¬ VER_013_stop (Q := Unit) blameNext finishVerdict := by
  intro h
  have := (h.2.1 satOracle (stopFrom 0 .cancelled) {} () queryStep [] {} .cancelled rfl rfl
    rfl).2.1
  revert this
  decide

/-- ✗ **Nothing starts after a stop** (line 3). Example: from a trail that already records a
cancellation, a runner that forgets it enters the query and starts its `z3` process. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_forget :
    ¬ VER_013_stop (Q := Unit) forgetStop finishVerdict := by
  intro h
  have := (h.2.2.1 satOracle noStop {} () [queryStep]
    { stopped := some (.cancelled, "linear bound") } (.cancelled, "linear bound") rfl).2.2
  revert this
  decide

/-- ✗ **A verdict reached before the stop stands** (line 4). Example: the query answered `sat`
and was then cancelled; a finisher that turns the `Proven` into `verification cancelled during
IC3/PDR query` throws a finished proof away. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_overwrite :
    ¬ VER_013_stop (Q := Unit) runPipeline overwrite := by
  intro h
  have := h.2.2.2.1 { stopped := some (.cancelled, "IC3/PDR query") } (.proven "IC3/PDR")
    (fun _ hv => by cases hv)
  revert this
  decide

/-- ✗ **An Unknown after a stop names the stop** (line 5). Example: a query refused because the
100 ms budget was spent must say `total verification budget of 100 ms exhausted during IC3/PDR
query`, not its own `z3 not started`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_innerReason :
    ¬ VER_013_stop (Q := Unit) runPipeline innerReason := by
  intro h
  have := h.2.2.2.2.1 { stopped := some (.budget 100, "IC3/PDR query") } "z3 not started"
  revert this
  decide

/-- ✗ **No budget, no stop** (line 6). Example: with no total budget and no cancellation, a runner
that records a 0 ms budget at its first poll stops the demo pipeline before it starts. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_selfStop :
    ¬ VER_013_stop (Q := Unit) selfStop finishVerdict := by
  intro h
  have := h.2.2.2.2.2 satOracle {} () demoSteps {} rfl
  revert this
  decide

/-- ✓ **The four transport blocks hold together.** Example: the code-point order, the reference
timeouts and clamp, the reference classifier and the reference pipeline with its finisher. -/
@[evidence consistent VER_013_order VER_013_args VER_013_classify VER_013_stop]
theorem VER_013_joint {Q : Type} :
    ∃ (lt : NameLt) (B : Budgets) (Cl : Clamp) (C : Classify) (RP : Runner Q) (Fin : Finisher),
      VER_013_order lt ∧ VER_013_args B Cl ∧ VER_013_classify C ∧ VER_013_stop RP Fin :=
  ⟨refNameLt, refBudgets, refClamp, refClassify, runPipeline, finishVerdict,
    VER_013_order_reference, VER_013_args_reference, VER_013_classify_reference,
    VER_013_stop_reference⟩

end Libpetri.Spec
