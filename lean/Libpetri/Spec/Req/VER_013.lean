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
  finisher `Fin`, stated step by step so that it binds at every point of a run: the run ends
  after its last step; a step whose guard fails is skipped; a stop found on entering a step is
  charged to the step that was running and ends the run, nothing entered and nothing started; a
  step let in is entered and its program runs with every solver call polling first, a stopped
  call starting no process, and an aside goes on with the remaining steps; a `Proven` or
  `Violated` stands and an `Unknown` takes the stop's reason. The witness is `runPipeline` and
  `finishVerdict` of `Spec/Verifier/Pipeline.lean`; the lines accept no other runner
  (`VER_013_stop_runPipeline`).
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

/-- **A raw reply**: the stdout and stderr lines, each trimmed, whether the watchdog killed the
process, and the exit status it reported. -/
structure RawReply where
  /-- The stdout lines, trimmed. -/
  out : List String
  /-- The stderr lines, trimmed. -/
  err : List String
  /-- The watchdog killed the process. -/
  killed : Bool := false
  /-- The exit status the process reported; 0 is a clean exit. -/
  exit : Nat := 0

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
  signoff "2026-11-13 2f8d789291561f24 ai"
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
  assumes "Ruling D90 (a): the formula is stated for a budget of at least 1 ms. At 0 the runtimes differ (Java and TypeScript raise the budget to 1 ms, Z3Solver.java timeoutMs and z3-process.ts timeoutBudget, so that -t:0, no limit to z3, never reaches the solver; Rust passes -t:0, z3_process.rs args_for), and the markdown says so. The -T value is z3_process.rs hard_timeout_secs ((t + 1000) rounded up to seconds, at least 1, which at t >= 1 is never the floor), and the watchdog watchdog_ms; Java and TypeScript have the same functions. Killed: a -t passed in seconds (VER_013_args_forbids_seconds), a -T rounded down (VER_013_args_forbids_floor: at 1 ms it would give -T:1) and a watchdog at one second of grace instead of two (VER_013_args_forbids_oneGrace)."
          "The clamp is total_budget.rs clamp: the remaining time is whole milliseconds rounded down, and a remainder of 0 (or a cancellation, which the model reads as nothing remaining) starts no process; the stop it records is VER_013_stop's. Every process passes one choke point per implementation (Java Z3Solver.run, TypeScript runZ3Text, Rust Z3Solver::run), which clamps first and then derives -t, -T and the watchdog from the clamped value (Rust: clamp, then args_for and watchdog_ms of its result). Rust, TypeScript and Java start no process when no whole millisecond remains (Java's Z3Solver.run reads remainingMs() once and refuses at 0, and its polls read the same whole-millisecond clock). A clamp that raises the whole milliseconds left to at least 1, which starts a process at -t:1 with less than 1 ms left (the Java behaviour RD-42 recorded), gives min n (max 1 r) and is killed by line 6 (VER_013_args_forbids_javaSubMs). That the clamped value, not the normal one, is what lines 1 to 3 are applied to is kind Q, since B and Cl are separate functions here: the runtimes' AC9 stub tests (Rust stub_z3, a wedged solver under a per-call timeout of a minute and a total budget of 1.5 s, must return within 1.5 s plus the 2 s slack plus 1.5 s) fail when the watchdog keeps the unclamped budget. A clamp that ignores the remaining time, one that starts a process with nothing left, at a budget of 0 or of 1 ms, and one that gives a budget without a total budget set are killed (VER_013_args_forbids_noClamp, VER_013_args_forbids_startAtZero, VER_013_args_forbids_javaSubMs, VER_013_args_forbids_clampUnset). The HORN query, the certificate script and its detail re-run each get the full per-call budget without a total budget: that is the normal budget n, set by the caller (kind N)."
          "The argument list (-smt2 -in, fp.engine=spacer for the HORN query), the single write of the script on stdin followed by end-of-file, the concurrent draining of both streams, the kill and reap on every exit path, the executable on PATH or LIBPETRI_Z3, the probe of --version against 4.8.0, and the LIBPETRI_SMT_DUMP file names are process handling, kind Q and N, as is AC6 (the report carries '  Solver: z3 <version>' in its solver phase, or '  Solver: z3 unavailable (<reason>)' followed by the UNKNOWN result line naming the same reason), which is report text; the runtimes' stub-solver tests (the stub_z3 tests of libpetri-verification) check them. AC9 (with a total budget of N ms, verify() returns within N ms plus one watchdog slack and one polling interval) is wall-clock time, kind Q; its reason text and 'no z3 process starts once the budget is spent' are VER_013_stop's lines 5 and 3 with line 6 here."
  signoff "2026-11-13 8c4c5184fbd153a4 ai"
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

/-- `-t` passed in seconds, as `-T` is. -/
def secondsBudgets : Budgets := fun t => (t / 1000, (t + 1000 + 999) / 1000, t + 2000)

/-- ✗ **`-t` is in milliseconds.** Example: a budget of 30 000 ms passed as `-t:30` gives `z3`
30 ms, a thousandth of its budget. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_seconds : ¬ VER_013_args secondsBudgets refClamp := by
  intro h
  have := (h.1 30000 (by omega)).1
  revert this
  decide

/-- The watchdog at one second of grace, `t + 1000`: the `-T` backstop's second misread as the
watchdog's. -/
def oneGraceBudgets : Budgets := fun t => (t, (t + 1000 + 999) / 1000, t + 1000)

/-- ✗ **The watchdog waits two seconds past the budget.** Example: at 30 000 ms the `-T:31`
backstop fires at 31 000 ms at the earliest; a watchdog at 31 000 ms kills a solver that is about
to print `timeout`, which turns the hard timeout into a kill. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_oneGrace : ¬ VER_013_args oneGraceBudgets refClamp := by
  intro h
  have := (h.1 30000 (by omega)).2.2
  revert this
  decide

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

/-- A wrong clamp: the whole milliseconds left raised to at least 1, so a process starts when none
remain (the Java `Z3Solver.run` behaviour RD-42 recorded). -/
def javaSubMs : Clamp := fun n r => match r with
  | none => some n
  | some r => some (min n (max 1 r))

/-- ✗ **No whole millisecond left, no process, not even at 1 ms** (line 6; the behaviour RD-42
recorded). Example: with
0.4 ms of the total budget left, the whole milliseconds remaining are 0; a clamp that raises them
to 1 starts `z3` with `-t:1`, `-T:2` and a 2001 ms watchdog, past the spent budget. -/
@[evidence forbids VER_013_args]
theorem VER_013_args_forbids_javaSubMs : ¬ VER_013_args refBudgets javaSubMs := by
  intro h
  have := h.2.2.2 30000
  simp [javaSubMs] at this

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
  reading "For every classifier C and raw reply r (trimmed stdout lines, trimmed stderr lines, whether the watchdog killed the process, the exit status): if the first verdict line of r's stdout spells a, C r is the answer a, whatever the stderr lines, the kill flag and the exit status;"
          "otherwise, if some stdout line is timeout, C r is a timeout-line failure;"
          "otherwise, if the watchdog killed the process, C r is a kill failure;"
          "otherwise, if some line of stdout and then stderr is an (error …) line, C r is an error-line failure whose reason is the first such line;"
          "otherwise, if some stderr line has text, C r is a stderr failure whose reason is the stderr text (its trimmed lines joined by line breaks);"
          "otherwise C r is an unexpected-output failure whose reason is the stdout itself (its trimmed lines joined by line breaks)."
  assumes "The raw reply holds the lines trimmed, as every runtime trims them (z3_process.rs classify_first_line, timeout_line, error_line; TypeScript smt-text.ts; Java SmtText), the kill flag and the exit status. No line reads the exit status: line 1 holds whatever it is, which is 'a non-zero exit included' (ruling D90 (a): AC4 is reworded from this paragraph, and the markdown says that a verdict line decides with an (error …) line or a non-zero exit beside it), and lines 2 to 6 hold whatever it is, as in the runtimes, whose failure reason reads only the kill (Rust failure_reason, Java Z3Process.failureReason, TypeScript failureReason, the same order in all three); TypeScript checks a cancellation kill first, which is VER_013_stop's stop. The reasons' substance is stated: the error line (line 4), the stderr text (line 5) and the stdout (line 6), as in Rust's 'Z3 error: <line>', 'Z3 error: <trimmed stderr>' and 'Unexpected Z3 output: <trimmed stdout>'. The prefixes, and the timeout and kill texts ('z3 hard timeout after <s>s', 'z3 did not exit within <ms> ms and was killed', whose numbers are VER_013_args's), are kind Q. The runtimes trim the whole text where the model joins trimmed lines, which differs only in blanks inside the text. Under the HORN query sat is Proven and unsat Violated: that is the fixpoint query's reading of the answer, the phase's (VER-001)."
          "Killed for line 1: a classifier that lets an (error …) line win over a verdict line, the literal reading of the old AC4 (VER_013_classify_forbids_errorFirst: the HORN script's paired (get-proof) and (get-model) always yield one (error …) line beside the verdict); one that lets a non-zero exit win (VER_013_classify_forbids_exitFirst); one that reads only the first stdout line (VER_013_classify_forbids_firstLineOnly, a banner before the verdict); one that keeps the last verdict line (VER_013_classify_forbids_lastVerdict); and one that looks for the verdict on stderr too (VER_013_classify_forbids_readsStderr). Killed for the failure order: one without the timeout line (VER_013_classify_forbids_noTimeout), one without the kill (VER_013_classify_forbids_noKill), one that reads stderr's error line before stdout's (VER_013_classify_forbids_stderrFirst), one that ignores other stderr text (VER_013_classify_forbids_noStderr), one that reports empty stderr as stderr text (VER_013_classify_forbids_stderrAlways) and one that builds the last two reasons from the wrong stream (VER_013_classify_forbids_swappedStreams)."
          "AC4 (a reply without a verdict line yields Unknown with a distinct reason per cause, a verdict line decides even with an (error …) line or a non-zero exit) is lines 1 to 6, with the Unknown itself VER_013_stop's line 4: a failure reaches the step as a failure, never an answer. 'No solver process is left behind' is process handling, kind Q. AC5 (a banner of arbitrary size before the verdict line, on either stream) is line 1: the banner lines are not verdict lines, and stderr is not read when a verdict line is there (VER_013_classify_nonvacuous). The certificate sentence of the paragraph and the certificate half of AC4 (the certificate script requires exactly three positional answers; an (error …) on either stream, a timeout line, a kill or a non-zero exit makes the check inconclusive and withholds Proven) are kind Q: the runtimes' stub-solver tests check them (Rust stub_z3 scenario V6, an (error …) on stderr during the certificate check beside three clean answers, and V6 (exit status), a non-zero exit with unparseable answers; TypeScript stub-z3.test.ts and Java StubZ3Test the same), and that an inconclusive check withholds Proven is the hand-over of VER-018 (ver018_refWrap_aside: a proof whose check did not pass steps aside)."
  signoff "2026-11-13 f0d294ca752190df ai"
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
        C r = .failure .stderrText (String.intercalate "\n" r.err)) ∧
      (firstAnswer r.out = none → "timeout" ∉ r.out → r.killed = false →
        firstError (r.out ++ r.err) = none → hasText r.err = false →
        C r = .failure .unexpected (String.intercalate "\n" r.out))

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
  · simp [refClassify, h1, h2, h3, h4, h5]
  · simp [refClassify, h1, h2, h3, h4, h5]

/-- ✓ **Banners and error lines around the verdict.** Example: stdout `WARNING: banner`,
`unsat`, `(error "proof is not available")` with stderr `noise` and exit status 1 reads `unsat`
(AC5: the banner, the stderr text and the exit status do not matter once a verdict line is
there); stdout `(error "x")` with nothing else is an error-line failure naming that line; stdout
`garbage` alone is unexpected output naming `garbage`; `Segmentation fault` on stderr alone is a
stderr failure naming it. -/
@[evidence nonvacuous VER_013_classify]
theorem VER_013_classify_nonvacuous :
    refClassify ⟨["WARNING: banner", "unsat", "(error \"proof is not available\")"], ["noise"],
      false, 1⟩ = .answer .unsat ∧
    refClassify ⟨["(error \"x\")"], [], false, 1⟩ = .failure .errorLine "(error \"x\")" ∧
    refClassify ⟨["garbage"], [], false, 0⟩ = .failure .unexpected "garbage" ∧
    refClassify ⟨[], ["Segmentation fault"], false, 139⟩ =
      .failure .stderrText "Segmentation fault" ∧
    (∃ why, refClassify ⟨["timeout"], [], true, 0⟩ = .failure .timeoutLine why) := by
  refine ⟨by decide, by decide, by decide, by decide, ⟨_, rfl⟩⟩

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
  have := (h ⟨["sat", "(error \"model is not available\")"], [], false, 0⟩).1 .sat (by decide)
  revert this
  decide

/-- A non-zero exit wins over a verdict line. -/
def exitFirst : Classify := fun r =>
  if r.exit ≠ 0 then .failure .nonZeroExit "z3 exited with a non-zero status" else refClassify r

/-- ✗ **A verdict line wins over a non-zero exit.** Example: `z3` prints `sat` and then exits
with status 1 because the paired `(get-model)` failed; the reply is `sat`. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_exitFirst : ¬ VER_013_classify exitFirst := by
  intro h
  have := (h ⟨["sat", "(error \"model is not available\")"], [], false, 1⟩).1 .sat (by decide)
  revert this
  decide

/-- Only the first stdout line is read for the verdict. -/
def firstLineOnly : Classify := fun r =>
  match firstAnswer (r.out.take 1) with
  | some a => .answer a
  | none => .failure .unexpected (String.intercalate "\n" r.out)

/-- ✗ **The verdict line is found wherever it appears.** Example: a build that prints
`WARNING: banner` before `unsat` still answers `unsat` (AC5). -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_firstLineOnly : ¬ VER_013_classify firstLineOnly := by
  intro h
  have := (h ⟨["WARNING: banner", "unsat"], [], false, 0⟩).1 .unsat (by decide)
  revert this
  decide

/-- The last verdict line decides: a reader that overwrites the verdict as it scans. -/
def lastVerdict : Classify := fun r =>
  match firstAnswer r.out.reverse with
  | some a => .answer a
  | none => refClassify r

/-- ✗ **The first verdict line decides.** Example: stdout `unknown` then `sat` is `unknown`. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_lastVerdict : ¬ VER_013_classify lastVerdict := by
  intro h
  have := (h ⟨["unknown", "sat"], [], false, 0⟩).1 .unknown (by decide)
  revert this
  decide

/-- The verdict looked for on stdout and then stderr, as when a runtime merges the streams. -/
def readsStderr : Classify := fun r =>
  match firstAnswer (r.out ++ r.err) with
  | some a => .answer a
  | none => refClassify r

/-- ✗ **The verdict is read off stdout only.** Example: `sat` on stderr with nothing on stdout
is stderr text, not an answer. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_readsStderr : ¬ VER_013_classify readsStderr := by
  intro h
  have := (h ⟨[], ["sat"], false, 0⟩).2.2.2.2.1 (by decide) (by decide) rfl (by decide)
    (by decide)
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
  obtain ⟨why, hw⟩ := (h ⟨["timeout"], [], false, 0⟩).2.1 (by decide) (by decide)
  have hm : noTimeout ⟨["timeout"], [], false, 0⟩ = .failure .unexpected "out" := by decide
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
  obtain ⟨why, hw⟩ := (h ⟨[], [], true, 0⟩).2.2.1 (by decide) (by decide) rfl
  have hm : noKill ⟨[], [], true, 0⟩ = .failure .unexpected "out" := by decide
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
  have := (h ⟨["(error \"a\")"], ["(error \"b\")"], false, 0⟩).2.2.2.1 (by decide) (by decide) rfl
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
      | none => .failure .unexpected (String.intercalate "\n" r.out)

/-- ✗ **Stderr text is the reason.** Example: a crash that prints `Segmentation fault` on stderr
and nothing on stdout is reported with that text, not as unexpected output. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_noStderr : ¬ VER_013_classify noStderr := by
  intro h
  have := (h ⟨[], ["Segmentation fault"], false, 139⟩).2.2.2.2.1 (by decide) (by decide)
    rfl (by decide) (by decide)
  revert this
  decide

/-- Empty stderr reported as stderr text. -/
def stderrAlways : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "timeout"
    else if r.killed then .failure .killed "killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none => .failure .stderrText (String.intercalate "\n" r.err)

/-- ✗ **Without stderr text, the stdout itself.** Example: stdout `garbage` with an empty stderr is
unexpected output naming `garbage`, not a stderr failure with nothing to show. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_stderrAlways : ¬ VER_013_classify stderrAlways := by
  intro h
  have := (h ⟨["garbage"], [], false, 0⟩).2.2.2.2.2 (by decide) (by decide) rfl
    (by decide) (by decide)
  revert this
  decide

/-- The last two reasons built from the wrong stream. -/
def swappedStreams : Classify := fun r =>
  match firstAnswer r.out with
  | some a => .answer a
  | none =>
    if "timeout" ∈ r.out then .failure .timeoutLine "z3 hard timeout"
    else if r.killed then .failure .killed "z3 did not exit and was killed"
    else match firstError (r.out ++ r.err) with
      | some e => .failure .errorLine e
      | none =>
        if hasText r.err then .failure .stderrText (String.intercalate "\n" r.out)
        else .failure .unexpected (String.intercalate "\n" r.err)

/-- ✗ **The stderr text and the stdout are the reasons.** Example: stdout `garbage` alone must be
reported as `garbage`; a classifier that builds the reason from the empty stderr reports nothing. -/
@[evidence forbids VER_013_classify]
theorem VER_013_classify_forbids_swappedStreams : ¬ VER_013_classify swappedStreams := by
  intro h
  have := (h ⟨["garbage"], [], false, 0⟩).2.2.2.2.2 (by decide) (by decide) rfl
    (by decide) (by decide)
  revert this
  decide

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
  reading "For every runner RP and finisher Fin, every solver O, stop, options o, query q, first step s, remaining steps ss and trail t:"
          "with no step left, RP decides nothing and leaves t as it is;"
          "if s's guard fails, RP on s followed by ss is RP on ss: s is skipped and makes no poll;"
          "if s applies and the poll made on entering it finds a stop (one t records already, or the stop answering k at t's poll count), RP on s followed by ss decides nothing and leaves the trail that poll leaves: one more poll, a new stop recorded as k and charged to t's running step or the recorded one kept, no step entered and no script started;"
          "if s applies and that poll finds no stop, s is entered (it becomes the running step, with its route, and is logged) and its program runs under O and the stop: a solver call polls first, and when stopped starts no process and gets a refusal to start, otherwise starts its script, gets O's reply as it is and polls again; a poll inside the step charges a stop it is the first to find to s; when the program steps aside, RP goes on with RP on ss from the trail it left, and when it decides, RP ends with s's route and that decision;"
          "Fin keeps every verdict that is not Unknown;"
          "Fin gives an Unknown the stop's reason when t records a stop, and keeps its reason otherwise."
  assumes "The model is Spec/Verifier/Pipeline.lean: a solver is a pure function from scripts to replies (Oracle; no solver state survives a query), a reply is a verdict line or a failure with a reason (the classification is VER_013_classify), a phase is a program that asks the solver and polls the stop (PhaseProg), a stop is what the i-th poll sees (Stop: the total budget or a cancellation, which share one stop), the poll is pollStop (a recorded stop stays recorded; a new one is charged to the running step), a program runs as execProg, and the trail records the polls, the running step and its route, the first stop with the step it was charged to, the steps entered and the scripts started. RP and Fin are abstract, and the lines accept exactly one runner, runPipeline (VER_013_stop_runPipeline), and one finisher, finishVerdict; the decider pipeVerify (entry poll, unresolved place, verified net, runPipeline, finishVerdict through packResult) meets VER-003 under every solver and every stop (pipeVerify_VER_003)."
          "The lines are stated step by step so that every quoted sentence binds at every point of a run, not only on the trail RP is handed. Lines 1 and 2 are the pipeline's structure: it ends after its last step, and a step whose guard fails is not entered and makes no poll (Rust's step! sits inside the step's guard; the order lines of VER-015, VER-018, VER-019 and NU-053 fix the steps). Killed: a runner that starts one more process once the pipeline ends undecided, a detail re-run after the last step (VER_013_stop_forbids_trailingRun), and one that polls on a step whose guard fails (VER_013_stop_forbids_pollAlways)."
          "Line 4 carries the first quoted sentence and 'a solver crash is a verdict, never a crashed host': a solver call gets O's reply as it is, a failure staying a failure and never an answer, or, when stopped, a refusal to start. A step that proves only on an answer therefore proves nothing from a failing solver (VER_013_stop_failing, for every runner the lines accept; demoQuery_failing is the shape). Killed: a runner that reads every call as sat (VER_013_stop_forbids_ignoreSolver) and one that refuses every process with no stop recorded (VER_013_stop_forbids_refuseAll: with no budget and no cancellation every verification would be Unknown). 'Never an escaping exception' is the totality of the functions, which no line states. AC2 (a missing executable) and AC3 (a version below 4.8.0, or none reported) are failures of this kind, missing and tooOld, and give Unknown by line 4; the reason naming the command and LIBPETRI_Z3, or both versions, is report text, kind Q."
          "Line 3 is the second quoted sentence, the entry poll (Rust's step! and total_budget::step, Java SmtVerifier.enter, TypeScript this.enter): the poll is made before the new step is recorded, so the stop is charged to the step that just ended, and the run ends there with nothing entered and nothing started. demo_blame shows the three cases on a two-step pipeline. Killed: a runner that records the new step first (VER_013_stop_forbids_blameNext) and one that starts a process once the entry poll found the stop, a call path that skips the clamp (VER_013_stop_forbids_extraAfterStop)."
          "The third quoted sentence is lines 1 to 4 together. A stop recorded before RP starts is found by the first entry poll (line 3), so nothing is decided, entered or started and the stop is kept (VER_013_stop_after, for every runner the lines accept). A stop first found at a later entry poll ends the run there, since an aside goes on as RP on the remaining steps (line 4) and their first applicable step's entry poll finds it (line 3). A stop first found at a poll inside a step (a graph build, a long loop, the poll after a solver call: Rust note_if_expired, TypeScript's check() in the unknown case of the IC3/PDR query) is charged to that step, the running one, and every later solver call of the step polls first and is refused (line 4: Rust's clamp in Z3Solver::run, Java Z3Solver.run, TypeScript runZ3Text); the next entry poll then ends the run. Rust (Z3Solver::run, note_if_expired; the clamp records the stop) and Java (Z3Solver.run) poll inside the call after each reply and record the stop of a refused call; TypeScript polls in the caller, with check() after an unknown or inconclusive reply and after a failed certificate check, and at the next enter(), on the clock its clamp reads. Java polls after every reply, clamped or not, and charges an unanswered reply past the deadline to the running step (Z3Solver.run); an answered reply stands, and the next poll finds the stop and charges it to the step still running, since enter checks before it names the next step (VerificationDeadline.enter). TypeScript's polls read the same whole-millisecond clock as its clamp (Deadline.passed), so a call refused with less than 1 ms left meets a poll that records the stop. A runner without the poll after the reply, which keeps the solver's reason (the Java behaviour RD-43 recorded), is killed by line 4 (VER_013_stop_forbids_noPostPoll); so is a runner whose refusal records no stop, which keeps the refusal's own reason without the phase and enters the next step (the TypeScript behaviour RD-42 recorded; VER_013_stop_forbids_refuseUnrecorded). Killed: a runner that forgets a recorded stop (VER_013_stop_forbids_forget), one that still enters steps after it (VER_013_stop_forbids_enterAfterStop), one that honours only a stop found at its first entry poll (VER_013_stop_forbids_ignoreLater: cancelled at poll 1, it enters the query, starts its process and proves) and one whose solver calls skip the poll (VER_013_stop_forbids_askNoPoll). What a step returns after its own poll found the stop is what its program returns: that this is an aside or an Unknown, never a Proven or Violated read off stopped work, is each phase's, since its programs give up on a stopped poll and a refused call is a failure (VER-017 line 9 for a stopped build, VER_012_build for Route B), and the Unknown then takes the stop's reason by line 6. A Proven the solver answered before the poll that found the stop stands (line 5; demo_finish)."
          "Lines 5 and 6 are the fourth quoted sentence. 'A verdict reached before the deadline stands' is line 5, and 'whichever stop comes first names the reason' is line 6 with the stickiness of the first stop (pollStop keeps a recorded stop; runPipeline_keeps). Killed: a finisher that lets a stop overwrite a Proven (VER_013_stop_forbids_overwrite) and one that keeps the inner reason (VER_013_stop_forbids_innerReason)."
          "The fifth quoted sentence and AC8 (with no total budget set, verdicts, reports and solver arguments are those of the requirement without it) follow from line 4 for every runner the lines accept: with no stop no poll finds one, so a run from a trail without a stop records none and Fin keeps every verdict (VER_013_stop_noStop); the reference pipeline without a stop is refVerify (pipeVerify_noStop, cited by ver013_ac8). Killed: a runner that records a stop on its own (VER_013_stop_forbids_selfStop). The total budget being off by default, and the per-language mechanism (TypeScript AbortSignal, Rust and Python CancelToken, Java thread interruption with the interrupt flag set again when verify() returns), are kind N."
          "AC9 (verify() returns within N ms plus one watchdog slack and one polling interval; the exhaustion reason; no process once the budget is spent) is wall-clock time, kind Q, for its bound, and lines 3, 4 and 6 for the rest, which every runtime meets, in the last millisecond and after an unclamped call too (Java StubZ3Test totalBudget_spentDuringAnUnclampedCallIsChargedToThatStep_VER013 and totalBudget_noProcessStartsWithoutAWholeMillisecondLeft_VER013_AC9, Java TotalBudgetTest subMillisecondRemainderStopsAsTheClampDoes_VER013_AC9, TypeScript total-budget.test.ts 'VER-013 AC9: with less than one whole millisecond left the poll stops as the clamp refuses'). AC10 and AC12 (a build stopped by the total budget or by cancellation leaves a state-space cache as it found it, and stops at its next poll) are VER-017's: the cache block keeps the entry after a stopped build (VER_017_cache, VER_017_forbids_storeStopped) and the route reads nothing off a stopped build (VER_017, line 9); Route B's build is VER_012_build. AC11 (a running process is killed at once on cancellation and the call returns long before its timeout; a call cancelled before it starts returns the same Unknown without a process; Java's interrupt flag) is process handling, kind Q, for the kill and the time, line 4 for no further process, and the entry poll of pipeVerify for a call cancelled before it starts (demo_ac11: verification cancelled during net preparation). The total budget's start before the terminal rewrite, the solver-free loops that poll, the colour-slot bound as its own step and the HORN query's share are the pipeline's structure (rtStepNames, the order lines of VER-015, VER-018, VER-019 and NU-053). SubnetDef.verify (MOD-051) and open-net verification (VER-022) reaching the budget only per query is kind N. Their honouring cancellation, the termination-ranking queries open-net verification runs outside verify() included (a cancelled call starts no further query), is kind Q: Rust open_net tests a_cancelled_call_builds_no_graph and a_cancelled_call_leaves_every_smt_part_undecided, TypeScript cancellation.test.ts 'cancellation of open-net verification', Java CancellationTest openNet_anInterruptedThreadStopsBeforeTheGraph_andStartsNoQuery; SubnetDef.verify runs verify() with the caller's configuration (the configure hook, Python verify_subnet(cancel=...)), so its call is one under these lines (kind N)."
          "Ruling D22 (a): VER-013 is SHOULD, and its shall sentences bind an implementation that offers verification; the total budget and cancellation are each a SHOULD offer."
  signoff "2026-11-13 5ed0de3600183abc ai"
  statement : ∀ {Q : Type}, Runner Q → Finisher → Prop :=
    fun RP Fin =>
      (∀ O stop o q (t : Trail), RP O stop o q [] t = (none, t)) ∧
      (∀ O stop o q (s : GStep _) ss (t : Trail), s.applies o q = false →
        RP O stop o q (s :: ss) t = RP O stop o q ss t) ∧
      (∀ O stop o q (s : GStep _) ss (t : Trail), s.applies o q = true →
        (pollStop stop t).1 = true → RP O stop o q (s :: ss) t = (none, (pollStop stop t).2)) ∧
      (∀ O stop o q (s : GStep _) ss (t : Trail), s.applies o q = true →
        (pollStop stop t).1 = false →
        RP O stop o q (s :: ss) t =
          match execProg O stop (s.run o q) ((pollStop stop t).2.enter s) with
          | (.aside _, t') => RP O stop o q ss t'
          | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')) ∧
      (∀ t v, (∀ why, v ≠ .unknown why) → Fin t v = v) ∧
      (∀ t why, Fin t (.unknown why) = .unknown (stopOrWhy t why))

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

/-- After a stop the pipeline enters no step. -/
theorem runPipeline_stopped_entered {O : Oracle} {stop : Stop} {o : Options} {q : Q}
    {x : StopKind × String} : ∀ (steps : List (GStep Q)) (t : Trail),
    t.stopped = some x → (runPipeline O stop o q steps t).2.entered = t.entered
  | [], _, _ => rfl
  | s :: ss, t, h => by
    by_cases ha : s.applies o q = true
    · rw [runPipeline, if_pos ha, if_pos (pollStop_keeps (stop := stop) h).1]
      exact pollStop_frame.2.2.1
    · rw [runPipeline, if_neg ha]
      exact runPipeline_stopped_entered ss t h

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
  refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro O stop o q s ss t ha
    rw [Verifier.runPipeline, if_neg (by simp [ha])]
  · intro O stop o q s ss t ha hp
    rw [Verifier.runPipeline, if_pos ha, if_pos hp]
  · intro O stop o q s ss t ha hp
    rw [Verifier.runPipeline, if_pos ha, if_neg (by simp [hp])]
    generalize Verifier.execProg O stop (s.run o q) ((Verifier.pollStop stop t).2.enter s) = e
    obtain ⟨out, t'⟩ := e
    cases out <;> rfl
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
    (Verifier.runPipeline Verifier.satOracle (Verifier.stopFrom 1 .cancelled) {} ()
        Verifier.demoSteps {}).2.started = [] ∧
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

/-- **The stop lines accept one runner**: every runner that meets them is the reference pipeline,
on every solver, stop, options, query, step list and trail. -/
theorem VER_013_stop_runPipeline {RP : Runner Q} {Fin : Finisher} (h : VER_013_stop RP Fin)
    (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    ∀ (steps : List (GStep Q)) (t : Trail),
      RP O stop o q steps t = runPipeline O stop o q steps t
  | [], t => by rw [h.1]; rfl
  | s :: ss, t => by
    by_cases ha : s.applies o q = true
    · by_cases hp : (pollStop stop t).1 = true
      · rw [h.2.2.1 O stop o q s ss t ha hp, runPipeline, if_pos ha, if_pos hp]
      · have hp' : (pollStop stop t).1 = false := by simpa using hp
        rw [h.2.2.2.1 O stop o q s ss t ha hp', runPipeline, if_pos ha, if_neg hp]
        generalize execProg O stop (s.run o q) ((pollStop stop t).2.enter s) = e
        obtain ⟨out, t'⟩ := e
        cases out with
        | aside n => exact VER_013_stop_runPipeline h O stop o q ss t'
        | decided v tr c => rfl
    · have ha' : s.applies o q = false := by simpa using ha
      rw [h.2.1 O stop o q s ss t ha', runPipeline, if_neg ha]
      exact VER_013_stop_runPipeline h O stop o q ss t

/-- **While a stop is recorded, nothing is decided, entered or started**, for every runner that
meets the stop lines, and the stop is kept. Example: from a trail cancelled in `linear bound`,
the demo pipeline enters neither step and starts no `z3` process. -/
@[evidence cites "VER-013" "While a stop is recorded"]
theorem VER_013_stop_after {RP : Runner Q} {Fin : Finisher} (h : VER_013_stop RP Fin)
    {O : Oracle} {stop : Stop} {o : Options} {q : Q} {steps : List (GStep Q)} {t : Trail}
    {x : StopKind × String} (hx : t.stopped = some x) :
    (RP O stop o q steps t).1 = none ∧ (RP O stop o q steps t).2.stopped = some x ∧
      (RP O stop o q steps t).2.entered = t.entered ∧
      (RP O stop o q steps t).2.started = t.started := by
  rw [VER_013_stop_runPipeline h]
  obtain ⟨h1, h2, h3⟩ := runPipeline_after_stop (O := O) (stop := stop) (o := o) (q := q) steps t hx
  exact ⟨h1, h2, runPipeline_stopped_entered steps t hx, h3⟩

/-- **No budget and no cancellation, no stop** ([VER-013] AC8), for every runner and finisher
that meet the stop lines: a run from a trail without a stop records none, and the finisher keeps
every verdict. -/
@[evidence cites "VER-013" "AC8"]
theorem VER_013_stop_noStop {RP : Runner Q} {Fin : Finisher} (h : VER_013_stop RP Fin)
    {O : Oracle} {o : Options} {q : Q} {steps : List (GStep Q)} {t : Trail}
    (ht : t.stopped = none) :
    (RP O noStop o q steps t).2.stopped = none ∧ ∀ v, Fin (RP O noStop o q steps t).2 v = v := by
  have hs : (RP O noStop o q steps t).2.stopped = none := by
    rw [VER_013_stop_runPipeline h]
    exact runPipeline_noStop' steps t ht
  refine ⟨hs, fun v => ?_⟩
  cases v with
  | unknown why => rw [h.2.2.2.2.2]; simp [stopOrWhy, hs]
  | proven m => exact h.2.2.2.2.1 _ _ (fun _ hv => by cases hv)
  | violated => exact h.2.2.2.2.1 _ _ (fun _ hv => by cases hv)

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
theorem VER_013_stop_failing {RP : Runner Q} {Fin : Finisher}
    (h : VER_013_stop RP Fin) {O : Oracle} (hO : FailingOracle O) {stop : Stop} {o : Options}
    {q : Q} {steps : List (GStep Q)} {t : Trail}
    (hP : ∀ s ∈ steps, ∀ meth tr c, ¬ Yields failing (s.run o q) (.decided (.proven meth) tr c))
    {r : Route} {meth : String} {tr : List String} {c : Option Bool} :
    (RP O stop o q steps t).1 ≠ some (r, .decided (.proven meth) tr c) := by
  rw [VER_013_stop_runPipeline h]
  intro hd
  obtain ⟨s, hs, -, -, hy, -⟩ := runPipeline_step hd
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

/-- Whether a run decided `Proven`. -/
def decidesProven (p : Option (Route × PhaseOut) × Trail) : Option Bool :=
  p.1.map fun x => match x.2 with
    | .decided (.proven _) _ _ => true
    | _ => false

/-- The first step of the demo pipeline, which steps aside. -/
def boundStep : GStep Unit :=
  { name := "linear bound", route := .smt, run := fun _ _ => .done (.aside "no weighting") }

/-- The query step of the demo pipeline. -/
def queryStep : GStep Unit := { name := "IC3/PDR query", route := .smt, run := fun _ _ => demoQuery "horn" }

/-- A step whose guard fails. -/
def skippedStep : GStep Unit :=
  { name := "witness phase", route := .smt, applies := fun _ _ => false,
    run := fun _ _ => .done (.aside "not applicable") }

/-- A runner that answers every solver call with `sat`, whatever the solver says. -/
def ignoreSolver : Runner Q := fun _ stop o q steps t => runPipeline satOracle stop o q steps t

/-- A solver that is never found. -/
def missingOracle : Oracle := fun _ => .failure .missing "z3 binary not found"

/-- A runner that refuses every solver process, with or without a stop. -/
def refuseAll : Runner Q := fun _ stop o q steps t =>
  runPipeline (fun _ => .failure .notStarted "refused") stop o q steps t

/-- A runner that starts one more process, a detail re-run, once the pipeline ends undecided. -/
def trailingRun : Runner Q := fun O stop o q steps t =>
  let r := runPipeline O stop o q steps t
  if r.1.isNone then (r.1, { r.2 with started := r.2.started ++ ["detail"] }) else r

/-- A runner whose entry poll comes before the guard, so a step whose guard fails polls too. -/
def pollAlways (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    List (GStep Q) → Trail → Option (Route × PhaseOut) × Trail
  | [], t => (none, t)
  | s :: ss, t =>
    if (pollStop stop t).1 then (none, (pollStop stop t).2)
    else if s.applies o q then
      match execProg O stop (s.run o q) ((pollStop stop t).2.enter s) with
      | (.aside _, t') => pollAlways O stop o q ss t'
      | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')
    else pollAlways O stop o q ss (pollStop stop t).2

/-- A runner that records the new step before its entry poll. -/
def blameNext : Runner Q := fun O stop o q steps t =>
  match steps with
  | [] => (none, t)
  | s :: ss => runPipeline O stop o q (s :: ss)
      (if s.applies o q then { t with running := s.name } else t)

/-- A runner that starts one more process, outside the clamp, once a stop is recorded. -/
def extraAfterStop : Runner Q := fun O stop o q steps t =>
  let r := runPipeline O stop o q steps t
  if t.stopped.isNone && r.2.stopped.isSome then
    (r.1, { r.2 with started := r.2.started ++ ["extra"] })
  else r

/-- A runner that forgets a recorded stop. -/
def forgetStop : Runner Q := fun O stop o q steps t =>
  runPipeline O stop o q steps { t with stopped := none }

/-- A runner that, from a stopped trail, still enters every applicable step, starting nothing
and deciding nothing: an entry check whose answer is ignored. -/
def enterAfterStop : Runner Q := fun O stop o q steps t =>
  match t.stopped with
  | some _ => (none, { t with entered := t.entered ++ (steps.filter (·.applies o q)).map (·.name) })
  | none => runPipeline O stop o q steps t

/-- A runner that honours a stop recorded already, or one found at its very first entry poll,
and ignores every later stop. -/
def ignoreLater : Runner Q := fun O stop o q steps t =>
  match t.stopped with
  | some _ => (none, t)
  | none =>
    match steps with
    | [] => runPipeline O noStop o q steps t
    | s :: _ =>
      if s.applies o q then
        match stop t.polls with
        | some k => (none, { t with polls := t.polls + 1, stopped := some (k, t.running) })
        | none => runPipeline O noStop o q steps t
      else runPipeline O noStop o q steps t

/-- A program run whose solver calls skip the poll before the process: every call starts. -/
def execNoPoll {α : Type} (O : Oracle) (stop : Stop) : PhaseProg α → Trail → α × Trail
  | .done a, t => (a, t)
  | .ask s k, t =>
    execNoPoll O stop (k (O s)) (pollStop stop { t with started := t.started ++ [s] }).2
  | .poll k, t => execNoPoll O stop (k (pollStop stop t).1) (pollStop stop t).2

/-- The pipeline over `execNoPoll`: a solver call path that bypasses the clamp. -/
def askNoPoll (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    List (GStep Q) → Trail → Option (Route × PhaseOut) × Trail
  | [], t => (none, t)
  | s :: ss, t =>
    if s.applies o q then
      if (pollStop stop t).1 then (none, (pollStop stop t).2)
      else
        match execNoPoll O stop (s.run o q) ((pollStop stop t).2.enter s) with
        | (.aside _, t') => askNoPoll O stop o q ss t'
        | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')
    else askNoPoll O stop o q ss t

/-- A wrong program run whose solver calls make no poll after the reply (the Java `Z3Solver.run`
behaviour after an unclamped call that RD-43 recorded). -/
def execNoPostPoll {α : Type} (O : Oracle) (stop : Stop) : PhaseProg α → Trail → α × Trail
  | .done a, t => (a, t)
  | .ask s k, t =>
    if (pollStop stop t).1 then
      execNoPostPoll O stop (k (.failure .notStarted (refusedReason (pollStop stop t).2.stopped)))
        (pollStop stop t).2
    else
      execNoPostPoll O stop (k (O s))
        { (pollStop stop t).2 with started := (pollStop stop t).2.started ++ [s] }
  | .poll k, t => execNoPostPoll O stop (k (pollStop stop t).1) (pollStop stop t).2

/-- The pipeline over `execNoPostPoll`. -/
def noPostPoll (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    List (GStep Q) → Trail → Option (Route × PhaseOut) × Trail
  | [], t => (none, t)
  | s :: ss, t =>
    if s.applies o q then
      if (pollStop stop t).1 then (none, (pollStop stop t).2)
      else
        match execNoPostPoll O stop (s.run o q) ((pollStop stop t).2.enter s) with
        | (.aside _, t') => noPostPoll O stop o q ss t'
        | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')
    else noPostPoll O stop o q ss t

/-- A wrong program run whose refused solver calls record no stop (the TypeScript `runZ3Text`
behaviour RD-42 recorded: refusing with less than 1 ms left while its polls still saw time). -/
def execRefuseUnrecorded {α : Type} (O : Oracle) (stop : Stop) : PhaseProg α → Trail → α × Trail
  | .done a, t => (a, t)
  | .ask s k, t =>
    if (pollStop stop t).1 then
      execRefuseUnrecorded O stop
        (k (.failure .notStarted (refusedReason (pollStop stop t).2.stopped)))
        { t with polls := t.polls + 1 }
    else
      execRefuseUnrecorded O stop (k (O s))
        (pollStop stop { (pollStop stop t).2 with started := (pollStop stop t).2.started ++ [s] }).2
  | .poll k, t => execRefuseUnrecorded O stop (k (pollStop stop t).1) (pollStop stop t).2

/-- The pipeline over `execRefuseUnrecorded`. -/
def refuseUnrecorded (O : Oracle) (stop : Stop) (o : Options) (q : Q) :
    List (GStep Q) → Trail → Option (Route × PhaseOut) × Trail
  | [], t => (none, t)
  | s :: ss, t =>
    if s.applies o q then
      if (pollStop stop t).1 then (none, (pollStop stop t).2)
      else
        match execRefuseUnrecorded O stop (s.run o q) ((pollStop stop t).2.enter s) with
        | (.aside _, t') => refuseUnrecorded O stop o q ss t'
        | (.decided v tr c, t') => (some (s.route, .decided v tr c), t')
    else refuseUnrecorded O stop o q ss t

/-- A solver that answers `unknown`. -/
def unknownOracle : Oracle := fun _ => .answer .unknown

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

end Ver013

open Verifier Ver013

/-- ✗ **The run ends after its last step** (line 1). Example: a runner that starts a detail
re-run once the pipeline ends undecided starts a `z3` process with no step running, even after
a stop. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_trailingRun :
    ¬ VER_013_stop (Q := Unit) trailingRun finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.started) (h.1 satOracle noStop {} () {})
  revert this
  decide

/-- ✗ **A step whose guard fails makes no poll** (line 2). Example: cancelled from poll 0, a
pipeline whose only step does not apply ends with no stop recorded; a runner that polls before
the guard records the cancellation. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_pollAlways :
    ¬ VER_013_stop (Q := Unit) pollAlways finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.stopped)
    (h.2.1 satOracle (stopFrom 0 .cancelled) {} () skippedStep [] {} rfl)
  revert this
  decide

/-- ✗ **A stop found on entry blames the step that just ended** (line 3). Example: a
cancellation seen on entering `IC3/PDR query` from the start of the run is charged to
`net preparation`, the step that was running; a runner that records the query first blames the
query. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_blameNext :
    ¬ VER_013_stop (Q := Unit) blameNext finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.stopped)
    (h.2.2.1 satOracle (stopFrom 0 .cancelled) {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **No process once the entry poll found the stop** (line 3). Example: cancelled from poll
0, the entry poll of `IC3/PDR query` ends the run with nothing started; a runner that then starts
one more process outside the clamp starts `extra`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_extraAfterStop :
    ¬ VER_013_stop (Q := Unit) extraAfterStop finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.started)
    (h.2.2.1 satOracle (stopFrom 0 .cancelled) {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **Nothing starts after a stop** (line 3). Example: from a trail that already records a
cancellation, a runner that forgets it enters the query and starts its `z3` process. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_forget :
    ¬ VER_013_stop (Q := Unit) forgetStop finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.started)
    (h.2.2.1 satOracle noStop {} () queryStep [] { stopped := some (.cancelled, "linear bound") }
      rfl rfl)
  revert this
  decide

/-- ✗ **No step is entered after a stop** (line 3). Example: from a trail cancelled in `linear
bound`, a runner whose entry check is ignored still enters `IC3/PDR query`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_enterAfterStop :
    ¬ VER_013_stop (Q := Unit) enterAfterStop finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.entered)
    (h.2.2.1 satOracle noStop {} () queryStep [] { stopped := some (.cancelled, "linear bound") }
      rfl rfl)
  revert this
  decide

/-- ✗ **A stop first found later in the run stops it there** (lines 3 and 4). Example: cancelled
from poll 1, the run steps aside in `linear bound` and the entry poll of `IC3/PDR query` finds
the cancellation, so nothing starts; a runner that honours only a stop found at its first entry
poll enters the query, starts `horn` and proves. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_ignoreLater :
    ¬ VER_013_stop (Q := Unit) ignoreLater finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.started)
    (h.2.2.2.1 satOracle (stopFrom 1 .cancelled) {} () boundStep [queryStep] {} rfl rfl)
  revert this
  decide

/-- ✗ **A solver call polls first and starts nothing when stopped** (line 4). Example: cancelled
from poll 1, inside `IC3/PDR query`, the query's call is refused and no process starts; a runner
whose calls skip that poll starts `horn`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_askNoPoll :
    ¬ VER_013_stop (Q := Unit) askNoPoll finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.started)
    (h.2.2.2.1 satOracle (stopFrom 1 .cancelled) {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **A solver call polls again after its reply** (line 4; the behaviour RD-43 recorded).
Example: a 100 ms budget
runs out during the IC3/PDR query's process (from poll 2, the poll after the reply) and `z3`
answers `unknown`; the reference charges the stop to the query and finishes with `total
verification budget of 100 ms exhausted during IC3/PDR query`, while a runner without the poll
after the reply records no stop and keeps `the solver answered unknown`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_noPostPoll :
    ¬ VER_013_stop (Q := Unit) noPostPoll finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.stopped)
    (h.2.2.2.1 unknownOracle (stopFrom 2 (.budget 100)) {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- The two finished verdicts of `VER_013_stop_forbids_noPostPoll`'s example. -/
example :
    finishVerdict (noPostPoll unknownOracle (stopFrom 2 (.budget 100)) {} () [queryStep] {}).2
        (.unknown "the solver answered unknown") = .unknown "the solver answered unknown" ∧
    finishVerdict (runPipeline unknownOracle (stopFrom 2 (.budget 100)) {} () [queryStep] {}).2
        (.unknown "the solver answered unknown") =
      .unknown "total verification budget of 100 ms exhausted during IC3/PDR query" := by
  decide

/-- ✗ **A refused call is a poll that records the stop** (line 4; the behaviour RD-42 recorded).
Example: with the
100 ms budget spent from poll 1, the query's call is refused; the reference records the stop
against the query, while a runner whose refusal records nothing ends with no stop, so its
`Unknown` keeps `solver failure: total verification budget of 100 ms exhausted; z3 not started`
without the phase, and a later step would still be entered. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_refuseUnrecorded :
    ¬ VER_013_stop (Q := Unit) refuseUnrecorded finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.stopped)
    (h.2.2.2.1 satOracle (stopFrom 1 (.budget 100)) {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **A failure is no answer** (line 4). Example: with `z3` missing, a runner that reads the
query's reply as `sat` proves the property; the query proves only on `sat`, so the reference
answers `Unknown`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_ignoreSolver :
    ¬ VER_013_stop (Q := Unit) ignoreSolver finishVerdict := by
  intro h
  have := congrArg decidesProven
    (h.2.2.2.1 missingOracle noStop {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **No refusal without a stop** (line 4). Example: with no total budget and no cancellation,
a runner that refuses every process leaves the query `Unknown` where `z3` answers `sat`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_refuseAll :
    ¬ VER_013_stop (Q := Unit) refuseAll finishVerdict := by
  intro h
  have := congrArg decidesProven
    (h.2.2.2.1 satOracle noStop {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **No budget, no stop** (line 4). Example: with no total budget and no cancellation, a
runner that records a 0 ms budget at its first poll stops the query before it starts. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_selfStop :
    ¬ VER_013_stop (Q := Unit) selfStop finishVerdict := by
  intro h
  have := congrArg (fun p => p.2.stopped)
    (h.2.2.2.1 satOracle noStop {} () queryStep [] {} rfl rfl)
  revert this
  decide

/-- ✗ **A verdict reached before the stop stands** (line 5). Example: the query answered `sat`
and was then cancelled; a finisher that turns the `Proven` into `verification cancelled during
IC3/PDR query` throws a finished proof away. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_overwrite :
    ¬ VER_013_stop (Q := Unit) runPipeline overwrite := by
  intro h
  have := h.2.2.2.2.1 { stopped := some (.cancelled, "IC3/PDR query") } (.proven "IC3/PDR")
    (fun _ hv => by cases hv)
  revert this
  decide

/-- ✗ **An Unknown after a stop names the stop** (line 6). Example: a query refused because the
100 ms budget was spent must say `total verification budget of 100 ms exhausted during IC3/PDR
query`, not its own `z3 not started`. -/
@[evidence forbids VER_013_stop]
theorem VER_013_stop_forbids_innerReason :
    ¬ VER_013_stop (Q := Unit) runPipeline innerReason := by
  intro h
  have := h.2.2.2.2.2 { stopped := some (.budget 100, "IC3/PDR query") } "z3 not started"
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
