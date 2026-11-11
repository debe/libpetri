set_option linter.missingDocs true

/-!
# EARS patterns over traces and over single steps

**For the reader who does not read Lean.** A requirement in the spec says which behaviour is
acceptable. We write requirements in sentence shapes from EARS (Easy Approach to Requirements
Syntax), each with a readable notation. There are two families.

*Trace forms.* A *trace* is the list of everything that happened in one run, oldest first.

| Notation | Reads as | EARS shape |
|---|---|---|
| `when T, shall R` | every `T` is followed (at it or later) by an `R` | event-driven |
| `after T, never B` | once a `T` has happened, no later event is a `B` | unwanted behaviour |
| `after T, until G, never B` | after each `T`, no `B` before the next `G` | unwanted behaviour, bounded |
| `until G, never B` | no `B` happens before the first `G` | state-driven ("while not G") |
| `at-most-once P` | at most one event is a `P` | ubiquitous |
| `occurs P` | some event is a `P` | (used in assumptions) |

*Run forms.* A liveness requirement ("every accepted event is eventually injected") is stated on
the runs an assumption calls ideal (`on-ideal-runs I, shall P`: every trace `I` admits satisfies
`P`); the assumption is a kind A line of the block, and a block pairs it with a witness run.

*State forms.* Most firing requirements talk about one step `s ⟶ s'` (a relation
`R : σ → σ → Prop`, for example "transition `t` fires from marking `m` to `m'`") and a property
of the state before it.

| Notation | Reads as | EARS shape |
|---|---|---|
| `while P, never R` | no `R` step starts in a state where `P` holds | state-driven, unwanted |
| `on R, shall Q` | every `R` step from `s` to `s'` satisfies `Q s s'` | event-driven |

The state forms use `on` rather than `when` so that they never compete with the trace form
`when T, shall R`. `while` is already a Lean keyword (the `do`-notation loop `while c do …`);
that parser lives in the `doElem` category and needs `do`, while `while P, never R` is a *term*
and needs `, never`, so the two do not overlap. A `do` block whose element starts with `while`
still parses as the loop (checked at the end of this file).

`#print` and hover show these forms back, because each notation has a plain definition as its
right-hand side.

**For the Lean reader.** Every trace pattern is a `Watch`: a left-to-right scan with a small
memory (`α`), a per-event check and a final check. Being `Bool`-valued, every trace pattern is
decidable, so acceptance examples are checked by `decide`, and `Watch.scan_append` lets a proof
about a run cut the trace into the blocks the system produced. The state forms quantify over all
states and are plain `Prop`s; they are decidable only when the state space is finite.

All notations are `scoped` to `Libpetri.Spec`: they are active inside `namespace Libpetri.Spec`
or after `open Libpetri.Spec`, and they reserve the words `after`, `until`, `never`, `shall`,
`occurs`, `on`, `at-most-once` and `on-ideal-runs` only there.
-/

namespace Libpetri.Spec

variable {σ α : Type}

/-! ## Trace forms -/

/-- A scan over a trace with memory `α`: `ok` checks each event given what was seen before it,
`next` updates the memory, `final` checks the memory at the end of the trace. -/
structure Watch (σ α : Type) where
  /-- Memory before the first event. -/
  init : α
  /-- Is this event acceptable, given the memory? -/
  ok : α → σ → Bool
  /-- Memory after this event. -/
  next : α → σ → α
  /-- Is the memory acceptable at the end of the trace? -/
  final : α → Bool

namespace Watch

/-- Scan a trace from memory `a`, checking every event and the end. -/
def scan (w : Watch σ α) : α → List σ → Bool
  | a, [] => w.final a
  | a, e :: rest => w.ok a e && w.scan (w.next a e) rest

/-- Check every event of a trace piece, without the end check. -/
def okAll (w : Watch σ α) : α → List σ → Bool
  | _, [] => true
  | a, e :: rest => w.ok a e && w.okAll (w.next a e) rest

/-- Memory after a trace piece. -/
def after (w : Watch σ α) : α → List σ → α
  | a, [] => a
  | a, e :: rest => w.after (w.next a e) rest

/-- Scanning `x ++ y` is scanning `x` without the end check, then `y` from where `x` left off. -/
theorem scan_append (w : Watch σ α) (a : α) (x y : List σ) :
    w.scan a (x ++ y) = (w.okAll a x && w.scan (w.after a x) y) := by
  induction x generalizing a with
  | nil => simp [okAll, after]
  | cons e x ih => simp [scan, okAll, after, ih, Bool.and_assoc]

/-- The trace is accepted by the watch. -/
def Holds (w : Watch σ α) (tr : List σ) : Prop := w.scan w.init tr = true

instance (w : Watch σ α) (tr : List σ) : Decidable (w.Holds tr) :=
  inferInstanceAs (Decidable (_ = true))

end Watch

/-- Memory: has `trig` happened? Check: no `bad` once it has. -/
def afterNever (trig bad : σ → Bool) : Watch σ Bool where
  init := false
  ok fired e := !(fired && bad e)
  next fired e := fired || trig e
  final _ := true

/-- Memory: has `go` happened? Check: no `bad` before it has. -/
def untilNever (go bad : σ → Bool) : Watch σ Bool where
  init := false
  ok seen e := seen || !bad e
  next seen e := seen || go e
  final _ := true

/-- Memory: is a response owed? A `trig` makes one owed, a `resp` pays it. Check: nothing owed
at the end. -/
def whenShall (trig resp : σ → Bool) : Watch σ Bool where
  init := false
  ok _ _ := true
  next owed e := (owed || trig e) && !resp e
  final owed := !owed

/-- Memory: is a `bad` forbidden now? A `trig` forbids it, the next `go` after that `trig` lifts
the ban. An event that is both a `go` and a `trig` lifts the old ban and starts a new one (the `go`
is not after the `trig`). Check: no `bad` while the ban stands; the `trig` itself is not checked
against its own ban, as in `afterNever`. -/
def afterUntilNever (trig go bad : σ → Bool) : Watch σ Bool where
  init := false
  ok banned e := !(banned && bad e)
  next banned e := (banned && !go e) || trig e
  final _ := true

/-- EARS unwanted behaviour: "If `trig`, then afterwards the system shall not `bad`." -/
def AfterNever (trig bad : σ → Bool) (tr : List σ) : Prop := (afterNever trig bad).Holds tr

/-- EARS state-driven: "While `go` has not happened, the system shall not `bad`." -/
def UntilNever (go bad : σ → Bool) (tr : List σ) : Prop := (untilNever go bad).Holds tr

/-- EARS event-driven: "When `trig`, the system shall `resp` (now or later)." -/
def WhenShall (trig resp : σ → Bool) (tr : List σ) : Prop := (whenShall trig resp).Holds tr

/-- EARS unwanted behaviour, bounded: "If `trig`, then the system shall not `bad` until `go`."
After each `trig`, no `bad` happens before the next `go`. -/
def AfterUntilNever (trig go bad : σ → Bool) (tr : List σ) : Prop :=
  (afterUntilNever trig go bad).Holds tr

/-- Ubiquitous: at most one event satisfies `p`. -/
def AtMostOnce (p : σ → Bool) (tr : List σ) : Prop := AfterNever p p tr

/-- Some event of the trace satisfies `p`. -/
def Occurs (p : σ → Bool) (tr : List σ) : Prop := tr.any p = true

instance {trig bad : σ → Bool} {tr : List σ} : Decidable (AfterNever trig bad tr) :=
  inferInstanceAs (Decidable (Watch.Holds ..))
instance {go bad : σ → Bool} {tr : List σ} : Decidable (UntilNever go bad tr) :=
  inferInstanceAs (Decidable (Watch.Holds ..))
instance {trig go bad : σ → Bool} {tr : List σ} : Decidable (AfterUntilNever trig go bad tr) :=
  inferInstanceAs (Decidable (Watch.Holds ..))
instance {trig resp : σ → Bool} {tr : List σ} : Decidable (WhenShall trig resp tr) :=
  inferInstanceAs (Decidable (Watch.Holds ..))
instance {p : σ → Bool} {tr : List σ} : Decidable (AtMostOnce p tr) :=
  inferInstanceAs (Decidable (Watch.Holds ..))
instance {p : σ → Bool} {tr : List σ} : Decidable (Occurs p tr) :=
  inferInstanceAs (Decidable (_ = true))

/-- The `occurs` pattern as a watch, for proofs: memory "seen yet?", end check "seen". -/
def occursW (p : σ → Bool) : Watch σ Bool := ⟨false, fun _ _ => true, fun a e => a || p e, id⟩

/-- Scanning with `occursW p` computes "seen before, or some event is a `p`". -/
theorem occursW_scan (p : σ → Bool) :
    ∀ (a : Bool) (tr : List σ), (occursW p).scan a tr = (a || tr.any p)
  | a, [] => by simp [Watch.scan, occursW]
  | a, e :: tr => by
    show (true && (occursW p).scan (a || p e) tr) = _
    rw [occursW_scan p _ tr]; simp [Bool.or_assoc]

/-! ### Patterns about events that never happen hold trivially -/

/-- If no event is `bad`, `after T, never B` holds from any memory. -/
theorem afterNever_scan_of_absent {trig bad : σ → Bool} :
    ∀ {tr : List σ} (a : Bool), (∀ e ∈ tr, bad e = false) → (afterNever trig bad).scan a tr = true
  | [], _, _ => rfl
  | e :: rest, a, h => by
    simp only [Watch.scan, afterNever, h e (List.mem_cons_self ..), Bool.and_false, Bool.not_false,
      Bool.true_and]
    exact afterNever_scan_of_absent _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- If no event is `bad`, `until G, never B` holds from any memory. -/
theorem untilNever_scan_of_absent {go bad : σ → Bool} :
    ∀ {tr : List σ} (a : Bool), (∀ e ∈ tr, bad e = false) → (untilNever go bad).scan a tr = true
  | [], _, _ => rfl
  | e :: rest, a, h => by
    simp only [Watch.scan, untilNever, h e (List.mem_cons_self ..), Bool.not_false, Bool.or_true,
      Bool.true_and]
    exact untilNever_scan_of_absent _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- If no event is `bad`, `after T, until G, never B` holds from any memory. -/
theorem afterUntilNever_scan_of_absent {trig go bad : σ → Bool} :
    ∀ {tr : List σ} (a : Bool), (∀ e ∈ tr, bad e = false) →
      (afterUntilNever trig go bad).scan a tr = true
  | [], _, _ => rfl
  | e :: rest, a, h => by
    simp only [Watch.scan, afterUntilNever, h e (List.mem_cons_self ..), Bool.and_false,
      Bool.not_false, Bool.true_and]
    exact afterUntilNever_scan_of_absent _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- Without a `go`, the ban never lifts: `after T, until G, never B` is `after T, never B`. -/
theorem afterUntilNever_no_go (trig bad : σ → Bool) :
    afterUntilNever trig (fun _ => false) bad = afterNever trig bad := by
  simp [afterUntilNever, afterNever]

/-- `after T, until G, never B` is monotone: fewer triggers, more lifts and fewer bad events
keep it. -/
theorem afterUntilNever_scan_mono {trig go bad trig' go' bad' : σ → Bool}
    (ht : ∀ e, trig' e = true → trig e = true) (hg : ∀ e, go e = true → go' e = true)
    (hb : ∀ e, bad' e = true → bad e = true) :
    ∀ (tr : List σ) (a a' : Bool), (a' = true → a = true) →
      (afterUntilNever trig go bad).scan a tr = true →
      (afterUntilNever trig' go' bad').scan a' tr = true
  | [], _, _, _, _ => rfl
  | e :: rest, a, a', ha, h => by
    simp only [Watch.scan, afterUntilNever, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    refine ⟨?_, afterUntilNever_scan_mono ht hg hb rest _ _ ?_ h.2⟩
    · cases ha' : a' <;> cases hb' : bad' e <;> simp_all
    · intro h'
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h' ⊢
      rcases h' with ⟨h1, h2⟩ | h1
      · refine Or.inl ⟨ha h1, ?_⟩
        cases hge : go e
        · rfl
        · simp [hg e hge] at h2
      · exact Or.inr (ht e h1)

/-- `after T, until G, never B` is monotone in its three event predicates. -/
theorem AfterUntilNever.mono {trig go bad trig' go' bad' : σ → Bool}
    (ht : ∀ e, trig' e = true → trig e = true) (hg : ∀ e, go e = true → go' e = true)
    (hb : ∀ e, bad' e = true → bad e = true) {tr : List σ}
    (h : AfterUntilNever trig go bad tr) : AfterUntilNever trig' go' bad' tr :=
  afterUntilNever_scan_mono ht hg hb tr false false (fun h => h) h

/-- If no event is a `trig`, `when T, shall R` holds when nothing is owed yet. -/
theorem whenShall_scan_of_absent {trig resp : σ → Bool} :
    ∀ {tr : List σ}, (∀ e ∈ tr, trig e = false) → (whenShall trig resp).scan false tr = true
  | [], _ => rfl
  | e :: rest, h => by
    simp only [Watch.scan, whenShall, h e (List.mem_cons_self ..), Bool.or_false, Bool.false_and,
      Bool.true_and]
    exact whenShall_scan_of_absent fun x hx => h x (List.mem_cons_of_mem _ hx)

/-! ## Run forms (liveness under an assumption) -/

/-- Kind A liveness over finite runs: `P` holds of every trace the assumption `Ideal` admits (for
the executor, `IdealRun` of `GlossaryExec`: the runs that reach their finish). An `Ideal` that
admits no trace makes every `OnIdealRuns` true (`onIdealRuns_of_none`), so a block pairs it with a
witness ideal run (nonvacuous evidence). -/
def OnIdealRuns (Ideal : List σ → Prop) (P : List σ → Prop) : Prop := ∀ tr, Ideal tr → P tr

/-- `OnIdealRuns` is antitone in the assumption and monotone in the property. -/
theorem OnIdealRuns.mono {I I' P P' : List σ → Prop} (hI : ∀ tr, I' tr → I tr)
    (hP : ∀ tr, P tr → P' tr) (h : OnIdealRuns I P) : OnIdealRuns I' P' :=
  fun tr hi => hP tr (h tr (hI tr hi))

/-- A property of every trace holds on the ideal runs. -/
theorem OnIdealRuns.of_forall {I P : List σ → Prop} (h : ∀ tr, P tr) : OnIdealRuns I P :=
  fun tr _ => h tr

/-- An assumption that admits no run makes every `OnIdealRuns` true. -/
theorem onIdealRuns_of_none {I P : List σ → Prop} (h : ∀ tr, ¬ I tr) : OnIdealRuns I P :=
  fun tr hi => absurd hi (h tr)

/-! ## State forms over single steps -/

/-- EARS state-driven unwanted behaviour over one step: "While `P` holds, the system shall not
take an `R` step." Every `R` step `s ⟶ s'` starts in a state where `P` does not hold. -/
def WhileNever (P : σ → Prop) (R : σ → σ → Prop) : Prop :=
  ∀ s s', R s s' → ¬ P s

/-- EARS event-driven over one step: "When an `R` step happens, the system shall establish `Q`."
Every `R` step `s ⟶ s'` satisfies `Q s s'`. -/
def StepShall (R : σ → σ → Prop) (Q : σ → σ → Prop) : Prop :=
  ∀ s s', R s s' → Q s s'

/-- `on R, shall Q` is `StepShall` with a post-condition that ignores the target state. -/
theorem stepShall_pre_iff {R : σ → σ → Prop} {Q : σ → Prop} :
    StepShall R (fun s _ => Q s) ↔ ∀ s s', R s s' → Q s := Iff.rfl

/-- `while P, never R` is `on R, shall ¬P` read on the source state. -/
theorem whileNever_iff_stepShall {P : σ → Prop} {R : σ → σ → Prop} :
    WhileNever P R ↔ StepShall R (fun s _ => ¬ P s) := Iff.rfl

/-- `WhileNever` is antitone in the step relation: forbidding a larger set of steps forbids
every smaller one. -/
theorem WhileNever.mono_rel {P : σ → Prop} {R R' : σ → σ → Prop}
    (hR : ∀ s s', R' s s' → R s s') (h : WhileNever P R) : WhileNever P R' :=
  fun s s' hs => h s s' (hR s s' hs)

/-- `WhileNever` is antitone in the guard: forbidding steps under a weaker guard forbids them
under every stronger one. -/
theorem WhileNever.mono_pre {P P' : σ → Prop} {R : σ → σ → Prop}
    (hP : ∀ s, P' s → P s) (h : WhileNever P R) : WhileNever P' R :=
  fun s s' hs hp => h s s' hs (hP s hp)

/-- `StepShall` is antitone in the step relation and monotone in the post-condition. -/
theorem StepShall.mono {R R' : σ → σ → Prop} {Q Q' : σ → σ → Prop}
    (hR : ∀ s s', R' s s' → R s s') (hQ : ∀ s s', Q s s' → Q' s s')
    (h : StepShall R Q) : StepShall R' Q' :=
  fun s s' hs => hQ s s' (h s s' (hR s s' hs))

/-- `StepShall` distributes over conjunction of post-conditions. -/
theorem stepShall_and {R : σ → σ → Prop} {Q Q' : σ → σ → Prop} :
    StepShall R (fun s s' => Q s s' ∧ Q' s s') ↔ StepShall R Q ∧ StepShall R Q' :=
  ⟨fun h => ⟨fun s s' hs => (h s s' hs).1, fun s s' hs => (h s s' hs).2⟩,
   fun h s s' hs => ⟨h.1 s s' hs, h.2 s s' hs⟩⟩

/-- Two guards forbidden separately are forbidden together: `WhileNever` distributes over
disjunction of guards. -/
theorem whileNever_or {P P' : σ → Prop} {R : σ → σ → Prop} :
    WhileNever (fun s => P s ∨ P' s) R ↔ WhileNever P R ∧ WhileNever P' R :=
  ⟨fun h => ⟨fun s s' hs hp => h s s' hs (.inl hp), fun s s' hs hp => h s s' hs (.inr hp)⟩,
   fun h s s' hs hp => hp.elim (h.1 s s' hs) (h.2 s s' hs)⟩

/-- An empty step relation satisfies every `WhileNever`, so a `holds` proof alone says nothing;
requirement blocks pair it with `nonvacuous` evidence. -/
theorem whileNever_of_empty {P : σ → Prop} {R : σ → σ → Prop} (h : ∀ s s', ¬ R s s') :
    WhileNever P R :=
  fun s s' hs => absurd hs (h s s')

/-- An empty step relation satisfies every `StepShall`. -/
theorem stepShall_of_empty {R Q : σ → σ → Prop} (h : ∀ s s', ¬ R s s') : StepShall R Q :=
  fun s s' hs => absurd hs (h s s')

/-- A guard that holds nowhere is never violated. -/
theorem whileNever_of_false {P : σ → Prop} {R : σ → σ → Prop} (h : ∀ s, ¬ P s) :
    WhileNever P R :=
  fun s _ _ => h s

/-! ## Notations -/

/-- `after T, never B`: once a `T` happened, no later event is a `B`. -/
scoped notation:max "after " trig ", " "never " bad => AfterNever trig bad
/-- `after T, until G, never B`: after each `T`, no `B` before the next `G`. -/
scoped notation:max "after " trig ", " "until " go ", " "never " bad => AfterUntilNever trig go bad
/-- `until G, never B`: no `B` before the first `G`. -/
scoped notation:max "until " go ", " "never " bad => UntilNever go bad
/-- `when T, shall R`: every `T` is followed, at it or later, by an `R`. -/
scoped notation:max "when " trig ", " "shall " resp => WhenShall trig resp
/-- `at-most-once P`: at most one event is a `P`. -/
scoped notation:max "at-most-once " p => AtMostOnce p
/-- `occurs P`: some event is a `P`. -/
scoped notation:max "occurs " p => Occurs p
/-- `while P, never R`: no `R` step starts in a state where `P` holds. -/
scoped notation:max "while " P ", " "never " R => WhileNever P R
/-- `on R, shall Q`: every `R` step from `s` to `s'` satisfies `Q s s'`. -/
scoped notation:max "on " R ", " "shall " Q => StepShall R Q
/-- `on-ideal-runs I, shall P`: every trace the assumption `I` admits satisfies `P`. -/
scoped notation:max "on-ideal-runs " I ", " "shall " P => OnIdealRuns I P

/-! ## Sanity checks of the notations -/

section Checks

/-- Events of the check traces. -/
private inductive Ev | start | stop | tick
  deriving DecidableEq

private def isStart : Ev → Bool := (· == .start)
private def isStop : Ev → Bool := (· == .stop)
private def isTick : Ev → Bool := (· == .tick)

example : (after isStop, never isTick) [.tick, .stop] := by decide
example : ¬ (after isStop, never isTick) [.stop, .tick] := by decide
example : (until isStart, never isTick) [.start, .tick] := by decide
example : ¬ (until isStart, never isTick) [.tick, .start] := by decide
example : (when isStart, shall isStop) [.start, .tick, .stop] := by decide
example : ¬ (when isStart, shall isStop) [.stop, .start] := by decide
example : (at-most-once isStart) [.start, .tick] := by decide
example : ¬ (at-most-once isStart) [.start, .start] := by decide
example : (occurs isTick) [.start, .tick] := by decide
example : (after isStart, until isStop, never isTick) [.start, .stop, .tick] := by decide
example : ¬ (after isStart, until isStop, never isTick) [.start, .tick, .stop] := by decide
example : ¬ (after isStart, until isStop, never isTick) [.start, .stop, .start, .tick] := by decide
example : (after isStart, until isStop, never isTick) [.tick, .start, .stop] := by decide
/- `after T, never B` still parses next to `after T, until G, never B`. -/
example : (after isStop, never isTick) [.tick, .stop] := by decide
example : (on-ideal-runs (fun tr : List Ev => tr.length ≤ 1), shall
    (fun tr => (at-most-once isStart) tr)) := fun tr h => by
  match tr, h with
  | [], _ => decide
  | [e], _ => cases e <;> decide

/-- A counter that only increments: it never steps from a state above 2. -/
private def incBelow3 (n n' : Nat) : Prop := n < 3 ∧ n' = n + 1

example : while (fun n => 3 ≤ n), never incBelow3 :=
  fun _ _ h hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h.1 hle)
example : on incBelow3, shall (fun n n' => n < n') :=
  fun _ _ h => h.2 ▸ Nat.lt_succ_self _

/- The state notations unfold to their definitions. -/
example (P : Nat → Prop) (R : Nat → Nat → Prop) :
    (while P, never R) = WhileNever P R := rfl
example (R Q : Nat → Nat → Prop) : (on R, shall Q) = StepShall R Q := rfl
example (t g b : Nat → Bool) : (after t, until g, never b) = AfterUntilNever t g b := rfl
example (I P : List Nat → Prop) : (on-ideal-runs I, shall P) = OnIdealRuns I P := rfl

/- With the notations open, the `do`-notation `while` loop still parses. -/
private def countdown (n : Nat) : Nat := Id.run do
  let mut k := n
  while k > 0 do
    k := k - 1
  return k

#guard countdown 3 = 0

/- `Watch.after` is still reachable as a dotted name. -/
example : (afterNever isStop isTick).after false [.stop] = true := rfl

end Checks

end Libpetri.Spec
