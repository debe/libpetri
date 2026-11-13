import Libpetri.Spec.Registry
import Libpetri.Spec.Verifier.Pipeline

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# NU-010 AC6: a declared mint that is not in the net (`spec/12-nu-nets.md`)

The ν routes read a transition as a mint only when the net declares it ([NU-010]). One way to
declare it is to name it on the verifier (`mintTransitions` / `mint_transitions`). A typo there
would silently leave a real mint undeclared, so a name that is not a transition of the net must
fail loudly, with one reason text at every entry point.

One block, `NU_010_unknownMint` (kind F), over an abstract entry point `E : MintCall → MintAnswer`:
a call (the solver, the stop, the options, the net, the property, the initial marking and the
names given as mint transitions) goes to an answer (a verdict, the entry point's ordinary output
such as scripts, or a failure with a message). Three lines:

* a call that names a mint transition the net does not have is refused: a failure or an
  `Unknown`, never `Proven`, `Violated` or scripts;
* the refusal's reason is `unknownMintReason`, the text
  `declared mint transition 'x' not in the net (NU-010)` naming each unknown name once in
  code-point order, unless the same call with no mint named gets the same answer (a refusal
  that does not depend on the declaration, such as a stop before the call starts, may come
  first);
* a call whose mint names are all transitions of the net is never refused with that text,
  whatever names it gives, unless the same call with no mint named gets the same answer.

Witnesses, both built by `mintGuard`: `refNuEntry`, verification over the reference pipeline of
`Spec/Verifier/Pipeline.lean` in Rust's order (stop at start, unresolved property place, the
mint check, then the pipeline), and `refEncodeEntry`, script encoding, which fails with the
reason or returns its scripts. The one text function is what makes the entry points fail "the
same way" (ruling D20).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.Seam Libpetri.Spec.Verifier

/-! ## Calls, answers and the reason text -/

/-- **A ν verification call**: the solver, the stop ([VER-013]), the options, the net the entry
point checks, the property, the initial marking, and the names given to the verifier as mint
transitions, in the order they were given. Places are `PlaceId`s, as in the other ν verifier
blocks; the block reads no place. -/
structure MintCall where
  /-- The solver. -/
  oracle : Oracle
  /-- The stop the call sees. -/
  stop : Stop
  /-- The options. -/
  opts : Options
  /-- The net the caller asks about: the caller's net for verification and script encoding,
  before any rewrite of the verifier's own; the closed net for open-net verification. -/
  net : Reference.TimedNet PlaceId
  /-- The property. -/
  prop : VerProp PlaceId
  /-- The initial marking. -/
  m0 : NMarking PlaceId
  /-- The names given to the verifier as mint transitions. -/
  mints : List String

/-- **What an entry point answers**: a verdict (verification, open-net verification), its
ordinary output (the scripts of script encoding), or a failure with a message (an exception, a
panic, a `ValueError`). -/
inductive MintAnswer where
  /-- A verdict. -/
  | verdict (v : Verdict)
  /-- The entry point's ordinary output, such as the scripts of script encoding. -/
  | output
  /-- A failure (exception, panic, `ValueError`) with its message. -/
  | fails (msg : String)
  deriving DecidableEq, Repr

/-- **The answer refuses with reason `m`**: a failure with message `m`, or `Unknown` with reason
`m`. -/
def MintRefuses (a : MintAnswer) (m : String) : Prop :=
  a = .fails m ∨ a = .verdict (.unknown m)

instance (a : MintAnswer) (m : String) : Decidable (MintRefuses a m) := by
  unfold MintRefuses; infer_instance

/-- The same call with no mint transition named. -/
def MintCall.undeclared (c : MintCall) : MintCall := { c with mints := [] }

/-- The transition names of the call's net. -/
def callTNames (c : MintCall) : List String := c.net.net.transitions.map (·.core.name)

/-- The declared names `ds` that are not among the transition names `ts`, each once, in
code-point order (Lean's `String` order compares code points). -/
def unknownMints (ts ds : List String) : List String :=
  ((ds.filter (fun x => x ∉ ts)).dedup).insertionSort (fun a b => a ≤ b)

/-- The reason text for the unknown names `xs`: `declared mint transition 'x' not in the net
(NU-010)` for one name, `declared mint transitions 'a', 'b' not in the net (NU-010)` for
several (Rust `unknown_mint_reason`, Java `NameFragment.unknownMintReason`, TypeScript
`unknownMintReason`). -/
def unknownMintText (xs : List String) : String :=
  "declared mint transition" ++ (if xs.length = 1 then "" else "s") ++ " " ++
    ", ".intercalate (xs.map fun x => "'" ++ x ++ "'") ++ " not in the net (NU-010)"

/-- **The reason** for the declaration `ds` on a net with transition names `ts`: `none` when
every declared name is a transition, else the text naming the unknown ones. -/
def unknownMintReason (ts ds : List String) : Option String :=
  if unknownMints ts ds = [] then none else some (unknownMintText (unknownMints ts ds))

/-- A name of the declaration that is not a transition is among the unknown names. -/
theorem mem_unknownMints {ts ds : List String} {x : String} :
    x ∈ unknownMints ts ds ↔ x ∈ ds ∧ x ∉ ts := by
  unfold unknownMints
  rw [List.mem_insertionSort, List.mem_dedup, List.mem_filter]
  simp

/-- The reason is given exactly when some declared name is not a transition. -/
theorem unknownMintReason_isSome {ts ds : List String} :
    (unknownMintReason ts ds).isSome ↔ ∃ x ∈ ds, x ∉ ts := by
  unfold unknownMintReason
  constructor
  · intro h
    split at h
    · simp at h
    · rename_i hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨x, (mem_unknownMints.1 hx).1, (mem_unknownMints.1 hx).2⟩
  · rintro ⟨x, hx, hn⟩
    have : unknownMints ts ds ≠ [] :=
      List.ne_nil_of_mem (mem_unknownMints.2 ⟨hx, hn⟩)
    simp [this]

/-- A declaration whose every name is a transition has no reason. -/
theorem unknownMintReason_none {ts ds : List String} (h : ∀ x ∈ ds, x ∈ ts) :
    unknownMintReason ts ds = none := by
  cases hr : unknownMintReason ts ds with
  | none => rfl
  | some r =>
    obtain ⟨x, hx, hn⟩ := unknownMintReason_isSome.1 (by rw [hr]; rfl)
    exact absurd (h x hx) hn

/-! ## The block -/

requirement NU_010_unknownMint
  id "NU-010"
  title "Fresh-Name Minting (a declared mint not in the net)"
  kind F
  scope "every entry point that takes a mint declaration: verification, script encoding ([VER-013]) and open-net verification ([VER-022]), all implementations (MUST where the ν routes are offered)"
  source verbatim "spec/12-nu-nets.md"
  quote "A declared mint that is not a transition of the net MUST be refused, by a failure or an `Unknown`, with the same reason naming it at every entry point (verification, script encoding ([VER-013]) and open-net verification ([VER-022])): `declared mint transition 'x' not in the net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several are not, each named once in code-point order."
        "A refusal that does not depend on the declaration, such as a stop before the call starts ([VER-013]) or an unresolved property place ([VER-003]), may come first, and that refusal is then the answer."
        "*If* a name given to the verifier as a mint transition is not a transition of the net, *then* verification, script encoding and open-net verification *shall* each refuse the request, by failing or by answering `Unknown`, and *shall not* answer `Proven` or `Violated` or return scripts."
        "*If* a name given to the verifier as a mint transition is not a transition of the net, *then* the reason of that refusal *shall* be `declared mint transition 'x' not in the net (NU-010)`, or `declared mint transitions 'a', 'b' not in the net (NU-010)` when several are not, naming each such name once and in code-point order, unless the same request with no mint transition named gets the same refusal."
        "*If* every name given to the verifier as a mint transition is a transition of the net, *then* verification, script encoding and open-net verification *shall not* refuse the request with the reason `declared mint transition 'x' not in the net (NU-010)` or `declared mint transitions 'a', 'b' not in the net (NU-010)`, whatever names it gives, unless the same request with no mint transition named gets the same refusal."
  reading "Let E be an entry point, from a call c (solver, stop, options, net, property, initial marking, and the names c.mints given as mint transitions) to an answer: a verdict, the entry point's ordinary output (scripts), or a failure with a message. E c refuses with m when it fails with message m or answers Unknown with reason m."
          "For every call c such that some name of c.mints is not a transition name of c.net: E c refuses with some reason;"
          "for every such c and reason m with which E c refuses: m is unknownMintReason of the transition names and c.mints, the text `declared mint transition 'x' not in the net (NU-010)` with each unknown name once, in code-point order, and `transitions` for several; or E answers the same call with no mint named exactly as it answers c;"
          "for every call c such that every name of c.mints is a transition name of c.net, and every list of names xs: if E c refuses with unknownMintText xs, the NU-010 text naming xs, then E answers the same call with no mint named exactly as it answers c."
  assumes "The model is one entry point E per call shape; verification, script encoding and open-net verification are three such E, and each meets the block with the one text function unknownMintReason, which is how the three are refused 'with the same reason' (ruling D20, nu-a NUA-10: 'the same way' was read as 'with the same reason text'). The mechanism is configuration (kind N) and the answer type folds it into a failure or an Unknown: Java throws IllegalArgumentException where the mint is declared, the open-net hook included (java/src/main/java/org/libpetri/smt/SmtVerifier.java:710-716, java/src/main/java/org/libpetri/smt/opennet/OpenNetVerifier.java:80-81); TypeScript throws where it is declared on a verifier (typescript/src/verification/smt-verifier.ts:536-543) and open-net verification answers Unknown (typescript/src/verification/open-net/verify-open-net.ts:93, :188-189); Rust answers Unknown from verification (rust/libpetri-verification/src/smt_verifier.rs:780, :1201-1219) and open-net verification (rust/libpetri-verification/src/open_net/verify_open_net.rs:194-200, :332) and panics from script encoding (SmtVerifier::encode_scripts); Python raises ValueError from script encoding (rust/libpetri-py/src/verification.rs:949-955) and answers as Rust from verification. The text is built by unknown_mint_reason in rust/libpetri-verification/src/name_fragment.rs, java/src/main/java/org/libpetri/analysis/NameFragment.java:122-138 and typescript/src/verification/analysis/name-fragment.ts:96-102: the unknown names deduplicated, sorted in code-point order, each in single quotes, joined by ', ', 'transition' for one name and 'transitions' for several. Each builder gives no text when every declared name is a transition of the net it is handed (unknown_mint_reason returns None on an empty list), and every runtime hands it c.net or a net that keeps every transition of c.net (read as below), so the third line holds of every runtime by construction."
          "Which names: the names given to the verifier (mintTransitions / mint_transitions, or a Java or TypeScript open-net configureSmt hook). A transition that consumes a declared budget place ([NU-040]) is declared too (declared_mints, name_fragment.rs:135-152), but it is a transition of the net by construction, so it never reaches this check. Java and TypeScript check each declaration call and throw at the first one that names an unknown transition, so the call's mints are the names declared up to that call; Rust checks the whole set when the entry point runs. Which net: c.net is the net the caller asks about: the caller's net for verification and script encoding, before any rewrite of the verifier's own, and the closed net for open-net verification, where all three runtimes check the declaration (verify_open_net.rs:194-200, verify-open-net.ts:93, OpenNetVerifier.java:80-81), so a name that only the closure adds, such as env:arrive[0]:p, is a transition of c.net there. Java and TypeScript check the caller's net at declaration (SmtVerifier.java:710-716, smt-verifier.ts:539) and TypeScript again in encodeScripts (smt-verifier.ts:1132, both on callerNet); Rust and Python script encoding check it too (encode_scripts, before with_arrivals; rust/libpetri-py/src/verification.rs:949-955), and so do Rust and Python verification: verify judges the declaration on the caller's net (smt_verifier.rs:780, before with_arrivals at :785) and verify_net answers that refusal before any route (:1201). The verifier's own rewrites, the Arrivals closure, the inert places, the in-flight split and the terminal rewrite, keep every transition of the caller's net and may add some, such as complete:t (completion_transition in in_flight.rs) or env:arrive?[0]:p under Arrivals(k) (close_arrivals in open_net/closure.rs, whose arrivals are all optional); a declaration of such a name is refused like any other name the caller's net lacks, at every entry point. An entry point that judged the rewritten net would accept it and answer a verdict, which breaks the first line; NU_010_unknownMint_forbids_rewrittenNet is that wrong entry point (the behaviour RD-38 recorded in spec/runtime-defects.md)."
          "Order of refusals: the second and third lines do not fix which refusal wins when the mint refusal meets one that does not depend on the declaration; they ask only that such a refusal be the answer the same call gets with no mint named. In Rust's verification the stop poll on entry ('net preparation', smt_verifier.rs:1146) and the unresolved property place refusal (smt_verifier.rs:1154) come before the mint check, and script encoding panics for a name-alignment property ([NU-055]) before it (encode_scripts); Java and TypeScript throw at declaration, so the mint refusal always comes first there. The reference refNuEntry follows Rust's order: the stop on entry, the unresolved place, the mint check, then the reference pipeline (pipeVerify). The lines read answers, so a refusal that came after the mint check but does not depend on the declaration also passes the second line; 'before any route runs' in the body (Rust) is the mechanism and not a line. The escape is needed: without it the second line rejects the reference, whose call that names frok and is cancelled before it starts gets the stop's reason (NU_010_unknownMint_escape_needed)."
          "What the block does not separate: the escapes accept any answer the same call with no mint named also gets, so an entry point that answers Unknown with one fixed reason to every call meets the block. The block tells a refusal for an unknown name, and the NU-010 text on a declaration of real transitions, from a refusal that does not depend on the declaration; it does not say that a declaration of real transitions leaves the verdict to the routes. That is AC4 ('Declared, it is Proven by Route B'), a verdict line that no block states (kind Q, NU_010.lean); refNuEntry_declared shows it for the reference."
          "Out of scope: the report sentences ('The report of a verdict from either route names the transitions whose mint contract it assumes', and the pointer when Route B declines only for an undeclared writer, undeclared_mints_pointer in name_fragment.rs) are report text (kind Q). The open-net note that the graph was skipped, 'a declared mint transition is not in the net (NU-010)' (verify_open_net.rs:164, verify-open-net.ts:65), is a report note, not the reason; an entry point whose reason is that note is forbidden (NU_010_unknownMint_forbids_vague). Open-net verification has no reference entry point here: its call carries a contract that MintCall does not (Spec/Verifier/OpenNet.lean, close and judge), so it is covered only as a third abstract E; a reference open-net entry is an open item."
          "AC6 ('A name given to the verifier as a mint transition that is not a transition of the net is refused, by a failure or an Unknown, with a reason naming it, unless a refusal that does not depend on the declaration is the answer; a name that is a transition of the net is not refused with that reason') is the three lines; its 'not refused with that reason' is the third line with its escape, since a refusal the same call with no mint named also gets does not come from the declaration. NU_010_unknownMint_nonvacuous works it on the net p0 -> t -> p1: the call that names frok is Unknown with `declared mint transition 'frok' not in the net (NU-010)`, the call that names z, frok, t and z again names frok and z once each, and script encoding fails with the same text; a call that names only t gets the reference verdict, Violated; a call cancelled before it starts gets `verification cancelled during net preparation`, as the same call with no mint named does."
  signoff "2026-11-13 f05b77a6fc501991 ai"
  statement : (MintCall → MintAnswer) → Prop :=
    fun E =>
      (∀ c, (∃ x ∈ c.mints, x ∉ callTNames c) → ∃ m, MintRefuses (E c) m) ∧
      (∀ c m, (∃ x ∈ c.mints, x ∉ callTNames c) → MintRefuses (E c) m →
        unknownMintReason (callTNames c) c.mints = some m ∨ E c.undeclared = E c) ∧
      (∀ c xs, (∀ x ∈ c.mints, x ∈ callTNames c) → MintRefuses (E c) (unknownMintText xs) →
        E c.undeclared = E c)

/- The pinned readable form of NU_010_unknownMint: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_010_unknownMint : (MintCall → MintAnswer) → Prop :=
fun E =>
  (∀ (c : MintCall), (∃ x ∈ c.mints, x ∉ callTNames c) → ∃ m, MintRefuses (E c) m) ∧
    (∀ (c : MintCall) (m : String),
        (∃ x ∈ c.mints, x ∉ callTNames c) →
          MintRefuses (E c) m → unknownMintReason (callTNames c) c.mints = some m ∨ E c.undeclared = E c) ∧
      ∀ (c : MintCall) (xs : List String),
        (∀ x ∈ c.mints, x ∈ callTNames c) → MintRefuses (E c) (unknownMintText xs) → E c.undeclared = E c
-/
#guard_msgs in #print NU_010_unknownMint

/-! ## The witnesses -/

/-- **The guard**: when `pre` holds (a refusal that does not read the declaration), answer as
`inner`; otherwise refuse with `refuse r` when the declaration names an unknown transition, and
answer as `inner` when it does not. -/
def mintGuard (pre : MintCall → Bool) (inner : MintCall → MintAnswer)
    (refuse : String → MintAnswer) : MintCall → MintAnswer := fun c =>
  if pre c then inner c else
    match unknownMintReason (callTNames c) c.mints with
    | some r => refuse r
    | none => inner c

/-- A guard refuses every call that names an unknown transition when `inner` refuses wherever
`pre` holds and every `refuse r` is a refusal (the first line). -/
theorem mintGuard_refuses {pre : MintCall → Bool} {inner : MintCall → MintAnswer}
    {refuse : String → MintAnswer}
    (hstop : ∀ c, pre c = true → ∃ m, MintRefuses (inner c) m)
    (hrefuse : ∀ r, ∃ m, MintRefuses (refuse r) m) (c : MintCall)
    (hbad : ∃ x ∈ c.mints, x ∉ callTNames c) : ∃ m, MintRefuses (mintGuard pre inner refuse c) m := by
  unfold mintGuard
  split
  · rename_i hp
    exact hstop c hp
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (unknownMintReason_isSome.2 hbad)
    rw [hr]
    exact hrefuse r

/-- A guard whose `pre` and `inner` do not read the declaration answers a call whose every mint
name is a transition as it answers the same call with no mint named (the third line). -/
theorem mintGuard_declared {pre : MintCall → Bool} {inner : MintCall → MintAnswer}
    {refuse : String → MintAnswer} (hpre : ∀ c, pre c.undeclared = pre c)
    (hinner : ∀ c, inner c.undeclared = inner c) (c : MintCall)
    (h : ∀ x ∈ c.mints, x ∈ callTNames c) :
    mintGuard pre inner refuse c.undeclared = mintGuard pre inner refuse c := by
  have hn : unknownMintReason (callTNames c) c.mints = none := unknownMintReason_none h
  have hu : unknownMintReason (callTNames c.undeclared) c.undeclared.mints = none :=
    unknownMintReason_none (by simp [MintCall.undeclared])
  unfold mintGuard
  rw [hpre c, hinner c, hu, hn]

/-- A guard meets the block when `pre` and `inner` do not read the declaration, `inner` refuses
wherever `pre` holds, and `refuse r` refuses with `r` and nothing else. -/
theorem mintGuard_meets {pre : MintCall → Bool} {inner : MintCall → MintAnswer}
    {refuse : String → MintAnswer} (hpre : ∀ c, pre c.undeclared = pre c)
    (hinner : ∀ c, inner c.undeclared = inner c)
    (hstop : ∀ c, pre c = true → ∃ m, MintRefuses (inner c) m)
    (hrefuse : ∀ r m, MintRefuses (refuse r) m ↔ m = r) :
    NU_010_unknownMint (mintGuard pre inner refuse) := by
  refine ⟨mintGuard_refuses hstop (fun r => ⟨r, (hrefuse r r).2 rfl⟩), fun c m hbad hm => ?_,
    fun c _ h _ => mintGuard_declared hpre hinner c h⟩
  by_cases hp : pre c = true
  · refine .inr ?_
    have hu : pre c.undeclared = true := (hpre c).trans hp
    simp only [mintGuard, hp, hu, if_true, hinner c]
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (unknownMintReason_isSome.2 hbad)
    have hE : mintGuard pre inner refuse c = refuse r := by
      simp only [mintGuard, hp, hr, Bool.false_eq_true, if_false]
    rw [hE, hrefuse] at hm
    exact .inl (hm ▸ hr)

/-- The refusals of the reference pipeline that do not read the declaration: a stop on entry
([VER-013]) and an unresolved property place ([VER-003]). -/
def pipePre (c : MintCall) : Bool :=
  (pollStop c.stop {}).1 || decide (Unresolved c.net c.prop c.m0)

/-- The reference pipeline of `Spec/Verifier/Pipeline.lean` on the call: `pipeVerify` with the
inert-place rewrite, the reference step list, the call's solver and stop. -/
def pipeInner (c : MintCall) : MintAnswer :=
  .verdict (pipeVerify inertAbs inertInvariants rtPipeline c.oracle c.stop c.opts c.net c.prop
    c.m0).verdict

/-- **The reference verification entry point**, in Rust's order: the stop on entry, the
unresolved property place, the mint check (`Unknown` with the reason), then the reference
pipeline. -/
def refNuEntry : MintCall → MintAnswer :=
  mintGuard pipePre pipeInner (fun r => .verdict (.unknown r))

/-- **The reference script-encoding entry point**: it fails with the reason (Rust's panic, the
Java and TypeScript exception, Python's `ValueError`) or returns its scripts. -/
def refEncodeEntry : MintCall → MintAnswer :=
  mintGuard (fun _ => false) (fun _ => .output) .fails

#spec_witness refNuEntry
#spec_witness refEncodeEntry

/-- Where the pipeline's own entry refusals apply, it refuses. -/
theorem pipeInner_refuses (c : MintCall) (h : pipePre c = true) :
    ∃ m, MintRefuses (pipeInner c) m := by
  unfold pipePre at h
  unfold pipeInner pipeVerify
  by_cases hs : (pollStop c.stop {}).1 = true
  · simp [hs, stoppedResult, MintRefuses]
  · have hu : Unresolved c.net c.prop c.m0 := by simpa [hs] using h
    simp [hs, hu, MintRefuses]

/-- ✓ **The reference verification entry point meets the block.** For example, on the net
`p0 → t → p1`, a call that names `frok` as a mint transition is `Unknown` with
`declared mint transition 'frok' not in the net (NU-010)`; a call cancelled before it starts is
`Unknown` with the stop's reason, as the same call with no mint named is. -/
@[evidence holds NU_010_unknownMint]
theorem NU_010_unknownMint_reference : NU_010_unknownMint refNuEntry :=
  mintGuard_meets (fun _ => rfl) (fun _ => rfl) pipeInner_refuses
    (fun r m => by simp [MintRefuses, eq_comm])

/-- ✓ **The reference script-encoding entry point meets the block.** For example, on the net
`p0 → t → p1`, encoding with `frok` named as a mint transition fails with
`declared mint transition 'frok' not in the net (NU-010)`, the text verification gives. -/
@[evidence holds NU_010_unknownMint]
theorem NU_010_unknownMint_encode : NU_010_unknownMint refEncodeEntry :=
  mintGuard_meets (fun _ => rfl) (fun _ => rfl) (fun _ h => by cases h)
    (fun r m => by simp [MintRefuses, eq_comm])

/-- A declaration whose every name is a transition changes nothing: the reference entry answers
as the reference pipeline. -/
theorem refNuEntry_declared (c : MintCall) (h : ∀ x ∈ c.mints, x ∈ callTNames c) :
    refNuEntry c = pipeInner c := by
  have hn : unknownMintReason (callTNames c) c.mints = none := unknownMintReason_none h
  unfold refNuEntry mintGuard
  split
  · rfl
  · rw [hn]

/-! ## Worked example (AC6) -/

/-- A call on the AC11 net `p0 → t → p1` from `{p0: 1}` with the property `DeadlockFree` with
sink `p1`, no stop, a solver that answers `sat`, naming the mint transitions `ds`. -/
def nu010Call (ds : List String) : MintCall :=
  { oracle := satOracle, stop := noStop, opts := {}, net := ver003X,
    prop := .deadlockFree [1] [], m0 := ver003P0, mints := ds }

/-- ✓ Worked example (AC6). On the net `p0 → t → p1`, naming `frok` as a mint transition makes
verification answer `Unknown` with `declared mint transition 'frok' not in the net (NU-010)`
and script encoding fail with the same text. Naming `z`, `frok`, `t` and `z` again names
`frok` and `z`, once each, in code-point order. Naming only `t`, which is a transition, changes
nothing: the answer is the reference verdict, `Violated`. Cancelled before it starts, the call
that names `frok` is `Unknown` with `verification cancelled during net preparation`, as the
same call with no mint named is. -/
@[evidence nonvacuous NU_010_unknownMint]
theorem NU_010_unknownMint_nonvacuous :
    refNuEntry (nu010Call ["frok"]) =
        .verdict (.unknown "declared mint transition 'frok' not in the net (NU-010)") ∧
      refEncodeEntry (nu010Call ["frok"]) =
        .fails "declared mint transition 'frok' not in the net (NU-010)" ∧
      refNuEntry (nu010Call ["z", "frok", "t", "z"]) =
        .verdict (.unknown "declared mint transitions 'frok', 'z' not in the net (NU-010)") ∧
      refNuEntry (nu010Call ["t"]) = .verdict .violated ∧
      refNuEntry { nu010Call ["frok"] with stop := stopFrom 0 .cancelled } =
        .verdict (.unknown "verification cancelled during net preparation") ∧
      refNuEntry { nu010Call ["frok"] with stop := stopFrom 0 .cancelled }.undeclared =
        refNuEntry { nu010Call ["frok"] with stop := stopFrom 0 .cancelled } := by
  decide

/-! ## Forbidden entry points -/

/-- An entry point that ignores the declaration and runs the pipeline as if every name were a
transition. -/
def nu010IgnoreEntry : MintCall → MintAnswer := pipeInner

/-- ✗ Worked example: an entry point that ignores a mint declaration it cannot resolve. On the
net `p0 → t → p1`, the call that names `frok` gets `Violated` from the pipeline, so a typo in the
declaration goes unnoticed. The first line fails: the call must be refused. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_ignore : ¬ NU_010_unknownMint nu010IgnoreEntry := by
  intro h
  obtain ⟨m, hm⟩ := h.1 (nu010Call ["frok"]) (by decide)
  have he : nu010IgnoreEntry (nu010Call ["frok"]) = .verdict .violated := by decide
  rw [he] at hm
  simp [MintRefuses] at hm

/-- The block without its first line: only the reason of a refusal is fixed. -/
def NU_010_unknownMint_mutant_reasonOnly (E : MintCall → MintAnswer) : Prop :=
  (∀ c m, (∃ x ∈ c.mints, x ∉ callTNames c) → MintRefuses (E c) m →
    unknownMintReason (callTNames c) c.mints = some m ∨ E c.undeclared = E c) ∧
  (∀ c xs, (∀ x ∈ c.mints, x ∈ callTNames c) → MintRefuses (E c) (unknownMintText xs) →
    E c.undeclared = E c)

/-- ✗ Worked example: the entry point that ignores the declaration answers every call as it
answers the same call with no mint named, so the second and third lines alone accept it. The
first line rules it out. -/
@[evidence mutant NU_010_unknownMint]
theorem NU_010_unknownMint_mutant_reasonOnly_killed :
    NU_010_unknownMint_mutant_reasonOnly nu010IgnoreEntry ∧
      ¬ NU_010_unknownMint nu010IgnoreEntry :=
  ⟨⟨fun _ _ _ _ => .inr rfl, fun _ _ _ _ => rfl⟩, NU_010_unknownMint_forbids_ignore⟩

/-- An entry point that refuses with the open-net note `a declared mint transition is not in the
net (NU-010)`, which does not name the transition. -/
def nu010VagueEntry : MintCall → MintAnswer :=
  mintGuard pipePre pipeInner
    (fun _ => .verdict (.unknown "a declared mint transition is not in the net (NU-010)"))

/-- ✗ Worked example: on the net `p0 → t → p1`, the call that names `frok` is refused with
`a declared mint transition is not in the net (NU-010)`. The caller cannot tell which name is
wrong, and without the declaration the call is `Violated`, so no earlier refusal explains the
text. The second line fails: the reason names `frok`. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_vague : ¬ NU_010_unknownMint nu010VagueEntry := by
  intro h
  have := h.2.1 (nu010Call ["frok"]) "a declared mint transition is not in the net (NU-010)"
    (by decide) (by decide)
  revert this
  decide

/-- The block without its second line: a refusal, with any reason. -/
def NU_010_unknownMint_mutant_refuseOnly (E : MintCall → MintAnswer) : Prop :=
  (∀ c, (∃ x ∈ c.mints, x ∉ callTNames c) → ∃ m, MintRefuses (E c) m) ∧
  (∀ c xs, (∀ x ∈ c.mints, x ∈ callTNames c) → MintRefuses (E c) (unknownMintText xs) →
    E c.undeclared = E c)

/-- ✗ Worked example: the vague entry point refuses every call that names an unknown mint
transition and leaves a declaration of real transitions alone, so the first and third lines
alone accept it. The second line rules it out. -/
@[evidence mutant NU_010_unknownMint]
theorem NU_010_unknownMint_mutant_refuseOnly_killed :
    NU_010_unknownMint_mutant_refuseOnly nu010VagueEntry ∧
      ¬ NU_010_unknownMint nu010VagueEntry :=
  ⟨⟨mintGuard_refuses pipeInner_refuses (fun _ => ⟨_, .inr rfl⟩),
      fun c _ h _ => mintGuard_declared (fun _ => rfl) (fun _ => rfl) c h⟩,
    NU_010_unknownMint_forbids_vague⟩

/-- The unknown names as declared: in declaration order, repeats kept. -/
def nu010AsDeclared (ts ds : List String) : List String := ds.filter (fun x => x ∉ ts)

/-- An entry point that names the unknown transitions in declaration order, repeats kept. -/
def nu010AsDeclaredEntry : MintCall → MintAnswer := fun c =>
  if pipePre c then pipeInner c else
    match nu010AsDeclared (callTNames c) c.mints with
    | [] => pipeInner c
    | xs => .verdict (.unknown (unknownMintText xs))

/-- ✗ Worked example: on the net `p0 → t → p1`, naming `z`, `frok` and `z` again is refused
with `declared mint transitions 'z', 'frok', 'z' not in the net (NU-010)`. Every runtime gives
`declared mint transitions 'frok', 'z' not in the net (NU-010)`: each name once, in code-point
order, so the text does not depend on how the names were declared. The second line fails. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_asDeclared : ¬ NU_010_unknownMint nu010AsDeclaredEntry := by
  intro h
  have := h.2.1 (nu010Call ["z", "frok", "z"])
    "declared mint transitions 'z', 'frok', 'z' not in the net (NU-010)" (by decide) (by decide)
  revert this
  decide

/-- An entry point that stops at the first declared name that is not a transition and names
only that one, as a loop that throws at the first bad name would. -/
def nu010FirstOnlyEntry : MintCall → MintAnswer := fun c =>
  if pipePre c then pipeInner c else
    match c.mints.find? (fun x => decide (x ∉ callTNames c)) with
    | some x => .verdict (.unknown (unknownMintText [x]))
    | none => pipeInner c

/-- ✗ Worked example: on the net `p0 → t → p1`, naming `z` and then `frok` is refused with
`declared mint transition 'z' not in the net (NU-010)`, so the caller fixes `z` and only then
learns about `frok`. Every runtime names both at once, as
`declared mint transitions 'frok', 'z' not in the net (NU-010)`. The second line fails. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_firstOnly : ¬ NU_010_unknownMint nu010FirstOnlyEntry := by
  intro h
  have := h.2.1 (nu010Call ["z", "frok"]) "declared mint transition 'z' not in the net (NU-010)"
    (by decide) (by decide)
  revert this
  decide

/-- A wrong entry point that checks the declared names against its own rewritten net: the
caller's transitions plus `complete:t`, the transition the in-flight split adds for `t` (the
behaviour RD-38 recorded for Rust and Python `SmtVerifier::verify`, whose check ran after the
verifier's rewrites). -/
def nu010RewrittenEntry : MintCall → MintAnswer := fun c =>
  if pipePre c then pipeInner c else
    match unknownMintReason (callTNames c ++ ["complete:t"]) c.mints with
    | some r => .verdict (.unknown r)
    | none => pipeInner c

/-- On the net `p0 → t → p1`, the call that names `complete:t` gets `Violated` from the entry
point that checks the rewritten net, and script encoding of the same call fails with the NU-010
reason: the two entry points answer one request in two ways. -/
theorem nu010_rewritten_vs_encode :
    nu010RewrittenEntry (nu010Call ["complete:t"]) = .verdict .violated ∧
      refEncodeEntry (nu010Call ["complete:t"]) =
        .fails "declared mint transition 'complete:t' not in the net (NU-010)" := by
  decide

/-- ✗ Worked example (the behaviour RD-38 recorded): on the net `p0 → t → p1`, a call that names
`complete:t`, which is not a transition of the caller's net, is answered `Violated` by a wrong
entry point that checks the names against its own rewritten net, where the in-flight split added
`complete:t`. Script encoding of the same call fails with `declared mint transition 'complete:t'
not in the net (NU-010)`, and every runtime refuses it in verification too. The first line fails:
the call must be refused. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_rewrittenNet : ¬ NU_010_unknownMint nu010RewrittenEntry := by
  intro h
  obtain ⟨m, hm⟩ := h.1 (nu010Call ["complete:t"]) (by decide)
  rw [nu010_rewritten_vs_encode.1] at hm
  simp [MintRefuses] at hm

/-- The text of an entry point that picks `transition` or `transitions` by counting the unknown
names before it drops the repeats. -/
def nu010PluralText (ts ds : List String) : String :=
  "declared mint transition" ++
    (if (ds.filter (fun x => x ∉ ts)).length = 1 then "" else "s") ++ " " ++
    ", ".intercalate ((unknownMints ts ds).map fun x => "'" ++ x ++ "'") ++
    " not in the net (NU-010)"

/-- An entry point that refuses with `nu010PluralText`. -/
def nu010PluralEntry : MintCall → MintAnswer := fun c =>
  if pipePre c then pipeInner c else
    if unknownMints (callTNames c) c.mints = [] then pipeInner c else
      .verdict (.unknown (nu010PluralText (callTNames c) c.mints))

/-- ✗ Worked example: on the net `p0 → t → p1`, naming `frok` twice is refused with
`declared mint transitions 'frok' not in the net (NU-010)`, plural for a single name, because
the count was taken before the repeat was dropped. Every runtime says
`declared mint transition 'frok' not in the net (NU-010)`. The second line fails. -/
@[evidence forbids NU_010_unknownMint]
theorem NU_010_unknownMint_forbids_plural : ¬ NU_010_unknownMint nu010PluralEntry := by
  intro h
  have := h.2.1 (nu010Call ["frok", "frok"])
    "declared mint transitions 'frok' not in the net (NU-010)" (by decide) (by decide)
  revert this
  decide

/-- An entry point that handles unknown names as the reference does, but also refuses a
declaration whose names are all transitions, with the NU-010 text naming them, as a second check
against the wrong net would. -/
def nu010FalseRefuseEntry : MintCall → MintAnswer := fun c =>
  if pipePre c then pipeInner c else
    match unknownMintReason (callTNames c) c.mints with
    | some r => .verdict (.unknown r)
    | none => if c.mints = [] then pipeInner c else .verdict (.unknown (unknownMintText c.mints))

/-- Where some declared name is not a transition, the false-refusal entry point answers the call,
and the same call with no mint named, as the reference does. -/
theorem nu010FalseRefuse_agrees (c : MintCall) (h : ∃ x ∈ c.mints, x ∉ callTNames c) :
    nu010FalseRefuseEntry c = refNuEntry c ∧
      nu010FalseRefuseEntry c.undeclared = refNuEntry c.undeclared := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (unknownMintReason_isSome.2 h)
  have hu : unknownMintReason (callTNames c.undeclared) c.undeclared.mints = none :=
    unknownMintReason_none (by simp [MintCall.undeclared])
  refine ⟨?_, ?_⟩
  · unfold nu010FalseRefuseEntry refNuEntry mintGuard
    split <;> simp [hr]
  · unfold nu010FalseRefuseEntry refNuEntry mintGuard
    split
    · rfl
    · rw [hu]; simp [MintCall.undeclared]

/-- The block without its third line. -/
def NU_010_unknownMint_mutant_unknownOnly (E : MintCall → MintAnswer) : Prop :=
  (∀ c, (∃ x ∈ c.mints, x ∉ callTNames c) → ∃ m, MintRefuses (E c) m) ∧
  (∀ c m, (∃ x ∈ c.mints, x ∉ callTNames c) → MintRefuses (E c) m →
    unknownMintReason (callTNames c) c.mints = some m ∨ E c.undeclared = E c)

/-- ✗ Worked example: on the net `p0 → t → p1`, naming `t`, which is a transition, is refused
with `declared mint transition 't' not in the net (NU-010)`, where the reference answers
`Violated`. On every call that names an unknown transition this entry point answers as the
reference, so the first two lines accept it. The third line rules it out: without the
declaration the call is `Violated`, so the declaration caused a refusal that says something
false. -/
@[evidence mutant NU_010_unknownMint]
theorem NU_010_unknownMint_mutant_unknownOnly_killed :
    NU_010_unknownMint_mutant_unknownOnly nu010FalseRefuseEntry ∧
      ¬ NU_010_unknownMint nu010FalseRefuseEntry := by
  have href := NU_010_unknownMint_reference
  refine ⟨⟨fun c hb => ?_, fun c m hb hm => ?_⟩, fun h => ?_⟩
  · rw [(nu010FalseRefuse_agrees c hb).1]; exact href.1 c hb
  · obtain ⟨h1, h2⟩ := nu010FalseRefuse_agrees c hb
    rw [h1] at hm ⊢; rw [h2]; exact href.2.1 c m hb hm
  · have := h.2.2 (nu010Call ["t"]) ["t"] (by decide) (by decide)
    revert this
    decide

/-- The second line without its escape: every refusal of a call that names an unknown
transition has the NU-010 reason. -/
def NU_010_unknownMint_strictReason (E : MintCall → MintAnswer) : Prop :=
  ∀ c m, (∃ x ∈ c.mints, x ∉ callTNames c) → MintRefuses (E c) m →
    unknownMintReason (callTNames c) c.mints = some m

/-- The escape of the second line is needed: on the net `p0 → t → p1`, the call that names
`frok` and is cancelled before it starts gets the stop's reason, not the NU-010 text, so the
second line without its escape rejects the reference. -/
theorem NU_010_unknownMint_escape_needed : ¬ NU_010_unknownMint_strictReason refNuEntry := by
  intro h
  have := h { nu010Call ["frok"] with stop := stopFrom 0 .cancelled }
    "verification cancelled during net preparation" (by decide) (by decide)
  revert this
  decide

end Libpetri.Spec
