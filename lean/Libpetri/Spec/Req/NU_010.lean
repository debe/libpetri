import Mathlib.Data.String.Basic
import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Reference.Nu
import Libpetri.Reference.NuMint
import Libpetri.Novel.RouteA.Plan
import Libpetri.Spec.Req.NU_051

set_option linter.missingDocs true

/-!
# NU-010: Fresh-Name Minting (`spec/12-nu-nets.md`)

An action mints a fresh name with `freshName()` and writes it into the tokens it produces, so the
sibling tokens of a fork share one correlation name that a matched join ([NU-020]) later joins
on. The verifier cannot tell a minting action from one that copies a correlation id, so it reads
a transition as a mint only when the net declares it, and then assumes the mint contract.

Four blocks share the ID:

* `NU_010_unique` (kind B), over a minting system `Sy : MintSys` (`Reference/NuMint.lean`): every
  run from an executor's initial state, interleaving `freshName()` calls and firing boundaries,
  returns pairwise distinct names, two calls in one firing included.
* `NU_010_replay` (kind F), over the same `Sy`: two runs from one scope whose calls come from the
  same transitions in the same order return the same names, wherever the firing boundaries fall
  (ruling D56 (a): the names follow the order of the calls, not the order of the firings).
* `NU_010_contract` (kind A), over one firing of a declared mint: every name it writes into a
  coloured place was minted in that firing, and it writes one name, the same everywhere (ruling
  D78 (a)). `nu010_contract_fresh` shows what this buys with the reference minter: the name is
  held in no coloured place, which is `MintContract`, the premise of Route B's soundness through
  `mintContract_iff_routeB`.
* `NU_010_classify` (kind F), over a fragment classifier `C : Classifier`
  (`Spec/GlossaryNuVer.lean`): only a declared mint gets the mint role, an undeclared writer of a
  coloured place gets no role, a transition whose timeout writes a coloured place is never a
  mint, a transition with a match specification or a coloured input is never a mint, a declared
  mint inside the fragment rules gets the mint role, and a transition with no match
  specification and no coloured input whose timeout writes a coloured place gets no role.

A fifth block, `NU_010_unknownMint` (kind F, `Spec/Req/NU_010_ac6.lean`), states AC6: a name
given to the verifier as a mint transition that is not a transition of the net is refused, with
the reason `declared mint transition 'x' not in the net (NU-010)` at every entry point, and a
declaration whose names are all transitions is never refused with that reason.

The witnesses are `refMintSys` and `refClassify`. The offer "the action context gives every call a
name" is not a line: it is the coverage conjunct `MintTotal` (`refMintSys_total`), because a
minter that never answers meets every "for every run" line. The fallback minter used without an
executor is not a block either: `nu010_fallback_unique` shows that it returns distinct names.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## NU-010, uniqueness -/

requirement NU_010_unique
  id "NU-010"
  title "Fresh-Name Minting (uniqueness)"
  kind B
  scope "the minter every executor installs on the action context"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* an action calls `freshName()`, the executor *shall* return a name that differs from every name it returned earlier in the same execution, whether the earlier call came in the same firing or in an earlier one."
  reading "Let Sy be a minting system (MintSys): a state, an initial state per scope, the mint relation of one freshName() call (state, calling transition, returned name, next state) and the step at a firing boundary."
          "For every scope s and every run of Sy from its initial state for s, a sequence of freshName() calls and firing boundaries in any interleaving, the names the calls return are pairwise distinct."
  assumes "The model is one minting system Sy, the minter of one executor. One execution is one run from the initial state for the executor's scope: a call returns a name and moves the state, a firing boundary moves the state by next. The reference refMintSys keeps the scope and ONE counter shared by every transition of the executor, starting at 0; a call by t returns t#scope:counter and advances the counter, and a firing boundary changes nothing. This is rust/libpetri-runtime/src/executor_core/executor.rs:180 and :203-217 (fresh_name_counter, fetch_add), java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java:1737-1739 and PrecompiledNetExecutor.java:436 and :465 (getAndIncrement), typescript/src/runtime/bitmap-net-executor.ts:1125-1126 and precompiled-net-executor.ts:1227. The state type is abstract, so a minter with a different state (NU-011's high-water mark) is a model too."
          "Names minted by another execution, a restored one included, are NU-011's: the scope keeps them apart (NU_011). The name format t#scope:n and the scope check are NU-011's lines."
          "The offer half ('A transition action MAY mint a fresh name via the action context'): every call is answered. A minter whose mint relation is empty meets this line vacuously, so the offer is the coverage conjunct MintTotal of the consistency theorem (refMintSys_total), not a line here."
          "'The executor installs the minter, one counter shared by all its transitions ([NU-011])': that the counter is one per executor, shared by every transition, is NU_011_format's last line (the i-th call, counting across all firings and transitions, returns t#s:i). A minter with one counter per transition that puts the transition into the name meets this line and the replay line, and NU_011_format rules it out. 'So the names follow the order of the freshName() calls, not the order of the firings' is the replay line."
          "'Absent an executor-installed minter, a fallback still guarantees uniqueness': which minter an action context uses when no executor installed one is configuration (kind N), and the fallback is not a line. Its uniqueness is cited by nu010_fallback_unique. The fallback is a process-wide counter that other action contexts may advance between two calls; Rust and TypeScript mint t#n (rust/libpetri-core/src/context.rs:204-212, typescript/src/core/transition-context.ts:19 and :308), Java mints t#<detached scope>:n (java/src/main/java/org/libpetri/core/TransitionContext.java:488-497). The theorem shows that both formats give pairwise distinct names in every run, from any counter value. The fallback is not replay-stable, and the body does not claim it is."
          "AC1 (two freshName() calls, within one firing or across firings, return unequal names) is the line. NU_010_unique_nonvacuous works it: two calls in one firing and one in the next return fork#s:0, fork#s:1 and fork#s:2. A counter reset at each firing boundary (NU_010_unique_forbids_resetPerFiring) and a counter per transition with the transition left out of the name (NU_010_unique_forbids_perTransition) are forbidden. The test derivation's three source tokens giving three distinct names is the same example; the join of each pair is NU_010_contract_nonvacuous."
  signoff "2026-11-13 fb41e4666108fdc8 ai"
  statement : MintSys → Prop :=
    fun Sy => ∀ s evs xs, MintRun Sy (Sy.init s) evs xs → xs.Nodup

/- The pinned readable form of NU_010_unique: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_010_unique : MintSys → Prop :=
fun Sy => ∀ (s : String) (evs : List MintEv) (xs : List String), MintRun Sy (Sy.init s) evs xs → xs.Nodup
-/
#guard_msgs in #print NU_010_unique

/-! ## NU-010, replay -/

requirement NU_010_replay
  id "NU-010"
  title "Fresh-Name Minting (replay)"
  kind F
  scope "the minter every executor installs on the action context"
  source verbatim "spec/12-nu-nets.md"
  quote "For a fixed scope and a fixed sequence of calling transitions, the executor *shall* return the same sequence of names to the `freshName()` calls, whichever firings the calls fall in."
  reading "For every scope s and every two runs of Sy from its initial state for s whose calls come from the same transitions in the same order (the firing boundaries may fall anywhere), the two runs return the same names."
  assumes "Ruling D56 (a): replay is a MUST keyed on the scope and the order of the freshName() calls, not on the order of the firings. One counter per executor is read when the action calls the minter, so two minting actions in flight at once (a Rust async action runs under tokio::spawn, rust/libpetri-runtime/src/executor_core/executor.rs:1679) may call it in either order; with one minting action in flight at a time, or synchronous actions only (executor_core/executor.rs:1491-1507), the call order is the firing order. Which order the calls come in is the executor's (RefExec), not the minter's, so the line needs no executor model. The sentence 'with one minting action in flight at a time the two orders agree, and actions that run concurrently may call the minter in either order' explains what the key means for the firings and adds no obligation."
          "The line starts every run from the initial state for the scope. A restored execution is NU-011's: every runtime resumes under a new scope (NU_011_lineage, with the host assumption NU_011_host), and the other mechanism NU-011 names, a restored high-water mark, is used by no runtime and is outside NU_011_format. Replay of a restored execution is the replay of a run under its own scope, which this line covers."
          "'What replays is the sequence within a minting scope': the default scope is drawn at random per executor (NU-011), so a host that needs the whole name reproduced pins the scope, and a test compares names structurally. The line fixes the scope; the default scope and its randomness are NU-011's."
          "AC3 (for a fixed sequence of calling transitions and a fixed scope, the sequence of minted names is reproducible) is the line. NU_010_replay_nonvacuous works it: [fork, fork] in one firing and [fork | fork] over two firings both return fork#s:0, fork#s:1. A minter that may return any unused name is unique but not reproducible (NU_010_replay_forbids_anyUnused, and NU_010_replay_mutant_uniqueOnly shows that uniqueness alone allows it); a counter that also moves at each firing boundary is unique and a function of its state, but keyed on the firings (NU_010_replay_forbids_boundaryTick)."
  signoff "2026-11-13 9dffc6d46a47f3cc ai"
  statement : MintSys → Prop :=
    fun Sy => ∀ s evs evs' xs ys, calls evs = calls evs' →
      MintRun Sy (Sy.init s) evs xs → MintRun Sy (Sy.init s) evs' ys → xs = ys

/- The pinned readable form of NU_010_replay: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_010_replay : MintSys → Prop :=
fun Sy =>
  ∀ (s : String) (evs evs' : List MintEv) (xs ys : List String),
    calls evs = calls evs' → MintRun Sy (Sy.init s) evs xs → MintRun Sy (Sy.init s) evs' ys → xs = ys
-/
#guard_msgs in #print NU_010_replay

/-! ## NU-010, the mint contract -/

requirement NU_010_contract
  id "NU-010"
  title "Fresh-Name Minting (mint contract)"
  kind A
  scope "the action of every declared mint, as the ν verification routes assume it"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* a declared mint that has no input arc on a coloured place fires, every name it writes into a coloured place *shall* be a name it minted with `freshName()` in that firing."
        "*When* a declared mint that has no input arc on a coloured place fires, every name it writes into coloured places *shall* be one and the same name, whether in one place or in several."
  reading "For one firing of a declared mint that has no input arc on a coloured place, let minted be the names its freshName() calls returned in that firing and wr c the names it writes into coloured place c:"
          "every name written into a coloured place is in minted;"
          "any two names written into coloured places, the same place or two places, are equal."
  assumes "The block is an assumption on the net author (kind A), not a behaviour of the executor: an action may write any value into a match key, a correlation id copied from its input included, and no analysis can tell a minting action from a copying one (the stock fork() action copies its input). No runtime checks it. The statement reads only what one firing minted and what it wrote into the coloured places, so it is a predicate on the action whatever executor runs it."
          "Ruling D78 (a): one fresh name per firing, the same in every coloured place it writes, which is what the analyses assume. The per-place reading (a fresh name in each place, two places possibly getting two different names) is set aside: Reference.eachFresh_not_mintContract shows it is weaker, and NU_010_contract_forbids_twoNames that the second line rules it out. The second line also covers two tokens in ONE place ('whether in one place or in several'): a reading that compares only two different places allows two fresh names in one place, and NU_010_contract_mutant_otherPlaces_killed rules it out."
          "The contract restricts what a firing writes and obliges no write: a firing that writes no coloured place keeps it ('Every name a declared mint writes ... MUST be ...' speaks of the names written). nu010_contract_fresh therefore asks, besides the contract, that the firing minted a name, so that MintContract has a name to give."
          "What the assumption buys is nu010_contract_fresh: with the reference minter, a firing that keeps the contract writes a name held in no coloured place, whenever every held name was minted earlier in the run or under another scope of the restore lineage (NU-011). That is Reference.MintContract, and Reference.mintContract_iff_routeB makes it Novel.RouteB.Contract at Role.mint, the premise of Route B's soundness ([NU-050]). On the reference ν executor the contract both routes' runs keep is this MintContract too: NuLink.nuContract_mint_iff (Route B) and NuLinkA.nuContract_mint_iff (Route A), which NU_050_soundB and NU_050_soundA cite. The assumption is load-bearing: a declared mint that copies its input breaks the Route B simulation (Novel.RouteB.copyingMint_breaks_simulation)."
          "Which transitions are declared mints ('by naming it as a mint transition on the verifier (`mintTransitions` / `mint_transitions`)', or 'by its consuming a declared budget place ([NU-040])') is the declaration the verifier computes (declared_mints, rust/libpetri-verification/src/name_fragment.rs:135-152); the classifier takes it as an input (NU_010_classify), the budget half is NU-040's line, and the named half (the names given to the verifier are declared) is a line of the verifier pipeline (open); a name given to the verifier that is not a transition of the net is refused (AC6, NU_010_unknownMint in Spec/Req/NU_010_ac6.lean). 'into a coloured place ([NU-051], [NU-054]) it writes without consuming one': the scope of the block is a declared mint with no input arc on a coloured place, as both quoted sentences now say. A declared mint that consumes a coloured place, such as a matched join that takes a permit from a declared budget place and relays its chosen name (NU-054) to a coloured relay target, writes a name it did not mint, and the contract does not bind it: NU-040 declares every transition with an input arc on a budget place (rust/libpetri-verification/src/name_fragment.rs:140-152), but the classifier gives such a transition the join or consume role and never the mint role (NU_010_classify's fourth line), so no verdict reads it as a mint."
          "AC2 (a fork that stamps both AND-branches with one minted name produces sibling tokens that a NU-020 join later correlates) is NU_010_contract_nonvacuous: the reference fork mints fork#s:0, writes it into places 1 and 2, keeps the contract, and the reference join on 1 and 2 then fires with that name and takes one token from each."
          "AC4 (the stock fork() copies its input: placeBound(DONE, 0) is not Proven unless mA and mB are declared; declared, Route B proves it and the report names mA, mB under the mint contract) is a verdict and report line ([NU-050]) that no block states (kind Q): Rust rust/libpetri/tests/nu_mint_contract a_copying_producer_is_not_read_as_a_mint_unless_declared and Java NuMintContractTest aCopyingProducerIsNotReadAsAMintUnlessDeclared check it, and refNuEntry_declared (NU_010_ac6.lean) shows that the reference entry point leaves a declaration of real transitions to the routes; the counterexample to the undeclared reading is Novel.RouteB.copyingMint_breaks_simulation."
  signoff "2026-11-13 71f124af5f453a48 ai"
  statement : ∀ {C Nm : Type}, List Nm → (C → List Nm) → Prop :=
    fun minted wr =>
      (∀ c, ∀ w ∈ wr c, w ∈ minted) ∧
      (∀ c c', ∀ w ∈ wr c, ∀ w' ∈ wr c', w = w')

/- The pinned readable form of NU_010_contract: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_010_contract : {C Nm : Type} → List Nm → (C → List Nm) → Prop :=
fun {C Nm} minted wr => (∀ (c : C), ∀ w ∈ wr c, w ∈ minted) ∧ ∀ (c c' : C), ∀ w ∈ wr c, ∀ w' ∈ wr c', w = w'
-/
#guard_msgs in #print NU_010_contract

/-! ## NU-010, the verifier reads only declared mints -/

requirement NU_010_classify
  id "NU-010"
  title "Fresh-Name Minting (declared mints in the fragment classifier)"
  kind F
  scope "the fragment classifier of every ν verifier"
  source verbatim "spec/12-nu-nets.md"
  quote "The fragment classifier ([NU-051]) *shall* give the mint role only to a declared mint."
        "*If* a transition without a match specification has no input arc on a coloured place, writes a coloured place and is not a declared mint, *then* the fragment classifier *shall* give it no role."
        "*If* the timeout outcome of a transition writes a coloured place, *then* the fragment classifier *shall not* give it the mint role."
        "The fragment classifier *shall not* give the mint role to a transition that has a match specification or an input arc on a coloured place."
        "*If* a declared mint has no match specification, no input arc on a coloured place and no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, writes a coloured place in some outcome and on timeout writes no coloured place, *then* the fragment classifier *shall* give it the mint role, in both BASE and EXTENDED."
        "*If* a transition without a match specification has no input arc on a coloured place and its timeout outcome writes a coloured place, *then* the fragment classifier *shall* give it no role."
  reading "For every coloured set col, fragment mode, list of timeout writes tw and transition T:"
          "C gives an undeclared T no mint role;"
          "if T has no match keys, none of its input arcs is on a coloured place, some branch outcome of T deposits into a coloured place and T is not declared, C gives T no role;"
          "if some timeout write of T is into a coloured place, C gives T no mint role, declared or not;"
          "if C gives T the mint role, T has no match keys and none of its input arcs is on a coloured place;"
          "if T is declared, has no match keys, no input arc on a coloured place and no reset, read or inhibitor arc on a coloured place, every branch puts one token and no drained batch into each coloured place it writes, some branch deposits into a coloured place and no timeout write is into a coloured place, C gives T the mint role;"
          "if T has no match keys, none of its input arcs is on a coloured place, every timeout write of T is into a place some outcome of T deposits into, and some timeout write is into a coloured place, C gives T no role, declared or not."
  assumes "The model is one fragment classifier C, per transition, as the glossary term Fragment classifier reads it (GlossaryNuVer): from the coloured set, the mode, whether the transition is a declared mint, its timeout writes and the transition, a role or none. No role means the net falls back to the name-blind over-approximation ([NU-050]); Rust's classify returns no fragment as soon as one transition is refused (classify in rust/libpetri-verification/src/name_fragment.rs, its per-transition early returns). That step, from one transition with no role to the net leaving Route B, is the pipeline's, not the classifier's, and no block states it: the pipeline model (Verifier/Pipeline.lean) does not model Route B's entry. The witness refClassify is Novel.RouteB.classifyS. Whether a transition is declared ('by naming it as a mint transition on the verifier', or 'by its consuming a declared budget place ([NU-040])') is an input; the budget half is NU-040's line and the named half a line of the verifier pipeline (open); a name given to the verifier that is not a transition of the net is refused (AC6, NU_010_unknownMint in Spec/Req/NU_010_ac6.lean)."
          "'Consumes' and 'without consuming one' are read as an input arc, the ColouredInputs of the glossary. A reset, read or inhibitor arc on a coloured place gives the transition no role at all (NU_051's fourth line), so the lines hold under either reading of reset arcs, and the fifth line asks for no such arc."
          "The fourth line is the shape of a mint in the body ('read a transition as a **mint**, one that writes a fresh name'; a declared mint writes into each coloured place 'it writes without consuming one'): a matched join takes its name from its keys ([NU-020]) and a coloured consumer is NU-051's, so neither is ever a mint, even when the declaration names it (declared_mints declares every transition that consumes a declared budget place, a join taking a permit included). A classifier that tests the declaration before the match specification gives such a join the mint role under BASE, where no admission line of NU-054 speaks for it; the fourth line forbids it (NU_010_classify_mutant_joinMint_killed)."
          "The fifth line is the admission ('Declared, it is Proven by Route B' in AC4 rests on it), on NU-051's pattern for the consume role: without it a classifier that refuses every transition meets the other lines (NU_010_classify_forbids_never). Its conditions are those of the shipped classifier (Novel.RouteB.classifyT and classifyS; rust/libpetri-verification/src/name_fragment.rs classify, the produces_coloured branch): the arc rule and the branch rule are NU-051's ColouredTestArc and SingleColouredWrites, and the mode plays no part."
          "'A transition that writes a coloured place without consuming one and is not declared keeps the net off both routes, and the verifier answers through the name-blind over-approximation' is the second line for Route B. Its Route A half is Novel.RouteA.shipped_mint, cited by NU_010_routeA_mint: a Mint row of the shipped Route A plan is declared and its timeout writes no coloured place. No Route A classifier is abstracted here, as for NU-051."
          "'What the executor writes on timeout ([IO-013], [IO-014]) is never a mint, declared or not: a `ForwardInput` copies a consumed token, name included, and an `Out.Place` writes a unit token, which has no name' is the third line: a timeout write into a coloured place keeps the mint role away whatever it writes (TW.unit or TW.forward). The sixth line says what the transition gets instead when it has no match keys and no coloured input: no role, declared or not, as in every runtime (the produces_coloured branch of classify in rust/libpetri-verification/src/name_fragment.rs, typescript/src/verification/analysis/name-fragment.ts:306, java/src/main/java/org/libpetri/analysis/NameFragment.java:444, each refusing a keyless writer with a coloured timeout write before the ordinary branch). The third line alone allows the ordinary role, whose name step is the identity (VER_012), so the name a timeout forward deposits would never reach the name layer: NU_010_classify_mutant_timeoutOrdinary_killed. A coloured consumer's and a join's timeout writes are NU-051's and NU-054's lines."
          "The outcomes of a transition are Route B's rows (Novel.RouteB.NuTrans.rows: the action branches, then the timeout deposits, rust/libpetri-verification/src/branch_outcomes.rs outcomes), and the timeout writes are the separate argument tw (Rust timeout_writes), as in NU_051. A timeout write therefore lands in a place some row writes; the model takes rows and tw apart, so the sixth line asks it as a premise (every timeout write is into a place of some row). Without it a tw that names a place no row writes would reach the ordinary branch of classifyT, a pair no runtime builds."
          "AC5 (t1 and t2 forward their requests into a and b on timeout, a join on a and b: placeBound(done, 0) is not Proven on either route, with t1 and t2 declared or with budget a declared budget place) is the third and sixth lines on the classifier (NU_010_classify_nonvacuous refuses a declared mint whose timeout writes a coloured place, and NU_010_classify_mutant_timeoutOrdinary_killed forbids reading it as ordinary, which the other five lines and NU-051 and NU-054 allow) and, for Route A, Novel.RouteA.Retro.forward_mint_refused; the verdict itself is stated by no block (kind Q: Rust rust/libpetri/tests/nu_mint_contract a_timeout_forward_into_a_match_key_is_never_a_mint, Java NuMintContractTest aTimeoutForwardIntoAMatchKeyIsNeverAMint_routeB and _routeA), and the false Proven the refusal prevents is Novel.RouteA.Retro.forward_mint_false_proven."
          "'A declared mint that is not a transition of the net MUST be refused, by a failure or an `Unknown`, with the same reason naming it at every entry point' and AC6 (a name given to the verifier as a mint transition that is not a transition of the net is refused with a reason naming it, and a name that is a transition is not refused with that reason) are the block NU_010_unknownMint (Spec/Req/NU_010_ac6.lean, nu.md skeptic S3): a call that names an unknown mint transition is refused, with the reason `declared mint transition 'x' not in the net (NU-010)` (unknown_mint_reason in rust/libpetri-verification/src/name_fragment.rs) unless a refusal that does not read the declaration comes first, and a call whose mint names are all transitions is not refused with that reason unless the same call with no mint named is. How each language and entry point fails (an exception, Unknown, a panic, a ValueError) is configuration (kind N), and 'the same way' is read as 'with the same reason text' (ruling D20). The report sentences ('The report of a verdict from either route names the transitions whose mint contract it assumes', and the pointer when Route B declines only for an undeclared writer, undeclared_mints_pointer in name_fragment.rs) are report lines (kind N) that no block states; Rust rust/libpetri/tests/nu_mint_contract a_copying_producer_is_not_read_as_a_mint_unless_declared checks the contract line, and rust/libpetri-verification/tests/mint_declarations a_route_b_decline_for_an_undeclared_mint_points_at_mint_transitions the pointer."
          "AC4 is NU_010_contract's (a verdict line no block states, kind Q); its classifier halves are the first line (the stock fork() undeclared is never a mint) and the fifth (declared, it is a mint), both in NU_010_classify_nonvacuous."
  signoff "2026-11-13 fd54872eff1e4beb ai"
  statement : Classifier → Prop :=
    fun C =>
      (∀ col mode tw T, C col mode false tw T ≠ some .mint) ∧
      (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] →
        (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) → C col mode false tw T = none) ∧
      (∀ col mode declared tw T, (∃ w ∈ tw, col w.1 = true) →
        C col mode declared tw T ≠ some .mint) ∧
      (∀ col mode declared tw T, C col mode declared tw T = some .mint →
        T.keys = none ∧ ColouredInputs col T = []) ∧
      (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] → ¬ ColouredTestArc col T →
        SingleColouredWrites col T → (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) →
        (∀ w ∈ tw, col w.1 = false) → C col mode true tw T = some .mint) ∧
      (∀ col mode declared tw T, T.keys = none → ColouredInputs col T = [] →
        (∀ w ∈ tw, ∃ r ∈ T.rows, w.1 ∈ r.places) → (∃ w ∈ tw, col w.1 = true) →
        C col mode declared tw T = none)

/- The pinned readable form of NU_010_classify: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_010_classify : Classifier → Prop :=
fun C =>
  (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (tw : List (PlaceId × Novel.RouteB.TW))
      (T : Novel.RouteB.NuTrans), C col mode false tw T ≠ some Novel.RouteB.Role.mint) ∧
    (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (tw : List (PlaceId × Novel.RouteB.TW))
        (T : Novel.RouteB.NuTrans),
        T.keys = none →
          ColouredInputs col T = [] → (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) → C col mode false tw T = none) ∧
      (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW))
          (T : Novel.RouteB.NuTrans),
          (∃ w ∈ tw, col w.1 = true) → C col mode declared tw T ≠ some Novel.RouteB.Role.mint) ∧
        (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW))
            (T : Novel.RouteB.NuTrans),
            C col mode declared tw T = some Novel.RouteB.Role.mint → T.keys = none ∧ ColouredInputs col T = []) ∧
          (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (tw : List (PlaceId × Novel.RouteB.TW))
              (T : Novel.RouteB.NuTrans),
              T.keys = none →
                ColouredInputs col T = [] →
                  ¬ColouredTestArc col T →
                    SingleColouredWrites col T →
                      (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) →
                        (∀ w ∈ tw, col w.1 = false) → C col mode true tw T = some Novel.RouteB.Role.mint) ∧
            ∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (declared : Bool)
              (tw : List (PlaceId × Novel.RouteB.TW)) (T : Novel.RouteB.NuTrans),
              T.keys = none →
                ColouredInputs col T = [] →
                  (∀ w ∈ tw, ∃ r ∈ T.rows, w.1 ∈ r.places) →
                    (∃ w ∈ tw, col w.1 = true) → C col mode declared tw T = none
-/
#guard_msgs in #print NU_010_classify

/-! ## Uniqueness: holds, worked example, forbidden minters -/

/-- ✓ The reference minter satisfies the uniqueness line: one counter per executor, read and
advanced at every call, never reset, so no two calls of a run get one name. -/
@[evidence holds NU_010_unique]
theorem NU_010_unique_reference : NU_010_unique refMintSys :=
  fun _ _ _ h => refRun_nodup h

/-- Two `freshName()` calls by `fork` in one firing, then one more in the next firing. -/
def nu010_evs : List MintEv := [.call "fork", .call "fork", .boundary, .call "fork"]

/-- ✓ Worked example (AC1). An executor with scope `s` runs a fork that calls `freshName()` twice
in its first firing and once in its second. The reference minter returns `fork#s:0`,
`fork#s:1` and `fork#s:2`: three different names, the two of one firing included. -/
@[evidence nonvacuous NU_010_unique]
theorem NU_010_unique_nonvacuous :
    MintRun refMintSys (refMintSys.init "s") nu010_evs ["fork#s:0", "fork#s:1", "fork#s:2"] ∧
      ["fork#s:0", "fork#s:1", "fork#s:2"].Nodup :=
  ⟨refRun_iff.2 (by decide), by decide⟩

/-- A minter that resets its counter at every firing boundary. -/
def nu010_resetSys : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next st := { st with ctr := 0 }

/-- ✗ Worked example: a counter reset at each firing boundary. A fork that mints once in each of
two firings gets `fork#s:0` both times, so two sibling groups would share a name and a join
would mix them. -/
@[evidence forbids NU_010_unique]
theorem NU_010_unique_forbids_resetPerFiring : ¬ NU_010_unique nu010_resetSys := by
  intro h
  have hr : MintRun nu010_resetSys (nu010_resetSys.init "s") [.call "fork", .boundary, .call "fork"]
      ["fork#s:0", "fork#s:0"] :=
    .call ⟨rfl, rfl⟩ (.boundary (.call ⟨rfl, rfl⟩ (.nil _)))
  exact absurd (h _ _ _ hr) (by decide)

/-- A minter with one counter per transition, which leaves the transition out of the name: the
state is the scope and the transitions that called so far. -/
def nu010_perTransSys : MintSys where
  St := String × List String
  init s := (s, [])
  mint st t x st' := x = st.1 ++ ":" ++ Nat.repr (st.2.count t) ∧ st' = (st.1, t :: st.2)
  next := id

/-- ✗ Worked example: a counter per transition, with the transition left out of the name. The
first call of `a` and the first call of `b` both get `s:0`. -/
@[evidence forbids NU_010_unique]
theorem NU_010_unique_forbids_perTransition : ¬ NU_010_unique nu010_perTransSys := by
  intro h
  have hr : MintRun nu010_perTransSys (nu010_perTransSys.init "s") [.call "a", .call "b"]
      ["s:0", "s:0"] :=
    .call ⟨by decide, rfl⟩ (.call ⟨by decide, rfl⟩ (.nil _))
  exact absurd (h _ _ _ hr) (by decide)

/-- The fallback minter of an action context that no executor gave a minter: a process-wide
counter, rendered by `fmt` with the calling transition. Other contexts of the process may take
counter values between two calls, so a call returns the name of SOME counter value at or above
the current one and moves the counter past it. -/
def nu010_fallbackSys (fmt : String → Nat → String) : MintSys where
  St := Nat
  init _ := 0
  mint n t x n' := ∃ k, n ≤ k ∧ x = fmt t k ∧ n' = k + 1
  next := id

/-- The Rust and TypeScript fallback format `<t>#<n>`. -/
def nu010_hashFmt (t : String) (n : Nat) : String := t ++ "#" ++ Nat.repr n

/-- The counter can be read back from a `<t>#<n>` name: the last `#` splits it off. -/
theorem nu010_hashFmt_counter_inj {t t' : String} {n n' : Nat}
    (h : nu010_hashFmt t n = nu010_hashFmt t' n') : n = n' := by
  have hl := congrArg String.toList h
  simp only [nu010_hashFmt, String.toList_append] at hl
  have h1 : t.toList ++ '#' :: (Nat.repr n).toList = t'.toList ++ '#' :: (Nat.repr n').toList := by
    simpa [List.append_assoc] using hl
  exact Nat.repr_inj.mp (String.toList_inj.mp
    (mint_split_last (hash_not_mem_repr n) (hash_not_mem_repr n') h1).2)

/-- A run of the fallback minter from counter `n` returns pairwise distinct names, each of a
counter at or above `n`, when the format lets the counter be read back. -/
theorem nu010_fallback_run {fmt : String → Nat → String}
    (hinj : ∀ t t' k k', fmt t k = fmt t' k' → k = k') {n : (nu010_fallbackSys fmt).St}
    {evs : List MintEv} {xs : List String} (h : MintRun (nu010_fallbackSys fmt) n evs xs) :
    xs.Nodup ∧ ∀ x ∈ xs, ∃ t k, @LE.le Nat _ n k ∧ x = fmt t k := by
  induction h with
  | nil => simp
  | @call s s' t x evs xs hm _ ih =>
    obtain ⟨k, hk, rfl, rfl⟩ := hm
    refine ⟨List.nodup_cons.2 ⟨fun hx => ?_, ih.1⟩, ?_⟩
    · obtain ⟨t', k', hk', he⟩ := ih.2 _ hx
      have := hinj _ _ _ _ he
      omega
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨t, k, hk, rfl⟩
      · obtain ⟨t', k', hk', rfl⟩ := ih.2 y hy
        exact ⟨t', k', by omega, rfl⟩
  | boundary _ ih => exact ih

/-- **The fallback is unique.** An action context that no executor gave a minter falls back to a
process-wide counter. Rust and TypeScript name the call `<t>#<n>`, Java `<t>#<detached scope>:<n>`.
Whatever value the counter has when a run starts, and however many names other contexts take in
between, the names a run gets are pairwise distinct: for example `fork#4`, `fork#5`, `fork#9`. -/
@[evidence cites "NU-010" "absent an executor-installed minter, a fallback still guarantees uniqueness"]
theorem nu010_fallback_unique :
    (∀ n evs xs, MintRun (nu010_fallbackSys nu010_hashFmt) n evs xs → xs.Nodup) ∧
      ∀ d n evs xs, MintRun (nu010_fallbackSys (fun t k => mintName t d k)) n evs xs →
        xs.Nodup :=
  ⟨fun _ _ _ h => (nu010_fallback_run (fun _ _ _ _ he => nu010_hashFmt_counter_inj he) h).1,
    fun _ _ _ _ h => (nu010_fallback_run (fun _ _ _ _ he => mintName_counter_inj he) h).1⟩

/-! ## Replay: holds, worked example, forbidden minters -/

/-- ✓ The reference minter satisfies the replay line: a run returns the reference names of its
calls, whatever the firing boundaries. -/
@[evidence holds NU_010_replay]
theorem NU_010_replay_reference : NU_010_replay refMintSys := by
  intro s evs evs' xs ys hc h h'
  rw [refRun_eq h, refRun_eq h', hc]

/-- ✓ Worked example (AC3). Under scope `s`, two calls by `fork` in one firing and the same two
calls split over two firings both return `fork#s:0`, `fork#s:1`. -/
@[evidence nonvacuous NU_010_replay]
theorem NU_010_replay_nonvacuous :
    MintRun refMintSys (refMintSys.init "s") [.call "fork", .call "fork"] ["fork#s:0", "fork#s:1"] ∧
      MintRun refMintSys (refMintSys.init "s") [.call "fork", .boundary, .call "fork"]
        ["fork#s:0", "fork#s:1"] :=
  ⟨refRun_iff.2 (by decide), refRun_iff.2 (by decide)⟩

/-- A minter that may return any name it has not returned before: the state is the names
returned so far. -/
def nu010_anyUnusedSys : MintSys where
  St := List String
  init _ := []
  mint used _ x used' := x ∉ used ∧ used' = x :: used
  next := id

/-- ✗ Worked example: a minter that may return any unused name. One call by `a` can return `p` in
one run and `q` in another, so a replay of the same calls does not reproduce the names. -/
@[evidence forbids NU_010_replay]
theorem NU_010_replay_forbids_anyUnused : ¬ NU_010_replay nu010_anyUnusedSys := by
  intro h
  have hp : MintRun nu010_anyUnusedSys (nu010_anyUnusedSys.init "s") [.call "a"] ["p"] :=
    .call ⟨by simp [nu010_anyUnusedSys], rfl⟩ (.nil _)
  have hq : MintRun nu010_anyUnusedSys (nu010_anyUnusedSys.init "s") [.call "a"] ["q"] :=
    .call ⟨by simp [nu010_anyUnusedSys], rfl⟩ (.nil _)
  exact absurd (h _ _ _ _ _ rfl hp hq) (by decide)

/-- The any-unused minter never repeats a name in a run, and its names avoid the names it
started with. -/
theorem nu010_anyUnused_run {st : nu010_anyUnusedSys.St} {evs : List MintEv} {xs : List String}
    (h : MintRun nu010_anyUnusedSys st evs xs) : xs.Nodup ∧ ∀ x ∈ xs, ¬ List.Mem x st := by
  induction h with
  | nil => simp
  | @call s s' t x evs xs hm _ ih =>
    obtain ⟨hx, rfl⟩ := hm
    refine ⟨List.nodup_cons.2 ⟨fun hm' => ih.2 x hm' List.mem_cons_self, ih.1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact fun hs => ih.2 y hy (List.mem_cons_of_mem _ hs)
  | boundary _ ih => exact ih

/-- The replay line weakened to the uniqueness line: no two calls of a run get one name, and
nothing more. -/
def NU_010_replay_mutant_uniqueOnly (Sy : MintSys) : Prop := NU_010_unique Sy

/-- ✗ Worked example: uniqueness alone does not give replay. The any-unused minter never returns
a name twice in a run, so it meets the uniqueness line, but the replay line rules it out. -/
@[evidence mutant NU_010_replay]
theorem NU_010_replay_mutant_uniqueOnly_killed :
    NU_010_replay_mutant_uniqueOnly nu010_anyUnusedSys ∧ ¬ NU_010_replay nu010_anyUnusedSys :=
  ⟨fun _ _ _ h => (nu010_anyUnused_run h).1, NU_010_replay_forbids_anyUnused⟩

/-- A minter whose counter also moves at every firing boundary. -/
def nu010_tickSys : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next st := { st with ctr := st.ctr + 1 }

/-- ✗ Worked example: a counter that also moves at each firing boundary is unique and a function
of its state, but keyed on the firings. Two calls by `fork` in one firing return `fork#s:0`,
`fork#s:1`; the same calls over two firings return `fork#s:0`, `fork#s:2`. -/
@[evidence forbids NU_010_replay]
theorem NU_010_replay_forbids_boundaryTick : ¬ NU_010_replay nu010_tickSys := by
  intro h
  have h1 : MintRun nu010_tickSys (nu010_tickSys.init "s") [.call "fork", .call "fork"]
      ["fork#s:0", "fork#s:1"] :=
    .call ⟨rfl, rfl⟩ (.call ⟨rfl, rfl⟩ (.nil _))
  have h2 : MintRun nu010_tickSys (nu010_tickSys.init "s") [.call "fork", .boundary, .call "fork"]
      ["fork#s:0", "fork#s:2"] :=
    .call ⟨rfl, rfl⟩ (.boundary (.call ⟨rfl, rfl⟩ (.nil _)))
  exact absurd (h _ _ _ _ _ (by rfl) h1 h2) (by decide)

/-! ## The mint contract: what it buys, worked example (AC2), forbidden actions -/

/-- **What the contract buys.** Take a reference run of an executor whose scope `s` holds no `#`,
whose calls returned `xs` before the firing and `minted` in it. Suppose every name a coloured
place holds was returned earlier in the run (`xs`) or minted under another scope without `#` (an
earlier execution of the restore lineage). Then a firing that keeps the contract, and minted at
least one name, writes one name that no coloured place holds: `MintContract`, which
`mintContract_iff_routeB` turns into Route B's premise. -/
@[evidence cites "NU-010" "Every name a declared mint writes into a coloured place it writes without consuming one MUST be a name it minted with `freshName()` in that firing, and all such names MUST be one and the same: with the reference minter that name is held in no coloured place, which is the mint contract the Route B soundness theorems assume"]
theorem nu010_contract_fresh {C : Type} {holds : C → String → Prop} {wr : C → List String}
    {s : String} {evs : List MintEv} {xs minted : List String} (hs : '#' ∉ s.toList)
    (h : MintRun refMintSys (refMintSys.init s) evs (xs ++ minted))
    (hheld : ∀ c y, holds c y → y ∈ xs ∨ ∃ s', '#' ∉ s'.toList ∧ s' ≠ s ∧ MintedUnder s' y)
    (hne : minted ≠ []) (hc : NU_010_contract minted wr) : MintContract holds wr := by
  have hnd := refRun_nodup h
  have hfresh : ∀ x ∈ minted, ∀ c, ¬ holds c x := by
    intro x hx c hh
    rcases hheld c x hh with hm | ⟨s', hs', hne', hu⟩
    · rw [List.nodup_append] at hnd
      exact hnd.2.2 x hm x hx rfl
    · exact hne' (mintedUnder_unique hs' hs hu
        (refRun_mintedUnder h x (List.mem_append_right _ hx)))
  by_cases hw : ∃ c, ∃ w, w ∈ wr c
  · obtain ⟨c, w, hw⟩ := hw
    exact ⟨w, hfresh w (hc.1 c w hw), fun c' w' hw' => hc.2 c' c w' hw' w hw⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil minted hne
    exact ⟨x, hfresh x hx, fun c w hw' => absurd ⟨c, w, hw'⟩ hw⟩

/-- The fork of AC2: consumes place 0, writes places 1 and 2 (an AND output), no match. -/
def nu010_fork : NuTrans Nat (KeyFn String String) :=
  { base := { core := { name := "fork", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := some (.and (.place 1) (.place 2)) }
    mspec := none }

/-- The join of AC2: keys places 1 and 2, a token's name being its value. -/
def nu010_jms : MatchSpec Nat (KeyFn String String) := { keys := [(1, some), (2, some)] }

/-- The join of AC2 on places 1 and 2, correlated by `nu010_jms`, depositing nothing. -/
def nu010_join : NuTrans Nat (KeyFn String String) :=
  { base := { core := { name := "join", inputs := [⟨1, .one⟩, ⟨2, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none }
    mspec := some nu010_jms }

/-- AC2's start: one request on place 0. -/
def nu010_M0 : QMarking Nat (Stamped String) := fun p => if p = 0 then [⟨"req", 0⟩] else []

/-- What the fork's action emits: the name it minted, `fork#s:0`, once into place 1 and once into
place 2. -/
def nu010_e : List (Nat × Stamped String) :=
  [(1, ⟨mintName "fork" "s" 0, 1⟩), (2, ⟨mintName "fork" "s" 0, 1⟩)]

/-- The marking the fork leaves. -/
def nu010_M1 : QMarking Nat (Stamped String) := qFire nu010_M0 nu010_fork.base nu010_e

/-- ✓ Worked example (AC2). An executor with scope `s` fires the fork on one request. Its action
calls `freshName()` once, gets `fork#s:0` from the reference minter, and writes it into both
AND-branches, places 1 and 2: the firing keeps the contract. The reference join on places 1 and
2 then fires with that name and takes one sibling token from each branch. -/
@[evidence nonvacuous NU_010_contract]
theorem NU_010_contract_nonvacuous :
    MintRun refMintSys (refMintSys.init "s") [.call "fork"] [mintName "fork" "s" 0] ∧
      RefNuFire nu010_fork nu010_M0 none (qDelivered nu010_M0 nu010_fork.base) nu010_e
        nu010_M1 ∧
      NU_010_contract [mintName "fork" "s" 0]
        (fun p => (qEmittedTo nu010_e p).map Stamped.val) ∧
      RefNuFire nu010_join nu010_M1 (some (mintName "fork" "s" 0))
        (nuDelivered nu010_jms nu010_join nu010_M1 (mintName "fork" "s" 0)) []
        (qAppend (nuConsume nu010_jms nu010_join nu010_M1 (mintName "fork" "s" 0)) []) ∧
      nuInputs nu010_jms nu010_join nu010_M1 (mintName "fork" "s" 0) 1 =
        [⟨mintName "fork" "s" 0, 1⟩] ∧
      nuInputs nu010_jms nu010_join nu010_M1 (mintName "fork" "s" 0) 2 =
        [⟨mintName "fork" "s" 0, 1⟩] := by
  refine ⟨refRun_iff.2 rfl, ⟨rfl, by decide, ⟨.action 0, by decide⟩, rfl, rfl⟩, ?_,
    ⟨_, rfl, by decide, by decide, ⟨.action 0, rfl⟩, fun r hr => by simp [nu010_jms] at hr,
      rfl, rfl⟩, by decide, by decide⟩
  refine ⟨fun p w hw => ?_, fun p p' w hw w' hw' => ?_⟩
  · rcases p with _ | _ | _ | p <;> simp_all [nu010_e, qEmittedTo]
  · rcases p with _ | _ | _ | p <;> rcases p' with _ | _ | _ | p' <;>
      simp_all [nu010_e, qEmittedTo]

/-- ✗ Worked example: the stock `fork()` copies the correlation id `7` it consumed into both
places. It writes one name everywhere, but not a name it minted (`fork#s:0`), so the first line
fails: the verifier would treat a copied id as fresh. -/
@[evidence forbids NU_010_contract]
theorem NU_010_contract_forbids_copy :
    ¬ NU_010_contract (C := Bool) [mintName "fork" "s" 0] (fun _ => ["7"]) := by
  intro h
  exact absurd (h.1 true "7" (by simp)) (by decide)

/-- ✗ Worked example (ruling D78): a fork that calls `freshName()` twice and writes `fork#s:0` into
place A and `fork#s:1` into place B. Both names are fresh, but a join on A and B could never
match them, and the analyses assume one name, so the second line fails. -/
@[evidence forbids NU_010_contract]
theorem NU_010_contract_forbids_twoNames :
    ¬ NU_010_contract (C := Bool) [mintName "fork" "s" 0, mintName "fork" "s" 1]
      (fun b => if b then [mintName "fork" "s" 0] else [mintName "fork" "s" 1]) := by
  intro h
  exact absurd (h.2 true false (mintName "fork" "s" 0) (by simp) (mintName "fork" "s" 1) (by simp))
    (by decide)

/-- The second contract line read for two DIFFERENT places only: names in one place may differ. -/
def NU_010_contract_mutant_otherPlaces {C Nm : Type} (minted : List Nm) (wr : C → List Nm) : Prop :=
  (∀ c, ∀ w ∈ wr c, w ∈ minted) ∧ (∀ c c', c ≠ c' → ∀ w ∈ wr c, ∀ w' ∈ wr c', w = w')

/-- ✗ Worked example: a fork with ONE coloured output place calls `freshName()` twice and writes
both names, `fork#s:0` and `fork#s:1`, into that place. Both names are fresh and no second place
is written, so a reading that compares only two different places accepts it. The second line
rules it out: the names of one place must be one name too. -/
@[evidence mutant NU_010_contract]
theorem NU_010_contract_mutant_otherPlaces_killed :
    NU_010_contract_mutant_otherPlaces (C := Unit) [mintName "fork" "s" 0, mintName "fork" "s" 1]
        (fun _ => [mintName "fork" "s" 0, mintName "fork" "s" 1]) ∧
      ¬ NU_010_contract (C := Unit) [mintName "fork" "s" 0, mintName "fork" "s" 1]
        (fun _ => [mintName "fork" "s" 0, mintName "fork" "s" 1]) := by
  refine ⟨⟨fun _ _ hw => hw, fun c c' hne => absurd (Subsingleton.elim c c') hne⟩, fun h => ?_⟩
  exact absurd (h.2 () () (mintName "fork" "s" 0) (by simp) (mintName "fork" "s" 1) (by simp))
    (by decide)

/-! ## The classifier: holds, worked example, forbidden classifiers -/

/-- A transition with no match keys and no coloured input that writes a coloured place is a mint
or refused by `classifyT`. -/
theorem nu010_classifyT_keylessWriter {col : PlaceId → Bool} {mode : Novel.RouteB.Mode}
    {T : Novel.RouteB.NuTrans} (hk : T.keys = none) (hci : ColouredInputs col T = [])
    (hw : ∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) :
    Novel.RouteB.classifyT col mode true T = none ∨
      Novel.RouteB.classifyT col mode true T = some .mint := by
  unfold ColouredInputs at hci
  unfold Novel.RouteB.classifyT
  simp only [hk, hci, List.isEmpty_nil, Bool.not_true]
  have hany : T.rows.any (fun r => r.places.any col) = true := by
    obtain ⟨r, hr, p, hp, hc⟩ := hw
    exact List.any_eq_true.2 ⟨r, hr, List.any_eq_true.2 ⟨p, hp, hc⟩⟩
  split_ifs <;> simp_all

/-- An undeclared transition with no match keys and no coloured input that writes a coloured
place gets no role from the shipped classifier: `classifyT` calls it a mint or refuses it, and
`classifyS` refuses an undeclared mint. -/
theorem nu010_classifyS_undeclaredWriter {col : PlaceId → Bool} {mode : Novel.RouteB.Mode}
    {tw : List (PlaceId × Novel.RouteB.TW)} {T : Novel.RouteB.NuTrans} (hk : T.keys = none)
    (hci : ColouredInputs col T = []) (hw : ∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) :
    Novel.RouteB.classifyS col mode false tw T = none := by
  rcases nu010_classifyT_keylessWriter (mode := mode) hk hci hw with h | h <;>
    simp [Novel.RouteB.classifyS, h]

/-- A transition with no match keys and no coloured input whose timeout writes a coloured place
that one of its outcomes writes gets no role from the shipped classifier, declared or not:
`classifyT` calls it a mint or refuses it, and `classifyS` refuses a mint with a coloured
timeout write. -/
theorem nu010_classifyS_timeoutWriter {col : PlaceId → Bool} {mode : Novel.RouteB.Mode}
    {declared : Bool} {tw : List (PlaceId × Novel.RouteB.TW)} {T : Novel.RouteB.NuTrans}
    (hk : T.keys = none) (hci : ColouredInputs col T = [])
    (hrw : ∀ w ∈ tw, ∃ r ∈ T.rows, w.1 ∈ r.places) (hcw : ∃ w ∈ tw, col w.1 = true) :
    Novel.RouteB.classifyS col mode declared tw T = none := by
  obtain ⟨w, hw, hc⟩ := hcw
  obtain ⟨r, hr, hp⟩ := hrw w hw
  have hall : tw.all (fun w => !col w.1) = false := by
    rw [Bool.eq_false_iff]
    intro ha
    have := List.all_eq_true.1 ha w hw
    simp [hc] at this
  rcases nu010_classifyT_keylessWriter (mode := mode) hk hci ⟨r, hr, w.1, hp, hc⟩ with h | h <;>
    simp [Novel.RouteB.classifyS, h, hall]

open Novel.RouteB in
/-- The shipped classifier gives the mint role only to a transition with no match keys and no
input arc on a coloured place. -/
theorem nu010_classifyS_mintShape {col : PlaceId → Bool} {mode : Mode} {declared : Bool}
    {tw : List (PlaceId × TW)} {T : Novel.RouteB.NuTrans}
    (h : classifyS col mode declared tw T = some .mint) :
    T.keys = none ∧ ColouredInputs col T = [] := by
  have hT := classifyS_sub h
  unfold ColouredInputs
  cases hk : T.keys with
  | some ks =>
    exfalso
    unfold classifyT at hT
    rw [hk] at hT
    simp only at hT
    split_ifs at hT
    all_goals first
      | cases hT
      | (cases hm : List.mapM (keyCount T) ks <;> simp [hm] at hT)
  | none =>
    refine ⟨rfl, ?_⟩
    by_contra hne
    have hne' : (!(T.base.inputs.filter fun s => col s.place).isEmpty) = true := by
      simpa [List.isEmpty_iff] using hne
    unfold classifyT at hT
    rw [hk] at hT
    simp only [hne', if_true] at hT
    split_ifs at hT
    all_goals first
      | cases hT
      | (split at hT <;> first | cases hT | (split at hT <;> cases hT))

open Novel.RouteB in
/-- The shipped classifier gives the mint role to a declared transition with no match keys, no
coloured input, no test arc on a coloured place, one token per coloured place a branch writes,
some coloured write and no coloured timeout write, in either mode. -/
theorem nu010_classifyS_declaredMint {col : PlaceId → Bool} {mode : Mode}
    {tw : List (PlaceId × TW)} {T : Novel.RouteB.NuTrans} (hk : T.keys = none)
    (hci : ColouredInputs col T = []) (hta : ¬ ColouredTestArc col T) (hsw : SingleColouredWrites col T)
    (hw : ∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) (htw : ∀ w ∈ tw, col w.1 = false) :
    classifyS col mode true tw T = some .mint := by
  have hany : T.rows.any (fun r => r.places.any col) = true := by
    obtain ⟨r, hr, p, hp, hc⟩ := hw
    exact List.any_eq_true.2 ⟨r, hr, List.any_eq_true.2 ⟨p, hp, hc⟩⟩
  have hT : classifyT col mode true T = some .mint := by
    unfold ColouredInputs at hci
    unfold classifyT
    simp only [nu051_arcsOk_true hta, nu051_rows_ok hsw, hk, hci, hany, List.isEmpty_nil,
      Bool.not_true, Bool.false_eq_true, if_false, if_true]
  have hall : tw.all (fun w => !col w.1) = true :=
    List.all_eq_true.2 fun w hw => by simp [htw w hw]
  simp [classifyS, hT, hall]

/-- ✓ The shipped classifier satisfies the block: an undeclared transition is never a mint
(`classifyS_undeclared`), an undeclared writer of a coloured place gets no role, a mint writes
no coloured place on timeout (`classifyS_mint`), a mint has no match keys and no coloured input,
a declared mint inside the fragment rules is a mint, and a keyless transition with no coloured
input whose timeout writes a coloured place gets no role. -/
@[evidence holds NU_010_classify]
theorem NU_010_classify_reference : NU_010_classify refClassify := by
  refine ⟨fun _ _ _ _ => Novel.RouteB.classifyS_undeclared,
    fun _ _ _ _ hk hci hw => nu010_classifyS_undeclaredWriter hk hci hw, ?_,
    fun _ _ _ _ _ h => nu010_classifyS_mintShape h,
    fun _ _ _ _ hk hci hta hsw hw htw => nu010_classifyS_declaredMint hk hci hta hsw hw htw,
    fun _ _ _ _ _ hk hci hrw hcw => nu010_classifyS_timeoutWriter hk hci hrw hcw⟩
  intro col mode declared tw T ⟨w, hw, hc⟩ h
  have := (Novel.RouteB.classifyS_mint h).2 w hw
  rw [hc] at this
  exact absurd this (by decide)

/-- The coloured set of the copying-mint fixture: places 0 and 1. -/
def nu010_col : PlaceId → Bool := fun p => Novel.RouteB.coM.contains p

/-- ✓ Worked example. `mB` consumes the uncoloured place 2 and writes the coloured place 1 (the
stock `fork()` of AC4). Declared, with no timeout write, it is a mint, in BASE and in EXTENDED.
Not declared, it gets no role, so the net leaves both routes. Declared but with a timeout that
writes a unit token into place 1 (as AC5's forward does), it gets no role either. -/
@[evidence nonvacuous NU_010_classify]
theorem NU_010_classify_nonvacuous :
    refClassify nu010_col .base true [] Novel.RouteB.tM = some .mint ∧
      refClassify nu010_col .extended true [] Novel.RouteB.tM = some .mint ∧
      refClassify nu010_col .base false [] Novel.RouteB.tM = none ∧
      refClassify nu010_col .base true [(1, .unit)] Novel.RouteB.tM = none ∧
      refClassify nu010_col .base true [(1, .forward 2)] Novel.RouteB.tM = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A classifier that reads every keyless writer of a coloured place as a mint, declared or not,
whatever its timeout writes: `classifyT` without the shipped gate. -/
def nu010_copyClassify : Classifier := fun col mode _ _ T => Novel.RouteB.classifyT col mode true T

/-- ✗ Worked example: reading every writer of a coloured place as a mint makes the stock `fork()`
of AC4, which copies its input and is not declared, a mint. The first line fails. -/
@[evidence forbids NU_010_classify]
theorem NU_010_classify_forbids_undeclaredMint : ¬ NU_010_classify nu010_copyClassify :=
  fun h => h.1 nu010_col .base [] Novel.RouteB.tM Novel.RouteB.classify_mint

/-- A classifier that reads an undeclared writer of a coloured place as an ordinary transition. -/
def nu010_ordinaryClassify : Classifier := fun col mode d tw T =>
  if d = false ∧ Novel.RouteB.classifyT col mode true T = some .mint then some .ordinary
  else refClassify col mode d tw T

/-- ✗ Worked example: an undeclared `fork()` read as an ordinary transition is never a mint, so
the first line holds, but the name layer would ignore the names it writes and could prove a join
unreachable that the executor fires. The second line fails: it must get no role. -/
@[evidence forbids NU_010_classify]
theorem NU_010_classify_forbids_ordinary : ¬ NU_010_classify nu010_ordinaryClassify := by
  intro h
  have := h.2.1 nu010_col .base [] Novel.RouteB.tM rfl (by decide) ⟨⟨[1], []⟩, by decide, 1,
    by decide, by decide⟩
  exact absurd this (by decide)

/-- A classifier that accepts a declared mint whatever its timeout writes. -/
def nu010_noTimeoutClassify : Classifier := fun col mode d tw T =>
  if d = true ∧ Novel.RouteB.classifyT col mode true T = some .mint then some .mint
  else refClassify col mode d tw T

/-- ✗ Worked example (AC5): a declared mint whose timeout writes a unit token into the coloured
place 1 is still read as a mint, although a timeout write is never fresh. The third line
fails. -/
@[evidence forbids NU_010_classify]
theorem NU_010_classify_forbids_timeoutMint : ¬ NU_010_classify nu010_noTimeoutClassify := by
  intro h
  exact h.2.2.1 nu010_col .base true [(1, .unit)] Novel.RouteB.tM ⟨(1, .unit), by simp, rfl⟩
    (by decide)

/-- A classifier that refuses every transition, so the net always falls back. -/
def nu010_neverClassify : Classifier := fun _ _ _ _ _ => none

/-- ✗ Worked example (AC4): a classifier that refuses every transition never gives a wrong role,
so the other lines hold. But the declared `mB` of AC4, which consumes the uncoloured place 2
and writes the coloured place 1 once, would then never be read as a mint, and Route B could
never prove the net. The fifth line fails. -/
@[evidence forbids NU_010_classify]
theorem NU_010_classify_forbids_never : ¬ NU_010_classify nu010_neverClassify := by
  intro h
  have := h.2.2.2.2.1 nu010_col .base [] Novel.RouteB.tM rfl (by decide)
    (fun ⟨p, _, hp⟩ => by simp [Novel.RouteB.tM] at hp)
    (by simp [SingleColouredWrites, Novel.RouteB.tM])
    ⟨⟨[1], []⟩, by decide, 1, by decide, by decide⟩ (by simp)
  exact absurd this (by simp [nu010_neverClassify])

/-- A matched join on the coloured place 1 that also takes a permit from the uncoloured place 2,
and writes nothing. Consuming a declared budget place makes it a declared mint. -/
def nu010_permitJoin : Novel.RouteB.NuTrans where
  base := { name := "j", inputs := [Novel.RouteB.inOne 1, Novel.RouteB.inOne 2], inhibitors := [],
            reads := [], resets := [] }
  rows := []
  keys := some [1]
  relays := []

/-- The shipped classifier with the declaration tested before the match specification, as a
reordered `classify` would do: under BASE a declared matched join with no coloured timeout write
gets the mint role instead of the join role. -/
def nu010_joinMintClassify : Classifier := fun col mode d tw T =>
  match refClassify col mode d tw T with
  | some (.join cin rel) =>
    if mode = .base ∧ d = true ∧ tw.all (fun w => !col w.1) = true then some .mint
    else some (.join cin rel)
  | r => r

/-- The shipped classifier gives the permit-taking join `j` the join role on its key, place 1,
counting one token, and no relay target. -/
theorem nu010_permitJoin_ref :
    refClassify nu010_col .base true [] nu010_permitJoin = some (.join [(1, 1)] []) := by
  decide

/-- The mutant refuses exactly what the shipped classifier refuses. -/
theorem nu010_joinMint_none_iff {col mode d tw T} :
    nu010_joinMintClassify col mode d tw T = none ↔ refClassify col mode d tw T = none := by
  unfold nu010_joinMintClassify
  split <;> simp_all
  split_ifs <;> simp

/-- The mutant gives the mint role only where the shipped classifier does, or to a declared
transition with no coloured timeout write. -/
theorem nu010_joinMint_mint {col mode d tw T}
    (h : nu010_joinMintClassify col mode d tw T = some .mint) :
    refClassify col mode d tw T = some .mint ∨
      (d = true ∧ tw.all (fun w => !col w.1) = true) := by
  unfold nu010_joinMintClassify at h
  split at h
  · split_ifs at h with hc
    · exact .inr ⟨hc.2.1, hc.2.2⟩
    · cases h
  · exact .inl h

/-- The classifier block without its fourth line (the shape of a mint). -/
def NU_010_classify_mutant_noShape (C : Classifier) : Prop :=
  (∀ col mode tw T, C col mode false tw T ≠ some .mint) ∧
  (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] →
    (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) → C col mode false tw T = none) ∧
  (∀ col mode declared tw T, (∃ w ∈ tw, col w.1 = true) →
    C col mode declared tw T ≠ some .mint) ∧
  (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) →
    (∀ w ∈ tw, col w.1 = false) → C col mode true tw T = some .mint) ∧
  (∀ col mode declared tw T, T.keys = none → ColouredInputs col T = [] →
    (∀ w ∈ tw, ∃ r ∈ T.rows, w.1 ∈ r.places) → (∃ w ∈ tw, col w.1 = true) →
    C col mode declared tw T = none)

/-- ✗ Worked example: the matched join `j` on place 1 takes a permit from a declared budget place,
so it counts as declared. The shipped classifier gives it the join role (`nu010_permitJoin_ref`);
a classifier that tests the declaration before the match specification gives it the mint role
under BASE, so the name layer would mint a fresh name for it instead of taking the matched name
from its key. That classifier meets the other five lines: the join is declared and writes nothing
on timeout. The fourth line rules it out: a transition with a match specification is never a
mint. -/
@[evidence mutant NU_010_classify]
theorem NU_010_classify_mutant_joinMint_killed :
    NU_010_classify_mutant_noShape nu010_joinMintClassify ∧
      ¬ NU_010_classify nu010_joinMintClassify := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := NU_010_classify_reference
  refine ⟨⟨fun col mode tw T hm => ?_, fun col mode tw T hk hci hw =>
      nu010_joinMint_none_iff.2 (h2 col mode tw T hk hci hw), ?_, ?_,
      fun col mode d tw T hk hci hrw hcw =>
        nu010_joinMint_none_iff.2 (h6 col mode d tw T hk hci hrw hcw)⟩, fun h => ?_⟩
  · rcases nu010_joinMint_mint hm with h | ⟨hd, -⟩
    · exact h1 col mode tw T h
    · cases hd
  · intro col mode declared tw T ⟨w, hw, hc⟩ hm
    rcases nu010_joinMint_mint hm with h | ⟨-, hall⟩
    · exact h3 col mode declared tw T ⟨w, hw, hc⟩ h
    · have := List.all_eq_true.1 hall w hw
      simp [hc] at this
  · intro col mode tw T hk hci hta hsw hw htw
    unfold nu010_joinMintClassify
    rw [h5 col mode tw T hk hci hta hsw hw htw]
  · have := (h.2.2.2.1 nu010_col .base true [] nu010_permitJoin (by decide)).1
    exact absurd this (by simp [nu010_permitJoin])

/-- A classifier that reads a declared keyless writer of a coloured place as an ordinary
transition where the shipped classifier refuses it for its coloured timeout write. Everywhere
else it is the shipped classifier. -/
def nu010_timeoutOrdClassify : Classifier := fun col mode d tw T =>
  match refClassify col mode d tw T with
  | none =>
    if d = true ∧ T.keys = none ∧ Novel.RouteB.classifyT col mode true T = some .mint then
      some .ordinary
    else none
  | some r => some r

/-- Where the shipped classifier gives a role, the mutant gives the same one. -/
theorem nu010_timeoutOrd_some {col mode d tw T} {r : Novel.RouteB.Role}
    (h : refClassify col mode d tw T = some r) : nu010_timeoutOrdClassify col mode d tw T = some r := by
  unfold nu010_timeoutOrdClassify; rw [h]

/-- The mutant gives the mint role only where the shipped classifier does. -/
theorem nu010_timeoutOrd_mint {col mode d tw T}
    (h : nu010_timeoutOrdClassify col mode d tw T = some .mint) :
    refClassify col mode d tw T = some .mint := by
  unfold nu010_timeoutOrdClassify at h
  cases hr : refClassify col mode d tw T with
  | none => rw [hr] at h; simp only at h; split_ifs at h; cases h
  | some r => rw [hr] at h; exact h

/-- The classifier block without its sixth line (no role for a keyless writer whose timeout
writes a coloured place). -/
def NU_010_classify_mutant_noTimeoutNone (C : Classifier) : Prop :=
  (∀ col mode tw T, C col mode false tw T ≠ some .mint) ∧
  (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] →
    (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) → C col mode false tw T = none) ∧
  (∀ col mode declared tw T, (∃ w ∈ tw, col w.1 = true) →
    C col mode declared tw T ≠ some .mint) ∧
  (∀ col mode declared tw T, C col mode declared tw T = some .mint →
    T.keys = none ∧ ColouredInputs col T = []) ∧
  (∀ col mode tw T, T.keys = none → ColouredInputs col T = [] → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) →
    (∀ w ∈ tw, col w.1 = false) → C col mode true tw T = some .mint)

/-- The AC5 shape: the declared `mB` whose timeout writes a unit token into the coloured place 1.
The shipped classifier refuses it, the mutant reads it as ordinary. -/
theorem nu010_timeoutOrd_ac5 :
    refClassify nu010_col .base true [(1, .unit)] Novel.RouteB.tM = none ∧
      nu010_timeoutOrdClassify nu010_col .base true [(1, .unit)] Novel.RouteB.tM =
        some .ordinary :=
  ⟨rfl, rfl⟩

/-- ✗ Worked example (AC5): the declared `mB` whose timeout writes a unit token into the coloured
place 1. The shipped classifier refuses it; a classifier that reads it as ordinary instead
(`nu010_timeoutOrd_ac5`) never
gives it the mint role, so the first five lines hold. But the ordinary role's name step is the
identity, so the name a timeout forward deposits into a join's coloured input never reaches the
name layer: the join can never fire on Route B and `placeBound(done, 0)` comes out `Proven`,
the false `Proven` AC5 forbids. The sixth line rules it out: such a transition gets no role. -/
@[evidence mutant NU_010_classify]
theorem NU_010_classify_mutant_timeoutOrdinary_killed :
    NU_010_classify_mutant_noTimeoutNone nu010_timeoutOrdClassify ∧
      ¬ NU_010_classify nu010_timeoutOrdClassify := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := NU_010_classify_reference
  refine ⟨⟨fun col mode tw T hm => h1 col mode tw T (nu010_timeoutOrd_mint hm), ?_,
      fun col mode d tw T hw hm => h3 col mode d tw T hw (nu010_timeoutOrd_mint hm),
      fun col mode d tw T hm => h4 col mode d tw T (nu010_timeoutOrd_mint hm),
      fun col mode tw T hk hci hta hsw hw htw =>
        nu010_timeoutOrd_some (h5 col mode tw T hk hci hta hsw hw htw)⟩, fun h => ?_⟩
  · intro col mode tw T hk hci hw
    unfold nu010_timeoutOrdClassify
    rw [h2 col mode tw T hk hci hw]
    simp
  · have := h.2.2.2.2.2 nu010_col .base true [(1, .unit)] Novel.RouteB.tM rfl (by decide)
      (fun w hw => ⟨⟨[1], []⟩, by decide, by simp at hw; simp [hw, Novel.RouteB.Row.places]⟩)
      ⟨(1, .unit), by simp, rfl⟩
    rw [nu010_timeoutOrd_ac5.2] at this
    cases this

/-- Route A refuses an undeclared mint, and a mint whose timeout writes a coloured place: a
`Mint` row of the shipped Route A plan is declared and its timeout writes no coloured place
(`Novel.RouteA.shipped_mint`). -/
@[evidence cites "NU-010" "A transition that writes a coloured place without consuming one and is not declared keeps the net off both routes; what the executor writes on timeout is never a mint, declared or not (Route A half)"]
theorem NU_010_routeA_mint {C : List PlaceId} {ext : Bool} {s : Novel.RouteA.SrcRow}
    {outs : List PlaceId}
    (h : Novel.RouteA.classifyRowG C ext (Novel.RouteA.shippedGate C s).1
      (Novel.RouteA.shippedGate C s).2 s.ms s.t s.d = some (.mint outs)) :
    s.declared = true ∧ ∀ w ∈ s.tw, w.1 ∉ C :=
  Novel.RouteA.shipped_mint h

end Libpetri.Spec
