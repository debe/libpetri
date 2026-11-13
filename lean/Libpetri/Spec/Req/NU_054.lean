import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Reference.Nu
import Libpetri.Spec.Req.NU_020
import Libpetri.Spec.Req.NU_051
import Libpetri.Spec.Text.NU_054

set_option linter.missingDocs true

/-!
# NU-054: Join relay (`spec/12-nu-nets.md`)

A matched join ([NU-020]) may declare **relay targets**: output places onto which it writes the
name it matched. NU-054 says how such a declaration is built, what the executor checks on every
firing, and how the fragment classifier of the ν verifiers reads it.

Three blocks share the ID here:

* `NU_054_build` (kind F), over a transition builder `NB`: a relay target declared twice, or one
  the output spec does not name, fails the build, with a message naming the transition and an
  offending relay target when every other check passes; a relay target that is one of the join's
  own match keys (the correlated self-loop) is allowed.
* `NU_054_check` (kind B), over a ν firing relation `R`: on a transition that builds, every token
  a firing deposits into a relay target, from an output branch or from the timeout outcome, has a
  name under that target's key projection, and that name is the chosen name. A completion that
  breaks the check is not a firing.
* `NU_054_verifier` (kind F), over an abstract fragment classifier `C` (`GlossaryNuVer.lean`):
  BASE refuses a join that writes a coloured place whatever it declares; EXTENDED refuses one that
  writes a coloured place it does not declare as a relay target; a coloured timeout write must
  forward a match key; EXTENDED admits a join that meets every fragment rule, with its declared
  relay targets; an admitted join relays to its declared targets under EXTENDED and to none under
  BASE; under BASE a relay declaration changes no role.

The witnesses are `refNuBuild` and `RefNuFire` (`Reference/Nu.lean`) and the shipped classifier
`refClassify` (`Novel.RouteB.classifyS`). The failure outcome of a firing that breaks the check
(a `TransitionFailed` event, the checked batch withheld, the relay error before the [IO-016]
multiplicity warning) is the block `NU_054_fail` (`NU_054_fail.lean`), on RefExec's fail label; it is not here.

Rulings: D24 (a) (the timeout outcome is not validated against the output spec, but the relay
check runs on it), D37 (a) (a key projection is partial: a token may have no name).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## NU-054, build checks -/

requirement NU_054_build
  id "NU-054"
  title "Join Relay (build checks)"
  kind F
  scope "every transition builder, on every construction path"
  source verbatim "spec/12-nu-nets.md"
  covers NU_054.s1, NU_054.s2, NU_054.s3
  reading "Let NB be the transition builder (NB t = none: t builds)."
          "For every ν transition t whose match specification lists one place twice among its relay targets, NB fails on t."
          "For every ν transition t whose match specification has a relay target p that the output spec of t does not name (no output arc on p, glossary: Output arc), NB fails on t."
          "For every ν transition t that builds (NuBuilds) and whose match specification has a relay target that is also one of its match keys, NB succeeds on t."
          "For every ν transition t that passes every other build-time check (it builds without its match, and the match keys distinct input places) and whose relay targets fail the relay checks (one is declared twice or is not an output place), NB fails on t with a message that names t and names a relay target that is declared twice or is not an output place."
  assumes "The model is the transition builder NB for a transition that may carry a match, read as the message a call fails with, none when the transition builds, as in NU_020_build. The reference is refNuBuild, which checks, per relay target in declaration order, 'declared twice' before 'not an output', after the key checks of NU-020 (TransitionBuilder::build in rust/libpetri-core/src/transition.rs, TransitionBuilder.build in typescript/src/core/transition.ts, Transition.Builder.build in java/src/main/java/org/libpetri/core/Transition.java). A relay target is checked when the transition is built, not when the match is built (MatchSpecBuilder::build in rust/libpetri-core/src/match_spec.rs)."
          "'An output of the transition (in at least one branch)' is read as a place the output spec names anywhere, an action branch or the timeout child (glossary: Output arc), as Rust's all_places, TypeScript's and Java's output place sets read it."
          "'Naming the transition and the place' (AC1) is the fourth line, as NU-060's rejection names the caller-side transition: the message contains the transition's name and the name of an offending relay target (MsgNames), whatever else it says. It is stated for a transition that passes every other build-time check, because the checks run in order and a transition that also fails an earlier check gets that check's message (NU_020_build); and it names some offending relay target, the first in declaration order in every runtime, since 'declared twice' and 'not an output' are checked per target in that order. The wording is configuration (kind N); the reference messages (msgRelayTwice, msgRelayNotOutput) are Rust's, as stand-ins, and NU_054_build_mutant_anyMessage_killed shows the line load-bearing. How a path fails (a panic, an exception) is kind N too."
          "Place identity. The places one transition names are assumed to have pairwise distinct names, and a relay target names the place object of the transition's own output arc, as TIME-010 and MOD-006 assume for their places. Java breaks the model only outside that assumption: it detects a relay target declared twice by name but checks relay-is-output with structural Place equality, name and token type (Transition.Builder.build in java/src/main/java/org/libpetri/core/Transition.java), so two relay targets on distinct places that share a name are rejected as declared twice, and a relay target whose place has an output's name but another token type is rejected as not an output. Rust (TransitionBuilder::build in rust/libpetri-core/src/transition.rs), TypeScript (TransitionBuilder.build in typescript/src/core/transition.ts) and Python (py_match_spec in rust/libpetri-py/src/model.rs) compare by name throughout. This is the Place-equality divergence of MOD-024."
          "The converse for relays (a transition whose relay targets are distinct output places builds when it passes every other check) is NU_020_build's last line, whose NuBuilds names every check a matched transition passes. The third line here is its self-loop case, which the spec states as a permission ('A relay target MAY also be one of the join's own match keys'); it is a line so that a builder that refuses a relay target on a key is a forbidden model under this ID (NU_054_build_forbids_noSelfLoop; that builder also breaks NU_020_build). 'Every other build-time check' is the list of the glossary entry Build-time checks, which names the match-key checks of NU-020 and the relay checks here after the output-spec checks (clash nu-a#9, ruling D20 (a)); NuBuilds is that list."
          "Under composition the relay targets are remapped with the keys ([NU-030], [NU-060]); a rewrite that maps two relay targets of one join onto one place yields a relay target declared twice, which the first line rejects at rebuild, since NB is the one builder every construction path goes through (NU_020_build's reading of 'on every construction path'). The rewrite itself is NU-030's and the composition model's (wave W8)."
          "AC1 (a relay target that is not an output of the transition, or is declared twice, is rejected at transition build with an error naming the transition and the place) is the first two lines and the fourth; NU_054_build_nonvacuous shows both rejections, each message naming the transition and the place, and the self-loop accepted."
  signoff "2026-11-13 8456e186fa5fd371 ai"
  statement : ∀ {N K : Type} [DecidableEq N] [ToString N], (NuTrans N K → Option String) → Prop :=
    fun NB =>
      (∀ t ms, t.mspec = some ms → ¬ ms.relayPlaces.Nodup → NB t ≠ none) ∧
      (∀ t ms, t.mspec = some ms → ∀ p ∈ ms.relayPlaces, ¬ OutputArc t.base p → NB t ≠ none) ∧
      (∀ t ms, t.mspec = some ms → NuBuilds t → (∃ p ∈ ms.relayPlaces, p ∈ ms.keyPlaces) →
        NB t = none) ∧
      (∀ t ms, t.mspec = some ms → Builds t.base → KeysDistinct ms → KeysOnInputs t ms →
        ¬ RelaysOK t ms → ∃ m, NB t = some m ∧ MsgNames m t.base.core.name ∧
          ∃ q ∈ ms.relayPlaces, (2 ≤ ms.relayPlaces.count q ∨ ¬ OutputArc t.base q) ∧
            MsgNames m (toString q))

/- The pinned readable form of NU_054_build: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_054_build : {N K : Type} → [DecidableEq N] → [ToString N] → (NuTrans N K → Option String) → Prop :=
fun {N K} [DecidableEq N] [ToString N] NB =>
  (∀ (t : NuTrans N K) (ms : MatchSpec N K), t.mspec = some ms → ¬ms.relayPlaces.Nodup → NB t ≠ none) ∧
    (∀ (t : NuTrans N K) (ms : MatchSpec N K),
        t.mspec = some ms → ∀ p ∈ ms.relayPlaces, ¬OutputArc t.base p → NB t ≠ none) ∧
      (∀ (t : NuTrans N K) (ms : MatchSpec N K),
          t.mspec = some ms → NuBuilds t → (∃ p ∈ ms.relayPlaces, p ∈ ms.keyPlaces) → NB t = none) ∧
        ∀ (t : NuTrans N K) (ms : MatchSpec N K),
          t.mspec = some ms →
            Builds t.base →
              KeysDistinct ms →
                KeysOnInputs t ms →
                  ¬RelaysOK t ms →
                    ∃ m,
                      NB t = some m ∧
                        MsgNames m t.base.core.name ∧
                          ∃ q ∈ ms.relayPlaces,
                            (2 ≤ List.count q ms.relayPlaces ∨ ¬OutputArc t.base q) ∧ MsgNames m (toString q)
-/
#guard_msgs in #print NU_054_build

/-! ## NU-054, the run-time relay check -/

requirement NU_054_check
  id "NU-054"
  title "Join Relay (run-time relay check)"
  kind B
  scope "every executor, with output validation on; one firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  covers NU_054.s4, NU_054.s5
  reading "For every transition t that builds (NuBuilds) with match specification ms and every firing of t in R (an executor with output validation on) with chosen name n that emits e: for every relay target (p, f) of ms and every token x that e puts on p, if f gives x a name m, then m = n."
          "For every such firing: for every relay target (p, f) of ms and every token x that e puts on p, f gives x a name."
  assumes "The model is a ν firing relation R over queue markings of stamped tokens (NuFireRel), as for NU_020_enable: R t M c δ e M' says that t fires from M with chosen name c, delivers δ, its action emits e (every token it deposits, whatever wrote it) and the firing leaves M'. The lines speak of firings that complete: a completion whose emission breaks the check is not a firing of R. The lines quantify over firings with a chosen name some n; that every matched firing has one is NU_020_enable's first line (a firing of a transition with a match specification has a chosen name, and it is eligible), so a model that fired a matched transition with no chosen name is forbidden there and cannot satisfy these lines vacuously. The two lines together are the relay check RelayOk of the reference (RefNuFire), split so that each half has its own forbidden model. The reference runs it on every outcome the output spec offers, an action branch or the timeout outcome (ruling D24 (a): the timeout outcome is not validated against the output spec, but the relay check runs on it, Executor::handle_completion in rust/libpetri-runtime/src/executor_core/executor.rs, processCompletedTransitions in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java and in typescript/src/runtime/bitmap-net-executor.ts), so the timeout outcome of an output spec such as And(A, Timeout(d, B)) fires in every runtime. An executor that validated the timeout outcome against the whole output spec, the Java and TypeScript behaviour RD-01 recorded, would never fire it."
          "A relay target of the branch the firing produced is a relay target the emission puts a token on; a relay target the branch does not write receives nothing, so the lines quantify over every relay target of the match. The lines speak of transitions that build (NuBuilds), as CONC_008_nu does: the runtimes fire only transitions that built, and a transition that builds declares each relay target once (NU_054_build), so one projection per place is checked, as the runtimes' relay_for lookup does (it reads the first relay entry per place). Without the premise a faithful model of that lookup would be forbidden on a match that declares one relay target twice, which never builds."
          "The key projection of a relay target is read as the check reads it (ruling D37 (a): partial). A token whose value is absent (null, undefined, None, the unit token an Out.place leaf deposits in a timeout branch), a value of another type, and a projection that throws or raises all give no name. That the check reports an absent value 'without calling the projection', that a Rust projection is infallible by type, and that a panicking projection propagates like a panic in the action are side effects and failure mechanisms (kind N), not lines: the tests pin them (absent_value_has_no_name_and_the_projection_is_not_called in rust/libpetri-runtime/src/nu_relay_tests.rs; validateRelays in typescript/src/runtime/executor-support.ts and in java/src/main/java/org/libpetri/runtime/ExecutorSupport.java)."
          "What a failing firing does is the block NU_054_fail (NU_054_fail.lean), on RefExec's fail label (ruling D17): it 'fails the firing like any other validation failure, with an error naming the transition, the place, the matched name and the name found', deposits none of the checked batch while tokens of a batch published earlier with ctx.flush() stay, emits no IO-016 AC4 multiplicity WARN because the relay check runs first, and in Rust makes a refused ctx.flush() return Err carrying the relay message; a batch published mid-action is checked when it is published. 'The check is on by default and is skipped only where output validation itself is skipped ([CONC-026])' is the precondition 'While output validation is on' of both quoted sentences: R is the firing relation of an executor with output validation on, and the validation skip, under which the relay check accepts everything with the rest of output validation, is NU_054_fail's (Cfg.SkipsValidation). 'The runtime check is independent of the mode' holds because the lines take no fragment mode."
          "Clash nu-c#8 (ruling D24 (a)): with the relay check a timed-out firing whose timeout outcome writes a unit token, or a forward of another input, into a relay target deposits nothing, where IO-013's quoted sentence says a timed-out firing deposits the tokens of the child. The exception is in IO-013's text (a firing whose timeout outcome fails the relay check fails and deposits none of the tokens of child), which the block IO_013 accounts for through NU_054_check and NU_054_fail, and in IO-014's paragraph on forwarding (a forward into a relay target is checked like every other token of the timeout outcome); this block states the check."
          "AC2 (a join whose action writes into a relay target a token projecting to another name, or to no name, fails that firing; the same net with a conforming action fires normally; both backends in every language agree; a projection that throws fails with the no-name error; no IO-016 AC4 WARN): the refusal is the two lines, worked in NU_054_check_nonvacuous; 'the same net with a conforming action fires normally' is the conjunct NuCovers of the consistency theorem (every enabled matched transition fires with every offered emission that passes the check), shown on the example by NU_054_check_nonvacuous; the failure event is NU_054_fail's, and the error text and the WARN order are test evidence there (kind Q, NU_054_fail's assumes); 'both executor backends in every language agree' is a test obligation (kind Q)."
  signoff "2026-11-13 09e07caac5591a2f ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      (∀ t ms, t.mspec = some ms → NuBuilds t → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun _ _ =>
          ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, ∀ m, r.2 x.val = some m → m = n)) ∧
      (∀ t ms, t.mspec = some ms → NuBuilds t → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun _ _ =>
          ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, r.2 x.val ≠ none))

/- The pinned readable form of NU_054_check: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_054_check : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        NuBuilds t →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun x x_1 =>
              ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, ∀ (m : Nm), r.2 x.val = some m → m = n) ∧
    ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        NuBuilds t →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun x x_1 =>
              ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, r.2 x.val ≠ none
-/
#guard_msgs in #print NU_054_check

/-! ## NU-054, the fragment classifier -/

/-- Every match key in `ks` is consumed through an input arc of `T`, and every input arc of `T` on
a match key has a fixed count: [IO-001] `One` or [IO-002] `Exactly`. -/
def KeysFixedCount (T : Novel.RouteB.NuTrans) (ks : List PlaceId) : Prop :=
  ∀ k ∈ ks, (∃ s ∈ T.base.inputs, s.place = k) ∧
    ∀ s ∈ T.base.inputs, s.place = k → s.card = .one ∨ ∃ c, s.card = .exactly c

requirement NU_054_verifier
  id "NU-054"
  title "Join Relay (fragment classifier)"
  kind F
  scope "the fragment classifier of every ν verifier"
  source verbatim "spec/12-nu-nets.md"
  covers NU_054.s9, NU_054.s10, NU_054.s11, NU_054.s12, NU_054.s13, NU_054.s14, NU_054.s15
  reading "For every coloured set col, mint declaration, list of timeout writes tw and transition T with match keys ks: under BASE, if some outcome (row) of T writes a coloured place, T gets no role."
          "Under EXTENDED, if some outcome of T writes a coloured place that is not one of T's relay targets, T gets no role."
          "In either mode, if some timeout write into a coloured place is not a forward of one of the places ks, T gets no role."
          "Under EXTENDED, if T has no reset, read or inhibitor arc on a coloured place, every row puts one token and no drained batch into each coloured place it writes, every coloured place a row writes is a relay target of T, every coloured input of T is on a place of ks, every place of ks is consumed through an input of count One or Exactly, and every timeout write into a coloured place forwards a place of ks, then T gets the join role with some counted keys whose places are ks, in some order, and with a relay list holding exactly T's relay targets."
          "Under EXTENDED, if T gets the join role with relay list rel, then a place is in rel exactly when it is one of T's relay targets."
          "Under BASE, if T gets the join role with relay list rel, then rel is empty."
          "Under BASE, T gets the role that T with its relay list emptied gets."
  assumes "The classifier is per transition, as in NU_051 (glossary: Fragment classifier): no role means the net falls back to the sound over-approximation with an 'EXTENDED declined' note ([NU-050]). The coloured set is an argument; that the relay targets of every join are unioned into it under EXTENDED, before the fragment rules are checked, and that BASE colours the match keys alone, is the coloured-set computation, which no block states: the verifier pipeline model (Verifier/Pipeline.lean, the block VER_003) does not model how a ν verifier builds the coloured set. It is Q-tested: Rust name_fragment.rs extended_colours_relay_targets_and_the_join_carries_them and a_relay_target_no_join_consumes_is_coloured_and_its_read_arc_rejects, and name_coloured_encoder.rs a_relay_target_no_join_consumes_is_coloured_and_produced_by_the_join (under EXTENDED a relay target is coloured, also one no join consumes). 'Under BASE the relay declarations are ignored by the analyzer' is the seventh line for the classifier (a relay declaration changes no BASE role, whatever the coloured set), with the first and sixth lines (the declarations neither let a coloured output in nor reach the role), and the pipeline's BASE coloured set for the rest."
          "The outcomes of a transition are Route B's rows (Novel.RouteB.NuTrans.rows: the action branches, then the timeout deposits), the timeout writes are the separate argument tw (Rust timeout_writes), as in NU_051. A unit token is TW.unit; a forward of an input is TW.forward with the input's place. 'No reset, read or inhibitor arc on a coloured place' and 'one token, and never a drained batch' are NU_051's ColouredTestArc and SingleColouredWrites."
          "The fourth line is the classification the relay exists for ('Relay targets change the classification only under EXTENDED'): it is the admission, on NU_051's pattern for the consume role, and makes a classifier that never gives a relaying join a role a forbidden model (NU_054_verifier_forbids_never). Its conditions are those of the shipped classifier (Novel.RouteB.classifyT and classifyS, rust/libpetri-verification/src/name_fragment.rs classify): the markdown names the coloured-output, off-key, test-arc and timeout rules; 'consumes each match key at a fixed count' is the key-count rule of the matched-join fragment (keyCount: One gives 1, Exactly(n) gives n, All and AtLeast are refused), which the markdown does not spell out and which the sentence states as the runtimes do. The counted keys (place and count per key) are the join's enabling counts, Route B's subject (NU-055); the line fixes only that their places are the keys, in some order."
          "The fourth and fifth lines read the relay targets as a set and the counted keys up to order, as the quotes do ('with the relay targets it declares', 'exactly the relay targets the transition declares'). The runtimes give the counted keys in code-point order of the place names and hold the relay targets as a set: Rust name_fragment.rs classify sorts coloured_in and collects relay_to into a BTreeSet; Java NameFragment.classify sorts colouredIn by CodePointOrder and copies relayTo into a Set (NameFragment.java); TypeScript name-fragment.ts classify sorts colouredIn by compareCodePoints and builds relayTo as a Set (verification/analysis/name-fragment.ts). The reference refClassify keeps the declared order of both; nu054_sortedClassify, which sorts both as the runtimes do, meets the block too (NU_054_verifier_sorted). Which order the counted keys take matters only to Route B's enabling test with a zero-count key (Novel.RouteB.joinEnab_perm_of_pos, zeroKey_order_matters), which is NU-055's concern, not the classifier's."
          "The fragment rules of the relay that are coloured-place rules of NU-051 are NU_051's lines, which apply to a relay target once it is coloured: 'a relay target that the same join also consumes through an input that is not one of its match keys' is NU_051's fifth line, 'a relay target carrying a read, inhibitor or reset arc on any transition' its fourth. 'A relay target no join consumes is still coloured: its consumers take the [NU-051] consume role and any other producer the mint role, when it is a declared mint ([NU-010])' is NU_051's and NU-010's lines over that coloured set. 'A coloured output of a join that is not a relay target, or a relay target produced with a count other than one, is outside the fragment' is the second line here and the branch rule (Novel.RouteB.classifyT: each coloured place a branch writes takes exactly one token, never a drained batch)."
          "The name step of a relaying join ('A join firing on symbol s removes s from its keys as before, then adds s once to each relay target in the fired branch'; a branch with no relay target drains s; an Xor join may relay on one branch and drain on another; the step mints nothing and commutes with renaming) is Route B's executable model, not a line: Novel.RouteB.joinStep with relOut (Name.lean, Graph.lean), joinStep_sym, and routeB_equivariant for the relay role. The Route A update of a relaying join (the per-colour guards and update terms, no update term on a key that is also a relay target) and the colour-slot weights are NU-053's encoding and the script goldens (VER-013), test-cited (kind Q). The canonical key format and byte parity are VER-012's subject."
          "'A verifier that meets a relay declaration under BASE MUST say in its report that the declaration was ignored and name EXTENDED' and the 'EXTENDED declined' note are report lines (kind N), which no block states; they are Q-tested (the BASE note: Rust tests/nu_join_relay fig12c_under_base_ignores_the_declaration_and_says_so, Java JoinRelayTest, TypeScript tests/verification/nu-join-relay.test.ts, Python tests/test_nu_join_relay.py test_base_ignores_the_declaration_and_says_so; the 'EXTENDED declined' note: NU_051's assumes); clash nu-c#7 (ruling D20 (a)) made the body's SHOULD the MUST of AC5."
          "The timeout rule is stated for the coloured places the timeout writes; under EXTENDED those include the relay targets, so it is the spec's 'a join whose Timeout branch writes a relay target by anything other than a forward of one of its match keys'. The run-time reason ('an Out.place leaf writes a unit token with no name, and a forward of another input carries that input's name, so that firing fails and deposits nothing') is NU_054_check with NU_054_fail."
          "AC3 (a relay join chain decided through Route B), AC5 (the BASE verdict unchanged, the report naming the ignored declaration), AC6 (Route A and Route B agree on small relay fixtures) and AC7 (no canonical key changes for a net without relay declarations) are verdict, report and fixture lines, which no block states (kind Q): AC3, AC5 and AC6 are tested in Rust tests/nu_join_relay (chain_reaches_done_and_is_deadlock_free_via_route_b, fig12c_under_base_ignores_the_declaration_and_says_so, routes_agree_on_the_relay_fixtures), with the same queries in Java JoinRelayTest and TypeScript tests/verification/nu-join-relay.test.ts, over spec/verification-fixtures/nu-relay-fixtures.json; AC7 is about VER-012's canonical keys, and no test names it. Their classifier halves are lines here: AC3's 'rather than falling back' for the join is the fourth line, AC5's 'the verdict it got without one' is the seventh (the BASE classification, and so the BASE net the verdict is computed on, does not see the declaration), shown in NU_054_verifier_nonvacuous. AC4's rejections are the second and third lines and NU_051's fourth and fifth (its 'neither Route B nor Route A decides it' has a Route B witness only: Novel.RouteA.shippedGate does not model the join-timeout refusal, as its docstring in Plan.lean says, so the Route A half is test-cited); NU_054_verifier_nonvacuous shows the unit-token timeout refused and the timeout forwarding a match key admitted."
  signoff "2026-11-13 1a773a8a0094cc2b ai"
  statement : Classifier → Prop :=
    fun C =>
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks, T.keys = some ks →
        (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) →
        C col .base declared tw T = none) ∧
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks, T.keys = some ks →
        (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true ∧ p ∉ T.relays) →
        C col .extended declared tw T = none) ∧
      (∀ col mode declared tw (T : Novel.RouteB.NuTrans) ks, T.keys = some ks →
        (∃ w ∈ tw, col w.1 = true ∧ ∀ k ∈ ks, w.2 ≠ Novel.RouteB.TW.forward k) →
        C col mode declared tw T = none) ∧
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks, T.keys = some ks →
        ¬ ColouredTestArc col T → SingleColouredWrites col T →
        (∀ r ∈ T.rows, ∀ p ∈ r.places, col p = true → p ∈ T.relays) →
        (∀ s ∈ ColouredInputs col T, s.place ∈ ks) → KeysFixedCount T ks →
        (∀ w ∈ tw, col w.1 = true → ∃ k ∈ ks, w.2 = Novel.RouteB.TW.forward k) →
        ∃ cin rel, (cin.map Prod.fst).Perm ks ∧ (∀ p, p ∈ rel ↔ p ∈ T.relays) ∧
          C col .extended declared tw T = some (.join cin rel)) ∧
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks cin rel, T.keys = some ks →
        C col .extended declared tw T = some (.join cin rel) → ∀ p, p ∈ rel ↔ p ∈ T.relays) ∧
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks cin rel, T.keys = some ks →
        C col .base declared tw T = some (.join cin rel) → rel = []) ∧
      (∀ col declared tw (T : Novel.RouteB.NuTrans) ks, T.keys = some ks →
        C col .base declared tw T = C col .base declared tw { T with relays := [] })

/- The pinned readable form of NU_054_verifier: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.NU_054_verifier : Classifier → Prop :=
fun C =>
  (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW)) (T : Novel.RouteB.NuTrans)
      (ks : List PlaceId),
      T.keys = some ks →
        (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true) → C col Novel.RouteB.Mode.base declared tw T = none) ∧
    (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW)) (T : Novel.RouteB.NuTrans)
        (ks : List PlaceId),
        T.keys = some ks →
          (∃ r ∈ T.rows, ∃ p ∈ r.places, col p = true ∧ p ∉ T.relays) →
            C col Novel.RouteB.Mode.extended declared tw T = none) ∧
      (∀ (col : PlaceId → Bool) (mode : Novel.RouteB.Mode) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW))
          (T : Novel.RouteB.NuTrans) (ks : List PlaceId),
          T.keys = some ks →
            (∃ w ∈ tw, col w.1 = true ∧ ∀ k ∈ ks, w.2 ≠ Novel.RouteB.TW.forward k) → C col mode declared tw T = none) ∧
        (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW)) (T : Novel.RouteB.NuTrans)
            (ks : List PlaceId),
            T.keys = some ks →
              ¬ColouredTestArc col T →
                SingleColouredWrites col T →
                  (∀ r ∈ T.rows, ∀ p ∈ r.places, col p = true → p ∈ T.relays) →
                    (∀ s ∈ ColouredInputs col T, s.place ∈ ks) →
                      KeysFixedCount T ks →
                        (∀ w ∈ tw, col w.1 = true → ∃ k ∈ ks, w.2 = Novel.RouteB.TW.forward k) →
                          ∃ cin rel,
                            (List.map Prod.fst cin).Perm ks ∧
                              (∀ (p : PlaceId), p ∈ rel ↔ p ∈ T.relays) ∧
                                C col Novel.RouteB.Mode.extended declared tw T =
                                  some (Novel.RouteB.Role.join cin rel)) ∧
          (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW)) (T : Novel.RouteB.NuTrans)
              (ks : List PlaceId) (cin : List (PlaceId × ℕ)) (rel : List PlaceId),
              T.keys = some ks →
                C col Novel.RouteB.Mode.extended declared tw T = some (Novel.RouteB.Role.join cin rel) →
                  ∀ (p : PlaceId), p ∈ rel ↔ p ∈ T.relays) ∧
            (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW))
                (T : Novel.RouteB.NuTrans) (ks : List PlaceId) (cin : List (PlaceId × ℕ)) (rel : List PlaceId),
                T.keys = some ks →
                  C col Novel.RouteB.Mode.base declared tw T = some (Novel.RouteB.Role.join cin rel) → rel = []) ∧
              ∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × Novel.RouteB.TW))
                (T : Novel.RouteB.NuTrans) (ks : List PlaceId),
                T.keys = some ks →
                  C col Novel.RouteB.Mode.base declared tw T =
                    C col Novel.RouteB.Mode.base declared tw
                      { base := T.base, rows := T.rows, keys := T.keys, relays := [] }
-/
#guard_msgs in #print NU_054_verifier

/-! ## Holds -/

section RelayMsgs

variable {N : Type} [DecidableEq N] [ToString N]

/-- When the relay checks fail, they fail at a relay target that was seen before (in `seen`),
is declared twice, or is not an output place, and the message is the one for that target. -/
theorem nu054_relayScan_some (t : Trans N) :
    ∀ (seen l : List N) (m : String), relayScan t seen l = some m →
      ∃ q ∈ l, (q ∈ seen ∨ 2 ≤ l.count q ∨ ¬ OutputArc t q) ∧
        (m = msgRelayTwice t q ∨ m = msgRelayNotOutput t q)
  | _, [], m, h => by simp [relayScan] at h
  | seen, p :: ps, m, h => by
    by_cases hp : p ∈ seen
    · simp only [relayScan, hp, if_true, Option.some.injEq] at h
      exact ⟨p, List.mem_cons_self, Or.inl hp, Or.inl h.symm⟩
    · by_cases ho : OutputArc t p
      · simp only [relayScan, hp, ho, if_true, if_false] at h
        obtain ⟨q, hq, hbad, hmsg⟩ := nu054_relayScan_some t (p :: seen) ps m h
        refine ⟨q, List.mem_cons_of_mem _ hq, ?_, hmsg⟩
        rcases hbad with hs | hc | ho'
        · rcases List.mem_cons.1 hs with rfl | hs
          · have := List.count_pos_iff.2 hq
            exact Or.inr (Or.inl (by rw [List.count_cons_self]; omega))
          · exact Or.inl hs
        · exact Or.inr (Or.inl (le_trans hc List.count_le_count_cons))
        · exact Or.inr (Or.inr ho')
      · simp only [relayScan, hp, ho, if_false, Option.some.injEq] at h
        exact ⟨p, List.mem_cons_self, Or.inr (Or.inr ho), Or.inr h.symm⟩

omit [DecidableEq N] in
/-- The message for a relay target declared twice names the transition and the place. -/
theorem nu054_msgRelayTwice_names (t : Trans N) (q : N) :
    MsgNames (msgRelayTwice t q) t.core.name ∧ MsgNames (msgRelayTwice t q) (toString q) := by
  unfold msgRelayTwice
  exact ⟨msgNames_app _ (msgNames_app _ (msgNames_app _ (msgNames_end _ _))),
    msgNames_app _ (msgNames_end _ _)⟩

omit [DecidableEq N] in
/-- The message for a relay target that is not an output names the transition and the place. -/
theorem nu054_msgRelayNotOutput_names (t : Trans N) (q : N) :
    MsgNames (msgRelayNotOutput t q) t.core.name ∧
      MsgNames (msgRelayNotOutput t q) (toString q) := by
  unfold msgRelayNotOutput
  exact ⟨msgNames_app _ (msgNames_app _ (msgNames_app _ (msgNames_end _ _))),
    msgNames_app _ (msgNames_end _ _)⟩

end RelayMsgs

/-- ✓ The reference builder satisfies the build lines: it rejects a relay target declared twice
and one the output spec does not name, with a message naming the transition and the offending
relay target, and it accepts every transition that builds, a correlated self-loop included
(`refNuBuild_eq_none_iff`). -/
@[evidence holds NU_054_build]
theorem NU_054_build_reference {N K : Type} [DecidableEq N] [ToString N] :
    NU_054_build (refNuBuild (N := N) (K := K)) := by
  refine ⟨fun t ms hm hd h => hd (((refNuBuild_eq_none_iff t).1 h).2 ms hm).2.2.1,
    fun t ms hm p hp ho h => ho ((((refNuBuild_eq_none_iff t).1 h).2 ms hm).2.2.2 p hp),
    fun t _ _ hb _ => (refNuBuild_eq_none_iff t).2 hb, fun t ms hm hb hkd hko hr => ?_⟩
  have hb' : refBuild t.base = none := (refBuild_eq_none_iff t.base).2 hb
  have hfr : firstRepeat [] ms.keyPlaces = none :=
    (firstRepeat_eq_none_iff [] _).2 ⟨hkd, by simp⟩
  have hfi : ms.keyPlaces.find? (fun p => decide (p ∉ inPlaces t.base)) = none :=
    List.find?_eq_none.2 fun p hp => by simpa using hko p hp
  have hscan : refNuBuild t = relayScan t.base [] ms.relayPlaces := by
    simp only [refNuBuild, hb', nuChecks, hm, hfr, hfi]
  cases hs : relayScan t.base [] ms.relayPlaces with
  | none =>
    obtain ⟨h1, -, h3⟩ := (relayScan_eq_none_iff t.base [] _).1 hs
    exact absurd ⟨h1, h3⟩ hr
  | some m =>
    obtain ⟨q, hq, hbad, hmsg⟩ := nu054_relayScan_some t.base [] ms.relayPlaces m hs
    refine ⟨m, hscan.trans hs, ?_, q, hq, ?_, ?_⟩
    · rcases hmsg with rfl | rfl
      · exact (nu054_msgRelayTwice_names t.base q).1
      · exact (nu054_msgRelayNotOutput_names t.base q).1
    · rcases hbad with h | h | h
      · exact absurd h List.not_mem_nil
      · exact Or.inl h
      · exact Or.inr h
    · rcases hmsg with rfl | rfl
      · exact (nu054_msgRelayTwice_names t.base q).2
      · exact (nu054_msgRelayNotOutput_names t.base q).2

/-- ✓ RefNuFire satisfies the relay-check lines: every reference firing passes `RelayOk`, so every
token it deposits into a relay target projects to the chosen name. -/
@[evidence holds NU_054_check]
theorem NU_054_check_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_054_check (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun t ms hm _ n δ e M M' hf r hr x hx m hm' => ?_,
    fun t ms hm _ n δ e M M' hf r hr x hx => ?_⟩
  · obtain ⟨n', hn, -, -, -, hrel, -⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rw [hrel r hr x hx] at hm'
    exact (Option.some.inj hm').symm
  · obtain ⟨n', hn, -, -, -, hrel, -⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rw [hrel r hr x hx]
    exact Option.some_ne_none _

/-! ### Bridge lemmas over the shipped classifier -/

/-- `keyCount` keeps the place it was asked for. -/
theorem nu054_keyCount_fst {T : Novel.RouteB.NuTrans} {p : PlaceId} {x : PlaceId × ℕ}
    (h : Novel.RouteB.keyCount T p = some x) : x.1 = p := by
  unfold Novel.RouteB.keyCount at h
  split at h
  · split at h <;> first | (cases h; rfl) | cases h
  · cases h

/-- The counted keys of a join are its keys, in order. -/
theorem nu054_mapM_keyCount_fst (T : Novel.RouteB.NuTrans) :
    ∀ (ks : List PlaceId) (cin : List (PlaceId × ℕ)),
      ks.mapM (Novel.RouteB.keyCount T) = some cin → cin.map Prod.fst = ks
  | [], cin, h => by
    simp only [List.mapM_nil] at h
    cases h; rfl
  | k :: ks, cin, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp [nu054_keyCount_fst hx, nu054_mapM_keyCount_fst T ks xs hxs]

/-- `classifyT` gives a matched transition only the join role, whose counted keys are the match
keys. -/
theorem nu054_classifyT_keyed {col : PlaceId → Bool} {mode : Novel.RouteB.Mode}
    {T : Novel.RouteB.NuTrans} {ks : List PlaceId} {r : Novel.RouteB.Role}
    (hk : T.keys = some ks) (h : Novel.RouteB.classifyT col mode true T = some r) :
    ∃ cin rel, r = .join cin rel ∧ cin.map Prod.fst = ks := by
  unfold Novel.RouteB.classifyT at h
  rw [hk] at h
  simp only at h
  split_ifs at h <;>
    first
      | cases h
      | (obtain ⟨cin, hm, hc⟩ := Option.map_eq_some_iff.mp h
         exact ⟨cin, _, hc.symm, nu054_mapM_keyCount_fst T ks cin hm⟩)

/-- When `classifyT` refuses, `classifyS` refuses. -/
theorem nu054_classifyS_none {col : PlaceId → Bool} {mode : Novel.RouteB.Mode} {declared : Bool}
    {tw : List (PlaceId × Novel.RouteB.TW)} {T : Novel.RouteB.NuTrans}
    (h : Novel.RouteB.classifyT col mode true T = none) :
    Novel.RouteB.classifyS col mode declared tw T = none := by
  simp [Novel.RouteB.classifyS, h]

/-- `classifyT` gives the join role the relay list of its mode. -/
theorem nu054_classifyT_join_rel {col : PlaceId → Bool} {mode : Novel.RouteB.Mode}
    {T : Novel.RouteB.NuTrans} {cin : List (PlaceId × ℕ)} {rel : List PlaceId}
    (h : Novel.RouteB.classifyT col mode true T = some (.join cin rel)) :
    rel = if mode = .extended then T.relays else [] := by
  cases hk : T.keys with
  | none =>
    exfalso
    unfold Novel.RouteB.classifyT at h
    rw [hk] at h
    simp only at h
    split_ifs at h
    all_goals first
      | cases h
      | (split at h <;> first | cases h | (split at h <;> cases h))
  | some ks =>
    unfold Novel.RouteB.classifyT at h
    rw [hk] at h
    simp only at h
    generalize hrel : (if mode = .extended then T.relays else []) = r at h ⊢
    split_ifs at h
    obtain ⟨c, _, hc⟩ := Option.map_eq_some_iff.mp h
    cases hc
    rfl

/-- `keyCount` counts a key consumed through inputs of fixed count. -/
theorem nu054_keyCount_some {T : Novel.RouteB.NuTrans} {k : PlaceId}
    (hex : ∃ s ∈ T.base.inputs, s.place = k)
    (hc : ∀ s ∈ T.base.inputs, s.place = k → s.card = .one ∨ ∃ c, s.card = .exactly c) :
    ∃ n, Novel.RouteB.keyCount T k = some (k, n) := by
  unfold Novel.RouteB.keyCount
  cases hf : T.base.inputs.find? (fun s => s.place == k) with
  | none =>
    obtain ⟨s, hs, hp⟩ := hex
    have := List.find?_eq_none.mp hf s hs
    simp [hp] at this
  | some s =>
    have hs := List.mem_of_find?_eq_some hf
    have hp : s.place = k := by simpa using List.find?_some hf
    rcases hc s hs hp with h | ⟨c, h⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨c, by simp [h]⟩

/-- Keys of fixed count are all counted. -/
theorem nu054_mapM_keyCount_some (T : Novel.RouteB.NuTrans) :
    ∀ ks : List PlaceId, KeysFixedCount T ks →
      ∃ cin, ks.mapM (Novel.RouteB.keyCount T) = some cin
  | [], _ => ⟨[], rfl⟩
  | k :: ks, h => by
    obtain ⟨n, hn⟩ := nu054_keyCount_some (h k (by simp)).1 (h k (by simp)).2
    obtain ⟨cin, hcin⟩ :=
      nu054_mapM_keyCount_some T ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    exact ⟨(k, n) :: cin, by simp [List.mapM_cons, hn, hcin]⟩

/-- ✓ The shipped classifier satisfies the relay lines: under BASE a join writing a coloured
place is refused, under EXTENDED one writing a coloured place outside its relay targets is
refused, a coloured timeout write that forwards no match key is refused in both modes, a join
that meets every fragment rule is admitted under EXTENDED with its relay targets, an admitted
join carries its relay targets under EXTENDED and none under BASE, and under BASE the relay
targets change no role. -/
@[evidence holds NU_054_verifier]
theorem NU_054_verifier_reference : NU_054_verifier refClassify := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro col declared tw T ks hk ⟨r, hr, p, hp, hc⟩
    apply nu054_classifyS_none
    have hany : T.rows.any (fun r => r.places.any fun p => col p && !([] : List PlaceId).contains p)
        = true :=
      List.any_eq_true.mpr ⟨r, hr, List.any_eq_true.mpr ⟨p, hp, by simp [hc]⟩⟩
    simp only [Novel.RouteB.classifyT, hk]
    split_ifs <;> first | rfl | simp_all
  · intro col declared tw T ks hk ⟨r, hr, p, hp, hc, hn⟩
    apply nu054_classifyS_none
    have hany : T.rows.any (fun r => r.places.any fun p => col p && !T.relays.contains p)
        = true :=
      List.any_eq_true.mpr ⟨r, hr, List.any_eq_true.mpr ⟨p, hp, by simp [hc, hn]⟩⟩
    simp only [Novel.RouteB.classifyT, hk]
    split_ifs <;> rfl
  · intro col mode declared tw T ks hk ⟨w, hw, hc, hnf⟩
    cases h : refClassify col mode declared tw T with
    | none => rfl
    | some r =>
      exfalso
      obtain ⟨cin, rel, rfl, hcin⟩ := nu054_classifyT_keyed hk (Novel.RouteB.classifyS_sub h)
      obtain ⟨k, hk', hfw⟩ := Novel.RouteB.classifyS_join h w hw hc
      exact hnf k.1 (hcin ▸ List.mem_map_of_mem hk') hfw
  · intro col declared tw T ks hk harc hw hrel hoff hkc htw
    obtain ⟨cin, hcin⟩ := nu054_mapM_keyCount_some T ks hkc
    have hfst := nu054_mapM_keyCount_fst T ks cin hcin
    have h1 := nu051_arcsOk_true harc
    have h2 := nu051_rows_ok hw
    have h3 : T.rows.any (fun r => r.places.any fun p => col p && !T.relays.contains p) = false := by
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨r, hr, hp⟩ := List.any_eq_true.mp hany
      obtain ⟨p, hp, hc⟩ := List.any_eq_true.mp hp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have hm : T.relays.contains p = true := List.contains_iff_mem.mpr (hrel r hr p hp hc.1)
      rw [hm] at hc
      exact absurd hc.2 (by decide)
    have h4 : ((T.base.inputs.filter fun s => col s.place).any fun s => !ks.contains s.place)
        = false := by
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨s, hs, hn⟩ := List.any_eq_true.mp hany
      have hm : ks.contains s.place = true := List.contains_iff_mem.mpr (hoff s hs)
      rw [hm] at hn
      exact Bool.false_ne_true hn
    have hT : Novel.RouteB.classifyT col .extended true T = some (.join cin T.relays) := by
      unfold Novel.RouteB.classifyT
      simp only [h1, h2, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_false, h3, h4,
        hcin, Option.map_some]
    refine ⟨cin, T.relays, hfst ▸ List.Perm.refl _, fun _ => Iff.rfl, ?_⟩
    have h5 : tw.all (fun w => !col w.1 || cin.any fun k => w.2 == Novel.RouteB.TW.forward k.1)
        = true := by
      rw [List.all_eq_true]
      intro w hw
      cases hc : col w.1 with
      | false => rfl
      | true =>
        obtain ⟨k, hk', hf⟩ := htw w hw hc
        rw [← hfst] at hk'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk'
        simp only [Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq]
        exact ⟨x, hx, hf⟩
    simp only [refClassify, Novel.RouteB.classifyS, hT, h5, if_true]
  · intro col declared tw T ks cin rel _ h p
    have : rel = T.relays := by simpa using nu054_classifyT_join_rel (Novel.RouteB.classifyS_sub h)
    rw [this]
  · intro col declared tw T ks cin rel _ h
    simpa using nu054_classifyT_join_rel (Novel.RouteB.classifyS_sub h)
  · intro col declared tw T ks _
    rfl

/-! ## Examples: building

Places are numbers; keys carry no data (`K := Unit`). The join has inputs 0 and 1, keyed both,
and the output spec `and(0, 2)`: it writes its own key 0 back and the place 2. -/

/-- The join of the build examples, with the relay targets `rs`. -/
def nu054_buildT (rs : List (Nat × Unit)) : NuTrans Nat Unit :=
  { base := { core := { name := "j", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := some (.and (.place 0) (.place 2)) }
    mspec := some { keys := [(0, ()), (1, ())], relays := rs } }

/-- ✓ Worked example (AC1 and the self-loop). The join `j` of inputs 0 and 1 that writes 0 and 2
builds with the relay target 2, and with the relay target 0, which is also one of its keys (a
correlated self-loop). It fails to build with the relay target 2 declared twice, with the message
"Transition 'j': relay target '2' is declared twice (NU-054)", and with the relay target 4, which
its output spec does not name, with the message "Transition 'j': relay target '4' is not an
output of the transition (NU-054)". -/
@[evidence nonvacuous NU_054_build]
theorem NU_054_build_nonvacuous :
    refNuBuild (nu054_buildT [(2, ())]) = none ∧ refNuBuild (nu054_buildT [(0, ())]) = none ∧
      refNuBuild (nu054_buildT [(2, ()), (2, ())]) =
        some "Transition 'j': relay target '2' is declared twice (NU-054)" ∧
      refNuBuild (nu054_buildT [(4, ())]) =
        some "Transition 'j': relay target '4' is not an output of the transition (NU-054)" := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Examples: the run-time check

The join `j1` of AC4: correlated inputs A = 0 and B = 1 (a token's name is its value), relay
target C = 2, and the sink E = 3. Value 0 stands for an absent value (the unit token of an
`Out.place` leaf in a timeout branch): the relay projection gives it no name. -/

/-- The relay projection of the examples: value 0 (an absent value) has no name; every other
value is its own name. -/
def nu054_relKey : KeyFn Nat Nat := fun v => if v = 0 then none else some v

/-- The match of `j1`: keys on 0 and 1, relay target 2. -/
def nu054_ms : MatchSpec Nat (KeyFn Nat Nat) :=
  { keys := [(0, nu020_key), (1, nu020_key)], relays := [(2, nu054_relKey)] }

/-- `j1` with the output spec `o`. -/
def nu054_j1 (o : Out Nat) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "j1", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := some o }
    mspec := some nu054_ms }

/-- AC4's first output spec: `xor(and(C, E), timeout(C))`. -/
def nu054_outUnit : Out Nat := .xor (.and (.place 2) (.place 3)) (.timeout (.place 2))

/-- `j1` with AC4's first output spec builds: two distinct keys on its inputs, and the relay
target C an output. -/
theorem nu054_j1_builds : NuBuilds (nu054_j1 nu054_outUnit) :=
  (refNuBuild_eq_none_iff _).1 (by decide)

/-- AC4's second output spec: `xor(and(C, E), timeout(forwardInput(A, C)))`. -/
def nu054_outFwd : Out Nat := .xor (.and (.place 2) (.place 3)) (.timeout (.forward 0 2))

/-- The marking: A holds X@0, B holds X@1 (X = 1). -/
def nu054_M : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0] else if p = 1 then [nu020_tok 1 1] else []

/-- A conforming action outcome: X into C, a token into E. -/
def nu054_eGood : List (Nat × Stamped Nat) := [(2, nu020_tok 1 5), (3, nu020_tok 7 5)]

/-- An action outcome with Y (= 2) in C. -/
def nu054_eOther : List (Nat × Stamped Nat) := [(2, nu020_tok 2 5), (3, nu020_tok 7 5)]

/-- The timeout outcome of `timeout(C)`: a unit token in C. -/
def nu054_eUnit : List (Nat × Stamped Nat) := [(2, nu020_tok 0 5)]

/-- The timeout outcome of `timeout(forwardInput(A, C))`: the X@0 token of A, forwarded to C. -/
def nu054_eFwd : List (Nat × Stamped Nat) := [(2, nu020_tok 1 0)]

/-- An emission whose tokens in C all project to X passes the relay check of `j1`. -/
theorem nu054_relayOk {e : List (Nat × Stamped Nat)}
    (h : ∀ x ∈ qEmittedTo e 2, nu054_relKey x.val = some 1) : RelayOk nu054_ms 1 e := by
  intro r hr x hx
  simp only [nu054_ms, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact h x hx

/-- A reference firing of `j1` passes the relay check. -/
theorem nu054_fire_relayOk {o : Out Nat} {δ e M'}
    (hf : RefNuFire (nu054_j1 o) nu054_M (some 1) δ e M') : RelayOk nu054_ms 1 e := by
  obtain ⟨n, hn, -, -, -, hrel, -⟩ := (refNuFire_matched rfl nu054_M _ δ e M').1 hf
  cases hn
  exact hrel

/-- ✓ Worked example (AC2, AC4). The join `j1` fires with X on A = [X@0], B = [X@1] when its
action writes X into the relay target C (and a token into E), and when its timeout forwards A's
X@0 token into C. It has no firing when the action writes Y into C, nor when the timeout writes a
unit token into C: that token has no name. -/
@[evidence nonvacuous NU_054_check]
theorem NU_054_check_nonvacuous :
    RefNuFire (nu054_j1 nu054_outUnit) nu054_M (some 1)
        (nuDelivered nu054_ms (nu054_j1 nu054_outUnit) nu054_M 1) nu054_eGood
        (qAppend (nuConsume nu054_ms (nu054_j1 nu054_outUnit) nu054_M 1) nu054_eGood) ∧
      RefNuFire (nu054_j1 nu054_outFwd) nu054_M (some 1)
        (nuDelivered nu054_ms (nu054_j1 nu054_outFwd) nu054_M 1) nu054_eFwd
        (qAppend (nuConsume nu054_ms (nu054_j1 nu054_outFwd) nu054_M 1) nu054_eFwd) ∧
      (¬ ∃ δ M', RefNuFire (nu054_j1 nu054_outUnit) nu054_M (some 1) δ nu054_eOther M') ∧
      (¬ ∃ δ M', RefNuFire (nu054_j1 nu054_outUnit) nu054_M (some 1) δ nu054_eUnit M') := by
  refine ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, by decide⟩,
      nu054_relayOk (by decide), rfl, rfl⟩,
    ⟨1, rfl, by decide, by decide, ⟨.timedOut 0, by decide⟩,
      nu054_relayOk (by decide), rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨δ, M', hf⟩
    have := nu054_fire_relayOk hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 2 5)
      (by decide)
    revert this; decide
  · rintro ⟨δ, M', hf⟩
    have := nu054_fire_relayOk hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 0 5)
      (by decide)
    revert this; decide

/-! ## Examples: the fragment classifier

Route B's view of `j1`: keys 0 and 1 at count one, rows `[2, 3]` (the action branch) and `[2]`
(the timeout outcome), relay target 2. Under EXTENDED the coloured set is `{0, 1, 2}` (the keys
and the relay target); under BASE it is `{0, 1}` (the keys alone). -/

/-- The coloured set under EXTENDED: the keys 0, 1 and the relay target 2. -/
def nu054_colExt : PlaceId → Bool := fun p => [0, 1, 2].contains p

/-- The coloured set under BASE: the keys 0, 1. -/
def nu054_colBase : PlaceId → Bool := fun p => [0, 1].contains p

/-- `j1` as Route B reads it, with the relay targets `rs`. -/
def nu054_vj1 (rs : List PlaceId) : Novel.RouteB.NuTrans where
  base := { name := "j1", inputs := [Novel.RouteB.inOne 0, Novel.RouteB.inOne 1], inhibitors := [],
            reads := [], resets := [] }
  rows := [⟨[2, 3], []⟩, ⟨[2], []⟩]
  keys := some [0, 1]
  relays := rs

/-- ✓ Worked example (AC3, AC4, AC5). Under EXTENDED the join `j1` that relays to C = 2 gets the
join role with relay target 2, also when its timeout forwards the key A = 0 into C; it gets no
role when its timeout writes a unit token into C, and none without the relay declaration (C is
then a re-mint). Under BASE, with C coloured, it gets no role whatever it declares; with the keys
alone coloured, as BASE computes them, it gets the join role with no relay target, the role it
gets without the declaration. -/
@[evidence nonvacuous NU_054_verifier]
theorem NU_054_verifier_nonvacuous :
    refClassify nu054_colExt .extended false [] (nu054_vj1 [2]) =
        some (.join [(0, 1), (1, 1)] [2]) ∧
      refClassify nu054_colExt .extended false [(2, .forward 0)] (nu054_vj1 [2]) =
        some (.join [(0, 1), (1, 1)] [2]) ∧
      refClassify nu054_colExt .extended false [(2, .unit)] (nu054_vj1 [2]) = none ∧
      refClassify nu054_colExt .extended false [] (nu054_vj1 []) = none ∧
      refClassify nu054_colExt .base false [] (nu054_vj1 [2]) = none ∧
      refClassify nu054_colBase .base false [] (nu054_vj1 [2]) =
        some (.join [(0, 1), (1, 1)] []) ∧
      refClassify nu054_colBase .base false [] (nu054_vj1 []) =
        some (.join [(0, 1), (1, 1)] []) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## A classifier that sorts, as the runtimes do -/

/-- A join role with its counted keys and its relay targets sorted by place, as the runtimes give
them (Rust `coloured_in.sort()` and a `BTreeSet` of relay targets, Java and TypeScript sort by
code point and hold a set). Every other role is unchanged. -/
def nu054_sortRole : Novel.RouteB.Role → Novel.RouteB.Role
  | .join cin rel =>
      .join (cin.insertionSort fun a b => a.1 ≤ b.1) (rel.insertionSort fun a b => a ≤ b)
  | r => r

/-- The shipped classifier with every join role sorted (`nu054_sortRole`). -/
def nu054_sortedClassify : Classifier := fun col mode declared tw T =>
  (refClassify col mode declared tw T).map nu054_sortRole

/-- A sorted role that is a join comes from a join, with the same places up to order. -/
theorem nu054_sortRole_join {r : Novel.RouteB.Role} {cin : List (PlaceId × ℕ)} {rel : List PlaceId}
    (h : nu054_sortRole r = .join cin rel) :
    ∃ cin0 rel0, r = .join cin0 rel0 ∧ rel = rel0.insertionSort (fun a b => a ≤ b) := by
  cases r with
  | join cin0 rel0 =>
    simp only [nu054_sortRole, Novel.RouteB.Role.join.injEq] at h
    exact ⟨cin0, rel0, rfl, h.2.symm⟩
  | _ => simp [nu054_sortRole] at h

/-- ✓ The block reads the counted keys up to order and the relay targets as a set: the classifier
that sorts both, as the runtimes do, meets it as the reference does. A block that asked for the
declared order would forbid all three runtimes on a join whose keys or relay targets are declared
out of order. -/
theorem NU_054_verifier_sorted : NU_054_verifier nu054_sortedClassify := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := NU_054_verifier_reference
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro col declared tw T ks hk h
    simp [nu054_sortedClassify, r1 col declared tw T ks hk h]
  · intro col declared tw T ks hk h
    simp [nu054_sortedClassify, r2 col declared tw T ks hk h]
  · intro col mode declared tw T ks hk h
    simp [nu054_sortedClassify, r3 col mode declared tw T ks hk h]
  · intro col declared tw T ks hk harc hw hrel hoff hkc htw
    obtain ⟨cin, rel, hp, hr, hc⟩ := r4 col declared tw T ks hk harc hw hrel hoff hkc htw
    refine ⟨cin.insertionSort (fun a b => a.1 ≤ b.1), rel.insertionSort (fun a b => a ≤ b),
      ((List.perm_insertionSort _ cin).map Prod.fst).trans hp,
      fun p => (List.perm_insertionSort _ rel).mem_iff.trans (hr p), ?_⟩
    simp [nu054_sortedClassify, hc, nu054_sortRole]
  · intro col declared tw T ks cin rel hk h p
    obtain ⟨r, hr, hs⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨cin0, rel0, rfl, rfl⟩ := nu054_sortRole_join hs
    exact (List.perm_insertionSort _ rel0).mem_iff.trans (r5 col declared tw T ks cin0 rel0 hk hr p)
  · intro col declared tw T ks cin rel hk h
    obtain ⟨r, hr, hs⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨cin0, rel0, rfl, rfl⟩ := nu054_sortRole_join hs
    rw [r6 col declared tw T ks cin0 rel0 hk hr]
    rfl
  · intro col declared tw T ks hk
    simp only [nu054_sortedClassify, r7 col declared tw T ks hk]

/-- The sorted classifier on `j1` with its keys and relay targets declared out of order: keys
`[1, 0]` and relay targets `[3, 2]` come back as `[(0, 1), (1, 1)]` and `[2, 3]`, a role the
reference does not give, which the fourth and fifth lines accept. -/
theorem nu054_sorted_reorders :
    nu054_sortedClassify (fun p => [0, 1, 2, 3].contains p) .extended false []
        { nu054_vj1 [3, 2] with keys := some [1, 0], rows := [⟨[2, 3], []⟩] } =
      some (.join [(0, 1), (1, 1)] [2, 3]) ∧
    refClassify (fun p => [0, 1, 2, 3].contains p) .extended false []
        { nu054_vj1 [3, 2] with keys := some [1, 0], rows := [⟨[2, 3], []⟩] } =
      some (.join [(1, 1), (0, 1)] [3, 2]) := by
  refine ⟨by decide, by decide⟩

/-! ## Forbidden models: building -/

/-- A transition builder that runs `refBuild`'s checks and the key checks, then the relay check
`rc` in place of NU-054's. -/
def nu054_NB (rc : NuTrans Nat Unit → MatchSpec Nat Unit → Bool) (t : NuTrans Nat Unit) :
    Option String :=
  match refBuild t.base with
  | some e => some e
  | none => match t.mspec with
    | none => none
    | some ms => if KeysDistinct ms ∧ KeysOnInputs t ms ∧ rc t ms = true then none else some "bad"

/-- ✗ A builder that checks only that every relay target is an output accepts the relay target 2
declared twice; the first line fails. -/
@[evidence forbids NU_054_build]
theorem NU_054_build_forbids_noTwice :
    ¬ NU_054_build (nu054_NB fun t ms => decide (∀ p ∈ ms.relayPlaces, OutputArc t.base p)) := by
  intro h
  exact h.1 (nu054_buildT [(2, ()), (2, ())]) _ rfl (by decide) (by decide)

/-- ✗ A builder that checks only that the relay targets are distinct accepts the relay target 4,
which the output spec does not name; the second line fails. -/
@[evidence forbids NU_054_build]
theorem NU_054_build_forbids_noOutput :
    ¬ NU_054_build (nu054_NB fun _ ms => decide ms.relayPlaces.Nodup) := by
  intro h
  exact h.2.1 (nu054_buildT [(4, ())]) _ rfl 4 (by decide) (by decide) (by decide)

/-- ✗ A builder that refuses a relay target that is also a match key refuses the correlated
self-loop that relays to its key 0; the third line fails. -/
@[evidence forbids NU_054_build]
theorem NU_054_build_forbids_noSelfLoop :
    ¬ NU_054_build (nu054_NB fun t ms =>
      decide (RelaysOK t ms ∧ ∀ p ∈ ms.relayPlaces, p ∉ ms.keyPlaces)) := by
  intro h
  exact absurd (h.2.2.1 (nu054_buildT [(0, ())]) _ rfl (by decide) ⟨0, by decide, by decide⟩)
    (by decide)

/-- NU-054's build block without its naming line: the first three lines. -/
def NU_054_build_mutant_anyMessage {N K : Type} [DecidableEq N] (NB : NuTrans N K → Option String) :
    Prop :=
  (∀ t ms, t.mspec = some ms → ¬ ms.relayPlaces.Nodup → NB t ≠ none) ∧
  (∀ t ms, t.mspec = some ms → ∀ p ∈ ms.relayPlaces, ¬ OutputArc t.base p → NB t ≠ none) ∧
  (∀ t ms, t.mspec = some ms → NuBuilds t → (∃ p ∈ ms.relayPlaces, p ∈ ms.keyPlaces) →
    NB t = none)

/-- ✗ Worked example: a builder that runs every check of the reference but rejects with the bare
message "bad" meets the three rejection and acceptance lines, but not NU-054: the join `j` with
the relay target 4, which its output spec does not name, is rejected with a message that names
neither `j` nor 4. The naming line is load-bearing. -/
@[evidence mutant NU_054_build]
theorem NU_054_build_mutant_anyMessage_killed :
    NU_054_build_mutant_anyMessage (nu054_NB fun t ms => decide (RelaysOK t ms)) ∧
      ¬ NU_054_build (nu054_NB fun t ms => decide (RelaysOK t ms)) := by
  refine ⟨⟨fun t ms hm hnd h => ?_, fun t ms hm p hp ho h => ?_, fun t ms hm hb _ => ?_⟩,
    fun h => ?_⟩
  · unfold nu054_NB at h
    split at h
    · cases h
    · rw [hm] at h
      simp only at h
      split at h
      · rename_i hc
        exact hnd (of_decide_eq_true hc.2.2).1
      · cases h
  · unfold nu054_NB at h
    split at h
    · cases h
    · rw [hm] at h
      simp only at h
      split at h
      · rename_i hc
        exact ho ((of_decide_eq_true hc.2.2).2 p hp)
      · cases h
  · unfold nu054_NB
    rw [(refBuild_eq_none_iff t.base).2 hb.1]
    simp only [hm]
    rw [if_pos ⟨(hb.2 ms hm).1, (hb.2 ms hm).2.1, decide_eq_true (hb.2 ms hm).2.2⟩]
  · obtain ⟨m, hm, hn, -⟩ := h.2.2.2 (nu054_buildT [(4, ())]) _ rfl (by decide) (by decide)
      (by decide) (by decide)
    have e : nu054_NB (fun t ms => decide (RelaysOK t ms)) (nu054_buildT [(4, ())]) =
        some "bad" := by decide
    rw [e] at hm
    cases hm
    have hj : (nu054_buildT [(4, ())]).base.core.name = "j" := rfl
    rw [hj] at hn
    unfold MsgNames at hn
    simp at hn
    revert hn
    decide

/-! ## Forbidden models: the run-time check

Every mutant is the reference firing with the relay check replaced by `rc`, which also sees how
the firing ended (an action branch or the timeout outcome). -/

/-- The reference ν firing over `Nat` with the relay check `rc ch ms n e` in place of
`RelayOk ms n e`, `ch` being how the firing ended. -/
def nu054Fire (rc : Novel.ForwardDeposit.Choice → MatchSpec Nat (KeyFn Nat Nat) → Nat →
    List (Nat × Stamped Nat) → Prop) : NuFireRel Nat Nat Nat := fun t M c δ e M' =>
  match t.mspec with
  | none => c = none ∧ RefQFire t.base M δ e M'
  | some ms => ∃ n, c = some n ∧ refSelect (matchIn ms t M) = some n ∧
      Enabled t.base (qCount M) ∧
      (∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst) ∧ rc ch ms n e) ∧
      δ = nuDelivered ms t M n ∧ M' = qAppend (nuConsume ms t M n) e

/-- A matched firing of `nu054Fire`, unfolded. -/
theorem nu054Fire_matched {rc} {t : NuTrans Nat (KeyFn Nat Nat)} {ms : MatchSpec Nat (KeyFn Nat Nat)}
    (h : t.mspec = some ms) (M : QMarking Nat (Stamped Nat)) (c δ e M') :
    nu054Fire rc t M c δ e M' ↔ ∃ n, c = some n ∧ refSelect (matchIn ms t M) = some n ∧
      Enabled t.base (qCount M) ∧
      (∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst) ∧ rc ch ms n e) ∧
      δ = nuDelivered ms t M n ∧ M' = qAppend (nuConsume ms t M n) e := by
  unfold nu054Fire; rw [h]

/-- The firing of `j1` (output spec `xor(and(C, E), timeout(C))`) on `nu054_M` with X and
emission `e` ending with `ch`, under the relay check `rc`. -/
theorem nu054Fire_j1 {rc} {e : List (Nat × Stamped Nat)}
    (ch : Novel.ForwardDeposit.Choice)
    (hd : deposit (corrTake nu054_ms (nu054_j1 nu054_outUnit) nu054_M 1)
      (nu054_j1 nu054_outUnit).base.out ch = some (e.map Prod.fst))
    (hrc : rc ch nu054_ms 1 e) :
    nu054Fire rc (nu054_j1 nu054_outUnit) nu054_M (some 1)
      (nuDelivered nu054_ms (nu054_j1 nu054_outUnit) nu054_M 1) e
      (qAppend (nuConsume nu054_ms (nu054_j1 nu054_outUnit) nu054_M 1) e) :=
  (nu054Fire_matched rfl _ _ _ _ _).2
    ⟨1, rfl, by decide, by decide, ⟨ch, hd, hrc⟩, rfl, rfl⟩

/-- ✗ A check that asks only for some name accepts Y written into the relay target C of a join
that chose X; the first line fails. -/
@[evidence forbids NU_054_check]
theorem NU_054_check_forbids_otherName :
    ¬ NU_054_check (nu054Fire fun _ ms _ e =>
      ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, (r.2 x.val).isSome) := by
  intro h
  have hf := nu054Fire_j1 (e := nu054_eOther)
    (rc := fun _ ms _ e => ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, (r.2 x.val).isSome)
    (.action 0) (by decide) (by
      intro r hr x hx
      simp only [nu054_ms, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      revert x; decide)
  have := h.1 _ _ rfl nu054_j1_builds _ _ _ _ _ hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 2 5)
    (by decide) 2 (by decide)
  revert this; decide

/-- ✗ A check that lets a token without a name through (the no-name token as a wildcard) accepts
the unit token the timeout of `xor(and(C, E), timeout(C))` writes into C; the second line
fails. -/
@[evidence forbids NU_054_check]
theorem NU_054_check_forbids_noNameWildcard :
    ¬ NU_054_check (nu054Fire fun _ ms n e =>
      ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, r.2 x.val = some n ∨ r.2 x.val = none) := by
  intro h
  have hf := nu054Fire_j1 (e := nu054_eUnit)
    (rc := fun _ ms n e => ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1,
      r.2 x.val = some n ∨ r.2 x.val = none)
    (.timedOut 0) (by decide) (by
      intro r hr x hx
      simp only [nu054_ms, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      revert x; decide)
  exact h.2 _ _ rfl nu054_j1_builds _ _ _ _ _ hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 0 5)
    (by decide) (by decide)

/-- The relay check run on action completions only, as output validation is (ruling D24 (a)
puts the relay check on the timeout outcome too). -/
def nu054_actionOnly : Novel.ForwardDeposit.Choice → MatchSpec Nat (KeyFn Nat Nat) → Nat →
    List (Nat × Stamped Nat) → Prop
  | .action _, ms, n, e => RelayOk ms n e
  | .timedOut _, _, _, _ => True

/-- ✗ A relay check skipped on the timeout outcome lets the timeout of
`xor(and(C, E), timeout(C))` deposit a unit token into the relay target C; the second line
fails. -/
@[evidence forbids NU_054_check]
theorem NU_054_check_forbids_actionOnly : ¬ NU_054_check (nu054Fire nu054_actionOnly) := by
  intro h
  have hf := nu054Fire_j1 (e := nu054_eUnit) (rc := nu054_actionOnly)
    (.timedOut 0) (by decide) trivial
  exact h.2 _ _ rfl nu054_j1_builds _ _ _ _ _ hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 0 5)
    (by decide) (by decide)

/-- ✗ NU-020 does not already contain the relay check: the reference firing without it meets
every line of `NU_020_frame` (outcome offered, reads, resets, places off the keys) and still
deposits Y into the relay target of a join that chose X, breaking the first line here. -/
@[evidence mutant NU_054_check]
theorem NU_054_check_mutant_noCheck_killed :
    NU_020_frame (nu054Fire fun _ _ _ _ => True) ∧
      ¬ NU_054_check (nu054Fire fun _ _ _ _ => True) := by
  refine ⟨⟨fun t ms hm n δ e M M' hf => ?_, fun t ms hm n δ e M M' hf => ?_,
    fun t ms hm n δ e M M' hf p hr => ?_, fun t ms hm n δ e M M' hf p hk => ?_,
    fun t ms hm n δ e M M' hf p hk hr => ?_⟩, ?_⟩
  · obtain ⟨n', hn, -, -, ⟨ch, hdep, -⟩, -⟩ := (nu054Fire_matched hm M _ δ e M').1 hf
    cases hn
    exact nu020_outcome_of_deposit hdep
  · obtain ⟨n', hn, -, -, -, rfl, rfl⟩ := (nu054Fire_matched hm M _ δ e M').1 hf
    cases hn
    rfl
  · obtain ⟨n', hn, -, -, -, rfl, rfl⟩ := (nu054Fire_matched hm M _ δ e M').1 hf
    cases hn
    rw [qAppend_apply]
    simp [nuConsume, hr]
  · obtain ⟨n', hn, -, -, -, rfl, rfl⟩ := (nu054Fire_matched hm M _ δ e M').1 hf
    cases hn
    simp [nuDelivered, nuInputs, hk]
  · obtain ⟨n', hn, -, -, -, rfl, rfl⟩ := (nu054Fire_matched hm M _ δ e M').1 hf
    cases hn
    rw [qAppend_apply]
    simp [nuConsume, hr, nuPost, hk]
  · intro h
    have hf := nu054Fire_j1 (e := nu054_eOther)
      (rc := fun _ _ _ _ => True) (.action 0) (by decide) trivial
    have := h.1 _ _ rfl nu054_j1_builds _ _ _ _ _ hf (2, nu054_relKey) (by simp [nu054_ms]) (nu020_tok 2 5)
      (by decide) 2 (by decide)
    revert this; decide

/-! ## Forbidden models: the fragment classifier -/

/-- A classifier that reads a matched transition under EXTENDED in both modes: under BASE it
honours the relay declarations. -/
def nu054_baseHonoursRelays : Classifier := fun col mode declared tw T =>
  match T.keys with
  | some _ => refClassify col .extended declared tw T
  | none => refClassify col mode declared tw T

/-- ✗ Honouring the relay declaration under BASE admits `j1`, which writes the coloured place 2,
as a join; the first line fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_baseHonoursRelays : ¬ NU_054_verifier nu054_baseHonoursRelays := by
  intro h
  have := h.1 nu054_colExt false [] (nu054_vj1 [2]) [0, 1] rfl
    ⟨⟨[2], []⟩, by decide, 2, by decide, by decide⟩
  revert this; decide

/-- A classifier that treats every place a matched transition writes as one of its relay
targets. -/
def nu054_everyOutputRelays : Classifier := fun col mode declared tw T =>
  refClassify col mode declared tw { T with relays := T.relays ++ T.rows.flatMap Novel.RouteB.Row.places }

/-- ✗ Reading every output as a relay target admits `j1` without its relay declaration under
EXTENDED, although it writes the coloured place 2 it does not declare (a re-mint); the second
line fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_everyOutputRelays :
    ¬ NU_054_verifier nu054_everyOutputRelays := by
  intro h
  have := h.2.1 nu054_colExt false [] (nu054_vj1 []) [0, 1] rfl
    ⟨⟨[2], []⟩, by decide, 2, by decide, by decide, by decide⟩
  revert this; decide

/-- The join arm of `classifyT` without the shipped timeout rule: it admits a unit-token timeout
write into a relay target. -/
def nu054_unitTimeout : Classifier := fun col mode _ _ T => Novel.RouteB.classifyT col mode true T

/-- ✗ Without the timeout rule `j1` keeps its join role under EXTENDED although its timeout writes
a unit token into the relay target 2; the third line fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_unitTimeout : ¬ NU_054_verifier nu054_unitTimeout := by
  intro h
  have := h.2.2.1 nu054_colExt .extended false [(2, .unit)] (nu054_vj1 [2]) [0, 1] rfl
    ⟨(2, .unit), by decide, by decide, by decide⟩
  revert this; decide

/-- A classifier that never gives a matched transition a role: a verifier without the relay
feature, which falls back on every relaying join. -/
def nu054_never : Classifier := fun col mode declared tw T =>
  match T.keys with
  | some _ => none
  | none => refClassify col mode declared tw T

/-- ✗ A verifier without the relay feature refuses `j1` under EXTENDED, although `j1` writes the
coloured place 2 only as its declared relay target, consumes its keys 0 and 1 at count one and
has no timeout write: the join chain falls back instead of being decided. The fourth line
fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_never : ¬ NU_054_verifier nu054_never := by
  intro h
  obtain ⟨cin, rel, -, -, hc⟩ := h.2.2.2.1 nu054_colExt false [] (nu054_vj1 [2]) [0, 1] rfl
    (by rintro ⟨p, -, hp | hp | hp⟩ <;> simp [nu054_vj1] at hp)
    (by simp [SingleColouredWrites, nu054_vj1])
    (by decide)
    (by simp [ColouredInputs, nu054_vj1, nu054_colExt, Novel.RouteB.inOne])
    (by simp [KeysFixedCount, nu054_vj1, Novel.RouteB.inOne])
    (by simp)
  exact absurd hc (by simp [nu054_never, nu054_vj1])

/-- A classifier that drops the relay targets of every join it admits. -/
def nu054_dropRelays : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some (.join cin _) => some (.join cin [])
  | r => r

/-- ✗ Dropping the relay targets gives `j1` under EXTENDED a join role that relays to nothing,
although it declares the relay target 2; the fifth line fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_dropRelays : ¬ NU_054_verifier nu054_dropRelays := by
  intro h
  have := h.2.2.2.2.1 nu054_colExt false [] (nu054_vj1 [2]) [0, 1] [(0, 1), (1, 1)] [] rfl
    (by decide) 2
  revert this; decide

/-- A classifier that gives every join it admits the relay targets the transition declares, in
both modes. -/
def nu054_baseKeepsRelays : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some (.join cin _) => some (.join cin T.relays)
  | r => r

/-- ✗ Keeping the relay targets under BASE gives `j1`, with the keys alone coloured, a join role
that relays to 2, so that BASE would carry the relay into the name layer; the sixth line
fails. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_baseKeepsRelays : ¬ NU_054_verifier nu054_baseKeepsRelays := by
  intro h
  have := h.2.2.2.2.2.1 nu054_colBase false [] (nu054_vj1 [2]) [0, 1] [(0, 1), (1, 1)] [2] rfl
    (by decide)
  revert this; decide

/-- A classifier that, under BASE, refuses every transition that declares a relay target. -/
def nu054_baseRefusesRelays : Classifier := fun col mode declared tw T =>
  if mode = .base ∧ T.relays ≠ [] then none else refClassify col mode declared tw T

/-- ✗ Refusing relay declarations under BASE sends `j1` with the relay target 2 to the
fallback, although without the declaration it gets the join role: the declaration changes the
BASE verdict. The seventh line fails, and only it: under BASE this classifier refuses more than
the shipped one, and under EXTENDED it is the shipped one. -/
@[evidence forbids NU_054_verifier]
theorem NU_054_verifier_forbids_baseRefusesRelays :
    ¬ NU_054_verifier nu054_baseRefusesRelays := by
  intro h
  have := h.2.2.2.2.2.2 nu054_colBase false [] (nu054_vj1 [2]) [0, 1] rfl
  revert this; decide

end Libpetri.Spec
