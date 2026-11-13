import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Nu
import Libpetri.Spec.Req.NU_022

set_option linter.missingDocs true

/-!
# NU-020: Match specification (`spec/12-nu-nets.md`)

NU-020 says how a transition with a **match specification** builds, when it is enabled and
which tokens its firing takes: it joins on one **chosen name** that every correlated input holds
at its required count, the chosen name is the one the tie-break picks, each correlated input
delivers the first tokens of that name in queue order and keeps the rest in order, and everything
off the keys is the firing of the same transition without the match.

Four blocks share the ID:

* `NU_020_build` (kind F), over a match builder `MB` and a transition builder `NB`: fewer than
  two keys, or a place keyed twice, fail the match builder; a transition that fails without its
  match, keys a place twice or keys a non-input place fails; everything else builds.
* `NU_020_enable` (kind B), over a ν firing relation `R`: a matched firing is enabled on its
  counts, its chosen name is eligible, and no eligible name precedes it.
* `NU_020_take` (kind B): the correlated take, delivered and kept.
* `NU_020_frame` (kind B, nu.md skeptic S1): the offered outcome, the reads, the reset places,
  and every place that is not a correlated input, as without the match.

The witnesses are `refMatchBuild`, `refNuBuild` and `RefNuFire` (`Reference/Nu.lean`). The
existence half ("an enabled matched transition fires under its selected name") is not a block
line: it is the conjunct `NuCovers` of `Spec/ConsistencyNu.lean`, which rules out the relation
that never fires.

Rulings: D30 (a) (the count-level sentences of CORE and IO carry the correlated-input exception;
`Reference.Trans` keeps no match, so their blocks stay over match-free transitions), D31 (a) (the
tie-break reads the earliest `createdAt` over every token of the name; the name order is a
parameter), D37 (a) (the match builder rejects fewer than two keys; a token whose key yields no
name is skipped).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## NU-020, build checks -/

requirement NU_020_build
  id "NU-020"
  title "Match Specification (build checks)"
  kind F
  scope "every match builder and every transition builder, on every construction path"
  source verbatim "spec/12-nu-nets.md"
  quote "*If* a match builder is given fewer than two keys, *then* building the match *shall* fail."
        "*If* a match specification keys one place twice, *then* building the match *shall* fail."
        "Building a match from two or more keys on distinct places *shall* succeed."
        "*If* a transition fails to build without its match specification, *then* building it with the match specification *shall* fail."
        "*If* the match specification of a transition keys one place twice, *then* building the transition *shall* fail."
        "*If* the match specification of a transition keys a place that is not an input place of the transition, *then* building the transition *shall* fail."
        "Building a transition with a match specification *shall* succeed when the transition builds without the match, the match keys distinct input places of the transition, and the match declares each relay target once and as an output place of the transition ([NU-054])."
  reading "Let MB be the match builder (MB keys = none: the match builds) and NB the transition builder (NB t = none: t builds)."
          "For every list of keys with fewer than two entries, MB fails."
          "For every list of keys that names one place twice, MB fails."
          "For every list of two or more keys on distinct places, MB succeeds."
          "For every ν transition t whose transition without the match does not build (glossary: Builds), NB fails on t."
          "For every ν transition t whose match keys one place twice, NB fails on t."
          "For every ν transition t whose match keys a place that is not an input place of t, NB fails on t."
          "For every ν transition t that builds without its match, whose match keys distinct input places of t and declares each relay target once and as an output place of t (NuBuilds), NB succeeds on t."
  assumes "The model is the pair (MB, NB). MB is the match builder, read as the message a call fails with, none when the match builds; it sees the keys only, as Rust's MatchSpecBuilder::build does (rust/libpetri-core/src/match_spec.rs): relay targets are checked when the transition is built. NB is the transition builder for a transition that may carry a match, read the same way. The reference pair is refMatchBuild and refNuBuild; refNuBuild runs refBuild's checks on the transition without its match, then a place keyed twice, then a key on a non-input place, then per relay target 'declared twice' before 'not an output', the order of TransitionBuilder::build in rust/libpetri-core/src/transition.rs, TransitionBuilder.build in typescript/src/core/transition.ts and Transition.Builder.build in java/src/main/java/org/libpetri/core/Transition.java."
          "Ruling D37 (a): the minimum of two keys is a check of the match builder only. A construction path that is not a match builder (Rust MatchSpec::from_keys, a TypeScript object literal; Java has none) leaves it to the caller, so NB does not check it and the firing blocks cover matches with fewer keys; a match without keys never fires (eligible needs a key). How a path fails (a panic, an exception, an error value) and the message texts are configuration (kind N): the spec fixes no message for these checks, so the lines claim rejection only. The reference messages are Rust's, as stand-ins."
          "'Building a match or a transition whose match keys one place twice MUST fail', AC5 and the transition lines: 'on every construction path' is read as: NB is the one transition builder every path goes through (the builders, a bindings layer, a composition remap, an object literal), so a transition a path yields builds exactly when NB accepts it. Which paths exist is not in the model; the composition rewrites that remap keys are NU-030's."
          "The order of the checks ('The match checks run after every other build-time check of the transition', the glossary entry Build-time checks) decides only which message a transition failing several checks gets; so does the order among the match checks ('a place keyed twice, then a key on a place that is not an input place, then the relay checks'), which refNuBuild follows and Rust, Java and TypeScript share. The first is the conjunct NuBuildExtends of the consistency theorem (refNuBuild_extends): on a transition the plain builder rejects, and on one without a match, NB answers what the plain builder answers. Neither order is a line here."
          "The last line's relay clause is NU-054's check, quoted here because the converse names every check a matched transition passes; the relay rejections themselves are NU-054's build lines."
          "Place identity. The places one transition names are assumed to have pairwise distinct names, and a key names the place object of the transition's own input arc, as TIME-010 and MOD-006 assume for their places. Java breaks the model only outside that assumption: it detects a place keyed twice by name (duplicateKeyMessage in java/src/main/java/org/libpetri/core/MatchSpec.java) but checks key-on-input with structural Place equality, name and token type (Transition.Builder.build in java/src/main/java/org/libpetri/core/Transition.java), so two keys on distinct places that share a name are rejected although the third and seventh lines say they build, and a key whose place has an input's name but another token type is rejected as a non-input. Rust (TransitionBuilder::build in rust/libpetri-core/src/transition.rs) and TypeScript (TransitionBuilder.build in typescript/src/core/transition.ts) compare by name throughout, and Python's match builder deduplicates by name (py_match_spec in rust/libpetri-py/src/model.rs). This is the Place-equality divergence of MOD-024."
          "AC5 (a match that keys one place twice is rejected when the match is built, and when a transition is built with such a match from any other construction path) is the second and fifth lines; worked examples in NU_020_build_nonvacuous."
  signoff "2026-11-13 f0147b0dac984906 ai"
  statement : ∀ {N K : Type} [DecidableEq N],
      (List (N × K) → Option String) → (NuTrans N K → Option String) → Prop :=
    fun MB NB =>
      (∀ ks, ks.length < 2 → MB ks ≠ none) ∧
      (∀ ks, ¬ (ks.map Prod.fst).Nodup → MB ks ≠ none) ∧
      (∀ ks, 2 ≤ ks.length → (ks.map Prod.fst).Nodup → MB ks = none) ∧
      (∀ t, ¬ Builds t.base → NB t ≠ none) ∧
      (∀ t ms, t.mspec = some ms → ¬ KeysDistinct ms → NB t ≠ none) ∧
      (∀ t ms, t.mspec = some ms → ¬ KeysOnInputs t ms → NB t ≠ none) ∧
      (∀ t, NuBuilds t → NB t = none)

/- The pinned readable form of NU_020_build: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_020_build : {N K : Type} →
  [DecidableEq N] → (List (N × K) → Option String) → (NuTrans N K → Option String) → Prop :=
fun {N K} [DecidableEq N] MB NB =>
  (∀ (ks : List (N × K)), ks.length < 2 → MB ks ≠ none) ∧
    (∀ (ks : List (N × K)), ¬(List.map Prod.fst ks).Nodup → MB ks ≠ none) ∧
      (∀ (ks : List (N × K)), 2 ≤ ks.length → (List.map Prod.fst ks).Nodup → MB ks = none) ∧
        (∀ (t : NuTrans N K), ¬Builds t.base → NB t ≠ none) ∧
          (∀ (t : NuTrans N K) (ms : MatchSpec N K), t.mspec = some ms → ¬KeysDistinct ms → NB t ≠ none) ∧
            (∀ (t : NuTrans N K) (ms : MatchSpec N K), t.mspec = some ms → ¬KeysOnInputs t ms → NB t ≠ none) ∧
              ∀ (t : NuTrans N K), NuBuilds t → NB t = none
-/
#guard_msgs in #print NU_020_build

/-! ## NU-020, enablement and the chosen name -/

requirement NU_020_enable
  id "NU-020"
  title "Match Specification (enablement and chosen name)"
  kind B
  scope "every executor; one firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* a transition with a match specification fires, it *shall* be enabled on its token counts ([CORE-022])."
        "*When* a transition with a match specification fires, every correlated input *shall* hold at least one token of the chosen name and at least its required count of tokens of that name."
        "*When* a transition with a match specification fires, no other name of which every correlated input holds at least its required count of tokens *shall* have an earlier earliest `createdAt` among its tokens in the correlated inputs than the chosen name, or the same and precede it in the name order."
  reading "For every transition t with match specification ms, every firing of t in R from M is enabled on the token counts of M (glossary: Enabled)."
          "For every transition t with match specification ms, every firing of t in R from M has a chosen name n, and n is eligible on the selection input read off M (the match has a key; every correlated input holds at least one token of n and at least its required count of them)."
          "For every transition t with match specification ms, every firing of t in R from M with chosen name n has, for every eligible name m, (earliest stamp of n, n) at most (earliest stamp of m, m) in the lexicographic order, the earliest stamp of a name being the least createdAt over every token of the name in every correlated input."
  assumes "The model is a ν firing relation R over queue markings of stamped tokens (NuFireRel): R t M c δ e M' says that t fires from M with chosen name c (none without a match), delivers δ to its action, the action emits e, and the firing leaves M'. Without a match a ν firing is a queue firing (the conjunct NuRestrictsTo of the consistency theorem), so the count blocks speak of those firings; the lines here are about matched firings. Timing and priority play no part: one firing is one atomic step."
          "Ruling D31 (a): 'oldest matched token' is read as the earliest createdAt over every token carrying the name in the correlated inputs, whether the firing consumes it or not (glossary: Chosen name); the name order is a parameter, any linear order (NU-001 fixes it on BMP names). The Determinism paragraph and AC4 are the third line together with NU-022. 'So all languages fire identically on names whose values hold only Basic Multilingual Plane characters' rests on NU-001's fifth line and on NU-022's uniqueness: the line fixes the chosen name once the order is fixed. That the chosen name is the selection function's answer is the conjunct NuSelectsBy of the consistency theorem."
          "Ruling D37 (a): a token whose key yields no name has no name on that input, so it is not counted for any name (matchIn keeps only the tokens with a name). A match without keys has no eligible name, so it never fires, as in every runtime. A match-key projection that throws is outside the model, since a key is a total function to an optional name (KeyFn). The runtimes differ there: Python reads a raise, or a result that is not a str, as no name (make_py_projection in rust/libpetri-py/src/model.rs); Java catches only ClassCastException (MatchKey.extract in java/src/main/java/org/libpetri/core/MatchSpec.java, fireTransition in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java) and TypeScript catches nothing (typescript/src/runtime/match-engine.ts, buildNameIndex; cacheAddToken and fireTransition in typescript/src/runtime/bitmap-net-executor.ts), so a throwing key propagates out of their executors; Rust keys cannot fail by type. The relay projection reads a throw as no name in every language (NU-054). Whether the spec states this divergence or a runtime defect is recorded is open."
          "The existence half of 'Enablement = the usual cardinality/bitmap/inhibitor checks and there exists a single name present in every correlated input with at least that input's required count' (an enabled matched transition fires) is an offer, not a safety line: it is the conjunct NuCovers of the consistency theorem, stated for the selected name and every outcome the output spec offers under the correlated takes. Without it the relation that never fires meets every line."
          "The firing pass is not in the model: a join whose correlated input received a same-pass deposit fires no earlier than the next pass (EXEC-003 AC4), and the Rust executor counts matches in the drainable prefix of the place (consume_for_firing in rust/libpetri-runtime/src/bitmap_backend.rs). No block states them: the executor model RefExec (Reference/Exec.lean) has no ν firing kernel. The timed ν join (TIME-012's ν clause: a join is armed only while a name is eligible) is the block TIME_012_nu, on the atomic timed ν step."
          "AC2 (with no name present in all correlated inputs the join is not enabled and its input tokens remain) is the second line: NU_020_ac2 shows that on such a marking the reference has no firing. AC4 (the tie-break selects the earliest-oldest name, then the least name in the name order) is the third line, worked in NU_020_enable_nonvacuous."
  signoff "2026-11-13 c9f3f65945103a4c ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      (∀ t ms, t.mspec = some ms → ∀ c δ e,
        on (fun M M' => R t M c δ e M'), shall (fun M _ => Enabled t.base (qCount M))) ∧
      (∀ t ms, t.mspec = some ms → ∀ c δ e,
        on (fun M M' => R t M c δ e M'), shall (fun M _ =>
          ∃ n, c = some n ∧ eligible (matchIn ms t M) n = true)) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M _ =>
          ∀ m, eligible (matchIn ms t M) m = true →
            selKey (matchIn ms t M) n ≤ selKey (matchIn ms t M) m))

/- The pinned readable form of NU_020_enable: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_020_enable : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        ∀ (c : Option Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
          on fun M M' => R t M c δ e M', shall fun M x => Enabled t.base (qCount M)) ∧
    (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
        t.mspec = some ms →
          ∀ (c : Option Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M c δ e M', shall fun M x => ∃ n, c = some n ∧ eligible (matchIn ms t M) n = true) ∧
      ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
        t.mspec = some ms →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun M x =>
              ∀ (m : Nm), eligible (matchIn ms t M) m = true → selKey (matchIn ms t M) n ≤ selKey (matchIn ms t M) m
-/
#guard_msgs in #print NU_020_enable

/-! ## NU-020, the correlated take -/

requirement NU_020_take
  id "NU-020"
  title "Match Specification (correlated take)"
  kind B
  scope "every executor; one firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* a transition with a match specification fires, its action *shall* receive from each correlated input the first tokens of the chosen name in queue order, as many as the consumption count of the input arc with `available` the number of tokens of the chosen name in the place ([IO-007])."
        "*When* a transition with a match specification fires, each correlated input that is not one of its reset places *shall* end the firing holding the tokens it did not deliver, in their order, followed by the tokens the firing deposited there."
  reading "For every transition t with match specification ms and every firing of t in R from M with chosen name n: on every correlated input p with key f, the delivered tokens are the first k tokens of M p whose key gives n, in queue order, k being the correlated take (the consumption count of the arc on p over the number of tokens of n in M p)."
          "For every transition t with match specification ms and every firing of t in R from M to M' with chosen name n: every correlated input p with key f that is not a reset place holds in M' its queue in M without its first k tokens of name n, every other token in its order, followed by the tokens the firing emitted to p, in emission order."
  assumes "The model is a ν firing relation R, as for NU_020_enable. A correlated input is a place the match keys (keyAt); a transition that builds keys it once and it is an input place (NU_020_build). On a correlated input the count-level rules of IO-001 to IO-005, IO-007 and CORE-013 apply to the tokens of the chosen name only (ruling D30 (a), glossary: Consume, Correlated take): a correlated One takes one token of the name, Exactly(k) k of them, All and AtLeast every token of the name (AC3), and tokens of other names stay in the place in their order. 'FIFO within a name' is 'the first tokens of the chosen name in queue order'."
          "Ruling D37 (a): a token whose key yields no name is never taken by that input (named keeps only the tokens of the name); reading it as a wildcard is a forbidden model (NU_020_take_forbids_wildcard), and so is taking the newest tokens of the name first (NU_020_take_forbids_newestFirst). A key that throws is outside the model, as for NU_020_enable."
          "The tokens the firing deposits are appended at the tail in emission order (EXEC-020), as for every firing; a correlated input that is also a reset place ends holding only the deposited tokens, which NU_020_frame's reset line states."
          "AC1 (a join correlates by name, not arrival order: with branch A = [X@t0, Y@t1] and B = [Y@t0, X@t1] the join produces the X-X and Y-Y pairings, never X-Y) is the first line with NU_020_enable's choice: NU_020_take_nonvacuous fires the reference twice on that marking and gets X from both inputs, then Y from both. Plain FIFO consumption pairs X with Y and is forbidden (NU_020_take_forbids_fifo). AC3 (a correlated Exactly(k) or AtLeast(m) input requires k or m tokens of the matched name; All consumes all tokens of the matched name) is the first two lines with the correlated take: NU_020_ac3 takes every X from a correlated All and leaves the Y. The test derivation's two tests are AC1 and AC2."
  signoff "2026-11-13 f96d5d770695b19a ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M _ =>
          ∀ p f, keyAt ms p = some f →
            δ.inputs p = (named f n (M p)).take (corrTake ms t M n p))) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M M' =>
          ∀ p f, keyAt ms p = some f → p ∉ t.base.core.resets →
            M' p = dropNamed f n (corrTake ms t M n p) (M p) ++ qEmittedTo e p))

/- The pinned readable form of NU_020_take: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_020_take : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
          on fun M M' => R t M (some n) δ e M', shall fun M x =>
            ∀ (p : N) (f : KeyFn V Nm),
              keyAt ms p = some f → δ.inputs p = List.take (corrTake ms t M n p) (named f n (M p))) ∧
    ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
          on fun M M' => R t M (some n) δ e M', shall fun M M' =>
            ∀ (p : N) (f : KeyFn V Nm),
              keyAt ms p = some f →
                p ∉ t.base.core.resets → M' p = dropNamed f n (corrTake ms t M n p) (M p) ++ qEmittedTo e p
-/
#guard_msgs in #print NU_020_take

/-! ## NU-020, everything off the keys (frame) -/

requirement NU_020_frame
  id "NU-020"
  title "Match Specification (outcome, reads, resets and non-correlated places)"
  kind B
  scope "every executor; one firing of a transition with a match specification"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* a transition with a match specification fires, its deposit *shall* be one its output spec offers for the tokens the firing takes ([IO-013], [IO-015])."
        "*When* a transition with a match specification fires, its read arcs *shall* deliver the head of each read place after the inputs are taken ([EXEC-012])."
        "*When* a transition with a match specification fires, each of its reset places *shall* end the firing holding only the tokens the firing deposited there ([CORE-034])."
        "*When* a transition with a match specification fires, each place that is not a correlated input *shall* deliver to its action, and keep, the tokens it would without the match specification: the tokens at the head of its queue, as many as the consumption count of its input arc and none without one, and, unless it is a reset place, the rest of its queue in order followed by the tokens the firing deposited there ([EXEC-010], [EXEC-020])."
  reading "For every transition t with match specification ms and every firing of t in R from M with chosen name n that emits e: either the places e writes are exactly the places of some output branch of t, one or more tokens each, or e puts in every place as many tokens as some timeout outcome of t when each input place gives up its correlated take for n."
          "For every such firing: the read tokens are, per read arc, the head of its place in the marking after the inputs are taken."
          "For every such firing to M': every reset place of t holds in M' exactly the tokens the firing emitted to it."
          "For every such firing: every place p that is not a correlated input delivers the first tokens of M p, as many as the queue firing takes (qInputs: the consumption count of the arc on p, none without an arc)."
          "For every such firing to M': every place p that is not a correlated input and not a reset place holds in M' the rest of its queue in M, in order, followed by the tokens the firing emitted to p."
  assumes "The model is a ν firing relation R, as for NU_020_enable. This block is nu.md's skeptic correction S1: without it no block constrains a matched firing off its keys, since D16 takes correlated inputs out of EXEC-010 and NuRestrictsTo covers only transitions without a match. The mutant tailNu (a non-correlated input delivered from the tail) satisfies NU_020_take and is forbidden here (NU_020_frame_mutant_takeOnly_killed). The runtimes agree: the non-keyed inputs are taken with remove_first (consume_for_firing in rust/libpetri-runtime/src/bitmap_backend.rs)."
          "'The tokens the firing takes' in the first line are the correlated takes for the chosen name on correlated inputs and the queue takes elsewhere (corrTake); a ForwardInput of a timeout outcome counts them (IO-014). The first line is stated at the granularity of CORE-036's outcome line: 'its deposit shall be one its output spec offers' is read as IO-015 validates it, as a produced set. An action branch fixes which places receive tokens, one or more each, not their order or how many (the runtimes validate the set of places written: validateOutput in java/src/main/java/org/libpetri/runtime/BitmapNetExecutor.java, processCompletedTransitions in typescript/src/runtime/bitmap-net-executor.ts, rust/libpetri-runtime/src/executor_core/output.rs validate_out_spec; IO-016 AC4 deposits repeats with a warning; CORE-036 AC2 and AC3 allow the write b, b, c and the order c, b, b), and a timeout outcome fixes how many tokens each place receives, in any order. The token values are the action's. The relay check of NU-054 (a token emitted to a relay target must project to the chosen name) is NU-054's line, not this block's. A timeout outcome is not validated against the output spec (EXEC-021, ruling D24 (a)): every executor runs only the NU-054 relay check on a timed-out firing (processCompletedTransitions in BitmapNetExecutor.java and in bitmap-net-executor.ts), so a timeout under an And, such as And(A, Timeout(d, B)), deposits B. An executor that validated it against the whole output spec, the Java and TypeScript behaviour RD-01 recorded, never fires that timeout outcome."
          "Reads see the marking after the inputs are taken and before the reset places are drained (EXEC-012, EXEC-013 AC4); under ruling D15 no place carries both an input arc and a read arc, so this is the head of the read place before the firing."
          "'The tokens at the head of its queue' are the first tokens in queue order (glossary: Queue order), not the tokens with the earliest createdAt: a ForwardInput token keeps its old stamp at the tail of the queue (IO-014), and the runtimes take the head (remove_first). The last two lines cover every place the match does not key, input or not; a place without an input arc delivers nothing and keeps its queue."
  signoff "2026-11-13 6f4b70c409548ace ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], NuFireRel N V Nm → Prop :=
    fun R =>
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M _ =>
          (∃ b, OutputBranch t.base b ∧ OnPlacesOf (e.map Prod.fst) b) ∨
          (∃ d₀, TimeoutOutcome t.base (corrTake ms t M n) d₀ ∧
            SamePerPlace (e.map Prod.fst) d₀))) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M _ =>
          δ.reads = qReadsBag (nuPost ms t M n) t.base.core.reads)) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun _ M' =>
          ∀ p ∈ t.base.core.resets, M' p = qEmittedTo e p)) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M _ =>
          ∀ p, keyAt ms p = none → δ.inputs p = qInputs M t.base p)) ∧
      (∀ t ms, t.mspec = some ms → ∀ n δ e,
        on (fun M M' => R t M (some n) δ e M'), shall (fun M M' =>
          ∀ p, keyAt ms p = none → p ∉ t.base.core.resets →
            M' p = qPostInput M t.base p ++ qEmittedTo e p))

/- The pinned readable form of NU_020_frame: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_020_frame : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → NuFireRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
      t.mspec = some ms →
        ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
          on fun M M' => R t M (some n) δ e M', shall fun M x =>
            (∃ b, OutputBranch t.base b ∧ OnPlacesOf (List.map Prod.fst e) b) ∨
              ∃ d₀, TimeoutOutcome t.base (corrTake ms t M n) d₀ ∧ SamePerPlace (List.map Prod.fst e) d₀) ∧
    (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
        t.mspec = some ms →
          ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
            on fun M M' => R t M (some n) δ e M', shall fun M x =>
              δ.reads = qReadsBag (nuPost ms t M n) t.base.core.reads) ∧
      (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
          t.mspec = some ms →
            ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
              on fun M M' => R t M (some n) δ e M', shall fun x M' => ∀ p ∈ t.base.core.resets, M' p = qEmittedTo e p) ∧
        (∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
            t.mspec = some ms →
              ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
                on fun M M' => R t M (some n) δ e M', shall fun M x =>
                  ∀ (p : N), keyAt ms p = none → δ.inputs p = qInputs M t.base p) ∧
          ∀ (t : NuTrans N (KeyFn V Nm)) (ms : MatchSpec N (KeyFn V Nm)),
            t.mspec = some ms →
              ∀ (n : Nm) (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)),
                on fun M M' => R t M (some n) δ e M', shall fun M M' =>
                  ∀ (p : N), keyAt ms p = none → p ∉ t.base.core.resets → M' p = qPostInput M t.base p ++ qEmittedTo e p
-/
#guard_msgs in #print NU_020_frame

/-! ## Holds -/

/-- ✓ The reference builders satisfy the build lines: the match builder rejects fewer than two
keys and a repeated place and accepts the rest; the transition builder rejects what `refBuild`
rejects, a repeated key and a key on a non-input place, and accepts every transition that builds
(`refNuBuild_eq_none_iff`). -/
@[evidence holds NU_020_build]
theorem NU_020_build_reference {N K : Type} [DecidableEq N] [ToString N] :
    NU_020_build (refMatchBuild (N := N) (K := K)) (refNuBuild (N := N) (K := K)) := by
  refine ⟨fun ks hl h => ?_, fun ks hd h => hd ((refMatchBuild_eq_none_iff ks).1 h).2,
    fun ks hl hd => (refMatchBuild_eq_none_iff ks).2 ⟨hl, hd⟩,
    fun t hb h => hb ((refNuBuild_eq_none_iff t).1 h).1,
    fun t ms hm hd h => hd (((refNuBuild_eq_none_iff t).1 h).2 ms hm).1,
    fun t ms hm hk h => hk (((refNuBuild_eq_none_iff t).1 h).2 ms hm).2.1,
    fun t hb => (refNuBuild_eq_none_iff t).2 hb⟩
  have := ((refMatchBuild_eq_none_iff ks).1 h).1
  omega

/-- ✓ RefNuFire satisfies the enablement lines: a matched reference firing is enabled on its
counts, and its chosen name is the `Selected` one, eligible and least by (earliest stamp, name). -/
@[evidence holds NU_020_enable]
theorem NU_020_enable_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_020_enable (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun t ms hm c δ e M M' hf => ?_, fun t ms hm c δ e M M' hf => ?_,
    fun t ms hm n δ e M M' hf => ?_⟩
  · obtain ⟨n, -, -, hen, -⟩ := (refNuFire_matched hm M c δ e M').1 hf
    exact hen
  · obtain ⟨n, rfl, hs⟩ := refNuFire_selected hm hf
    exact ⟨n, rfl, hs.1⟩
  · obtain ⟨n', hn', hs⟩ := refNuFire_selected hm hf
    cases hn'
    exact hs.2

/-- ✓ RefNuFire satisfies the correlated-take lines: it delivers `nuInputs`, the first tokens of
the chosen name, and leaves `dropNamed` of the queue with the emission appended. -/
@[evidence holds NU_020_take]
theorem NU_020_take_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_020_take (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun t ms hm n δ e M M' hf p f hk => ?_, fun t ms hm n δ e M M' hf p f hk hr => ?_⟩
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    simp [nuDelivered, nuInputs, hk]
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rw [qAppend_apply]
    simp [nuConsume, hr, nuPost, hk]

/-- A deposit the output spec offers is an outcome at CORE-036's granularity: an action branch
gives a produced set that is that branch's places, and a timeout outcome gives a deposit that
puts as many tokens in every place as that outcome. -/
theorem nu020_outcome_of_deposit {N : Type} [DecidableEq N] {t : Trans N} {c : N → Nat}
    {ch : Novel.ForwardDeposit.Choice} {d : List N} (h : deposit c t.out ch = some d) :
    (∃ b, OutputBranch t b ∧ OnPlacesOf d b) ∨ (∃ d₀, TimeoutOutcome t c d₀ ∧ SamePerPlace d d₀) := by
  unfold OutputBranch TimeoutOutcome
  cases ho : t.out with
  | none =>
    rw [ho] at h
    cases ch with
    | action i =>
      cases i with
      | zero =>
        cases h
        exact Or.inl ⟨[], rfl, fun _ => Iff.rfl⟩
      | succ _ => cases h
    | timedOut _ => cases h
  | some o =>
    rw [ho] at h
    cases ch with
    | action i => exact Or.inl ⟨d, List.mem_of_getElem? h, fun _ => Iff.rfl⟩
    | timedOut j =>
      simp only [Reference.deposit] at h
      cases hc : o.findTimeout with
      | none => rw [hc] at h; cases h
      | some c' =>
        rw [hc] at h
        exact Or.inr ⟨d, ⟨o, c', rfl, hc, List.mem_of_getElem? h⟩, fun _ => rfl⟩

/-- ✓ RefNuFire satisfies the frame lines: its outcome is offered under the correlated takes, its
reads are the heads after the inputs are taken, its reset places hold only the emission, and off
the keys it is the queue firing. -/
@[evidence holds NU_020_frame]
theorem NU_020_frame_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_020_frame (RefNuFire (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun t ms hm n δ e M M' hf => ?_, fun t ms hm n δ e M M' hf => ?_,
    fun t ms hm n δ e M M' hf p hr => ?_, fun t ms hm n δ e M M' hf p hk => ?_,
    fun t ms hm n δ e M M' hf p hk hr => ?_⟩
  · obtain ⟨n', hn, -, -, ⟨ch, hdep⟩, -⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    exact nu020_outcome_of_deposit hdep
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rfl
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rw [qAppend_apply]
    simp [nuConsume, hr]
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    simp [nuDelivered, nuInputs, hk]
  · obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := (refNuFire_matched hm M _ δ e M').1 hf
    cases hn
    rw [qAppend_apply]
    simp [nuConsume, hr, nuPost, hk]

/-! ## Examples over values and names in `Nat` -/

/-- A token with value (and name) `v`, created at `s`. -/
def nu020_tok (v : Nat) (s : Int) : Stamped Nat := ⟨v, s⟩

/-- The key used throughout: a token's name is its value. -/
def nu020_key : KeyFn Nat Nat := some

/-- A match that keys places 0 and 1. -/
def nu020_ms : MatchSpec Nat (KeyFn Nat Nat) := { keys := [(0, nu020_key), (1, nu020_key)] }

/-- A join of places 0 and 1 with the given cards, correlated by `nu020_ms`, depositing nothing. -/
def nu020_join (c0 c1 : Card) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, c0⟩, ⟨1, c1⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none }
    mspec := some nu020_ms }

/-- AC1's marking: branch A (place 0) holds X@0, Y@1; branch B (place 1) holds Y@0, X@1, with
X = 1 and Y = 2. -/
def nu020_ac1 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0, nu020_tok 2 1]
  else if p = 1 then [nu020_tok 2 0, nu020_tok 1 1] else []

/-- AC2's marking: A holds X only, B holds Y only. -/
def nu020_ac2 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0] else if p = 1 then [nu020_tok 2 0] else []

/-- AC3's marking: A holds X@0, Y@1, X@2; B holds X@3. -/
def nu020_ac3 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0, nu020_tok 2 1, nu020_tok 1 2]
  else if p = 1 then [nu020_tok 1 3] else []

/-- A richer join: correlated inputs 0 and 1, a plain input 3, an inhibitor on 5, a read arc on
4, a reset arc on 6, and output place 2. -/
def nu020_rich : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩, ⟨3, .one⟩],
                        inhibitors := [5], reads := [4], resets := [6] },
              out := some (.place 2) }
    mspec := some nu020_ms }

/-- A marking for `nu020_rich`: AC1's branches, two tokens on the plain input 3, one on the read
place 4, one on the reset place 6. -/
def nu020_M : QMarking Nat (Stamped Nat) := fun p =>
  if p = 3 then [nu020_tok 7 0, nu020_tok 8 1]
  else if p = 4 then [nu020_tok 9 0]
  else if p = 6 then [nu020_tok 6 0]
  else nu020_ac1 p

/-- `nu020_M` with the inhibitor place 5 marked. -/
def nu020_Minh : QMarking Nat (Stamped Nat) := fun p =>
  if p = 5 then [nu020_tok 0 0] else nu020_M p

/-- The emission of one firing of `nu020_rich`: one token to its output place 2. -/
def nu020_e : List (Nat × Stamped Nat) := [(2, nu020_tok 0 5)]

/-! ## Nonvacuity and the acceptance criteria -/

/-- The two build examples of AC5 and the minimum of two keys: a key list `[(0, ()), (0, ())]` and
a transition carrying it. -/
def nu020_dupKeys : List (Nat × Unit) := [(0, ()), (0, ())]

/-- A transition with inputs 0 and 1 whose match keys 0 twice. -/
def nu020_dupT : NuTrans Nat Unit :=
  { base := { core := { name := "j", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none }
    mspec := some { keys := nu020_dupKeys } }

/-- A transition with input 0 only whose match keys 0 and the non-input place 1. -/
def nu020_nonInputT : NuTrans Nat Unit :=
  { base := { core := { name := "j", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := none }
    mspec := some { keys := [(0, ()), (1, ())] } }

/-- A transition with inputs 0 and 1 whose match keys both once: it builds. -/
def nu020_goodT : NuTrans Nat Unit :=
  { base := { core := { name := "j", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none }
    mspec := some { keys := [(0, ()), (1, ())] } }

/-- ✓ Worked example (AC5 and the two-key minimum). The match builder accepts keys on places 0
and 1, and rejects a single key and a key list naming place 0 twice. The transition builder
accepts a join of inputs 0 and 1 keyed once each, and rejects the same join keyed on 0 twice and a
join keyed on place 1 that is not one of its inputs. -/
@[evidence nonvacuous NU_020_build]
theorem NU_020_build_nonvacuous :
    refMatchBuild ([(0, ()), (1, ())] : List (Nat × Unit)) = none ∧
      refMatchBuild ([(0, ())] : List (Nat × Unit)) ≠ none ∧
      refMatchBuild nu020_dupKeys ≠ none ∧
      refNuBuild nu020_goodT = none ∧ refNuBuild nu020_dupT ≠ none ∧
      refNuBuild nu020_nonInputT ≠ none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ✓ Worked example (AC1, AC4). On AC1's marking, branch A = [X@0, Y@1] and branch B = [Y@0,
X@1], both X and Y are in both branches. Each has an earliest token at time 0, so the name order
breaks the tie and X is chosen. The reference join fires with X, and the line conclusions are not
trivial there: the transition is enabled on its counts, X is eligible, and so is Y, which X
precedes. -/
@[evidence nonvacuous NU_020_enable]
theorem NU_020_enable_nonvacuous :
    RefNuFire (nu020_join .one .one) nu020_ac1 (some 1)
        (nuDelivered nu020_ms (nu020_join .one .one) nu020_ac1 1)
        []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1 1) []) ∧
      Enabled (nu020_join .one .one).base (qCount nu020_ac1) ∧
      eligible (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 1 = true ∧
      eligible (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 2 = true ∧
      selKey (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 1 <
        selKey (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 2 :=
  ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩,
    by decide, by decide, by decide, by decide⟩

/-- AC2: with no name in both branches (A holds X only, B holds Y only) the reference join has no
firing, although both places are marked: no name is eligible, so the selection returns none. -/
theorem NU_020_ac2 :
    ¬ ∃ c δ e M', RefNuFire (nu020_join .one .one) nu020_ac2 c δ e M' := by
  rintro ⟨c, δ, e, M', hf⟩
  obtain ⟨n, -, hs⟩ := refNuFire_selected (ms := nu020_ms) rfl hf
  have h := refSelect_eq_some_iff.2 hs
  have h0 : refSelect (matchIn nu020_ms (nu020_join .one .one) nu020_ac2) = none := by decide
  rw [h0] at h
  cases h

/-- The marking AC1's join leaves after its first firing (with X). -/
def nu020_ac1_after : QMarking Nat (Stamped Nat) :=
  qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1 1) []

/-- ✓ Worked example (AC1). On A = [X@0, Y@1], B = [Y@0, X@1] the reference join first fires with
X and receives X@0 from A and X@1 from B: an X-X pair, although B's head is Y. It leaves A = [Y@1],
B = [Y@0], and fires again with Y, receiving Y from both: a Y-Y pair. -/
@[evidence nonvacuous NU_020_take]
theorem NU_020_take_nonvacuous :
    RefNuFire (nu020_join .one .one) nu020_ac1 (some 1)
        (nuDelivered nu020_ms (nu020_join .one .one) nu020_ac1 1)
        []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1 1) []) ∧
      nuInputs nu020_ms (nu020_join .one .one) nu020_ac1 1 0 = [nu020_tok 1 0] ∧
      nuInputs nu020_ms (nu020_join .one .one) nu020_ac1 1 1 = [nu020_tok 1 1] ∧
      nu020_ac1_after 0 = [nu020_tok 2 1] ∧ nu020_ac1_after 1 = [nu020_tok 2 0] ∧
      RefNuFire (nu020_join .one .one) nu020_ac1_after (some 2)
        (nuDelivered nu020_ms (nu020_join .one .one) nu020_ac1_after 2) []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1_after 2) []) ∧
      nuInputs nu020_ms (nu020_join .one .one) nu020_ac1_after 2 0 = [nu020_tok 2 1] ∧
      nuInputs nu020_ms (nu020_join .one .one) nu020_ac1_after 2 1 = [nu020_tok 2 0] :=
  ⟨NU_020_enable_nonvacuous.1, by decide, by decide, by decide, by decide,
    ⟨2, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩, by decide, by decide⟩

/-- AC3 against IO-003: a correlated `All` on A = [X@0, Y@1, X@2] with B = [X@3] takes both X
tokens and leaves Y in A, where a plain `All` would empty A. -/
theorem NU_020_ac3 :
    RefNuFire (nu020_join .all .one) nu020_ac3 (some 1)
        (nuDelivered nu020_ms (nu020_join .all .one) nu020_ac3 1) []
        (qAppend (nuConsume nu020_ms (nu020_join .all .one) nu020_ac3 1) []) ∧
      nuInputs nu020_ms (nu020_join .all .one) nu020_ac3 1 0 = [nu020_tok 1 0, nu020_tok 1 2] ∧
      nuPost nu020_ms (nu020_join .all .one) nu020_ac3 1 0 = [nu020_tok 2 1] ∧
      qInputs nu020_ac3 (nu020_join .all .one).base 0 =
        [nu020_tok 1 0, nu020_tok 2 1, nu020_tok 1 2] :=
  ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩, by decide, by decide, by decide⟩

/-- ✓ Worked example. The rich join (correlated 0 and 1, plain input 3, read 4, reset 6, output 2)
fires with X on `nu020_M`, emitting one token to place 2, which the output spec offers. The plain
input 3 delivers its head 7@0 and keeps 8@1; the read arc delivers the head 9@0 of place 4; the
reset place 6 ends empty. -/
@[evidence nonvacuous NU_020_frame]
theorem NU_020_frame_nonvacuous :
    RefNuFire nu020_rich nu020_M (some 1) (nuDelivered nu020_ms nu020_rich nu020_M 1) nu020_e
        (qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) nu020_e) ∧
      nuInputs nu020_ms nu020_rich nu020_M 1 3 = [nu020_tok 7 0] ∧
      qReadsBag (nuPost nu020_ms nu020_rich nu020_M 1) nu020_rich.base.core.reads 4 =
        [nu020_tok 9 0] ∧
      qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) nu020_e 3 = [nu020_tok 8 1] ∧
      qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) nu020_e 6 = [] :=
  ⟨⟨1, rfl, by decide, by decide, ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩, by decide, by decide, by decide,
    by decide⟩

/-! ## Forbidden models

Every mutant is the reference with one part changed (`NuMut`): the selection, whether the counts
are checked, whether the emission is checked against the output spec, what is delivered, and what
the firing leaves. -/

/-- A family of ν firing relations over `Nat`: the reference with one part replaceable. -/
structure NuMut where
  /-- The selection. -/
  sel : MatchSelect Nat := refSelect
  /-- Whether the counts are checked. -/
  counts : Bool := true
  /-- Whether the emission must be an offered outcome. -/
  offered : Bool := true
  /-- What the firing delivers. -/
  deliver : MatchSpec Nat (KeyFn Nat Nat) → NuTrans Nat (KeyFn Nat Nat) →
    QMarking Nat (Stamped Nat) → Nat → QDelivered Nat (Stamped Nat) := nuDelivered
  /-- What the firing leaves. -/
  result : MatchSpec Nat (KeyFn Nat Nat) → NuTrans Nat (KeyFn Nat Nat) →
    QMarking Nat (Stamped Nat) → Nat → List (Nat × Stamped Nat) → QMarking Nat (Stamped Nat) :=
    fun ms t M n e => qAppend (nuConsume ms t M n) e

/-- The firing relation of a `NuMut`. -/
def NuMut.fire (X : NuMut) : NuFireRel Nat Nat Nat := fun t M c δ e M' =>
  match t.mspec with
  | none => c = none ∧ RefQFire t.base M δ e M'
  | some ms => ∃ n, c = some n ∧ X.sel (matchIn ms t M) = some n ∧
      (X.counts = true → Enabled t.base (qCount M)) ∧
      (X.offered = true →
        ∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst)) ∧
      RelayOk ms n e ∧ δ = X.deliver ms t M n ∧ M' = X.result ms t M n e

/-- The build lines' mutants: a match builder that checks only repeated places. -/
def nu020_dupOnlyMB (ks : List (Nat × Unit)) : Option String :=
  match firstRepeat [] (ks.map Prod.fst) with
  | some _ => some "dup"
  | none => none

/-- ✗ A match builder that does not check the two-key minimum accepts a single key, breaking the
first line. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_oneKey : ¬ NU_020_build nu020_dupOnlyMB refNuBuild := by
  intro h
  exact h.1 [(0, ())] (by decide) (by decide)

/-- ✗ A match builder that checks only the number of keys accepts `[(0, ()), (0, ())]`, a place
keyed twice, breaking the second line. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_matchDup :
    ¬ NU_020_build (fun ks : List (Nat × Unit) => if ks.length < 2 then some "few" else none)
      refNuBuild := by
  intro h
  exact h.2.1 nu020_dupKeys (by decide) (by decide)

/-- ✗ A match builder that rejects every match breaks the third line: keys on places 0 and 1 must
build. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_rejectAll :
    ¬ NU_020_build (fun _ : List (Nat × Unit) => some "no") refNuBuild := by
  intro h
  exact absurd (h.2.2.1 [(0, ()), (1, ())] (by decide) (by decide)) (by simp)

/-- A transition with two input arcs on place 0 and no match: it does not build. -/
def nu020_badBaseT : NuTrans Nat Unit :=
  { base := { core := { name := "j", inputs := [⟨0, .one⟩, ⟨0, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := none } }

/-- ✗ A transition builder that runs only the match checks accepts a transition with two input
arcs on place 0, which does not build without its match; the fourth line fails. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_matchChecksOnly :
    ¬ NU_020_build refMatchBuild (nuChecks (N := Nat) (K := Unit)) := by
  intro h
  exact h.2.2.2.1 nu020_badBaseT (by decide) (by decide)

/-- A transition builder that skips the repeated-key check. -/
def nu020_noDupNB (t : NuTrans Nat Unit) : Option String :=
  match refBuild t.base with
  | some e => some e
  | none => match t.mspec with
    | none => none
    | some ms => if KeysOnInputs t ms ∧ RelaysOK t ms then none else some "bad"

/-- ✗ Skipping the repeated-key check accepts a join keyed on place 0 twice; the fifth line
fails. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_noDup : ¬ NU_020_build refMatchBuild nu020_noDupNB := by
  intro h
  exact h.2.2.2.2.1 nu020_dupT _ rfl (by decide) (by decide)

/-- A transition builder that skips the input-place check. -/
def nu020_noInputNB (t : NuTrans Nat Unit) : Option String :=
  match refBuild t.base with
  | some e => some e
  | none => match t.mspec with
    | none => none
    | some ms => if KeysDistinct ms ∧ RelaysOK t ms then none else some "bad"

/-- ✗ Skipping the input-place check accepts a join keyed on place 1, which is not one of its
inputs; the sixth line fails. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_noInputCheck : ¬ NU_020_build refMatchBuild nu020_noInputNB := by
  intro h
  exact h.2.2.2.2.2.1 nu020_nonInputT _ rfl (by decide) (by decide)

/-- ✗ A transition builder that rejects every matched transition breaks the last line: the join of
inputs 0 and 1 keyed once each builds. -/
@[evidence forbids NU_020_build]
theorem NU_020_build_forbids_rejectMatched :
    ¬ NU_020_build refMatchBuild
      (fun t : NuTrans Nat Unit => match t.mspec with
        | none => refBuild t.base
        | some _ => some "no") := by
  intro h
  exact absurd (h.2.2.2.2.2.2 nu020_goodT (by decide)) (by simp [nu020_goodT])

/-- ✗ A matched firing that skips the count check fires the rich join while its inhibitor place 5
is marked; the first enablement line fails. -/
@[evidence forbids NU_020_enable]
theorem NU_020_enable_forbids_noCounts : ¬ NU_020_enable (NuMut.fire { counts := false }) := by
  intro h
  have hf : NuMut.fire { counts := false } nu020_rich nu020_Minh (some 1)
      (nuDelivered nu020_ms nu020_rich nu020_Minh 1) nu020_e
      (qAppend (nuConsume nu020_ms nu020_rich nu020_Minh 1) nu020_e) :=
    ⟨1, rfl, by decide, fun h => absurd h (by decide), fun _ => ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.1 nu020_rich nu020_ms rfl _ _ _ _ _ hf
  revert this
  decide

/-- ✗ Count-level matching (any name, no join): on AC2's marking, where A holds X only and B holds
Y only, a firing that picks X anyway breaks the second enablement line, since X is not in B. -/
@[evidence forbids NU_020_enable]
theorem NU_020_enable_forbids_anyName :
    ¬ NU_020_enable (NuMut.fire { sel := fun _ => some 1 }) := by
  intro h
  have hf : NuMut.fire { sel := fun _ => some 1 } (nu020_join .one .one) nu020_ac2 (some 1)
      (nuDelivered nu020_ms (nu020_join .one .one) nu020_ac2 1) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac2 1) []) :=
    ⟨1, rfl, rfl, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  obtain ⟨n, hn, he⟩ := h.2.1 (nu020_join .one .one) nu020_ms rfl _ _ _ _ _ hf
  cases hn
  revert he
  decide

/-- A marking where name 2 is older: A = [2@0, 1@1], B = [1@2, 2@3]. -/
def nu020_older2 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 2 0, nu020_tok 1 1]
  else if p = 1 then [nu020_tok 1 2, nu020_tok 2 3] else []

/-- ✗ A tie-break by name order only picks name 1 on A = [2@0, 1@1], B = [1@2, 2@3], although
name 2's earliest token (time 0) is older than name 1's (time 1); the third enablement line
fails. -/
@[evidence forbids NU_020_enable]
theorem NU_020_enable_forbids_nameOnly :
    ¬ NU_020_enable (NuMut.fire { sel := nu022_nameFirst }) := by
  intro h
  have hf : NuMut.fire { sel := nu022_nameFirst } (nu020_join .one .one) nu020_older2 (some 1)
      (nuDelivered nu020_ms (nu020_join .one .one) nu020_older2 1) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_older2 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.2 (nu020_join .one .one) nu020_ms rfl _ _ _ _ _ hf 2 (by decide)
  revert this
  decide

/-- ✗ Plain FIFO consumption on a matched transition: on AC1's marking the join chooses X but takes
B's head Y@0, pairing X with Y; the first take line fails at place 1. -/
@[evidence forbids NU_020_take]
theorem NU_020_take_forbids_fifo :
    ¬ NU_020_take (NuMut.fire { deliver := fun _ t M _ => qDelivered M t.base }) := by
  intro h
  have hf : NuMut.fire { deliver := fun _ t M _ => qDelivered M t.base } (nu020_join .one .one)
      nu020_ac1 (some 1) (qDelivered nu020_ac1 (nu020_join .one .one).base) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_ac1 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.1 (nu020_join .one .one) nu020_ms rfl _ _ _ _ _ hf 1 nu020_key rfl
  revert this
  decide

/-- The draining mutant: a correlated input ends empty (apart from the deposit), as IO-003 read
literally would leave a correlated `All`. -/
def nu020_drain : NuMut where
  result ms t M n e := qAppend (fun p => if (keyAt ms p).isSome then [] else nuConsume ms t M n p) e

/-- ✗ A correlated `All` read as IO-003 literally, emptying the place: on AC3's marking A = [X@0,
Y@1, X@2] ends empty instead of keeping Y@1; the second take line fails. -/
@[evidence forbids NU_020_take]
theorem NU_020_take_forbids_drain : ¬ NU_020_take nu020_drain.fire := by
  intro h
  have hf : nu020_drain.fire (nu020_join .all .one) nu020_ac3 (some 1)
      (nuDelivered nu020_ms (nu020_join .all .one) nu020_ac3 1) []
      (nu020_drain.result nu020_ms (nu020_join .all .one) nu020_ac3 1 []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2 (nu020_join .all .one) nu020_ms rfl _ _ _ _ _ hf 0 nu020_key rfl (by decide)
  revert this
  decide

/-- The newest-first mutant: the right name and count on each correlated input, but the last
tokens of the name in queue order. -/
def nu020_newest : NuMut where
  deliver ms t M n := ⟨fun p => match keyAt ms p with
      | some f => (named f n (M p)).reverse.take (corrTake ms t M n p)
      | none => qInputs M t.base p,
    qReadsBag (nuPost ms t M n) t.base.core.reads⟩

/-- A marking where A holds two X tokens: A = [X@0, X@2], B = [X@3]. -/
def nu020_twoX : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 0, nu020_tok 1 2] else if p = 1 then [nu020_tok 1 3] else []

/-- ✗ Newest first within a name: on A = [X@0, X@2], B = [X@3] the join chooses X and takes X@2
from A, the newer of its two X tokens, instead of X@0; the first take line fails. -/
@[evidence forbids NU_020_take]
theorem NU_020_take_forbids_newestFirst : ¬ NU_020_take nu020_newest.fire := by
  intro h
  have hf : nu020_newest.fire (nu020_join .one .one) nu020_twoX (some 1)
      (nu020_newest.deliver nu020_ms (nu020_join .one .one) nu020_twoX 1) []
      (qAppend (nuConsume nu020_ms (nu020_join .one .one) nu020_twoX 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.1 (nu020_join .one .one) nu020_ms rfl _ _ _ _ _ hf 0 nu020_key rfl
  revert this
  decide

/-- A partial key: value 0 has no name, every other value is its own name. -/
def nu020_partialKey : KeyFn Nat Nat := fun v => if v = 0 then none else some v

/-- A match that keys places 0 and 1 with the partial key. -/
def nu020_partialMs : MatchSpec Nat (KeyFn Nat Nat) :=
  { keys := [(0, nu020_partialKey), (1, nu020_partialKey)] }

/-- The join of places 0 and 1 (one token each), correlated by the partial key. -/
def nu020_partialJoin : NuTrans Nat (KeyFn Nat Nat) :=
  { base := (nu020_join .one .one).base, mspec := some nu020_partialMs }

/-- A marking whose branch A starts with a token that has no name: A = [0@0, X@1], B = [X@2]. -/
def nu020_noName : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 0 0, nu020_tok 1 1] else if p = 1 then [nu020_tok 1 2] else []

/-- The wildcard mutant (ruling D37 (b)): on a correlated input a token whose key yields no name
counts as a token of the chosen name. -/
def nu020_wildcard : NuMut where
  deliver ms t M n := ⟨fun p => match keyAt ms p with
      | some f => ((M p).filter fun x => decide (f x.val = some n ∨ f x.val = none)).take
          (corrTake ms t M n p)
      | none => qInputs M t.base p,
    qReadsBag (nuPost ms t M n) t.base.core.reads⟩

/-- ✗ Ruling D37 (a), worked example: branch A = [0@0, X@1] starts with a token whose key yields
no name, and B = [X@2]. The join chooses X; the reference takes X@1 from A and leaves the nameless
token alone. Reading the nameless token as a wildcard takes 0@0 instead; the first take line
fails. -/
@[evidence forbids NU_020_take]
theorem NU_020_take_forbids_wildcard : ¬ NU_020_take nu020_wildcard.fire := by
  intro h
  have hf : nu020_wildcard.fire nu020_partialJoin nu020_noName (some 1)
      (nu020_wildcard.deliver nu020_partialMs nu020_partialJoin nu020_noName 1) []
      (qAppend (nuConsume nu020_partialMs nu020_partialJoin nu020_noName 1) []) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_partialMs] at hr, rfl, rfl⟩
  have := h.1 nu020_partialJoin nu020_partialMs rfl _ _ _ _ _ hf 0 nu020_partialKey rfl
  revert this
  decide

/-- ✗ An emission the output spec does not offer: the rich join emits to place 5 instead of its
output place 2; the first frame line fails. -/
@[evidence forbids NU_020_frame]
theorem NU_020_frame_forbids_unoffered : ¬ NU_020_frame (NuMut.fire { offered := false }) := by
  intro h
  have hf : NuMut.fire { offered := false } nu020_rich nu020_M (some 1)
      (nuDelivered nu020_ms nu020_rich nu020_M 1) [(5, nu020_tok 0 5)]
      (qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) [(5, nu020_tok 0 5)]) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun h => absurd h (by decide),
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  rcases h.1 nu020_rich nu020_ms rfl _ _ _ _ _ hf with ⟨b, hb, hon⟩ | ⟨d₀, ⟨o, c, ho, hc, -⟩, -⟩
  · simp only [OutputBranch, nu020_rich, Out.branches, List.mem_singleton] at hb
    subst hb
    exact absurd ((hon 5).1 (by simp)) (by simp)
  · simp only [nu020_rich, Option.some.injEq] at ho
    subst ho
    cases hc

/-- ✗ A firing that delivers no read tokens: the rich join's read arc on place 4 (holding 9@0)
delivers nothing; the second frame line fails. -/
@[evidence forbids NU_020_frame]
theorem NU_020_frame_forbids_noReads :
    ¬ NU_020_frame
      (NuMut.fire { deliver := fun ms t M n => ⟨nuInputs ms t M n, fun _ => []⟩ }) := by
  intro h
  have hf : NuMut.fire { deliver := fun ms t M n => ⟨nuInputs ms t M n, fun _ => []⟩ } nu020_rich
      nu020_M (some 1) ⟨nuInputs nu020_ms nu020_rich nu020_M 1, fun _ => []⟩ nu020_e
      (qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) nu020_e) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := congrFun (h.2.1 nu020_rich nu020_ms rfl _ _ _ _ _ hf) 4
  revert this
  decide

/-- ✗ A firing that does not drain its reset places: the rich join's reset place 6 keeps 6@0; the
third frame line fails. -/
@[evidence forbids NU_020_frame]
theorem NU_020_frame_forbids_noReset :
    ¬ NU_020_frame (NuMut.fire { result := fun ms t M n e => qAppend (nuPost ms t M n) e }) := by
  intro h
  have hf : NuMut.fire { result := fun ms t M n e => qAppend (nuPost ms t M n) e } nu020_rich
      nu020_M (some 1) (nuDelivered nu020_ms nu020_rich nu020_M 1) nu020_e
      (qAppend (nuPost nu020_ms nu020_rich nu020_M 1) nu020_e) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.2.1 nu020_rich nu020_ms rfl _ _ _ _ _ hf 6 (by decide)
  revert this
  decide

/-- The tail-delivery mutant (nu.md skeptic S1): name-correct on the keys, but a place without a
key delivers from the tail of its queue. -/
def nu020_tail : NuMut where
  deliver ms t M n := ⟨fun p => match keyAt ms p with
      | some _ => nuInputs ms t M n p
      | none => (M p).reverse.take (qTake M t.base p),
    qReadsBag (nuPost ms t M n) t.base.core.reads⟩

/-- ✗ Tail delivery off the keys: the rich join's plain input 3 holds 7@0, 8@1 and delivers 8@1
instead of the head 7@0; the fourth frame line fails. -/
@[evidence forbids NU_020_frame]
theorem NU_020_frame_forbids_tail : ¬ NU_020_frame nu020_tail.fire := by
  intro h
  have hf : nu020_tail.fire nu020_rich nu020_M (some 1) (nu020_tail.deliver nu020_ms nu020_rich
      nu020_M 1) nu020_e (qAppend (nuConsume nu020_ms nu020_rich nu020_M 1) nu020_e) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.2.2.1 nu020_rich nu020_ms rfl _ _ _ _ _ hf 3 rfl
  revert this
  decide

/-- The mutant that empties every place without a key that it takes from. -/
def nu020_dropRest : NuMut where
  result ms t M n e := qAppend (fun p =>
    if (keyAt ms p).isNone ∧ 0 < qTake M t.base p then [] else nuConsume ms t M n p) e

/-- ✗ A firing that empties every place without a key that it takes from: the rich join's plain
input 3 ends empty instead of keeping 8@1; the last frame line fails. -/
@[evidence forbids NU_020_frame]
theorem NU_020_frame_forbids_dropRest : ¬ NU_020_frame nu020_dropRest.fire := by
  intro h
  have hf : nu020_dropRest.fire nu020_rich nu020_M (some 1)
      (nuDelivered nu020_ms nu020_rich nu020_M 1) nu020_e
      (nu020_dropRest.result nu020_ms nu020_rich nu020_M 1 nu020_e) :=
    ⟨1, rfl, by decide, fun _ => by decide, fun _ => ⟨.action 0, by decide⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩
  have := h.2.2.2.2 nu020_rich nu020_ms rfl _ _ _ _ _ hf 3 rfl (by decide)
  revert this
  decide

/-! ## The frame block is load-bearing beyond the take block -/

/-- The tail-delivery mutant satisfies every correlated-take line: it is name-correct on the
keys. -/
theorem nu020_tail_take : NU_020_take nu020_tail.fire := by
  refine ⟨fun t ms hm n δ e M M' hf p f hk => ?_, fun t ms hm n δ e M M' hf p f hk hr => ?_⟩
  · unfold NuMut.fire at hf
    rw [hm] at hf
    obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := hf
    cases hn
    simp [nu020_tail, nuInputs, hk]
  · unfold NuMut.fire at hf
    rw [hm] at hf
    obtain ⟨n', hn, -, -, -, -, rfl, rfl⟩ := hf
    cases hn
    change qAppend (nuConsume ms t M n) e p = _
    rw [qAppend_apply]
    simp [nuConsume, hr, nuPost, hk]

/-- ✗ Worked example: the tail-delivery mutant meets NU-020's correlated-take block, because it
takes the right tokens of the chosen name, but not the frame block: its plain input delivers the
newest token. Without the frame block no line would constrain a matched firing off its keys. -/
@[evidence mutant NU_020_frame]
theorem NU_020_frame_mutant_takeOnly_killed :
    NU_020_take nu020_tail.fire ∧ ¬ NU_020_frame nu020_tail.fire :=
  ⟨nu020_tail_take, NU_020_frame_forbids_tail⟩

end Libpetri.Spec
