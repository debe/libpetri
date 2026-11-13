import Libpetri.Spec.Registry
import Libpetri.Spec.Req.NU_050
import Libpetri.Spec.Verifier.Graph

set_option linter.missingDocs true

/-!
# VER-012: Name-aware state class graph (`spec/07-verification.md`)

Route B decides a ν-net on a state-class graph whose classes carry a name layer: abstract,
interchangeable name-symbols on the coloured places. Two blocks, both kind F, one per part of
the graph the section constrains:

* `VER_012` (the graph): a predicate over the parts of one graph step (`NameGraph`): the name
  successors of a firing, the canonical key of a name layer, the key of a class and the base
  step on the count marking. A ν-join fires only on a name every correlated input holds at its
  count (AC1), a coloured consumer only on a name its input holds, and each on every such name up
  to renaming (the free-choice semantics the graph explores, ruling D59 (a) and VD-1 (a)); a mint
  stamps a name no place holds and an ordinary transition keeps the name layer; two name layers
  share a key exactly when one is a renaming of the other (AC2); a class is identified by its
  whole base and the key of its name layer (the memory note); every input takes from its place
  what [IO-007] says it consumes, so an `All` or `AtLeast` input leaves nothing behind (AC4).
  Witness `refNameGraph`: `Novel.RouteB.nameSuccs`, `canonicalKey`, `keyOf` and the untimed base
  `untimedBase`. `ver012_succs_keys` shows the name step of any graph meeting it is
  key-equivariant.
* `VER_012_build` (the build): a predicate over an abstract build loop (`RBBuild`): every stored
  class is reachable in the graph; a closed build expanded every class and, for a key-equivariant
  step, stored a class of every key the graph reaches (complete for the graph's own semantics,
  AC3, for safety and quiescence alike); the early stop of AC5 gives the verdict of the build
  without it, unless that build is stopped; an early-stopped build is not closed. Witness
  `refRBBuild`: `Novel.RouteB.Decide.build`.

The verdict read off a built graph (the prefix rule, a truncated or stopped graph never `Proven`)
is NU-050's (`NU_050_prefix`); soundness against the reference ν executor is NU-050's too
(`NU_050_soundB`, cited here as `ver012_sound_executor`). The timed half (name-gated clocks,
dropped latest bounds) is not modelled (gap R6). `VER_012_joint` shows the two blocks and NU-050's
verdict and soundness blocks hold together on one Route B.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB

/-! ## The models -/

/-- The parts of one step of the Route B graph that VER-012 constrains:

* `succs co r M d B c`: the name layers one firing of a transition of role `r` yields from the
  name layer `M` (support below `B`) on a branch depositing into `d`, minting `c`;
* `key co M`: the canonical key of a name layer;
* `ckey S`: the key two classes are identified by (the pair of intern ids);
* `fire a t r`: the base successor on the count marking `a` of a firing of `t` on the branch
  outcome `r` (`none`: no successor). -/
structure NameGraph where
  /-- The name successors of one firing. -/
  succs : (co : List PlaceId) → Role → NM co → Novel.ForwardDeposit.Deposit → ℕ → ℕ → List (NM co)
  /-- The canonical key of a name layer. -/
  key : (co : List PlaceId) → NM co → List (List (ℕ ×ₗ ℕ))
  /-- The key of a class. -/
  ckey : {β : Type} → {co : List PlaceId} → NState co β → β × List (List (ℕ ×ₗ ℕ))
  /-- The base successor on the count marking. -/
  fire : AMarking → Transition → Novel.RouteB.Row → Option AMarking

/-- **The shipped graph step**: `name_successors` (`Novel.RouteB.nameSuccs`), the canonical key
(`canonicalKey`), the class key (`keyOf`: the base and the name key) and the untimed base step
(`untimedBase.fire`: `fireAD` over the branch outcome with drained forwards resolved).
Registered as a witness model. -/
noncomputable def refNameGraph : NameGraph where
  succs co r M d B c := nameSuccs co r M d B c
  key _ M := Novel.CanonicalKey.canonicalKey M
  ckey S := keyOf S
  fire := untimedBase.fire

#spec_witness refNameGraph

/-- A build loop of a class graph: from the explorer, the class bound, the total-budget oracle,
the early-stop predicate and switch, the fuel and the initial class, the built graph. -/
abbrev RBBuild :=
  (S K L : Type) → Explorer S K L → ℕ → (ℕ → Bool) → (S → Bool) → Bool → ℕ → S → Decide.Out S

/-- **The shipped build loop** (`build_until`, `Novel.RouteB.Decide.build`). Registered as a
witness model. -/
noncomputable def refRBBuild : RBBuild := fun _ _ _ E => Decide.build E

#spec_witness refRBBuild


/-! ## VER-012 (F): the graph step -/

requirement VER_012
  id "VER-012"
  title "Name-Aware State Class Graph: the graph step"
  kind F
  scope "every verifier that offers the Route B name-partition graph (MAY); one step of the graph, the untimed base"
  source verbatim "spec/07-verification.md"
  quote "*When* the Route B graph fires a ν-join on a name-symbol, every correlated input *shall* hold at least the required count of that symbol, and the firing *shall* remove the required count of that symbol from each correlated input and add one token of it to each relay target of the fired branch ([NU-054])."
        "*If* every correlated input of a ν-join holds at least the required count of a name-symbol, *then* the name successors of a firing of that join *shall* include one with the canonical key of the join fired on that symbol."
        "*When* the Route B graph fires a coloured consumer ([NU-051]), it *shall* fire it on a name-symbol its coloured input holds, removing one token of that symbol from the input and adding one token of it to each coloured output of the fired branch."
        "*If* the coloured input of a coloured consumer holds a name-symbol, *then* the name successors of a firing of that consumer *shall* include one with the canonical key of the consumer fired on that symbol."
        "*When* the Route B graph fires a minting transition, its one name successor *shall* add one token of a name-symbol that no coloured place of the class holds to each coloured output of the fired branch."
        "*When* the Route B graph fires a transition that neither mints, joins nor consumes a name-symbol, its one name successor *shall* be the name layer of the class unchanged."
        "Two name layers *shall* have the same canonical key exactly when one is the other with its name-symbols renamed by a permutation."
        "The Route B graph *shall* identify two classes exactly when they have the same base class and their name layers have the same canonical key."
        "*When* the Route B graph fires a transition, the successor *shall* hold on each place the transition does not reset the tokens the place held, less the tokens the transition's input on that place consumes by [IO-007] (all of them for an `All` or `AtLeast` input), plus the tokens the fired branch deposits there."
  reading "Let G be the graph step: succs (the name successors of one firing), key (the canonical key of a name layer), ckey (the key of a class) and fire (the base step on the count marking)."
          "For every coloured set co, correlated inputs cin with their required counts, relay targets rel, name layer M, branch places d, support bound B and mint counter c: every name successor of a join (role join cin rel) is joinStep on some symbol s that joinEnab accepts (a token of s in the first correlated input and the required count of s in every one): the required count of s removed from each correlated input, one token of s added to each relay target of the branch (relOut d rel)."
          "For the same data, with M supported below B: for every symbol s that joinEnab accepts, some name successor of the join has the key of joinStep on s."
          "For every coloured set co, consumed input inp, name layer M, branch places d, bound B and counter c: every name successor of a coloured consumer (role consume inp) is consumeStep on some symbol s resident in inp (a token of s in inp): one token of s removed from inp, one token of s added to each coloured output of the branch (colOut d)."
          "For the same data, with M supported below B: for every symbol s resident in inp, some name successor of the consumer has the key of consumeStep on s."
          "For every coloured set co, name layer M supported below B, branch places d and mint counter c at or above B: the name successors of a mint (role mint) are the one layer mintStep on some symbol s of which no coloured place holds a token in M: one token of s added to each coloured output of the branch."
          "For every coloured set co, name layer M, branch places d, bound B and counter c: the name successors of an ordinary transition (role ordinary) are the one layer M."
          "For every two name layers M and N with finite support: key M = key N exactly when N = M ∘ σ for some permutation σ of the symbols."
          "For every base type β, coloured set co and two classes S and S': ckey S = ckey S' exactly when S.b = S'.b and key S.m = key S'.m."
          "For every count marking a, transition t, branch outcome r and place p that t does not reset: if fire a t r = some a', then a' p = a p - consumedA a t p + the number of tokens the branch, its drained forwards resolved at a, deposits on p; consumedA a t p is what t's input on p takes: a p for an All or AtLeast input, the required count for a One or Exactly input, 0 when t has no input on p."
  assumes "The model is the graph step NameGraph. succs is name_successors (name_state_class_graph.rs; Novel.RouteB.nameSuccs), key is NameMarking::canonical_key (Novel.CanonicalKey.canonicalKey), ckey is the pair of intern ids the graph dedups by (Novel.RouteB.keyOf), fire is the base successor of the untimed base layer (Novel.RouteB.untimedBase, fireAD over the branch outcome with each drained forward resolved at the marking fired in). The witness refNameGraph is the explorer's own step: the Route B explorer Novel.RouteB.routeB keys its classes with refNameGraph.ckey and fires the untimed base with refNameGraph.fire (ver012_routeB_key, ver012_untimedBase_fire). The build loop and the verdict are VER_012_build's and NU-050's (NU_050_prefix)."
          "Which role a transition gets (join for a matched transition, consume, mint, ordinary) is an input of succs, as it is of name_successors. It is the fragment classifier's (Novel.RouteB.classifyT and classifyS, name_fragment.rs classify): a matched transition gets only the join role, with its counted keys and relay targets, by NU_054_verifier; the coloured-consumer role is NU_051's; the mint role, given only to a declared mint, is NU-010's (Novel.RouteB.classifyS_mint); a transition the classifier gives no role makes the net fall back to the sound over-approximation (NU-050). The classifier refuses an `All` or `AtLeast` match key (keyCount) and gives the consumer role only at count one (NU_051 line 2), so no coloured place is drained by a batch and line 9 needs no name-layer counterpart."
          "AC1 (a ν-join fires only on a name shared by all correlated inputs; a marking reachable only by equating two distinct names is not reachable, with no budget place required) is lines 1 and 2. joinEnab is the shipped enabling_symbols: a token in the first correlated input and the required count in every one. Every correlated input takes at least one token (TransitionBuilder::build rejects a zero count, Classify.builderOK_posKeys), so on a built net joinEnab is the quoted sentences' 'every correlated input holds at least the required count'; a net with a zero-count key cannot be built and is out of scope (Classify.zeroKey_refused). 'With no budget place required' is that lines 1 and 2 have no premise on the base marking: the join's name test reads the name layer alone. VER_012_nonvacuous shows a crossed layer (name 0 in one input, name 1 in the other) with no join successor; VER_012_forbids_firstInput kills a join that reads a name in its first input only. NU-050 AC1 (a counterexample that equates two names is not reported) is the same fact read at the verdict, NU-050's block."
          "Lines 2 and 4 are the free-choice half of ruling D59 (a) and VD-1 (a) (clashes ver-d#1, nu-b#3): the graph fires a join on every name that enables it, and a coloured consumer on every name its input holds, up to renaming, where the executor picks one by the NU-020 rule (the oldest token, EXEC-010). The informative sentence of the body ('the graph fires it on each of them, up to renaming, and a coloured consumer on each resident name') is lines 2 and 4. That is why a closed graph is complete for the graph's own semantics and not for the executor. VER_012_forbids_leastName and VER_012_forbids_consumeLeast kill a graph that fires a join, or a consumer, on one name only (the least one, standing for the executor's choice). Lines 3 and 4 constrain only which names the consumer step is applied to; the step's count update on one name is also NU_051_relay's line. The orbit dedup (one successor per distinct signature, the implementation note) is lines 2 and 4's 'up to renaming': Novel.RouteB.dedup_perm shows it keeps the keyed successors of every signature. VER_012_forbids_anySymbol kills a consumer fired on a name its input does not hold, which creates a token from nothing."
          "Line 5 is the body's 'a minting fork introduces a globally-fresh symbol': the minted symbol is fresh for the class (no coloured place holds it). The Rust mints next_sym, next_sym + 1, ... across one expansion, the model the counter c; the line allows any fresh symbol, and the key does not depend on which (Novel.RouteB.mint_key). That the symbol is also fresh across the whole run, and differs from every name the executor minted earlier, is NU-010's executor line; on the graph a symbol no place holds is interchangeable with every other such symbol, so freshness for the class is all the quotient can see. VER_012_forbids_mintZero kills a mint that reuses symbol 0, which merges a fresh name with a live one. Line 6 is the ordinary role: a transition that touches no coloured place leaves the name layer as it was; VER_012_forbids_ordinaryDrop kills a step that empties it."
          "AC2 (two markings differing only by a permutation of name-symbols are the same state class) is lines 7 and 8: the name key is renaming-invariant and separates layers that are no renaming of each other (Novel.CanonicalKey.canonicalKey_eq_iff_exists_perm). Its parenthesis ('the quotient is finite when the live-name pool is structurally bounded') is not stated: it is the reason the graph can close, and a graph that does not close is truncated (VER_012_build, NU_050_prefix). Open item: a finiteness theorem for a structurally bounded live-name pool. VER_012_forbids_identityKey kills a key that reads a symbol's identity; VER_012_forbids_nameBlind kills a key that forgets the name layer, which merges the aligned and the crossed layer and is the value-blind count abstraction."
          "Line 8 says the class key keeps the whole base class. The model's base type is abstract (BaseLayer β), and the only concrete instance is the untimed base (AMarking), which has no zone and no earliest-ready times. So the memory note's two MUST sentences (the base intern key includes the class-relative earliest-ready times alongside marking and zone; two arrivals that disagree on the earliest-ready times stay two classes) and the body's 'for a timed net its marking, zone and earliest-ready times' have no Lean content beyond 'the key keeps the whole base': the timed base class is gap R6 (open item: give the timed base layer its zone and readyEarliest components and state that the key keeps them). VER_012_forbids_baseBlind kills a class key that hides the base. The runtime base intern keys keep the whole base marking: Rust's intern_base keys by the escaped canonical_key (name_state_class_graph.rs, marking_state.rs push_key_name), TypeScript's internBase by baseKeyOf over MarkingState.key(), the JSON of the sorted [name, count] entries, and Java by the structured BaseKey. A base intern key that renders the base marking as a string that does not escape place names, the behaviour RD-40 recorded, gives two base classes with different markings and no clocks one intern id, so line 8 fails there: the graph keeps the first arrival's base and loses the other marking, and AC3's completeness of a closed graph fails on such a net. Why the key must keep everything the step reads is Libpetri.equivariance_is_necessary (Interning.lean): a step that reads a datum the key hides loses a reachable class under interning; for the shipped step Novel.RouteB.routeB_equivariant discharges it, and Novel.RouteB.routeB_interned_keys_eq shows the hash-consed graph is the plain quotient graph (interning is semantics-free). That class indices and the reported trace may differ from a build without interning is report shape (kind Q)."
          "AC4 (All and AtLeast inputs drain their place in the graph as at run time; an inhibitor arc on that place is then satisfied in the successor) and the exactness precondition's first MUST sentence (the successor step derives each input's count from consumptionCount of IO-007, so All and AtLeast consume every available token) are line 9, for every input: All and AtLeast take every token of the place, One and Exactly(n) their required count (consumedA, the IO-007 contract on counts). VER_012_forbids_requiredCount kills a base step that takes requiredCount from an All input: it leaves a phantom residue, which keeps an inhibitor arc on the place unsatisfied; VER_012_forbids_noConsume kills one that takes nothing from a One input. The inhibitor consequence follows from line 9 and the enabling test (enabledA). A place the transition resets is not an input count: its successor count is the base graph's (VER-010), not this line's. The precondition's last MUST sentence ('delegate to the same cardinality contract the executor uses rather than restating it') is a rule on code structure (kind N): the line states the counts, not how the code obtains them."
          "AC3 is split under ruling D59 (a) and VD-1 (a). Its closed-graph sentence, reworded to 'sound for every executor run and complete for the free-choice name semantics the graph explores', is: soundness, NU_050_soundB (cited as ver012_sound_executor; a Route B Proven holds of every marking the untimed reference ν executor reaches, under the contracts of NU-010 and NU-051); completeness, VER_012_build lines 2 and 3 with lines 2 and 4 here (ver012_build_complete_violated for reachability-safety, ver012_build_complete_quiescence for quiescence). Line 3 of VER_012_build needs a key-equivariant successor step; ver012_succs_keys shows that the name successors of every graph meeting this block have keys that depend only on the key of the layer fired from, and for the shipped step the whole premise is Novel.RouteB.routeB_equivariant. Its truncation sentences (a stored violating class gives Violated with the shortest witness, a truncated graph never Proven, Unknown otherwise) are NU_050_prefix and VER-017's rule; the shortest witness is Verifier.Graph.trace (trace_spec: a shortest path of the built graph). The sentence on a graph that keeps a latest bound (an on-time executor whose actions take no time, the report says so) and the PNID Fig. 11(b) fixture are the timed graph and a report line: not modelled (gap R6, kind Q)."
          "AC5 (early stop) is VER_012_build lines 4 and 5. The report note text, 'the parent ... does not count as expanded' and the PNID fixture are report shape and timing (kind Q); the model's build does not count the parent as expanded (Decide.loop). That quiescence properties do not stop early is the decider's choice: the reference Route B decider builds with the early stop for a safety property only (refRouteB, NU-050)."
          "The body sentence on the timed firing domain is reworded under VD-5 (item 3, ruling D20): the domain of VER-011 is carried beside the name partition, a matched join's clock gated by name-enablement (NU-050) and, unless assumeNoReaping is set, without latest bounds (TIME-013). None of the timed layer is modelled here: the base layer of Novel.RouteB.Graph is abstract and the end-to-end theorems are for the untimed instance. Novel.RouteB.nameEnabled_comp shows the clock gate is renaming-invariant, so the timed step stays key-equivariant; the timed base step itself is not stated. Open items under gap R6: the timed graph (name-gated clocks, dropped latest bounds, the timed base class of line 8), and AC3's soundness for a timed net, since NU_050_soundB is against the untimed reference ν executor only."
          "The exactness precondition's phrase 'in the [EXEC-010] FIFO order' is deleted under VD-1 (a): a name layer counts tokens per symbol and holds no queue order, and the graph takes any resident name where the executor takes the oldest. What the graph keeps of the executor is the count per place (line 9) and, for a join or a consumer, the name fired on (lines 1 to 4)."
          "The implementation notes (the three runtimes and Python, the shared key format, interning as an option, the orbit dedup's measurements, the counterexample path read from per-class labelled successor lists, solver-free, Route A preferred for budget-declared untimed reachability-safety) are configuration and report shape (kinds N and Q), except the memory note's MUST sentences (line 8, open item above) and the orbit dedup's claim that the class set and the (label, key) successor pairs are unchanged (Novel.RouteB.dedup_perm, lines 2 and 4)."
  signoff "2026-11-13 41a4de83f8732bd6 ai"
  statement : NameGraph → Prop :=
    fun G =>
      (∀ co cin rel (M : NM co) d B c M', M' ∈ G.succs co (.join cin rel) M d B c →
        ∃ s, joinEnab co cin M s = true ∧ M' = joinStep co cin (relOut d rel) s M) ∧
      (∀ co cin rel (M : NM co) d B c s, Supp M B → joinEnab co cin M s = true →
        ∃ M' ∈ G.succs co (.join cin rel) M d B c,
          G.key co M' = G.key co (joinStep co cin (relOut d rel) s M)) ∧
      (∀ co inp (M : NM co) d B c M', M' ∈ G.succs co (.consume inp) M d B c →
        ∃ s, resident co inp M s = true ∧ M' = consumeStep co inp (colOut co d) s M) ∧
      (∀ co inp (M : NM co) d B c s, Supp M B → resident co inp M s = true →
        ∃ M' ∈ G.succs co (.consume inp) M d B c,
          G.key co M' = G.key co (consumeStep co inp (colOut co d) s M)) ∧
      (∀ co (M : NM co) d B c, Supp M B → B ≤ c →
        ∃ s, (∀ i, M s i = 0) ∧ G.succs co .mint M d B c = [mintStep co (colOut co d) s M]) ∧
      (∀ co (M : NM co) d B c, G.succs co .ordinary M d B c = [M]) ∧
      (∀ co (M N : NM co) B B', Supp M B → Supp N B' →
        (G.key co M = G.key co N ↔ ∃ σ : Equiv.Perm ℕ, N = M ∘ σ)) ∧
      (∀ (β : Type) co (S S' : NState co β),
        G.ckey S = G.ckey S' ↔ S.b = S'.b ∧ G.key co S.m = G.key co S'.m) ∧
      (∀ a t r a' p, G.fire a t r = some a' → t.resets.contains p = false →
        a' p = a p - Novel.TransferRows.consumedA a t p +
          (r.resolve (Novel.TransferRows.consumedA a t)).count p)

/- The pinned readable form of VER_012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_012 : NameGraph → Prop :=
fun G =>
  (∀ (co : List PlaceId) (cin : List (PlaceId × ℕ)) (rel : List PlaceId) (M : NM co) (d : Novel.ForwardDeposit.Deposit)
      (B c : ℕ),
      ∀ M' ∈ G.succs co (Role.join cin rel) M d B c,
        ∃ s, joinEnab co cin M s = true ∧ M' = joinStep co cin (relOut d rel) s M) ∧
    (∀ (co : List PlaceId) (cin : List (PlaceId × ℕ)) (rel : List PlaceId) (M : NM co)
        (d : Novel.ForwardDeposit.Deposit) (B c s : ℕ),
        Supp M B →
          joinEnab co cin M s = true →
            ∃ M' ∈ G.succs co (Role.join cin rel) M d B c,
              G.key co M' = G.key co (joinStep co cin (relOut d rel) s M)) ∧
      (∀ (co : List PlaceId) (inp : PlaceId) (M : NM co) (d : Novel.ForwardDeposit.Deposit) (B c : ℕ),
          ∀ M' ∈ G.succs co (Role.consume inp) M d B c,
            ∃ s, resident co inp M s = true ∧ M' = consumeStep co inp (colOut co d) s M) ∧
        (∀ (co : List PlaceId) (inp : PlaceId) (M : NM co) (d : Novel.ForwardDeposit.Deposit) (B c s : ℕ),
            Supp M B →
              resident co inp M s = true →
                ∃ M' ∈ G.succs co (Role.consume inp) M d B c,
                  G.key co M' = G.key co (consumeStep co inp (colOut co d) s M)) ∧
          (∀ (co : List PlaceId) (M : NM co) (d : Novel.ForwardDeposit.Deposit) (B c : ℕ),
              Supp M B →
                B ≤ c →
                  ∃ s,
                    (∀ (i : Fin co.length), M s i = 0) ∧
                      G.succs co Role.mint M d B c = [mintStep co (colOut co d) s M]) ∧
            (∀ (co : List PlaceId) (M : NM co) (d : Novel.ForwardDeposit.Deposit) (B c : ℕ),
                G.succs co Role.ordinary M d B c = [M]) ∧
              (∀ (co : List PlaceId) (M N : NM co) (B B' : ℕ),
                  Supp M B → Supp N B' → (G.key co M = G.key co N ↔ ∃ σ, N = M ∘ ⇑σ)) ∧
                (∀ (β : Type) (co : List PlaceId) (S S' : NState co β),
                    G.ckey S = G.ckey S' ↔ S.b = S'.b ∧ G.key co S.m = G.key co S'.m) ∧
                  ∀ (a : AMarking) (t : Transition) (r : Novel.RouteB.Row) (a' : AMarking) (p : PlaceId),
                    G.fire a t r = some a' →
                      t.resets.contains p = false →
                        a' p =
                          a p - Novel.TransferRows.consumedA a t p +
                            List.count p (Row.resolve (Novel.TransferRows.consumedA a t) r)
-/
#guard_msgs in #print VER_012

/-! ### The reference -/

/-- The Route B explorer keys its classes with the class key of `refNameGraph`. -/
theorem ver012_routeB_key {β : Type} {co : List PlaceId} (base : BaseLayer β)
    (net : List Novel.RouteB.NuTrans) (role : Novel.RouteB.NuTrans → Role) (conflict : Bool) :
    (routeB (co := co) base net role conflict).key = fun S => refNameGraph.ckey S := rfl

/-- The untimed base layer fires with the base step of `refNameGraph`. -/
theorem ver012_untimedBase_fire : untimedBase.fire = refNameGraph.fire := rfl

/-- What an input takes from its place: every token for `All` and `AtLeast`, the required count
otherwise. -/
theorem ver012_consumedA_eq (a : AMarking) (t : Transition) (p : PlaceId) :
    Novel.TransferRows.consumedA a t p = if consumeAllAt t p then a p else pre t p := by
  unfold Novel.TransferRows.consumedA consumeAllAt pre
  cases specAt t p with
  | none => rfl
  | some s => cases s.card.consumesAll <;> rfl

/-- ✓ **The shipped graph step meets VER-012.** Example: on a layer where name `0` sits in both
inputs of a join and name `1` in one input only, the join fires once, on name `0`; when the two
inputs hold different names, it does not fire, since its merge needs equal names. A mint with
counter `1` stamps the new name `1`, which no place held. Swapping two names in a layer gives the
same class key, so the graph stores the class once. -/
-- Lines 1 and 2: a join fires on the first symbol of each signature among the enabling symbols
-- (`key_swap`); lines 3 and 4: the same for a consumer over the resident symbols; line 5: a mint
-- stamps the counter; line 6: an ordinary transition copies the layer; line 7:
-- `canonicalKey_eq_iff_exists_perm`; line 8: the class key is the pair of base and name key;
-- line 9: `fireAD` takes what each input consumes and adds the deposit.
@[evidence holds VER_012]
theorem VER_012_reference : VER_012 refNameGraph := by
  refine ⟨fun co cin rel M d B c M' hM' => ?_, fun co cin rel M d B c s hM hs => ?_,
    fun co inp M d B c M' hM' => ?_, fun co inp M d B c s hM hs => ?_,
    fun co M d B c hM hc => ⟨c, fun i => hM c hc i, rfl⟩, fun co M d B c => rfl,
    fun co M N B B' hM hN => ?_, fun β co S S' => ?_, fun a t r a' p hf hp => ?_⟩
  · simp only [refNameGraph, nameSuccs, List.mem_map] at hM'
    obtain ⟨s, hs, rfl⟩ := hM'
    exact ⟨s, (mem_dsig_range hs).2, rfl⟩
  · have hB : ∀ u, joinEnab co cin M u = true → u < B :=
      fun u hu => lt_of_live hM (joinEnab_live cin M u hu)
    obtain ⟨u, hu, he⟩ := (dsig_transversal (M := M) hB).cover s hs
    refine ⟨joinStep co cin (relOut d rel) u M, ?_, ?_⟩
    · simp only [refNameGraph, nameSuccs, List.mem_map]
      exact ⟨u, hu, rfl⟩
    · exact key_swap (joinStep_sym cin (relOut d rel)) (sig_eq_iff.mp he)
  · simp only [refNameGraph, nameSuccs, List.mem_map] at hM'
    obtain ⟨s, hs, rfl⟩ := hM'
    exact ⟨s, (mem_dsig_range hs).2, rfl⟩
  · have hB : ∀ u, resident co inp M u = true → u < B :=
      fun u hu => lt_of_live hM (resident_live inp M u hu)
    obtain ⟨u, hu, he⟩ := (dsig_transversal (M := M) hB).cover s hs
    refine ⟨consumeStep co inp (colOut co d) u M, ?_, ?_⟩
    · simp only [refNameGraph, nameSuccs, List.mem_map]
      exact ⟨u, hu, rfl⟩
    · exact key_swap (consumeStep_sym inp (colOut co d)) (sig_eq_iff.mp he)
  · exact Novel.CanonicalKey.canonicalKey_eq_iff_exists_perm (liveSet_finite hM)
      (liveSet_finite hN)
  · show keyOf S = keyOf S' ↔ _
    simp only [keyOf, Prod.mk.injEq]
    rfl
  · simp only [refNameGraph, untimedBase, Option.some.injEq] at hf
    subst hf
    rw [ver012_consumedA_eq a t p]
    unfold Novel.ForwardDeposit.fireAD
    simp only [hp, Bool.false_eq_true, if_false]
    split <;> simp

/-! ### Examples: two correlated inputs -/

/-- The coloured set of the examples: the two correlated inputs `0` and `1`. -/
def ver012_co : List PlaceId := [0, 1]

/-- A join that takes one token from each of the inputs `0` and `1`. -/
def ver012_cin : List (PlaceId × ℕ) := [(0, 1), (1, 1)]

/-- Name `0` holds a token in both inputs; name `1` holds one in input `1` only. -/
def ver012_aligned : NM ver012_co := fun s i => if s = 0 then 1 else if s = 1 ∧ i.1 = 1 then 1 else 0

/-- Crossed names: name `0` in input `0`, name `1` in input `1`. -/
def ver012_crossed : NM ver012_co := fun s i => if s = i.1 then 1 else 0

/-- Two names in both inputs: name `0` once in each, name `1` twice in each. -/
def ver012_twoNames : NM ver012_co := fun s _ => if s = 0 then 1 else if s = 1 then 2 else 0

/-- A transition that drains place `0` (`All`). -/
def ver012_drain : Transition :=
  { name := "drain", inputs := [⟨0, .all, none⟩], inhibitors := [], reads := [], resets := [] }

/-- A transition that takes one token from place `0` (`One`). -/
def ver012_take : Transition :=
  { name := "take", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- A name with no token anywhere enables no join of the examples. -/
theorem ver012_joinEnab_dead {M : NM ver012_co} {s : ℕ} (h : ∀ i, M s i = 0) :
    joinEnab ver012_co ver012_cin M s = false := by
  have : Novel.RouteB.cnt ver012_co M s 0 = 0 := by
    unfold Novel.RouteB.cnt; split <;> simp only [h]
  simp [joinEnab, ver012_cin, this]

/-- No name enables the join on the crossed layer. -/
theorem ver012_crossed_dead (s : ℕ) : joinEnab ver012_co ver012_cin ver012_crossed s = false := by
  rcases s with _ | _ | s
  · decide
  · decide
  · exact ver012_joinEnab_dead fun i => by
      simp only [ver012_crossed]
      have := i.2
      simp only [ver012_co, List.length_cons, List.length_nil] at this
      rw [if_neg (by omega)]

/-- The two-name layer is supported below `2`. -/
theorem ver012_twoNames_supp : Supp ver012_twoNames 2 := by
  intro s hs i
  simp only [ver012_twoNames]
  rw [if_neg (by omega), if_neg (by omega)]

/-! ### Violation: a join that reads a name in its first input only (line 1) -/

/-- A graph whose join fires on every name its first correlated input holds, without asking the
other inputs for the same name: the count-level reading of a join. -/
noncomputable def ver012_firstInput : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .join cin rel => match cin with
        | [] => []
        | (p0, _) :: _ => ((List.range B).filter (resident co p0 M)).map fun s =>
            joinStep co cin (relOut d rel) s M
      | r => nameSuccs co r M d B c }

/-- ✗ A join that reads its first input only violates VER-012 (line 1). Name `0` sits in input `0`
and name `1` in input `1`; no name is in both, yet this graph fires the join on name `0`. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_firstInput : ¬ VER_012 ver012_firstInput := by
  intro h
  have hmem : joinStep ver012_co ver012_cin [] 0 ver012_crossed ∈
      ver012_firstInput.succs ver012_co (.join ver012_cin []) ver012_crossed [] 2 0 := by
    have : ver012_firstInput.succs ver012_co (.join ver012_cin []) ver012_crossed [] 2 0 =
        [joinStep ver012_co ver012_cin [] 0 ver012_crossed] := rfl
    rw [this]; exact List.mem_singleton_self _
  obtain ⟨s, hs, -⟩ := h.1 _ _ _ _ _ _ _ _ hmem
  rw [ver012_crossed_dead] at hs
  cases hs

/-! ### Violation: a join fired on one name only (line 2) -/

/-- A graph whose join fires on one enabling name only, the least one: one name chosen, as the
executor chooses one, where the graph must explore every name up to renaming. -/
noncomputable def ver012_leastName : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .join cin rel => match (List.range B).find? (joinEnab co cin M) with
        | some s => [joinStep co cin (relOut d rel) s M]
        | none => []
      | r => nameSuccs co r M d B c }

/-- ✗ A join fired on one name only violates VER-012 (line 2). Name `0` holds one token and name
`1` two tokens in each input. Firing on name `0` leaves name `1` with two tokens per input;
firing on name `1` leaves one token of each name. No renaming turns one into the other, yet this
graph keeps only the first. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_leastName : ¬ VER_012 ver012_leastName := by
  intro h
  obtain ⟨M', hM', hk⟩ := h.2.1 ver012_co ver012_cin [] ver012_twoNames [] 2 0 1
    ver012_twoNames_supp (by decide)
  have hl : ver012_leastName.succs ver012_co (.join ver012_cin []) ver012_twoNames [] 2 0 =
      [joinStep ver012_co ver012_cin [] 0 ver012_twoNames] := rfl
  rw [hl, List.mem_singleton] at hM'
  subst hM'
  have hloc := joinStep_local (co := ver012_co) ver012_cin []
  have hs0 : Supp (joinStep ver012_co ver012_cin [] 0 ver012_twoNames) 2 :=
    supp_of_local hloc ver012_twoNames_supp (by omega) (Nat.le_refl _)
  have hs1 : Supp (joinStep ver012_co ver012_cin [] 1 ver012_twoNames) 2 :=
    supp_of_local hloc ver012_twoNames_supp (by omega) (Nat.le_refl _)
  obtain ⟨σ, hσ⟩ := Novel.CanonicalKey.canonicalKey_complete (liveSet_finite hs0)
    (liveSet_finite hs1) hk
  have hv := congrFun (congrFun hσ (σ.symm 1)) ⟨0, by decide⟩
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hv
  have h2 : joinStep ver012_co ver012_cin [] 0 ver012_twoNames 1 ⟨0, by decide⟩ = 2 := by decide
  rw [h2] at hv
  by_cases hu : σ.symm 1 = 1
  · rw [hu] at hv
    have : joinStep ver012_co ver012_cin [] 1 ver012_twoNames 1 ⟨0, by decide⟩ = 1 := by decide
    omega
  · rw [hloc 1 ver012_twoNames _ hu] at hv
    simp only [ver012_twoNames] at hv
    split at hv <;> omega

/-! ### Examples: one coloured place -/

/-- One coloured place. -/
def ver012_co1 : List PlaceId := [0]

/-- One token of name `0` on the place. -/
def ver012_one : NM ver012_co1 := fun s _ => if s = 0 then 1 else 0

/-- The one-token layer is supported below `1`. -/
theorem ver012_one_supp : Supp ver012_one 1 := fun s hs i => by
  simp only [ver012_one]; rw [if_neg (by omega)]

/-- Only name `0` is resident in the place of the one-token layer. -/
theorem ver012_one_resident {s : ℕ} (h : resident ver012_co1 0 ver012_one s = true) : s = 0 := by
  rcases s with _ | s
  · rfl
  · exfalso
    have : Novel.RouteB.cnt ver012_co1 ver012_one (s + 1) 0 = 0 := by
      unfold Novel.RouteB.cnt; split <;> simp [ver012_one]
    simp [resident, this] at h

/-! ### Violation: a consumer fired on a name its input does not hold (line 3) -/

/-- A graph whose coloured consumer fires on every symbol below the support bound, resident in its
input or not. -/
noncomputable def ver012_anySymbol : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .consume inp => (List.range B).map fun s => consumeStep co inp (colOut co d) s M
      | r => nameSuccs co r M d B c }

/-- ✗ A consumer fired on a name its input does not hold violates VER-012 (line 3). The place holds
one token of name `0`; this graph also fires the consumer on name `1`, which takes nothing and
leaves the layer as it was, a firing no name of the input allows. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_anySymbol : ¬ VER_012 ver012_anySymbol := by
  intro h
  have hmem : consumeStep ver012_co1 0 [] 1 ver012_one ∈
      ver012_anySymbol.succs ver012_co1 (.consume 0) ver012_one [] 2 0 := by
    show _ ∈ (List.range 2).map fun s => consumeStep ver012_co1 0 [] s ver012_one
    exact List.mem_map.mpr ⟨1, List.mem_range.mpr (by decide), rfl⟩
  obtain ⟨s, hs, he⟩ := h.2.2.1 _ _ _ _ _ _ _ hmem
  rw [ver012_one_resident hs] at he
  have := congrFun (congrFun he 0) ⟨0, by decide⟩
  revert this
  decide

/-! ### Violation: a consumer fired on one name only (line 4) -/

/-- A graph whose coloured consumer fires on one resident name only, the least one. -/
noncomputable def ver012_consumeLeast : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .consume inp => match (List.range B).find? (resident co inp M) with
        | some s => [consumeStep co inp (colOut co d) s M]
        | none => []
      | r => nameSuccs co r M d B c }

/-- ✗ A consumer fired on one name only violates VER-012 (line 4). Input `0` holds one token of
name `0` and two of name `1`. Consuming name `0` leaves name `1` with two tokens in each place;
consuming name `1` leaves it one token in input `0`. No renaming turns one into the other, yet
this graph keeps only the first. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_consumeLeast : ¬ VER_012 ver012_consumeLeast := by
  intro h
  obtain ⟨M', hM', hk⟩ := h.2.2.2.1 ver012_co 0 ver012_twoNames [] 2 0 1
    ver012_twoNames_supp (by decide)
  have hl : ver012_consumeLeast.succs ver012_co (.consume 0) ver012_twoNames [] 2 0 =
      [consumeStep ver012_co 0 [] 0 ver012_twoNames] := rfl
  have hc : colOut ver012_co [] = [] := rfl
  rw [hl, List.mem_singleton] at hM'
  rw [hc] at hk
  subst hM'
  have hloc := consumeStep_local (co := ver012_co) 0 []
  have hs0 : Supp (consumeStep ver012_co 0 [] 0 ver012_twoNames) 2 :=
    supp_of_local hloc ver012_twoNames_supp (by omega) (Nat.le_refl _)
  have hs1 : Supp (consumeStep ver012_co 0 [] 1 ver012_twoNames) 2 :=
    supp_of_local hloc ver012_twoNames_supp (by omega) (Nat.le_refl _)
  obtain ⟨σ, hσ⟩ := Novel.CanonicalKey.canonicalKey_complete (liveSet_finite hs0)
    (liveSet_finite hs1) hk
  have hv := congrFun (congrFun hσ (σ.symm 1)) ⟨0, by decide⟩
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hv
  have h2 : consumeStep ver012_co 0 [] 0 ver012_twoNames 1 ⟨0, by decide⟩ = 2 := by decide
  rw [h2] at hv
  by_cases hu : σ.symm 1 = 1
  · rw [hu] at hv
    have : consumeStep ver012_co 0 [] 1 ver012_twoNames 1 ⟨0, by decide⟩ = 1 := by decide
    omega
  · rw [hloc 1 ver012_twoNames _ hu] at hv
    simp only [ver012_twoNames] at hv
    split at hv <;> omega

/-! ### Violation: a mint that reuses a live name (line 5) -/

/-- A graph whose mint always stamps symbol `0`, live or not. -/
noncomputable def ver012_mintZero : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .mint => [mintStep co (colOut co d) 0 M]
      | r => nameSuccs co r M d B c }

/-- ✗ A mint that reuses a live name violates VER-012 (line 5). The place holds one token of name
`0`; this mint adds a second token of name `0` where it must add a name no place holds, so the
fresh name and the live one become one and a join could fire on the pair. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_mintZero : ¬ VER_012 ver012_mintZero := by
  intro h
  obtain ⟨s, hs, he⟩ := h.2.2.2.2.1 ver012_co1 ver012_one [0] 1 1 ver012_one_supp (Nat.le_refl _)
  have hl : ver012_mintZero.succs ver012_co1 .mint ver012_one [0] 1 1 =
      [mintStep ver012_co1 (colOut ver012_co1 [0]) 0 ver012_one] := rfl
  rw [hl, List.cons.injEq] at he
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := hs ⟨0, by decide⟩
    revert this
    decide
  have hv := congrFun (congrFun he.1 0) ⟨0, by decide⟩
  rw [mintStep_local _ s ver012_one 0 (Ne.symm hs0)] at hv
  revert hv
  decide

/-! ### Violation: an ordinary transition that drops the names (line 6) -/

/-- A graph whose ordinary transitions have no name successor. -/
noncomputable def ver012_ordinaryDrop : NameGraph :=
  { refNameGraph with
    succs := fun co r M d B c => match r with
      | .ordinary => []
      | r => nameSuccs co r M d B c }

/-- ✗ An ordinary transition without a name successor violates VER-012 (line 6). A transition that
touches no coloured place must keep the one token of name `0` where it is; this graph loses the
firing altogether. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_ordinaryDrop : ¬ VER_012 ver012_ordinaryDrop := by
  intro h
  have := h.2.2.2.2.2.1 ver012_co1 ver012_one [] 1 0
  cases this

/-! ### Violation: a key that reads the names (line 7) -/

/-- A graph whose name key lists the tokens of name `0` per place: it reads a symbol's
identity. -/
noncomputable def ver012_identityKey : NameGraph :=
  { refNameGraph with key := fun co M => (List.finRange co.length).map fun i => [toLex (M 0 i, 0)] }

/-- ✗ A key that reads the names violates VER-012 (line 7). One token of name `0`, and the same
token renamed to name `1`: a renaming, so one class, yet this key tells them apart. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_identityKey : ¬ VER_012 ver012_identityKey := by
  intro h
  have hN : Supp (ver012_one ∘ Equiv.swap 0 1) 2 := fun s hs i => by
    simp only [Function.comp_apply, ver012_one]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), if_neg (by omega)]
  have := (h.2.2.2.2.2.2.1 ver012_co1 _ _ 1 2 ver012_one_supp hN).2 ⟨Equiv.swap 0 1, rfl⟩
  revert this
  decide

/-! ### Violation: a key that forgets the names (line 7) -/

/-- A graph whose name key is empty: classes are told apart by their base alone, the counts. -/
noncomputable def ver012_nameBlind : NameGraph := { refNameGraph with key := fun _ _ => [] }

/-- ✗ A name-blind key violates VER-012 (line 7). The empty layer and a layer with one token are
no renaming of each other, yet this key gives them one key. On a class key it merges the aligned
layer with the crossed one, which is the value-blind count abstraction Route B exists to avoid. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_nameBlind : ¬ VER_012 ver012_nameBlind := by
  intro h
  have hM : Supp (fun _ _ => 0 : NM ver012_co1) 0 := fun _ _ _ => rfl
  obtain ⟨σ, hσ⟩ := (h.2.2.2.2.2.2.1 ver012_co1 _ _ 0 1 hM ver012_one_supp).1 rfl
  have := congrFun (congrFun hσ 0) ⟨0, by decide⟩
  simp [ver012_one] at this

/-! ### Violation: a class key that hides the base (line 8) -/

/-- A graph whose class key keeps the name key and hides the base: two classes that differ in
their base (their earliest-ready times, say) get one key. -/
noncomputable def ver012_baseBlind : NameGraph :=
  { refNameGraph with
    ckey := fun S => (Classical.choice ⟨S.b⟩, Novel.CanonicalKey.canonicalKey S.m) }

/-- The class with base `b` and no coloured place. -/
def ver012_cls (b : Bool) : NState [] Bool := ⟨b, fun _ i => i.elim0, 0, fun _ _ i => i.elim0⟩

/-- ✗ A class key that hides the base violates VER-012 (line 8). Two classes with the same (empty)
name layer and bases `true` and `false` must stay two classes, as two arrivals with different
earliest-ready times must; this key merges them. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_baseBlind : ¬ VER_012 ver012_baseBlind := by
  intro h
  have := ((h.2.2.2.2.2.2.2.1 Bool [] (ver012_cls true) (ver012_cls false)).1 rfl).1
  cases this

/-! ### Violation: an `All` input that consumes its required count (line 9) -/

/-- A graph whose base step takes `requiredCount` tokens from every input, `All` and `AtLeast`
included. -/
noncomputable def ver012_requiredCount : NameGraph :=
  { refNameGraph with
    fire := fun a t r => some fun p =>
      if t.resets.contains p then (r.resolve (Novel.TransferRows.consumedA a t)).count p
      else a p - pre t p + (r.resolve (Novel.TransferRows.consumedA a t)).count p }

/-- ✗ Consuming the required count violates VER-012 (line 9). `drain` takes `All` from place `0`,
which holds 3 tokens; this step takes 1 and leaves 2 behind, a phantom residue that keeps an
inhibitor arc on place `0` unsatisfied. The shipped step leaves the place empty. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_requiredCount : ¬ VER_012 ver012_requiredCount := by
  intro h
  have := h.2.2.2.2.2.2.2.2 (fun _ => 3) ver012_drain ⟨[], []⟩ _ 0 rfl (by decide)
  revert this
  decide

/-! ### Violation: a `One` input that consumes nothing (line 9) -/

/-- A graph whose base step drains `All` and `AtLeast` inputs but takes nothing from a `One` or
`Exactly` input. -/
noncomputable def ver012_noConsume : NameGraph :=
  { refNameGraph with
    fire := fun a t r => some fun p =>
      if t.resets.contains p || consumeAllAt t p then
        (r.resolve (Novel.TransferRows.consumedA a t)).count p
      else a p + (r.resolve (Novel.TransferRows.consumedA a t)).count p }

/-- ✗ Taking nothing from a `One` input violates VER-012 (line 9). `take` takes one token from
place `0`, which holds 3; this step leaves all 3, so the token the transition consumed is still
there to be consumed again. The shipped step leaves 2. -/
@[evidence forbids VER_012]
theorem VER_012_forbids_noConsume : ¬ VER_012 ver012_noConsume := by
  intro h
  have := h.2.2.2.2.2.2.2.2 (fun _ => 3) ver012_take ⟨[], []⟩ _ 0 rfl (by decide)
  revert this
  decide

/-! ### The lines exercised -/

/-- The shipped step on the examples. On the layer where name `0` is in both inputs and name `1`
in input `1` only, the join fires once, on name `0` (lines 1 and 2). On the crossed layer it does
not fire at all: reaching its merge would need two names to be equal. A consumer of the one-token
place fires on name `0` and empties the place (lines 3 and 4). A mint with counter `1` stamps
name `1` beside it (line 5). Renaming the two names of the crossed layer keeps its key (line 7).
Draining place `0` from 3 tokens leaves it empty, and taking one leaves 2 (line 9). -/
@[evidence nonvacuous VER_012]
theorem VER_012_nonvacuous :
    refNameGraph.succs ver012_co (.join ver012_cin []) ver012_aligned [] 2 0 =
        [joinStep ver012_co ver012_cin [] 0 ver012_aligned] ∧
      joinEnab ver012_co ver012_cin ver012_aligned 0 = true ∧
      refNameGraph.succs ver012_co (.join ver012_cin []) ver012_crossed [] 2 0 = [] ∧
      refNameGraph.succs ver012_co1 (.consume 0) ver012_one [] 1 1 =
        [consumeStep ver012_co1 0 [] 0 ver012_one] ∧
      consumeStep ver012_co1 0 [] 0 ver012_one 0 ⟨0, by decide⟩ = 0 ∧
      refNameGraph.succs ver012_co1 .mint ver012_one [0] 1 1 =
        [mintStep ver012_co1 [0] 1 ver012_one] ∧
      mintStep ver012_co1 [0] 1 ver012_one 1 ⟨0, by decide⟩ = 1 ∧
      refNameGraph.key ver012_co (ver012_crossed ∘ Equiv.swap 0 1) =
        refNameGraph.key ver012_co ver012_crossed ∧
      (refNameGraph.fire (fun _ => 3) ver012_drain ⟨[], []⟩).map (· 0) = some 0 ∧
      (refNameGraph.fire (fun _ => 3) ver012_take ⟨[], []⟩).map (· 0) = some 2 := by
  refine ⟨rfl, by decide, rfl, rfl, by decide, rfl, by decide,
    Novel.CanonicalKey.canonicalKey_comp _ _, by decide, by decide⟩

/-! ### Consequence: the name step is key-equivariant -/

/-- A key that meets line 7 does not see a renaming. -/
theorem ver012_key_comp {G : NameGraph} (h : VER_012 G) {co : List PlaceId} {X : NM co}
    {σ : Equiv.Perm ℕ} {B B' : ℕ} (hX : Supp X B) (hXσ : Supp (X ∘ σ) B') :
    G.key co (X ∘ σ) = G.key co X :=
  ((h.2.2.2.2.2.2.1 co X (X ∘ σ) B B' hX hXσ).2 ⟨σ, rfl⟩).symm

/-- **The name successors of a graph that meets VER-012 depend only on the key of the layer they
are fired from.** Take two name layers with one key, say name `0` alone and the same layer with
name `0` renamed to `5`, each with a fresh mint counter. Whatever the role, every name successor
of the second has a name successor of the first with the same key: a join or a consumer fired on
`5` has its twin fired on `0`, a mint stamps a fresh name either way. This is the name-layer half
of the premise of the build's completeness line; the shipped step meets the whole premise
(`Novel.RouteB.routeB_equivariant`). -/
@[evidence cites "VER-012" "up to renaming"]
theorem ver012_succs_keys {G : NameGraph} (h : VER_012 G) {co : List PlaceId} (r : Role)
    (d : Novel.ForwardDeposit.Deposit) {M N : NM co} {B B' c c' : ℕ} (hM : Supp M B)
    (hN : Supp N B') (hc : B ≤ c) (hc' : B' ≤ c') (hk : G.key co M = G.key co N) :
    ∀ N' ∈ G.succs co r N d B' c', ∃ M' ∈ G.succs co r M d B c, G.key co M' = G.key co N' := by
  obtain ⟨σ, rfl⟩ := (h.2.2.2.2.2.2.1 co M N B B' hM hN).1 hk
  intro N' hN'
  cases r with
  | ordinary =>
    rw [h.2.2.2.2.2.1] at hN'
    rw [List.mem_singleton.mp hN']
    exact ⟨M, by rw [h.2.2.2.2.2.1]; exact List.mem_singleton_self _, hk⟩
  | mint =>
    obtain ⟨s, hs, hl⟩ := h.2.2.2.2.1 co M d B c hM hc
    obtain ⟨s', hs', hl'⟩ := h.2.2.2.2.1 co (M ∘ σ) d B' c' hN hc'
    rw [hl', List.mem_singleton] at hN'
    subst hN'
    refine ⟨mintStep co (colOut co d) s M, by rw [hl]; exact List.mem_singleton_self _, ?_⟩
    have hloc := mintStep_local (co := co) (colOut co d)
    have h1 : mintStep co (colOut co d) s' (M ∘ σ) = mintStep co (colOut co d) (σ s') M ∘ σ := by
      have := mintStep_sym (co := co) (colOut co d) σ (σ s') M
      simpa using this
    have hfix : M ∘ Equiv.swap s (σ s') = M := by
      funext u
      simp only [Function.comp]
      have hrow : M s = M (σ s') := by
        funext i
        rw [hs i]
        exact (hs' i).symm
      by_cases h1 : u = s
      · subst h1; rw [Equiv.swap_apply_left, hrow]
      · by_cases h2 : u = σ s'
        · subst h2; rw [Equiv.swap_apply_right, hrow]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    have h2 : mintStep co (colOut co d) (σ s') M =
        mintStep co (colOut co d) s M ∘ Equiv.swap s (σ s') := by
      have := mintStep_sym (co := co) (colOut co d) (Equiv.swap s (σ s')) s M
      rw [Equiv.symm_swap, Equiv.swap_apply_left, hfix] at this
      exact this
    have hS1 : Supp (mintStep co (colOut co d) s M) (max B (s + 1)) :=
      supp_of_local hloc hM (by omega) (Nat.le_max_left _ _)
    have hS2 : Supp (mintStep co (colOut co d) (σ s') M) (max B (σ s' + 1)) :=
      supp_of_local hloc hM (by omega) (Nat.le_max_left _ _)
    have hS3 : Supp (mintStep co (colOut co d) s' (M ∘ σ)) (max B' (s' + 1)) :=
      supp_of_local hloc hN (by omega) (Nat.le_max_left _ _)
    rw [h1] at hS3 ⊢
    rw [ver012_key_comp h hS2 hS3, h2]
    rw [h2] at hS2
    exact (ver012_key_comp h hS1 hS2).symm
  | join cin rel =>
    obtain ⟨u, hu, rfl⟩ := h.1 co cin rel (M ∘ σ) d B' c' N' hN'
    have hu' : joinEnab co cin M (σ u) = true := by rw [← joinEnab_inv cin M σ u]; exact hu
    obtain ⟨M', hM', hk'⟩ := h.2.1 co cin rel M d B c (σ u) hM hu'
    refine ⟨M', hM', hk'.trans ?_⟩
    have hloc := joinStep_local (co := co) cin (relOut d rel)
    have h1 : joinStep co cin (relOut d rel) u (M ∘ σ) =
        joinStep co cin (relOut d rel) (σ u) M ∘ σ := by
      have := joinStep_sym (co := co) cin (relOut d rel) σ (σ u) M
      simpa using this
    have hS1 : Supp (joinStep co cin (relOut d rel) (σ u) M) B :=
      supp_of_local hloc hM (lt_of_live hM (joinEnab_live cin M _ hu')) (Nat.le_refl _)
    have hS2 : Supp (joinStep co cin (relOut d rel) u (M ∘ σ)) B' :=
      supp_of_local hloc hN (lt_of_live hN (joinEnab_live cin _ _ hu)) (Nat.le_refl _)
    rw [h1] at hS2 ⊢
    exact (ver012_key_comp h hS1 hS2).symm
  | consume inp =>
    obtain ⟨u, hu, rfl⟩ := h.2.2.1 co inp (M ∘ σ) d B' c' N' hN'
    have hu' : resident co inp M (σ u) = true := by rw [← resident_inv inp M σ u]; exact hu
    obtain ⟨M', hM', hk'⟩ := h.2.2.2.1 co inp M d B c (σ u) hM hu'
    refine ⟨M', hM', hk'.trans ?_⟩
    have hloc := consumeStep_local (co := co) inp (colOut co d)
    have h1 : consumeStep co inp (colOut co d) u (M ∘ σ) =
        consumeStep co inp (colOut co d) (σ u) M ∘ σ := by
      have := consumeStep_sym (co := co) inp (colOut co d) σ (σ u) M
      simpa using this
    have hS1 : Supp (consumeStep co inp (colOut co d) (σ u) M) B :=
      supp_of_local hloc hM (lt_of_live hM (resident_live inp M _ hu')) (Nat.le_refl _)
    have hS2 : Supp (consumeStep co inp (colOut co d) u (M ∘ σ)) B' :=
      supp_of_local hloc hN (lt_of_live hN (resident_live inp _ _ hu)) (Nat.le_refl _)
    rw [h1] at hS2 ⊢
    exact (ver012_key_comp h hS1 hS2).symm

/-! ## The early stop: the verdict of the build without it -/

section EarlyStop

variable {S K L : Type} (E : Explorer S K L)

/-- The classes of a build that stopped early at its first violating class: classes none of
which is bad, then one bad class. -/
def ver012FirstBad (bad : S → Bool) (l : List S) : Prop :=
  ∃ pre y, l = pre ++ [y] ∧ (∀ z ∈ pre, bad z = false) ∧ bad y = true

/-- Without the early stop an expansion never ends early. -/
theorem ver012_expandB_false (bad : S → Bool) :
    ∀ (cls : List S) (ys : List (L × S)), (Decide.expandB E bad false cls ys).2 = false
  | cls, [] => by simp [Decide.expandB]
  | cls, (l, y) :: ys => by
    classical
    unfold Decide.expandB
    split
    · exact ver012_expandB_false bad cls ys
    · rw [if_neg (by simp)]
      exact ver012_expandB_false bad _ ys

/-- One expansion with and without the early stop, from classes none of which is bad: either
both give the same result and every class is still not bad, or the early stop ended at the first
bad class it found and the expansion without it went on from there. -/
theorem ver012_expandB_cmp (bad : S → Bool) :
    ∀ (ys : List (L × S)) (cls : List S), (∀ z ∈ cls, bad z = false) →
      ((Decide.expandB E bad true cls ys).2 = false →
        Decide.expandB E bad true cls ys = Decide.expandB E bad false cls ys ∧
          ∀ z ∈ (Decide.expandB E bad true cls ys).1, bad z = false) ∧
      ((Decide.expandB E bad true cls ys).2 = true →
        ver012FirstBad bad (Decide.expandB E bad true cls ys).1 ∧
          (Decide.expandB E bad true cls ys).1 <+: (Decide.expandB E bad false cls ys).1)
  | [], cls, h => by simp [Decide.expandB]; exact h
  | (l, y) :: ys, cls, h => by
    classical
    by_cases hk : ∃ z ∈ cls, E.key z = E.key y
    · have e1 : Decide.expandB E bad true cls ((l, y) :: ys) = Decide.expandB E bad true cls ys := by
        rw [Decide.expandB, if_pos hk]
      have e2 : Decide.expandB E bad false cls ((l, y) :: ys) =
          Decide.expandB E bad false cls ys := by
        rw [Decide.expandB, if_pos hk]
      rw [e1, e2]
      exact ver012_expandB_cmp bad ys cls h
    · cases hb : bad y
      · have e1 : Decide.expandB E bad true cls ((l, y) :: ys) =
            Decide.expandB E bad true (cls ++ [y]) ys := by
          rw [Decide.expandB, if_neg hk, if_neg (by simp [hb])]
        have e2 : Decide.expandB E bad false cls ((l, y) :: ys) =
            Decide.expandB E bad false (cls ++ [y]) ys := by
          rw [Decide.expandB, if_neg hk, if_neg (by simp)]
        rw [e1, e2]
        refine ver012_expandB_cmp bad ys (cls ++ [y]) fun z hz => ?_
        rcases List.mem_append.mp hz with hz | hz
        · exact h z hz
        · rw [List.mem_singleton.mp hz]; exact hb
      · have e1 : Decide.expandB E bad true cls ((l, y) :: ys) = (cls ++ [y], true) := by
          rw [Decide.expandB, if_neg hk, if_pos (by simp [hb])]
        have e2 : Decide.expandB E bad false cls ((l, y) :: ys) =
            Decide.expandB E bad false (cls ++ [y]) ys := by
          rw [Decide.expandB, if_neg hk, if_neg (by simp)]
        rw [e1, e2]
        refine ⟨fun h' => absurd h' (by simp), fun _ => ⟨⟨cls, y, rfl, h, hb⟩, ?_⟩⟩
        obtain ⟨⟨t, ht, -⟩, -⟩ := Decide.expandB_spec E bad false ys (cls ++ [y])
        exact ⟨t, ht.symm⟩

/-- The loop with and without the early stop, from classes none of which is bad: the same
result, or an early stop at the first bad class that was not stopped, whose classes the loop
without it stores first. -/
theorem ver012_loop_cmp (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) :
    ∀ fuel cls exp c, (∀ z ∈ cls, bad z = false) →
      Decide.loop E maxClasses cut bad true fuel cls exp c =
          Decide.loop E maxClasses cut bad false fuel cls exp c ∨
        ((Decide.loop E maxClasses cut bad true fuel cls exp c).stopped = false ∧
          ver012FirstBad bad (Decide.loop E maxClasses cut bad true fuel cls exp c).cls ∧
          (Decide.loop E maxClasses cut bad true fuel cls exp c).cls <+:
            (Decide.loop E maxClasses cut bad false fuel cls exp c).cls)
  | 0, cls, exp, c, _ => Or.inl rfl
  | fuel + 1, cls, exp, c, h => by
    cases hx : cls[exp]? with
    | none => left; simp only [Decide.loop, hx]
    | some x =>
      by_cases hm : maxClasses ≤ cls.length
      · left; simp only [Decide.loop, hx, if_pos hm]
      by_cases hc : cut fuel = true
      · left; simp only [Decide.loop, hx, if_neg hm, if_pos hc]
      obtain ⟨h1, h2⟩ := ver012_expandB_cmp E bad (E.succ c x) cls h
      have hf := ver012_expandB_false E bad cls (E.succ c x)
      rcases hr : Decide.expandB E bad true cls (E.succ c x) with ⟨cls1, _ | _⟩
      · obtain ⟨heq, hall⟩ := h1 (by rw [hr])
        rw [hr] at heq hall
        have hr2 : Decide.expandB E bad false cls (E.succ c x) = (cls1, false) := heq.symm
        have ht : Decide.loop E maxClasses cut bad true (fuel + 1) cls exp c =
            Decide.loop E maxClasses cut bad true fuel cls1 (exp + 1)
              (Decide.nextC E c (E.succ c x)) := by
          simp only [Decide.loop, hx, if_neg hm, if_neg hc, hr]
        have hfl : Decide.loop E maxClasses cut bad false (fuel + 1) cls exp c =
            Decide.loop E maxClasses cut bad false fuel cls1 (exp + 1)
              (Decide.nextC E c (E.succ c x)) := by
          simp only [Decide.loop, hx, if_neg hm, if_neg hc, hr2]
        rw [ht, hfl]
        exact ver012_loop_cmp maxClasses cut bad fuel cls1 (exp + 1) _ hall
      · obtain ⟨hfb, hpre⟩ := h2 (by rw [hr])
        rw [hr] at hfb hpre
        obtain ⟨cls2, hr2⟩ : ∃ cls2, Decide.expandB E bad false cls (E.succ c x) = (cls2, false) :=
          ⟨_, Prod.ext rfl hf⟩
        rw [hr2] at hpre
        have ht : Decide.loop E maxClasses cut bad true (fuel + 1) cls exp c =
            ⟨cls1, exp, false, false, true⟩ := by
          simp only [Decide.loop, hx, if_neg hm, if_neg hc, hr]
        have hfl : Decide.loop E maxClasses cut bad false (fuel + 1) cls exp c =
            Decide.loop E maxClasses cut bad false fuel cls2 (exp + 1)
              (Decide.nextC E c (E.succ c x)) := by
          simp only [Decide.loop, hx, if_neg hm, if_neg hc, hr2]
        rw [ht, hfl]
        refine Or.inr ⟨rfl, hfb, ?_⟩
        obtain ⟨u, hu⟩ := Verifier.Graph.loop_prefix E maxClasses cut bad false fuel cls2 (exp + 1)
          (Decide.nextC E c (E.succ c x))
        exact hpre.trans ⟨u, hu.symm⟩

/-- The build with and without the early stop: the same result, or an early stop at the first
bad class that was not stopped, whose classes the build without it stores first. -/
theorem ver012_build_cmp (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (fuel : ℕ) (x0 : S) :
    Decide.build E maxClasses cut bad true fuel x0 = Decide.build E maxClasses cut bad false fuel x0 ∨
      ((Decide.build E maxClasses cut bad true fuel x0).stopped = false ∧
        ver012FirstBad bad (Decide.build E maxClasses cut bad true fuel x0).cls ∧
        (Decide.build E maxClasses cut bad true fuel x0).cls <+:
          (Decide.build E maxClasses cut bad false fuel x0).cls) := by
  have hfl : Decide.build E maxClasses cut bad false fuel x0 =
      Decide.loop E maxClasses cut bad false fuel [x0] 0 (E.bound x0) := by
    simp [Decide.build]
  cases hb : bad x0
  · have ht : Decide.build E maxClasses cut bad true fuel x0 =
        Decide.loop E maxClasses cut bad true fuel [x0] 0 (E.bound x0) := by
      simp [Decide.build, hb]
    rw [ht, hfl]
    exact ver012_loop_cmp E maxClasses cut bad fuel [x0] 0 _ (by simpa using hb)
  · have ht : Decide.build E maxClasses cut bad true fuel x0 = ⟨[x0], 0, false, false, true⟩ := by
      simp [Decide.build, hb]
    rw [ht, hfl]
    refine Or.inr ⟨rfl, ⟨[], x0, rfl, by simp, hb⟩, ?_⟩
    obtain ⟨u, hu⟩ := Verifier.Graph.loop_prefix E maxClasses cut bad false fuel [x0] 0 (E.bound x0)
    exact ⟨u, hu.symm⟩

/-- On a range, `find?` returns the first index at which the test holds. -/
theorem ver012_find_range {p : ℕ → Bool} {i : ℕ} (hi : p i = true) (hlt : ∀ j < i, p j = false) :
    ∀ n, i < n → (List.range n).find? p = some i := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge i n with h | h
    · rw [ih h]; rfl
    · have : i = n := by omega
      subst this
      rw [List.find?_eq_none.mpr (fun j hj => by
        have := hlt j (List.mem_range.mp hj); simp [this])]
      simp [hi]

/-- A graph that was not stopped, whose classes start with classes that are not bad and then a
bad one, is `Violated` at that bad class for the safety property. -/
theorem ver012_verdict_at {o : Decide.Out S} {bad : S → Bool} (hs : o.stopped = false)
    {pre : List S} {y : S} {u : List S} (hcls : o.cls = pre ++ [y] ++ u)
    (hpre : ∀ z ∈ pre, bad z = false) (hy : bad y = true) :
    Decide.verdict E o (.safety bad) = .violated pre.length := by
  have hfind : (List.range o.cls.length).find? (Decide.violatesAt E o (.safety bad)) =
      some pre.length := by
    refine ver012_find_range ?_ (fun j hj => ?_) _ (by simp [hcls])
    · simp [Decide.violatesAt, hcls, hy]
    · simp only [Decide.violatesAt, hcls, List.append_assoc]
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
      exact hpre _ (List.getElem_mem hj)
  simp only [Decide.verdict, hs, Bool.false_eq_true, if_false, hfind]

/-- **The early stop gives the verdict of the build without it.** For a safety property, the build
that stops at the first violating class answers what the build without the early stop answers,
whenever that build is not stopped by the total budget or a cancellation: the same `Violated` at
the same class, or the same answer when no class violates. -/
theorem ver012_early_verdict (maxClasses : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (fuel : ℕ) (x0 : S)
    (h2 : (Decide.build E maxClasses cut bad false fuel x0).stopped = false) :
    Decide.verdict E (Decide.build E maxClasses cut bad true fuel x0) (.safety bad) =
      Decide.verdict E (Decide.build E maxClasses cut bad false fuel x0) (.safety bad) := by
  rcases ver012_build_cmp E maxClasses cut bad fuel x0 with he | ⟨hs1, ⟨pre, y, hcls, hpre, hy⟩, u, hu⟩
  · rw [he]
  · rw [ver012_verdict_at E hs1 (u := []) (by simp [hcls]) hpre hy,
      ver012_verdict_at E h2 (u := u) (by rw [← hu, hcls]) hpre hy]

end EarlyStop


/-! ## VER-012 (F): the build -/

requirement VER_012_build
  id "VER-012"
  title "Name-Aware State Class Graph: the build"
  kind F
  scope "every verifier that offers the Route B name-partition graph (MAY); the build loop of the graph"
  source verbatim "spec/07-verification.md"
  quote "Every class the Route B build stores *shall* be reachable in the graph from the initial class, whether the build closed, was truncated, was stopped or stopped early."
        "*If* the Route B build closes, *then* it *shall* have expanded every class it stored."
        "*While* the graph's successor step gives any two classes with the same key the same transition labels and successor keys, up to order, *if* the Route B build closes, *then* it *shall* have stored a class with the key of every class the graph reaches from the initial class."
        "*If* the Route B build stops early at a violating class of a reachability-safety property, *then* its verdict for that property *shall* be the verdict of the same build without the early stop, unless that build is stopped by the total budget or a cancellation."
        "*If* the Route B build stops early, *then* it *shall not* report the graph as closed."
  reading "Let B be the build loop. For every explorer E (classes S, keys K, labels L), class bound, total-budget oracle cut, predicate bad, fuel and initial class x0, with or without the early stop:"
          "every class B stores is reachable in E from x0 (Explorer.Reach: a path of successors, each under a counter fresh for its source);"
          "if B closed, B expanded every stored class (exp = the number of classes);"
          "if E is key-equivariant (Explorer.Equivariant: two classes with the same key have, under any counters fresh for each, (label, key) successor lists that are permutations of each other) and B closed, B stores a class with the key of every class E reaches from x0;"
          "if the build without the early stop is not stopped, the verdict for the safety property bad (Decide.verdict, the shared predicate) of the build with the early stop is the verdict of the build without it;"
          "if B stopped early, B did not close."
  assumes "The model is the build loop RBBuild: from an explorer (Interning.lean's Explorer: the key, the support bound, the successor list under a mint counter), the class bound, the total budget or cancellation as an oracle cut, the early-stop predicate and switch, the Lean fuel and the initial class, the built graph (Decide.Out: the stored classes in discovery order, the number expanded, closed, stopped, stopped early). The witness refRBBuild is Decide.build (name_state_class_graph.rs build_until). The verdict read off a build is NU_050_prefix's (Decide.verdict, the shared predicate of VER-017); line 4 reads it as vocabulary."
          "Line 1 is 'every explored class is reachable' of AC5's note and of the implementation note on the early stop (Lean build_reach), for every build. A Violated therefore names a class the graph reaches (Decide.prefix_safety_sound, Decide.prefix_quiescence_sound). VER_012_build_forbids_staleCounter kills a build that mints with a counter that is not fresh: it stores a class the graph does not reach."
          "Lines 2 and 3 are AC3's completeness, reworded under ruling D59 (a) and VD-1 (a) to 'complete for the free-choice name semantics the graph explores': on a closed graph every stored class was expanded and every class the graph reaches has a stored twin, so a reachable class that violates a reachability-safety property gives Violated (ver012_build_complete_violated), and so does a reachable class that rests in the graph and violates a quiescence property (ver012_build_complete_quiescence). The free choice is VER_012 lines 2 and 4: the graph fires a join on every enabling name and a consumer on every resident name, up to renaming. Line 3's premise, the key-equivariance of the successor step, is in the quoted sentence: the build alone cannot give it. Route B's explorer Novel.RouteB.routeB is key-equivariant (Novel.RouteB.routeB_equivariant), and for every graph step meeting VER_012 the name successors' keys depend only on the key fired from (ver012_succs_keys); the base step and the NU-052 prune read only what the class key keeps. Soundness against the executor is NU_050_soundB (ver012_sound_executor). VER_012_build_forbids_truncAsClosed kills a build that reports a truncated graph as closed; VER_012_build_forbids_forgetClosed kills a closed build that loses a reachable class."
          "Line 4 is AC5: verdict and route identical to a build without the early stop, the witness ending at the same class. The verdict includes the violating class (Violated i), the class the witness ends at; the route is Route B either way. AC5 is reworded so that which of several equally short paths to that class the witness takes may differ: with the early stop the parent of the violating class is opened (Verifier.Graph.opened) and its edge list may break a tie between equal-length paths differently (W10-graph note 1). The test derivation's 'the early-stop witness ends at the class the witness from a build without it ends at' is line 4. 'Unless that build is stopped': a total budget or a cancellation that would cut the full build after the early stop found its class leaves the full build Unknown (NU_050_prefix line 1) while the early stop answers Violated; the line excludes that case. The early-stopped build is not stopped (ver012_build_cmp). BFS order (the lowest-index violating class, the shortest path) is Decide.build's FIFO queue; VER_012_build_forbids_dropBad kills an early stop that ends without storing the violating class. 'When the bound is hit first, criterion 3 applies unchanged' is the case where the two builds are equal (ver012_build_cmp, left disjunct)."
          "Line 5 is AC5's 'An early-stopped graph is not complete and MUST NOT be treated as closed', as the build's own flag: the state-space cache of VER-017 stores only a closed graph (Verifier.Graph.store), so an early-stopped graph never serves another property. VER_012_build_forbids_earlyClosed kills a build that flags it closed."
          "AC5's list of safety properties, its report note, 'the parent ... does not count as expanded', 'Quiescence properties do not stop early' and the PNID fixture are the decider's and the report's: the reference Route B decider builds with the early stop for a safety property and without it for a quiescence property (refRouteB, NU-050); the note text (its 'a shortest one to any violation' included) and the timing are report shape (kind Q). That the early stop is Route B only (the enumeration route of VER-017 and the timed check of VER-023 build in full) is VER-017's and VER-023's. AC1, AC2 and AC4 are VER_012's; AC3's truncation and timed sentences are NU_050_prefix's and VER_012's assumes."
  signoff "2026-11-13 550823c0327b11ab ai"
  statement : RBBuild → Prop :=
    fun B => ∀ (S K L : Type) (E : Explorer S K L) (m : ℕ) (cut : ℕ → Bool) (bad : S → Bool)
      (fuel : ℕ) (x0 : S),
      (∀ stopAt, ∀ z ∈ (B S K L E m cut bad stopAt fuel x0).cls, Explorer.Reach E x0 z) ∧
      (∀ stopAt, (B S K L E m cut bad stopAt fuel x0).complete = true →
        (B S K L E m cut bad stopAt fuel x0).exp = (B S K L E m cut bad stopAt fuel x0).cls.length) ∧
      (∀ stopAt, E.Equivariant → (B S K L E m cut bad stopAt fuel x0).complete = true →
        ∀ y, Explorer.Reach E x0 y → ∃ z ∈ (B S K L E m cut bad stopAt fuel x0).cls, E.key z = E.key y) ∧
      ((B S K L E m cut bad false fuel x0).stopped = false →
        Decide.verdict E (B S K L E m cut bad true fuel x0) (.safety bad) =
          Decide.verdict E (B S K L E m cut bad false fuel x0) (.safety bad)) ∧
      (∀ stopAt, (B S K L E m cut bad stopAt fuel x0).early = true →
        (B S K L E m cut bad stopAt fuel x0).complete = false)

/- The pinned readable form of VER_012_build: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_012_build : RBBuild → Prop :=
fun B =>
  ∀ (S K L : Type) (E : Explorer S K L) (m : ℕ) (cut : ℕ → Bool) (bad : S → Bool) (fuel : ℕ) (x0 : S),
    (∀ (stopAt : Bool), ∀ z ∈ (B S K L E m cut bad stopAt fuel x0).cls, E.Reach x0 z) ∧
      (∀ (stopAt : Bool),
          (B S K L E m cut bad stopAt fuel x0).complete = true →
            (B S K L E m cut bad stopAt fuel x0).exp = (B S K L E m cut bad stopAt fuel x0).cls.length) ∧
        (∀ (stopAt : Bool),
            E.Equivariant →
              (B S K L E m cut bad stopAt fuel x0).complete = true →
                ∀ (y : S), E.Reach x0 y → ∃ z ∈ (B S K L E m cut bad stopAt fuel x0).cls, E.key z = E.key y) ∧
          ((B S K L E m cut bad false fuel x0).stopped = false →
              Decide.verdict E (B S K L E m cut bad true fuel x0) (Decide.Prop'.safety bad) =
                Decide.verdict E (B S K L E m cut bad false fuel x0) (Decide.Prop'.safety bad)) ∧
            ∀ (stopAt : Bool),
              (B S K L E m cut bad stopAt fuel x0).early = true → (B S K L E m cut bad stopAt fuel x0).complete = false
-/
#guard_msgs in #print VER_012_build

/-! ### The reference -/

/-- ✓ **The shipped build loop meets the build block.** Example: on the chain `0 → 1 → 2` with
class `2` bad, the build with the early stop stores `0, 1, 2`, stops at class `2` without
closing, and answers `Violated` there; the full build closes with all three classes expanded and
gives the same answer. Every class it stores is reachable from class `0`. -/
-- Every stored class is reachable (`build_reach`); a closed build expanded every class
-- (`build_spec`) and, under key-equivariance, has a stored twin of every reachable class
-- (`complete_twin`); the early stop answers what the full build answers
-- (`ver012_early_verdict`); a closed build was not stopped early (`Verifier.Graph.build_flags`).
@[evidence holds VER_012_build]
theorem VER_012_build_reference : VER_012_build refRBBuild := by
  intro S K L E m cut bad fuel x0
  refine ⟨fun stopAt z hz => Decide.build_reach E hz, fun stopAt hc => ?_, fun stopAt hE hc => ?_,
    fun h2 => ver012_early_verdict E m cut bad fuel x0 h2, fun stopAt he => ?_⟩
  · obtain ⟨-, -, -, hall⟩ := Decide.build_spec E m cut bad stopAt fuel x0
    exact hall hc
  · obtain ⟨-, hclosed, -, hall⟩ := Decide.build_spec E m cut bad stopAt fuel x0
    exact Decide.complete_twin hE (Decide.x0_mem_build _ _ _ _ _ x0) hclosed (hall hc)
  · change (Decide.build E m cut bad stopAt fuel x0).complete = false
    cases hc : (Decide.build E m cut bad stopAt fuel x0).complete
    · rfl
    · have := (Verifier.Graph.build_flags E hc).2
      change (Decide.build E m cut bad stopAt fuel x0).early = true at he
      rw [he] at this; cases this

/-! ### Consequences of the lines -/

/-- **A closed graph is complete for its own semantics: safety.** For a build that meets the lines,
on a key-equivariant explorer: if the build closed and was not stopped, and some class the graph
reaches violates a safety predicate that reads only the key, the verdict is `Violated`. -/
@[evidence cites "VER-012" "complete for the free-choice name semantics the graph explores"]
theorem ver012_build_complete_violated {B : RBBuild} (h : VER_012_build B) {S K L : Type}
    (E : Explorer S K L) (hE : E.Equivariant) {bad : S → Bool}
    (hbad : ∀ a b, E.key a = E.key b → bad a = bad b) {m : ℕ} {cut : ℕ → Bool}
    {stopBad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (B S K L E m cut stopBad stopAt fuel x0).complete = true)
    (hs : (B S K L E m cut stopBad stopAt fuel x0).stopped = false)
    {y : S} (hy : Explorer.Reach E x0 y) (hb : bad y = true) :
    ∃ i, Decide.verdict E (B S K L E m cut stopBad stopAt fuel x0) (.safety bad) = .violated i := by
  obtain ⟨z, hz, hk⟩ := (h S K L E m cut stopBad fuel x0).2.2.1 stopAt hE hc y hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hilt : i < (B S K L E m cut stopBad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (B S K L E m cut stopBad stopAt fuel x0).cls.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hi; cases hi
  simp only [Decide.verdict, hs, Bool.false_eq_true, if_false]
  cases hf : (List.range (B S K L E m cut stopBad stopAt fuel x0).cls.length).find?
      (Decide.violatesAt E (B S K L E m cut stopBad stopAt fuel x0) (.safety bad)) with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf i (List.mem_range.mpr hilt)
    simp only [Decide.violatesAt, hi, hbad z y hk, hb] at this
    exact absurd trivial this

/-- **A closed graph is complete for its own semantics: quiescence.** For a build that meets the
lines, on a key-equivariant explorer: if the build closed and was not stopped, and some class the
graph reaches rests (every firing out of it is of a reapable transition; with nothing reapable,
it has no successor) and violates a quiescence predicate that reads only the key, the verdict is
`Violated`. For example, a class where a join waits forever because its two inputs hold
different names rests, and a closed build reports it. -/
@[evidence cites "VER-012" "complete for the free-choice name semantics the graph explores"]
theorem ver012_build_complete_quiescence {B : RBBuild} (h : VER_012_build B) {S K L : Type}
    (E : Explorer S K L) (hE : E.Equivariant) {bad : S → Bool} {reap : L → Bool}
    (hbad : ∀ a b, E.key a = E.key b → bad a = bad b) {m : ℕ} {cut : ℕ → Bool}
    {stopBad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S}
    (hc : (B S K L E m cut stopBad stopAt fuel x0).complete = true)
    (hs : (B S K L E m cut stopBad stopAt fuel x0).stopped = false)
    {y : S} (hy : Explorer.Reach E x0 y) (hb : bad y = true) {c : ℕ} (hcy : E.bound y ≤ c)
    (hrest : ∀ ly ∈ E.succ c y, reap ly.1 = true) :
    ∃ i, Decide.verdict E (B S K L E m cut stopBad stopAt fuel x0) (.quiescence bad reap) =
      .violated i := by
  have hall := (h S K L E m cut stopBad fuel x0).2.1 stopAt hc
  obtain ⟨z, hz, hk⟩ := (h S K L E m cut stopBad fuel x0).2.2.1 stopAt hE hc y hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hilt : i < (B S K L E m cut stopBad stopAt fuel x0).cls.length := by
    rcases Nat.lt_or_ge i (B S K L E m cut stopBad stopAt fuel x0).cls.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hi; cases hi
  have hzr := Decide.rests_transfer hE reap hk.symm hcy (Nat.le_refl _) hrest
  have hv : Decide.violatesAt E (B S K L E m cut stopBad stopAt fuel x0) (.quiescence bad reap) i =
      true := by
    simp only [Decide.violatesAt, Decide.quiescentAt, hi, hbad z y hk, hb, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hall ▸ hilt, hzr⟩
  simp only [Decide.verdict, hs, Bool.false_eq_true, if_false]
  cases hf : (List.range (B S K L E m cut stopBad stopAt fuel x0).cls.length).find?
      (Decide.violatesAt E (B S K L E m cut stopBad stopAt fuel x0) (.quiescence bad reap)) with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf i (List.mem_range.mpr hilt)
    rw [hv] at this
    exact absurd rfl this

/-- **Every class the Route B graph reaches is stored by a closed build**, read through the class
key of the graph step: the build block's line 3 at the Route B explorer, whose key-equivariance
is `Novel.RouteB.routeB_equivariant`. -/
@[evidence cites "VER-012" "every class the graph reaches is stored and expanded"]
theorem ver012_routeB_closed_stores {β : Type} {co : List PlaceId} (base : BaseLayer β)
    (net : List Novel.RouteB.NuTrans) (role : Novel.RouteB.NuTrans → Role) (conflict : Bool)
    {m : ℕ} {cut : ℕ → Bool} {bad : NState co β → Bool} {stopAt : Bool} {fuel : ℕ}
    {x0 : NState co β}
    (hc : (refRBBuild _ _ _ (routeB base net role conflict) m cut bad stopAt fuel x0).complete =
      true) (y : NState co β) (hy : Explorer.Reach (routeB base net role conflict) x0 y) :
    ∃ z ∈ (refRBBuild _ _ _ (routeB base net role conflict) m cut bad stopAt fuel x0).cls,
      refNameGraph.ckey z = refNameGraph.ckey y :=
  (VER_012_build_reference _ _ _ (routeB base net role conflict) m cut bad fuel x0).2.2.1 stopAt
    routeB_equivariant hc y hy

/-- **Route B's `Proven` is sound for the executor** ([NU-050]): a `Proven` of the reference Route B
decider holds of every marking the untimed reference ν executor reaches (and, for a quiescence
property, rests at), while the actions keep their contracts. -/
@[evidence cites "VER-012" "sound for every executor run"]
theorem ver012_sound_executor : NU_050_soundB refRouteB := NU_050_soundB_reference

/-- **VER-012 and NU-050 hold together on one Route B.** One graph step, one build loop, one
verdict function and one decider meet VER-012's two blocks and NU-050's verdict and soundness
blocks, and they are one route: the Route B explorer keys its classes with the step's class key,
and the decider's verdict is the verdict function read off the build loop's graph, with the early
stop for a safety property and without it for a quiescence property. -/
@[evidence consistent VER_012 VER_012_build NU_050_prefix NU_050_soundB]
theorem VER_012_joint :
    ∃ (G : NameGraph) (B : RBBuild) (V : ClassVerdict) (D : RouteBDecider),
      VER_012 G ∧ VER_012_build B ∧ NU_050_prefix V ∧ NU_050_soundB D ∧
      (∀ {β : Type} {co : List PlaceId} (base : BaseLayer β) (net : List Novel.RouteB.NuTrans)
          (role : Novel.RouteB.NuTrans → Role) (conflict : Bool),
        (routeB (co := co) base net role conflict).key = fun S => G.ckey S) ∧
      (∀ q bad, D q (.safety bad) = V _ _ _ (routeBE q)
          (B _ _ _ (routeBE q) q.maxClasses q.cut (fun S => bad S.b) true q.fuel
            (initState q.co (Reference.qCount q.M0))) (.safety fun S => bad S.b)) ∧
      (∀ q bad, D q (.quiescence bad) = V _ _ _ (routeBE q)
          (B _ _ _ (routeBE q) q.maxClasses q.cut (fun S => bad S.b) false q.fuel
            (initState q.co (Reference.qCount q.M0)))
          (.quiescence (fun S => bad S.b) (reapNames q.X))) :=
  ⟨refNameGraph, refRBBuild, refClassVerdict, refRouteB, VER_012_reference, VER_012_build_reference,
    NU_050_prefix_reference, NU_050_soundB_reference, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

/-! ### Examples: a chain -/

/-- The chain `0 → 1 → 2` by `t`, as an explorer whose classes are numbers. -/
def ver012_chainE : Explorer ℕ ℕ String := Verifier.Graph.idExplorer Verifier.Graph.chainSucc

/-- The safety predicate "class `2` is bad". -/
def ver012_bad2 : ℕ → Bool := fun n => n == 2

/-- Class `2` is reachable on the chain: `0 → 1 → 2`. -/
theorem ver012_chain_reach2 : Explorer.Reach ver012_chainE 0 2 :=
  Explorer.Reach.step (s := 2) (c := 0) (l := "t")
    (Explorer.Reach.step (s := 1) (c := 0) (l := "t") Explorer.Reach.init (Nat.le_refl _) (by decide))
    (Nat.le_refl _) (by decide)

/-! ### Violation: a build that mints with a stale counter (line 1) -/

/-- An explorer whose classes are numbers, a class's support bound being the number itself; the
one successor of a class mints the counter, `c + 1`. -/
def ver012_mintE : Explorer ℕ ℕ String := ⟨id, id, fun c _ => [("mint", c + 1)]⟩

/-- From class `5` the mint explorer reaches only classes from `5` up. -/
theorem ver012_mint_reach {z : ℕ} (h : Explorer.Reach ver012_mintE 5 z) : 5 ≤ z := by
  induction h with
  | init => exact Nat.le_refl _
  | @step a c l s _ hb hmem ih =>
    simp only [ver012_mintE, List.mem_singleton, Prod.mk.injEq] at hmem
    change a ≤ c at hb
    omega

/-- A build that expands every class with the counter `0`, fresh or not. -/
noncomputable def ver012_staleCounter : RBBuild := fun _ _ _ E =>
  Decide.build { E with succ := fun _ x => E.succ 0 x }

/-- ✗ Minting with a stale counter violates VER-012 (line 1). From class `5`, whose names reach up
to `5`, the build mints name `1` again and stores class `1`, which no run of the graph reaches:
every fresh name is above the live ones. -/
@[evidence forbids VER_012_build]
theorem VER_012_build_forbids_staleCounter : ¬ VER_012_build ver012_staleCounter := by
  intro h
  have hmem : 1 ∈ (ver012_staleCounter ℕ ℕ String ver012_mintE 10 (fun _ => false)
      (fun _ => false) false 10 5).cls := by
    show 1 ∈ (Decide.build _ 10 (fun _ => false) (fun _ => false) false 10 5).cls
    rw [← Verifier.Graph.buildD_eq]
    decide
  have := ver012_mint_reach ((h ℕ ℕ String ver012_mintE 10 (fun _ => false) (fun _ => false) 10 5).1
    false 1 hmem)
  omega

/-! ### Violation: a truncated graph flagged closed (line 2) -/

/-- A build that flags every graph closed that was neither stopped nor stopped early, a truncated
one included. -/
noncomputable def ver012_truncAsClosed : RBBuild := fun _ _ _ E m cut bad stopAt fuel x0 =>
  let o := Decide.build E m cut bad stopAt fuel x0
  { o with complete := !o.stopped && !o.early }

/-- ✗ Flagging a truncated graph closed violates VER-012 (line 2). At a class bound of 2 the chain
`0 → 1 → 2` stores `0` and `1` and expands only `0`; flagged closed, it leaves class `1`
unexpanded. -/
@[evidence forbids VER_012_build]
theorem VER_012_build_forbids_truncAsClosed : ¬ VER_012_build ver012_truncAsClosed := by
  intro h
  have h2 := (h ℕ ℕ String ver012_chainE 2 (fun _ => false) (fun _ => false) 20 0).2.1 false
  simp only [ver012_truncAsClosed, ← Verifier.Graph.buildD_eq] at h2
  have := h2 (by decide)
  revert this
  decide

/-! ### Violation: a closed graph that loses a reachable class (line 3) -/

/-- A build that, once closed, forgets the last class it stored and counts one expansion less. -/
noncomputable def ver012_forgetClosed : RBBuild := fun _ _ _ E m cut bad stopAt fuel x0 =>
  let o := Decide.build E m cut bad stopAt fuel x0
  if o.complete then { o with cls := o.cls.dropLast, exp := o.exp - 1 } else o

/-- ✗ A closed graph that loses a reachable class violates VER-012 (line 3). The chain `0 → 1 → 2`
closes with all three classes expanded; this build reports `0` and `1` only, both expanded, and
class `2`, which the graph reaches, has no stored twin. -/
@[evidence forbids VER_012_build]
theorem VER_012_build_forbids_forgetClosed : ¬ VER_012_build ver012_forgetClosed := by
  intro h
  have h3 := (h ℕ ℕ String ver012_chainE 10 (fun _ => false) (fun _ => false) 20 0).2.2.1 false
    (Verifier.Graph.idExplorer_equivariant _)
  have hc : (ver012_forgetClosed ℕ ℕ String ver012_chainE 10 (fun _ => false) (fun _ => false)
      false 20 0).complete = true := by
    simp only [ver012_forgetClosed, ← Verifier.Graph.buildD_eq]
    decide
  have hcls : (ver012_forgetClosed ℕ ℕ String ver012_chainE 10 (fun _ => false) (fun _ => false)
      false 20 0).cls = [0, 1] := by
    simp only [ver012_forgetClosed, ← Verifier.Graph.buildD_eq]
    decide
  obtain ⟨z, hz, hk⟩ := h3 hc 2 ver012_chain_reach2
  rw [hcls] at hz
  change z = 2 at hk
  subst hk
  revert hz
  decide

/-! ### Violation: an early stop that drops its class (line 4) -/

/-- A build whose early stop ends without the violating class it found. -/
noncomputable def ver012_dropBad : RBBuild := fun _ _ _ E m cut bad stopAt fuel x0 =>
  let o := Decide.build E m cut bad stopAt fuel x0
  if o.early then { o with cls := o.cls.dropLast } else o

/-- ✗ Dropping the violating class at the early stop violates VER-012 (line 4). On the chain
`0 → 1 → 2` with class `2` bad, the full build closes and answers `Violated` at class `2`; this
early stop keeps `0` and `1` only and answers `Unknown`. -/
@[evidence forbids VER_012_build]
theorem VER_012_build_forbids_dropBad : ¬ VER_012_build ver012_dropBad := by
  intro h
  have h4 := (h ℕ ℕ String ver012_chainE 10 (fun _ => false) ver012_bad2 20 0).2.2.2.1
  simp only [ver012_dropBad, ← Verifier.Graph.buildD_eq] at h4
  have := h4 (by decide)
  revert this
  decide

/-! ### Violation: an early-stopped graph flagged closed (line 5) -/

/-- A build that flags an early-stopped graph closed. -/
noncomputable def ver012_earlyClosed : RBBuild := fun _ _ _ E m cut bad stopAt fuel x0 =>
  let o := Decide.build E m cut bad stopAt fuel x0
  { o with complete := o.complete || o.early }

/-- ✗ Flagging an early-stopped graph closed violates VER-012 (line 5). On the chain `0 → 1 → 2`
with class `2` bad, the early stop ends at class `2` before class `1`'s expansion is finished;
this build calls the graph closed, so a cache would serve it to another property. -/
@[evidence forbids VER_012_build]
theorem VER_012_build_forbids_earlyClosed : ¬ VER_012_build ver012_earlyClosed := by
  intro h
  have h5 := (h ℕ ℕ String ver012_chainE 10 (fun _ => false) ver012_bad2 20 0).2.2.2.2 true
  simp only [ver012_earlyClosed, ← Verifier.Graph.buildD_eq] at h5
  have := h5 (by decide)
  revert this
  decide

/-! ### The lines exercised -/

/-- The shipped build on the chain `0 → 1 → 2` with class `2` bad. With the early stop it stores
`0, 1, 2`, stops early at class `2`, is not closed, and answers `Violated` at class `2`; without
it the build closes with all three classes expanded and answers the same. -/
@[evidence nonvacuous VER_012_build]
theorem VER_012_build_nonvacuous :
    (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 true 20 0).cls = [0, 1, 2] ∧
      (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 true 20 0).early = true ∧
      (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 true 20 0).complete = false ∧
      Decide.verdict ver012_chainE
          (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 true 20 0)
          (.safety ver012_bad2) = .violated 2 ∧
      (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 false 20 0).complete = true ∧
      (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 false 20 0).exp = 3 ∧
      Decide.verdict ver012_chainE
          (refRBBuild _ _ _ ver012_chainE 10 (fun _ => false) ver012_bad2 false 20 0)
          (.safety ver012_bad2) = .violated 2 := by
  simp only [refRBBuild, ← Verifier.Graph.buildD_eq]
  decide

end Libpetri.Spec
