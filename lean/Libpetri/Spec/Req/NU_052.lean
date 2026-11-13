import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Novel.RouteB.Exec
import Libpetri.Novel.RouteB.Retrodict

set_option linter.missingDocs true

/-!
# NU-052: Conflict-only priority for the Route B name-SCG (`spec/12-nu-nets.md`)

Under `CONFLICT` the Route B graph leaves a base-enabled transition `L` unexpanded from a class
when another transition `H` pre-empts it (glossary: Pre-empt); under `NONE` it expands every
base-enabled transition. The requirement is a predicate over a pair of models:

* `E : Expand β`, one expansion of a class of the Route B graph (the successor step of
  `build_until`), from the coloured set, the base layer, the net, the roles, the mode
  (`true`: `CONFLICT`) and the mint counter. The witness is `refExpand`, the shipped step
  `Novel.RouteB.succ`.
* `C : Compete`, the competition test on a class's count marking (`shares_consumed_input`). The
  witness is `refCompete`, `Novel.RouteB.sharesConsumed`, which is the `compete` of the untimed
  base layer `untimedBase` (`nu052_untimedBase_compete`).

The base layer is abstract, as in `Graph.lean`: whether `H` is ready no later than `L`
(`readyLe`), whether `H` has a firing in flight (`idle`) and whether `H` and `L` compete
(`compete`) are what the base layer reports. Their timed and split readings (the DBM lower bound
of each clock, the count of `inflight:<H>`) are later lines.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB

/-! ## The models -/

/-- One expansion of a class of the Route B graph: from the coloured set, the base layer, the
net, the roles the classifier gave, the mode (`true`: `CONFLICT`, `false`: `NONE`), the mint
counter and a class, the labelled successors of the class, each labelled with the name of the
transition that fired. -/
abbrev Expand (β : Type) :=
  (co : List PlaceId) → BaseLayer β → List NuTrans → (NuTrans → Role) → Bool → ℕ →
    NState co β → List (String × NState co β)

/-- The shipped expansion (`Novel.RouteB.succ`, the per-class loop of `build_until`),
registered as a witness model. -/
def refExpand {β : Type} : Expand β :=
  fun _ base net role conflict c S => succ base net role conflict c S

#spec_witness refExpand

/-- A competition test: from a class's count marking and two transitions `H` and `L`, whether
they compete for a consumed input. -/
abbrev Compete := AMarking → Transition → Transition → Bool

/-- The shipped competition test (`Novel.RouteB.sharesConsumed`, the Rust
`shares_consumed_input`), registered as a witness model. -/
def refCompete : Compete := sharesConsumed

#spec_witness refCompete

/-- The untimed base layer reads competition through `refCompete`. -/
theorem nu052_untimedBase_compete : untimedBase.compete = refCompete := rfl

/-- An input cardinality whose firing consumes a fixed number of tokens: `One` (one token) and
`Exactly(n)` (`n` tokens). For these the required count is the number of tokens one firing
consumes ([IO-007]); for `All` and `AtLeast` it is not. Line 2 reads the required count for
every cardinality (ruling D97 (a)); the wrong competition test `nu052_wholePair` reads this. -/
def fixedCard : Card → Bool
  | .one => true
  | .exactly _ => true
  | _ => false

instance nu052_decPreEmpts {co : List PlaceId} {β : Type} (base : BaseLayer β)
    (role : NuTrans → Role) (S : NState co β) (H L : NuTrans) :
    Decidable (PreEmpts base role S H L) := by
  unfold PreEmpts; infer_instance

/-! ## NU-052 -/

requirement NU_052
  id "NU-052"
  title "Conflict-Only Priority for the Route B Name-SCG"
  kind F
  scope "the Route B successor step, under CONFLICT and NONE"
  source verbatim "spec/12-nu-nets.md"
  quote "*While* the mode is `CONFLICT`, the Route B graph *shall* leave a base-enabled transition `L` unexpanded from a class exactly when another transition `H` of the net pre-empts `L` in that class, and *shall* expand every other base-enabled transition of the class as under `NONE`, in the same order."
        "*While* the mode is `CONFLICT`, the Route B graph *shall* take two transitions `H` and `L` to compete in a class exactly when some place is a consumed input of both and its token count in the class marking is less than the sum of their demands on it, where a transition's demand on a place is the sum of the required counts ([IO-007]) of its input arcs on that place."
        "*While* the mode is `NONE`, the Route B graph *shall* expand each base-enabled transition of a class, in the class's clock order (the code-point order of the transitions' names, [VER-010] AC1), with the successors the transition has when it is expanded alone from the same class and the same base layer, *shall* expand no other transition, and *shall not* read the readiness, in-flight state or competition of any transition."
        "*While* the mode is `NONE`, the Route B graph *shall* give a base-enabled transition at least one successor labelled with its name when the base layer can fire one of its branches in the class and the transition will fire on the name layer (always for an ordinary or minting transition, with an enabling name for a join, with a resident name for a consumer)."
  reading "Let E be the Route B expansion and C the competition test."
          "For every net whose transition names are distinct, every base layer whose competition is C read on the count marking κ of the class, and every class: the CONFLICT successors of the class are its NONE successors, in order, without those labelled with the name of a transition L of the net that some transition H of the net pre-empts in the class (glossary: Pre-empt, read as PreEmpts over the base layer's enabled, readyLe, idle and compete and the will-fire test of H's role)."
          "For every count marking a and transitions H and L: C a H L holds exactly when some input arc of H is on a place that is also the place of an input arc of L and holds fewer tokens in a than the sum of H's and L's demands on it, a transition's demand on a place being the sum of the required counts of its input arcs there (demandOn over Card.required: 1 for One and All, n for Exactly(n) and AtLeast(n))."
          "For every base layer, every class and every net whose transitions are listed in the code-point order of their names: the NONE successors of the class are, in that order, the NONE successors each base-enabled transition T has when the step is given T alone (the net [T]), from the same class and the same base layer."
          "For every two base layers that agree on enablement and firing: the NONE successors of every class are the same under both."
          "For every base layer, class and transition T that is base-enabled, has a branch the base layer fires in the class, and whose role will fire on the class's name layer (willFire): the NONE successors of the class in the net [T] include one labelled with T's name."
  assumes "The model is the pair (E, C). E is one expansion of a class of the name-aware state-class graph of Route B ([VER-012]): the coloured set, the base layer (Novel.RouteB.BaseLayer: enabled, fire, readyLe, compete and idle), the net with its roles, the mode (true for CONFLICT, false for NONE), the mint counter and the class give the labelled successors, each labelled with the name of the transition that fired. The witness is refExpand, the shipped step Novel.RouteB.succ (name_state_class_graph.rs build_until). C is the competition test on a class's count marking; the witness is refCompete, Novel.RouteB.sharesConsumed (shares_consumed_input). The step reads competition through the base layer (as in Graph.lean), so line 1 is stated for the base layers whose compete is C read on the class's count marking κ; that is what makes C the graph's competition and not a separate function. The untimed base is such a layer, with κ the identity (nu052_untimedBase_compete). The timed base, whose count marking is the marking of the timed class, is not in the model (gap R6, the open item of VER_012); a base layer whose compete is not of this form is a wrong base layer, not a wrong graph, and is not this requirement's subject: that the base layer of a Route B call reads competition by line 2 is the companion block NU_052_split, line 7, which a base layer reading a demand as the tokens one firing consumes breaks (NU_052_split_forbids_consumedBase). The pruning predicate itself is the glossary term Pre-empt; its shipped form is refPrune (GlossaryNuVer, refPrune_iff)."
          "The first quoted sentence is line 1. 'Exactly when' restates the body's 'is not expanded from a class when' together with the soundness paragraph's 'The pruning removes only interleavings in which a lower-priority transition fires ahead of a ready, conflicting, strictly-higher-priority one': under CONFLICT the graph prunes and does nothing else. 'Another transition' is read as another name: the line is stated for nets whose transition names are distinct, because the shipped step labels successors with names and compares H and L by name (name_state_class_graph.rs:587, `h.name() != l.name()`). Transitions are identified by name (ruling D10, with D23 settling that distinct names are one shared assumption for every name-keyed requirement), so the premise is that assumption and the quoted sentence needs no narrowing. Outside it, on a net where two transitions share a name, the Rust prune never lets one pre-empt the other, while the Java and TypeScript prunes compare by identity (NameStateClassGraph.java:402, name-state-class-graph.ts:336) and do; D10 puts that net out of scope, so the case is not encoded."
          "Line 1 reads every bullet of the body through the glossary term Pre-empt: strictly higher priority, competition (the base layer's compete, line 2 on count markings), ready no later than L (the base layer's readyLe), no firing in flight (the base layer's idle) and 'actually fires in this class' (willFire of H's role: a join needs an enabling name, a consumer a resident one, so a name-disabled join pre-empts nothing). H ranges over the base-enabled transitions of the class, as the body's 'another enabled transition H in the same class'. 'Actually fires in this class' is read on the name layer, as the body's own gloss ('a name-disabled join, whose inputs carry no shared name, produces no name-successor') and the shipped prune (dominated reads will_fire and no firing of the base) do; whether H has a branch the base layer can fire is not part of it. On the untimed base every enabled transition fires. On a timed base, H ready no later than L (readyLe) makes H firable whenever L is, and when L is not firable pruning it removes no successor; that this holds of the timed readyLe is the timed base's subject (gap R6)."
          "The second quoted sentence is line 2, for every cardinality. Ruling D97 (a) (clash nu-c#3) reads a demand as the required count of [IO-007], what all three runtimes compute (consumed_demand over required_count in name_state_class_graph.rs, consumedDemand in NameStateClassGraph.java and name-state-class-graph.ts) and the Lean model's demandOn: 1 for All and n for AtLeast(n), not the tokens one firing consumes. The body's bullet says so too. The tokens-consumed reading competes on more pairs (two All arcs on a place with two tokens), so it would prune more; the required count prunes a subset and stays sound (ClashesNu.clashNu_demand, cited). A test with the tokens-consumed reading breaks line 2 (NU_052_forbids_consumed), as does one that gives up on a pair over an All or AtLeast arc on a place only one of them consumes from (NU_052_forbids_wholePair). 'Read and inhibitor arcs do not count' is line 2's 'consumed input of both': only input arcs occur in it."
          "The body's 'becomes ready no later than L by the class-relative residual earliest: the DBM lower bound of each enabled clock captured before time is let to pass (readyEarliest, parallel to the enabled set)', the comparison within a float epsilon, and the sentence '*While* the mode is `CONFLICT`, the Route B graph *shall* take `H` to be ready no later than `L` in a class exactly when `readyEarliest[H] <= readyEarliest[L]` within a float epsilon, where `readyEarliest` is the DBM lower bound of each enabled clock before time is let to pass.' are a timing line over a timed base layer, as are the body's claims that a static H.earliest() <= L.earliest() does not suffice, that the rule subsumes the immediate-H case and that it also prunes sound non-zero-earliest conflicts. The base layer here is abstract (readyLe); its timed instance needs the timed class of RefScg (VER-010), so this sentence is not encoded here; the timed base layer is gap R6 (the open item of VER_012). On the untimed base every transition is ready at once (untimedBase.readyLe is true)."
          "The third quoted sentence is lines 3 and 4. It restates 'The default mode, NONE, MUST reproduce the prior Route B behaviour byte-for-byte' with the first paragraph's 'it expands every base-enabled transition': line 3 says no transition's NONE successors depend on another transition, that they come in the class's clock order and that a transition not base-enabled adds none, so NONE prunes nothing by priority; line 4 says NONE reads none of the base layer's readyLe, idle and compete, the inputs only the prune reads."
          "'In the class's clock order': the runtimes walk a class's enabled transitions in the class's canonical clock order, ascending transition name in code-point order ([VER-010] AC1; the Rust, Java and TypeScript name-state-class graphs walk the base class's enabled list, which the state-class graph permutes into canonical order when it builds a class). The model's step walks the net list it is given, so line 3 is stated for a net listed in that order (the Pairwise premise), and the model's list order is then the runtimes' order on every class. A net listed in another order is the same net handed to the step in another enumeration; line 1's 'in the same order' compares CONFLICT with NONE on one enumeration and needs no premise."
          "'Expanded alone from the same class and the same base layer' is the net [T] with the class and the base layer unchanged. The base layer is the class's own: the base successor of T is computed over the whole net (its clocks, enabled set and readyEarliest, state_class_graph.rs compute_successor_gated), and in the model that whole-net computation is inside base.fire, which line 3 does not vary, so [T] is not the net holding T alone. The minted symbols are compared up to the canonical key of the class ([VER-012] AC2): the runtimes thread one mint counter across the expansions of a class and across classes (name_state_class_graph.rs next_sym), while line 3 passes the same counter c to every transition, so the raw symbol numbers of the runtimes agree with the model only after interning."
          "The fourth quoted sentence is line 5. It is the least that 'expands' says of one transition: a transition that fires on both layers yields a successor labelled with its name, so an expansion that yields nothing is ruled out (NU_052_forbids_empty). The will-fire condition is the body's name-disabled join, which 'produces no name-successor', read the other way. Which successors one transition yields, all of them and byte for byte, is VER-012's subject, so 'the prior Route B behaviour' is not stated as a fixed function here."
          "Which mode the verifier hands the step is outside the step, and is the companion block NU_052_split (ruling D97 (a), clash nu-c#4): it says to which calls conflict priority applies (none on a net with a transition read as reapable, [VER-002]; a name-alignment call on a net without a ν-join included), and that every other call is verified as under NONE. The lines here hold for whatever mode the step is given."
          "The paragraph 'In-flight actions' (split every pruner and every transition depositing into an input or read place of a pruner, never let H pre-empt while inflight:<H> is marked, the NONE verdict naming the transition when one cannot be split, the pruning kept under assumeAtomicFiring) is the companion block NU_052_split, over the verifier's setup of a call and the in-flight test of the base layer; the split itself is VER_004_split. What this block keeps of it is the in-flight guard as the base layer's idle in line 1; NU_052_split line 6 says that idle is the count of inflight:<H> being 0. 'A direct call to Route B ... applies no split and prunes as before' is this block: the step prunes by line 1 whatever net it is given."
          "The paragraph 'Soundness' (the pruned firings are ones the eager, priority-ordered executor never performs; L is re-examined after H fires) relates the graph to the executor. It is descriptive (it carries no shall or MUST) and is not stated as a line: that needs a reference executor with a priority-ordered ν pass and actions in flight, and RefExec has neither priorities nor a ν kernel (a gap of the reference model; VER_004_exec, the executor link of the split, leaves priorities out too). A line would also have to list EXEC-003 AC4 (a ν-join that received a same-pass deposit fires no earlier than the next cycle). Ruling D8 (b) makes re-entrancy implementation-defined, so the Java and TypeScript wording of the in-flight case stays. Its evidence is cited, not stated: the retrodictions Libpetri.willFire_guard_is_necessary and Libpetri.inFlight_guard_is_necessary (Priority.lean) show, on the untimed fragment with a boolean name layer, that the prune without each guard drops a firing the executor performs and the shipped prune keeps it. Libpetri.postFixPrune_agrees_with_executor (Priority.lean) is true by construction and is no evidence for it."
          "The option names prioritySemantics / priority_semantics, that CONFLICT is opt-in and that an implementation MAY omit it are configuration, not encoded."
          "AC1 (NONE is the default and the only mode an implementation MUST provide; NONE leaves every existing Route B verdict unchanged) is lines 3, 4 and 5 for the step: NONE expands each base-enabled transition on its own, reads nothing the prune reads and gives every transition that fires a successor. The default and the verdicts are configuration and VER-012's graph; not encoded beyond that."
          "AC2 (the fork-threaded co-mint plus immediate ν-join plus delayed lower-priority drain fixture: Violated under NONE, Proven under CONFLICT on Route B called directly and under assumeAtomicFiring; through verify() with the split on, the NONE verdict and a report note) needs the timed base (a delayed drain) and the verdict, which are not encoded here; its pipeline half (the join cannot be split, so the call is verified as under NONE and the report names the join) is NU_052_split line 5 (NU_052_split_ac2). Its step-level core, that under CONFLICT the join's competitor is pruned when the join pre-empts it, is line 1 (NU_052_nonvacuous on the untimed base)."
          "AC3 (no over-pruning: a genuine orphan, whose join is name-disabled, still reaches its drain) is line 1's will-fire condition. The Route B retrodiction of commit c23cd9e (Novel.RouteB.WF: a priority-10 join whose keys hold two different names and a priority-0 drain competing for one token) is the evidence: the pre-fix prune without the will-fire guard stalls the class (NU_052_forbids_preFix), and the shipped step keeps the drain's edge (NU_052_orphan_not_pruned). The verdicts Violated without a drain and Proven with one are VER-012's graph and are not encoded here."
          "AC4 (only consumed-input conflicts prune; a read or inhibitor arc on the shared place creates no conflict) is line 2 (NU_052_forbids_reads, NU_052_nonvacuous)."
          "AC5 (a delayed(100) ν-join still pre-empts a delayed(200) lower-priority drain, so DEADLETTER is unreachable under CONFLICT and reachable under NONE) is the residual-earliest comparison over a timed base and a verdict, not encoded here (gap R6). Line 1 keeps the readiness condition (NU_052_forbids_noReady)."
          "AC6 (when the shared consumed place holds enough tokens for both transitions, CONFLICT does not prune the lower-priority one) is line 2 (NU_052_forbids_noCount) and, on the step, NU_052_nonvacuous (two tokens: both expanded)."
          "AC7 (a pruner in flight pre-empts nothing: H with an asynchronous action, L, the refill g, Unreachable(bad) Violated under CONFLICT with L in the trace) needs the verdict over the split net, which is not encoded here. Line 1 keeps the in-flight condition as the base layer's idle (NU_052_forbids_noIdle); NU_052_split line 6 reads idle on inflight:<H> and shows that a pruner in flight leaves L expanded (NU_052_split_nonvacuous); which transitions are split is VER_004_split_ac7; the count-level witness is Libpetri.inFlight_guard_is_necessary (Priority.lean)."
          "The test derivation (the ν-join versus timed dead-letter drain fixture, the genuine orphan, every verdict attributed to Route B) is AC2 and AC3: their verdicts are VER-012's graph and are not encoded here."
  signoff "2026-11-13 ce33b84a192a3bb8 ai"
  statement : ∀ {β : Type}, Expand β → Compete → Prop :=
    fun E C =>
      (∀ co (base : BaseLayer _) (κ : _ → AMarking) net role c (S : NState co _),
        (∀ b, base.compete b = C (κ b)) → (net.map fun T => T.base.name).Nodup →
        E co base net role true c S = (E co base net role false c S).filter fun x =>
          !decide (∃ L ∈ net, L.base.name = x.1 ∧ ∃ H ∈ net, PreEmpts base role S H L)) ∧
      (∀ (a : AMarking) (H L : Transition),
        C a H L = true ↔ ∃ sh ∈ H.inputs, (∃ sl ∈ L.inputs, sl.place = sh.place) ∧
          a sh.place < demandOn H sh.place + demandOn L sh.place) ∧
      (∀ co (base : BaseLayer _) net role c (S : NState co _),
        net.Pairwise (fun T U => T.base.name < U.base.name) →
        E co base net role false c S =
          (net.filter fun T => base.enabled S.b T.base).flatMap fun T => E co base [T] role false c S) ∧
      (∀ co (base base' : BaseLayer _) net role c (S : NState co _),
        base'.enabled = base.enabled → base'.fire = base.fire →
          E co base' net role false c S = E co base net role false c S) ∧
      (∀ co (base : BaseLayer _) (T : NuTrans) role c (S : NState co _) (d : Novel.RouteB.Row),
        base.enabled S.b T.base = true → d ∈ T.rows → (base.fire S.b T.base d).isSome = true →
        willFire co (role T) S.m S.bound = true →
          ∃ x ∈ E co base [T] role false c S, x.1 = T.base.name)

/- The pinned readable form of NU-052: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_052 : {β : Type} → Expand β → Compete → Prop :=
fun {β} E C =>
  (∀ (co : List PlaceId) (base : BaseLayer β) (κ : β → AMarking) (net : List NuTrans) (role : NuTrans → Role) (c : ℕ)
      (S : NState co β),
      (∀ (b : β), base.compete b = C (κ b)) →
        (List.map (fun T => T.base.name) net).Nodup →
          E co base net role true c S =
            List.filter (fun x => !decide (∃ L ∈ net, L.base.name = x.1 ∧ ∃ H ∈ net, PreEmpts base role S H L))
              (E co base net role false c S)) ∧
    (∀ (a : AMarking) (H L : Transition),
        C a H L = true ↔
          ∃ sh ∈ H.inputs,
            (∃ sl ∈ L.inputs, sl.place = sh.place) ∧ a sh.place < demandOn H sh.place + demandOn L sh.place) ∧
      (∀ (co : List PlaceId) (base : BaseLayer β) (net : List NuTrans) (role : NuTrans → Role) (c : ℕ)
          (S : NState co β),
          List.Pairwise (fun T U => T.base.name < U.base.name) net →
            E co base net role false c S =
              List.flatMap (fun T => E co base [T] role false c S)
                (List.filter (fun T => base.enabled S.b T.base) net)) ∧
        (∀ (co : List PlaceId) (base base' : BaseLayer β) (net : List NuTrans) (role : NuTrans → Role) (c : ℕ)
            (S : NState co β),
            base'.enabled = base.enabled →
              base'.fire = base.fire → E co base' net role false c S = E co base net role false c S) ∧
          ∀ (co : List PlaceId) (base : BaseLayer β) (T : NuTrans) (role : NuTrans → Role) (c : ℕ) (S : NState co β)
            (d : Novel.RouteB.Row),
            base.enabled S.b T.base = true →
              d ∈ T.rows →
                (base.fire S.b T.base d).isSome = true →
                  willFire co (role T) S.m S.bound = true → ∃ x ∈ E co base [T] role false c S, x.1 = T.base.name
-/
#guard_msgs in #print NU_052

/-! ### The reference -/

section Reference

variable {co : List PlaceId} {β : Type}

/-- The successors one transition `T` yields from a class, the body of the shipped step's loop
(`expand_transition`, `compute_successor`, `name_successors`). -/
def nu052_expandT (base : BaseLayer β) (role : NuTrans → Role) (c : ℕ) (S : NState co β)
    (T : NuTrans) : List (String × NState co β) :=
  T.rows.flatMap fun d =>
    match base.fire S.b T.base d with
    | none => []
    | some b' => (nameSuccs co (role T) S.m d.places S.bound c).attach.map fun M' =>
        (T.base.name, ⟨b', M'.1, max S.bound (c + 1), nameSuccs_supp S.supp M'.1 M'.2⟩)

/-- The shipped step, per transition: each base-enabled transition contributes its own
successors, or none when the prune applies. -/
theorem nu052_succ_eq (base : BaseLayer β) (net : List NuTrans) (role : NuTrans → Role)
    (cf : Bool) (c : ℕ) (S : NState co β) :
    succ base net role cf c S = (net.filter fun T => base.enabled S.b T.base).flatMap fun T =>
      if cf && dominated base net role S T then [] else nu052_expandT base role c S T := rfl

/-- Every successor `T` yields is labelled with `T`'s name. -/
theorem nu052_expandT_label {base : BaseLayer β} {role : NuTrans → Role} {c : ℕ}
    {S : NState co β} {T : NuTrans} {x : String × NState co β}
    (hx : x ∈ nu052_expandT base role c S T) : x.1 = T.base.name := by
  simp only [nu052_expandT, List.mem_flatMap] at hx
  obtain ⟨d, -, hx⟩ := hx
  split at hx
  · simp at hx
  · simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨_, rfl⟩ := hx
    rfl

/-- `distinct_signatures` keeps a nonempty list nonempty: the first symbol is always kept. -/
theorem nu052_dsig_ne_nil (M : NM co) {l : List ℕ} (h : l ≠ []) : dsig co M l ≠ [] := by
  unfold dsig
  split
  · exact h
  · cases l with
    | nil => exact absurd rfl h
    | cons s ss => simp [dsigAux]

/-- A role that will fire yields at least one name layer. -/
theorem nu052_nameSuccs_ne_nil (r : Role) (M : NM co) (d : Novel.ForwardDeposit.Deposit) (B c : ℕ)
    (h : willFire co r M B = true) : nameSuccs co r M d B c ≠ [] := by
  cases r with
  | ordinary => simp [nameSuccs]
  | mint => simp [nameSuccs]
  | join cin rel =>
    simp only [nameSuccs, ne_eq, List.map_eq_nil_iff]
    refine nu052_dsig_ne_nil M ?_
    simp only [willFire, List.any_eq_true] at h
    obtain ⟨s, hs, he⟩ := h
    exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hs, he⟩)
  | consume inp =>
    simp only [nameSuccs, ne_eq, List.map_eq_nil_iff]
    refine nu052_dsig_ne_nil M ?_
    simp only [willFire, List.any_eq_true] at h
    obtain ⟨s, hs, he⟩ := h
    exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hs, he⟩)

end Reference

/-- The reference satisfies NU-052. Line 1: under `CONFLICT` the shipped step drops the
successors of a transition `T` exactly when `dominated` holds, which is "some `H` pre-empts `T`"
(`refPrune_iff`); every successor of `T` is labelled with `T`'s name (`nu052_expandT_label`),
and with distinct names the only transition of the net with that name is `T`. Line 2 is
`sharesConsumed` unfolded, for every cardinality. Lines 3 and 4: under `NONE` the step is the per-transition expansion and reads neither
`readyLe` nor `idle` nor `compete`. -/
@[evidence holds NU_052]
theorem NU_052_reference {β : Type} : NU_052 (refExpand (β := β)) refCompete := by
  refine ⟨fun co base _ net role c S _ hnd => ?_, fun a H L => ?_,
    fun co base net role c S _ => ?_, fun co base base' net role c S h1 h2 => ?_,
    fun co base T role c S d hen hd hf hw => ?_⟩
  · simp only [refExpand]
    rw [nu052_succ_eq, nu052_succ_eq, List.filter_flatMap]
    refine List.flatMap_congr fun T hT => ?_
    have hTn : T ∈ net := (List.mem_filter.1 hT).1
    have key : (∃ L ∈ net, L.base.name = T.base.name ∧ ∃ H ∈ net, PreEmpts base role S H L) ↔
        dominated base net role S T = true := by
      rw [← show refPrune co base net role S T = dominated base net role S T from rfl,
        refPrune_iff]
      constructor
      · rintro ⟨L, hL, hn, h⟩
        rwa [List.inj_on_of_nodup_map hnd hL hTn hn] at h
      · exact fun h => ⟨T, hTn, rfl, h⟩
    simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false]
    by_cases hd : dominated base net role S T = true
    · rw [if_pos hd, eq_comm, List.filter_eq_nil_iff]
      intro x hx
      rw [nu052_expandT_label hx]
      simpa using key.2 hd
    · rw [if_neg hd, eq_comm, List.filter_eq_self]
      intro x hx
      rw [nu052_expandT_label hx]
      simpa using fun h => hd (key.1 h)
  · simp [refCompete, sharesConsumed, List.any_eq_true]
  · simp only [refExpand]
    rw [nu052_succ_eq]
    refine List.flatMap_congr fun T hT => ?_
    rw [nu052_succ_eq]
    simp [List.filter, (List.mem_filter.1 hT).2]
  · obtain ⟨en, fi, r, cp, id⟩ := base
    obtain ⟨en', fi', r', cp', id'⟩ := base'
    simp only at h1 h2
    subst h1 h2
    rfl
  · obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨M, hM⟩ := List.exists_mem_of_ne_nil _
      (nu052_nameSuccs_ne_nil (role T) S.m d.places S.bound c hw)
    refine ⟨(T.base.name, ⟨b', M, max S.bound (c + 1), nameSuccs_supp S.supp M hM⟩), ?_, rfl⟩
    simp only [refExpand]
    rw [nu052_succ_eq]
    simp only [List.filter_cons, hen, if_true, List.filter_nil, Bool.false_and,
      Bool.false_eq_true, if_false, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [nu052_expandT, List.mem_flatMap]
    refine ⟨d, hd, ?_⟩
    rw [hb']
    simp only [List.mem_map, List.mem_attach, true_and]
    exact ⟨⟨M, hM⟩, rfl⟩


/-! ### Fixtures -/

/-- A transition of the fixtures with name `n`, priority `pr`, input arcs `ins` and read arcs
`rs`, no inhibitor and no reset arc. -/
def nu052_tr (n : String) (pr : Int) (ins : List InSpec) (rs : List PlaceId := []) :
    Transition :=
  { name := n, inputs := ins, inhibitors := [], reads := rs, resets := [], priority := pr }

/-- The fixture transition `nu052_tr n pr ins rs` with one branch outcome, one token into
`out`, no match spec and no relay. -/
def nu052_nt (n : String) (pr : Int) (ins : List InSpec) (out : PlaceId)
    (rs : List PlaceId := []) : NuTrans :=
  { base := nu052_tr n pr ins rs, rows := [⟨[out], []⟩], keys := none, relays := [] }

/-- `hi : one(0) → 1` at priority 10. -/
def nu052_hi : NuTrans := nu052_nt "hi" 10 [inOne 0] 1

/-- `lo : one(0) → 2` at priority 0: it competes with `hi` for place `0`. -/
def nu052_lo : NuTrans := nu052_nt "lo" 0 [inOne 0] 2

/-- `rd : read(0) → 2` at priority 0: it reads place `0` and consumes nothing. -/
def nu052_rd : NuTrans := nu052_nt "rd" 0 [] 2 [0]

/-- The count marking with `k` tokens on place `0` and none elsewhere. -/
def nu052_a (k : ℕ) : AMarking := fun p => if p = 0 then k else 0

/-- Every transition ordinary. -/
def nu052_ord : NuTrans → Role := fun _ => .ordinary

/-- A base layer on `Unit`: every transition enabled and firing, competition read by
`refCompete` on the count marking with one token on `0`, with readiness `ready` and in-flight
test `idle` given. -/
def nu052_base (ready idle : Bool) : BaseLayer Unit where
  enabled _ _ := true
  fire _ _ _ := some ()
  readyLe _ _ _ := ready
  compete _ H L := refCompete (nu052_a 1) H L
  idle _ _ := idle

/-- The class of the `Unit` base over no coloured place. -/
def nu052_S : NState [] Unit := ⟨(), fun _ i => i.elim0, 0, fun _ _ i => i.elim0⟩

/-! ### Line 1: the readiness condition -/

/-- An expansion whose prune ignores readiness: `H` pre-empts `L` whatever their readiness (a
static priority test). -/
def nu052_noReady {β : Type} : Expand β :=
  fun _ base net role cf c S => succ { base with readyLe := fun _ _ _ => true } net role cf c S

/-- ✗ A prune without the readiness condition violates NU-052 (line 1; AC5): with `hi` not
ready before `lo` it still drops `lo`. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_noReady : ¬ NU_052 (nu052_noReady (β := Unit)) refCompete := by
  intro h
  have := congrArg (List.map Prod.fst) ((h.1 [] (nu052_base false true) (fun _ => nu052_a 1)
    [nu052_hi, nu052_lo] nu052_ord 0 nu052_S (fun _ => rfl) (by decide)))
  revert this
  decide

/-! ### Line 1: the in-flight condition -/

/-- An expansion whose prune ignores the in-flight guard: `H` pre-empts `L` while a firing of
`H` is in flight. -/
def nu052_noIdle {β : Type} : Expand β :=
  fun _ base net role cf c S => succ { base with idle := fun _ _ => true } net role cf c S

/-- ✗ A prune without the in-flight condition violates NU-052 (line 1; AC7): with `hi` in
flight it still drops `lo`. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_noIdle : ¬ NU_052 (nu052_noIdle (β := Unit)) refCompete := by
  intro h
  have := congrArg (List.map Prod.fst) ((h.1 [] (nu052_base true false) (fun _ => nu052_a 1)
    [nu052_hi, nu052_lo] nu052_ord 0 nu052_S (fun _ => rfl) (by decide)))
  revert this
  decide

/-! ### Line 1: the will-fire condition (the retrodiction of `c23cd9e`) -/

/-- The expansion before commit `c23cd9e`: under `CONFLICT`, the prune without the will-fire
and in-flight conditions (`Novel.RouteB.succPre`); under `NONE`, the shipped step. -/
def nu052_preFix {β : Type} : Expand β :=
  fun co base net role cf c S => if cf then succPre co base net role c S else succ base net role false c S

/-- The class of the retrodiction: name `0` in `A`, name `1` in `B`, so the priority-10 join
`J : A, B` is base-enabled but name-disabled, and the priority-0 drain `D : A` competes with it
for `A`'s one token. -/
noncomputable def nu052_wfS : NState WF.co AMarking := view WF.co id WF.m

/-- Under `CONFLICT` the shipped step keeps an edge from the retrodiction's class: the
name-disabled join does not pre-empt the drain (AC3, the genuine orphan). -/
@[evidence nonvacuous NU_052]
theorem NU_052_orphan_not_pruned :
    ∃ l S', (l, S') ∈ refExpand WF.co untimedBase WF.net WF.role true nu052_wfS.bound nu052_wfS :=
  WF.willFire_guard_is_necessary_routeB.2.2.imp fun _ h => h.imp fun _ h => h.1

/-- ✗ The pre-fix prune violates NU-052 (line 1; AC3): it removes the drain, so the class of the
retrodiction has no successor under `CONFLICT`, while line 1 asks for the `NONE` successors less
those of pre-empted transitions, which the shipped step shows to be nonempty. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_preFix : ¬ NU_052 (nu052_preFix (β := AMarking)) refCompete := by
  intro h
  have hnd : (WF.net.map fun T => T.base.name).Nodup := by decide
  have h1 := h.1 WF.co untimedBase id WF.net WF.role nu052_wfS.bound nu052_wfS (fun _ => rfl) hnd
  have href := (NU_052_reference (β := AMarking)).1 WF.co untimedBase id WF.net WF.role
    nu052_wfS.bound nu052_wfS (fun _ => rfl) hnd
  have hpre : succPre WF.co untimedBase WF.net WF.role nu052_wfS.bound nu052_wfS = [] :=
    List.isEmpty_iff.mp WF.pre_fix_stalls
  simp only [nu052_preFix, if_true, Bool.false_eq_true, if_false, hpre] at h1
  simp only [refExpand] at href
  rw [← h1] at href
  obtain ⟨l, S', hm⟩ := NU_052_orphan_not_pruned
  simp only [refExpand, href] at hm
  exact List.not_mem_nil hm

/-! ### Line 2: the multiplicity precondition and read arcs -/

/-- A competition test that ignores multiplicity: `H` and `L` compete whenever they share a
consumed input place. -/
def nu052_noCount : Compete := fun _ H L =>
  H.inputs.any fun sh => L.inputs.any fun sl => sl.place == sh.place

/-- ✗ A competition test that ignores multiplicity violates NU-052 (line 2; AC6): two `one()`
consumers of a place holding two tokens do not compete. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_noCount : ¬ NU_052 (refExpand (β := Unit)) nu052_noCount := by
  intro h
  have := h.2.1 (nu052_a 2) nu052_hi.base nu052_lo.base
  revert this
  decide

/-- A competition test that counts a read arc of `L` as a demand of one token on the place. -/
def nu052_reads : Compete := fun a H L =>
  H.inputs.any fun sh =>
    (L.inputs.any (fun sl => sl.place == sh.place) || L.reads.contains sh.place) &&
      decide (a sh.place < demandOn H sh.place + demandOn L sh.place + L.reads.count sh.place)

/-- ✗ A competition test that counts read arcs violates NU-052 (line 2; AC4): a consumer and a
reader of a place holding one token do not compete. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_reads : ¬ NU_052 (refExpand (β := Unit)) nu052_reads := by
  intro h
  have := h.2.1 (nu052_a 1) nu052_hi.base nu052_rd.base
  revert this
  decide

/-- A competition test that gives up on the whole pair as soon as any input arc of `H` or `L`
has cardinality `All` or `AtLeast`, even on a place the two do not share (a `consumed_demand`
whose `None` for one variable arc is propagated to the whole pair). -/
def nu052_wholePair : Compete := fun a H L =>
  if (H.inputs ++ L.inputs).all (fun s => fixedCard s.card) then refCompete a H L else false

/-- `hiAll : one(0), all(1)` at priority 10: it competes with `lo` for place `0` and drains
place `1`, which `lo` does not touch. -/
def nu052_hiAll : Transition :=
  nu052_tr "hi" 10 [inOne 0, { place := 1, card := .all, guard := none }]

/-- ✗ A competition test that drops the pair over a variable-cardinality arc on an unshared
place violates NU-052 (line 2). Worked example: the shared place `0` carries `One` arcs only and
holds one token, fewer than the two the pair demands, so `hiAll` and `lo` compete. The `All` arc
is on place `1`, which only `hiAll` consumes from, and changes nothing. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_wholePair : ¬ NU_052 (refExpand (β := Unit)) nu052_wholePair := by
  intro h
  have := h.2.1 (nu052_a 1) nu052_hiAll nu052_lo.base
  revert this
  decide

/-- A competition test that reads a demand as the tokens one firing consumes: an `All` or
`AtLeast` arc demands every token its place holds (the body's wording before ruling D97). -/
def nu052_consumed : Compete := fun a H L =>
  let dem (t : Transition) (p : PlaceId) : ℕ :=
    ((t.inputs.filter fun s => s.place == p).map fun s =>
      if s.card.consumesAll then a p else s.card.required).sum
  H.inputs.any fun sh =>
    L.inputs.any (fun sl => sl.place == sh.place) && decide (a sh.place < dem H sh.place + dem L sh.place)

/-- `hiDrain : all(0)` at priority 10: it drains place `0`. -/
def nu052_hiDrain : Transition := nu052_tr "hi" 10 [{ place := 0, card := .all, guard := none }]

/-- ✗ A demand read as the tokens consumed violates NU-052 (line 2, ruling D97 (a)). Worked
example: `hiDrain : all(0)` and `lo : one(0)` share place `0`, which holds two tokens. Their
required counts are 1 and 1, which two tokens cover, so they do not compete and `lo` is not
pruned. Read as tokens consumed, `hiDrain` would demand both tokens and the two would compete. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_consumed : ¬ NU_052 (refExpand (β := Unit)) nu052_consumed := by
  intro h
  have := h.2.1 (nu052_a 2) nu052_hiDrain nu052_lo.base
  revert this
  decide

/-! ### Line 3: `NONE` expands each transition on its own -/

/-- An expansion whose `NONE` applies a static priority: the prune with readiness, in-flight
state and competition all taken as true. -/
def nu052_staticNone {β : Type} : Expand β :=
  fun _ base net role cf c S =>
    succ (if cf then base else
      { base with readyLe := fun _ _ _ => true, compete := fun _ _ _ => true,
                  idle := fun _ _ => true }) net role true c S

/-- ✗ A `NONE` that prunes by static priority violates NU-052 (line 3; AC1): in the net
`hi, lo` it drops `lo`, which it expands in the net `lo` alone. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_staticNone : ¬ NU_052 (nu052_staticNone (β := Unit)) refCompete := by
  intro h
  have := congrArg (List.map Prod.fst) ((h.2.2.1 [] (nu052_base true true) [nu052_hi, nu052_lo]
    nu052_ord 0 nu052_S (by decide)))
  revert this
  decide

/-! ### Line 4: `NONE` reads no in-flight state -/

/-- An expansion whose `NONE` skips every transition with a firing in flight. -/
def nu052_idleNone {β : Type} : Expand β :=
  fun _ base net role cf c S =>
    succ base (if cf then net else net.filter fun T => base.idle S.b T.base) role cf c S

/-- ✗ A `NONE` that reads the in-flight state violates NU-052 (line 4; AC1): two base layers
that agree on enablement and firing, one reporting `hi` and `lo` in flight, give different
successors. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_idleNone : ¬ NU_052 (nu052_idleNone (β := Unit)) refCompete := by
  intro h
  have := congrArg (List.map Prod.fst) ((h.2.2.2.1 [] (nu052_base true false)
    (nu052_base true true) [nu052_hi, nu052_lo] nu052_ord 0 nu052_S rfl rfl))
  revert this
  decide

/-! ### Mutant: no in-flight condition -/

/-- Mutant reading of NU-052 whose line 1 reads Pre-empt without the in-flight condition (the
base layer's `idle` taken as true): the body's bullet "has no firing in flight" is dropped. Lines
2 to 5 are as in NU-052. -/
def NU_052_mutant_noIdle {β : Type} (E : Expand β) (C : Compete) : Prop :=
  (∀ co (base : BaseLayer _) (κ : _ → AMarking) net role c (S : NState co _),
    (∀ b, base.compete b = C (κ b)) → (net.map fun T => T.base.name).Nodup →
    E co base net role true c S = (E co base net role false c S).filter fun x =>
      !decide (∃ L ∈ net, L.base.name = x.1 ∧ ∃ H ∈ net,
        PreEmpts { base with idle := fun _ _ => true } role S H L)) ∧
  (∀ (a : AMarking) (H L : Transition),
    C a H L = true ↔ ∃ sh ∈ H.inputs, (∃ sl ∈ L.inputs, sl.place = sh.place) ∧
      a sh.place < demandOn H sh.place + demandOn L sh.place) ∧
  (∀ co (base : BaseLayer _) net role c (S : NState co _),
    net.Pairwise (fun T U => T.base.name < U.base.name) →
    E co base net role false c S =
      (net.filter fun T => base.enabled S.b T.base).flatMap fun T => E co base [T] role false c S) ∧
  (∀ co (base base' : BaseLayer _) net role c (S : NState co _),
    base'.enabled = base.enabled → base'.fire = base.fire →
      E co base' net role false c S = E co base net role false c S) ∧
  (∀ co (base : BaseLayer _) (T : NuTrans) role c (S : NState co _) (d : Novel.RouteB.Row),
    base.enabled S.b T.base = true → d ∈ T.rows → (base.fire S.b T.base d).isSome = true →
    willFire co (role T) S.m S.bound = true →
      ∃ x ∈ E co base [T] role false c S, x.1 = T.base.name)

/-- The prune without the in-flight guard kills the mutant: it is the shipped step over the base
layer whose `idle` is always true, so it meets the mutant reading (lines 1 to 5 of the reference,
over that base layer, which `NONE` cannot tell from the given one), but NU-052 keeps `lo` while
`hi` is in flight (`NU_052_forbids_noIdle`, AC7). -/
@[evidence mutant NU_052]
theorem NU_052_mutant_noIdle_killed :
    NU_052_mutant_noIdle (nu052_noIdle (β := Unit)) refCompete ∧
      ¬ NU_052 (nu052_noIdle (β := Unit)) refCompete := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := NU_052_reference (β := Unit)
  refine ⟨⟨fun co base κ net role c S hc hnd => ?_, r2,
      fun co base net role c S hs => ?_, fun co base base' net role c S h1 h2 => ?_,
      fun co base T role c S d hen hd hf hw => ?_⟩, NU_052_forbids_noIdle⟩
  · exact r1 co { base with idle := fun _ _ => true } κ net role c S hc hnd
  · exact r3 co { base with idle := fun _ _ => true } net role c S hs
  · exact r4 co { base with idle := fun _ _ => true } { base' with idle := fun _ _ => true }
      net role c S h1 h2
  · exact r5 co { base with idle := fun _ _ => true } T role c S d hen hd hf hw

/-! ### Line 5: a transition that fires yields a successor -/

/-- An expansion that yields no successor at all. It meets lines 1, 3 and 4. -/
def nu052_empty {β : Type} : Expand β := fun _ _ _ _ _ _ _ => []

/-- ✗ An expansion with no successors violates NU-052 (line 5; AC1): the ordinary `hi`, enabled
and with a branch the base layer fires, yields nothing. -/
@[evidence forbids NU_052]
theorem NU_052_forbids_empty : ¬ NU_052 (nu052_empty (β := Unit)) refCompete := by
  intro h
  obtain ⟨x, hx, -⟩ := h.2.2.2.2 [] (nu052_base true true) nu052_hi nu052_ord 0 nu052_S
    ⟨[1], []⟩ rfl (by decide) rfl rfl
  simp [nu052_empty] at hx

/-! ### Every line exercised -/

/-- Every line of NU-052 bites on the reference, on the untimed base with `hi : one(0)` at
priority 10 and `lo : one(0)` at priority 0, both ordinary: with one token on `0`, `CONFLICT`
expands `hi` only and `NONE` both (line 1, the step-level core of AC2); with two tokens
`CONFLICT` expands both (line 2, AC6); with `rd : read(0)` in place of `lo` and one token,
`CONFLICT` expands both (line 2, AC4); and the competition test answers accordingly. -/
@[evidence nonvacuous NU_052]
theorem NU_052_nonvacuous :
    (refExpand [] untimedBase [nu052_hi, nu052_lo] nu052_ord true 0
        (initState [] (nu052_a 1))).map Prod.fst = ["hi"] ∧
      (refExpand [] untimedBase [nu052_hi, nu052_lo] nu052_ord false 0
        (initState [] (nu052_a 1))).map Prod.fst = ["hi", "lo"] ∧
      (refExpand [] untimedBase [nu052_hi, nu052_lo] nu052_ord true 0
        (initState [] (nu052_a 2))).map Prod.fst = ["hi", "lo"] ∧
      (refExpand [] untimedBase [nu052_hi, nu052_rd] nu052_ord true 0
        (initState [] (nu052_a 1))).map Prod.fst = ["hi", "rd"] ∧
      refCompete (nu052_a 1) nu052_hi.base nu052_lo.base = true ∧
      refCompete (nu052_a 2) nu052_hi.base nu052_lo.base = false ∧
      refCompete (nu052_a 1) nu052_hi.base nu052_rd.base = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Libpetri.Spec
