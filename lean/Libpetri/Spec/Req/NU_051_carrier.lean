import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Spec.Verifier.Result

set_option linter.missingDocs true

/-!
# NU-051: the carrier lines (`spec/12-nu-nets.md`, the carrier bullet)

Two blocks share the ID NU-051 with the blocks of `NU_051.lean`.

* `NU_051_colours` is a predicate over an abstract coloured-set function: from the fragment mode,
  the declared carrier places and the net, the coloured set the fragment classifier gives roles
  against. Under EXTENDED it is the set with no carrier declared plus the declared carriers, and
  nothing else; under BASE the declared carriers change nothing. It is checked against the set
  `classify` builds (`refColourSet`, step 1 of `name_fragment.rs::classify`) and against a set
  that ignores carriers in both modes, one that reads them in both modes and one that colours more
  than the carriers once a carrier is declared.
* `NU_051_carrier` is a predicate over an abstract verifier call that reads a ν configuration
  (the fragment mode and the declared carriers): a declared carrier that is not a place of the
  net is refused loudly, naming only missing carriers, in both modes and for every query (ruling
  D95 (a)). It is checked against the guard in front of any decider (`refCarrierVerify`, the
  Unknown form), the builder rejection of Java and TypeScript and the Rust and Python form that
  names every absent carrier, and against a wrong shape that checks only under EXTENDED inside
  Route B and loses the refusal when Route B defers to Route A (the behaviour RD-27 recorded).
* `Nu051CarrierCovers` is the offer of the bullet, a coverage clause and not a line: a
  declaration whose carriers the net has is accepted in either mode.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB

/-! ## The coloured set with carriers -/

/-- A coloured-set function, abstractly: from the fragment mode, the declared carrier places and
the net's transitions, the coloured set against which the fragment classifier gives roles (the
`col` argument of the glossary `Classifier`). -/
abbrev ColourSet := Mode → List PlaceId → List NuTrans → PlaceId → Bool

/-- The coloured set `classify` builds (`name_fragment.rs::classify` step 1, and step 1 of
`name_coloured_encoder.rs::build_plan`): every match key of a matched transition; under EXTENDED
also every declared carrier and every relay target of a matched transition. Registered as a
witness model. -/
def refColourSet : ColourSet := fun mode carriers net p =>
  net.any (fun T => (T.keys.getD []).contains p) ||
    (decide (mode = .extended) &&
      (carriers.contains p || net.any (fun T => T.keys.isSome && T.relays.contains p)))

#spec_witness refColourSet

requirement NU_051_colours
  id "NU-051"
  title "EXTENDED Coloured-Consumer Fragment"
  kind F
  scope "the coloured set every ν verifier computes for a call"
  source verbatim "spec/12-nu-nets.md"
  quote "*While* the fragment mode is EXTENDED, the fragment classifier *shall* give roles against the coloured set it uses with no carrier declared, with every declared carrier place added and no other place."
        "*While* the fragment mode is BASE, the fragment classifier *shall* give roles against the same coloured set whatever carrier places are declared."
  reading "For every list of declared carriers cs, net and place p:"
          "under EXTENDED, p is coloured with cs declared exactly when p is coloured with no carrier declared or p is in cs;"
          "under BASE, the coloured set with cs declared is the coloured set with no carrier declared."
  assumes "The coloured set is per call, as the glossary term Coloured place reads it ('The classifier computes the coloured set for each call'); the role each transition then gets from it is the block NU_051 (refClassify takes the coloured set as its argument). 'The analyzer unions the declared carriers into the coloured set before role assignment' is line 1 with that composition: line 1 says the EXTENDED set is the union of the set without carriers and the carriers, nothing more and nothing less, and the classifier reads that set. A set that colours a further place once a carrier is declared breaks line 1 (NU_051_colours_forbids_footprint). 'so the existing mint co-mints one fresh name into all of them' is shown, not stated: NU_051_colours_nonvacuous classifies a fork that writes a key and a declared carrier as a mint of both under EXTENDED, while under BASE the consumer of the carrier writes the key without consuming a coloured place, the shape of a second, independent mint."
          "Line 2 speaks of the classifier's coloured set only. The in-flight split of [VER-004] reads the declared carriers in both modes (it refuses to split a transition that writes one: in_flight.rs first_unsplittable, InFlight.firstUnsplittable in Java, firstUnsplittable in TypeScript, each called without the mode), which the edited sentence 'Under BASE, the fragment classifier ignores declared carriers (a documented no-op); the in-flight split of [VER-004] reads them in both modes.' says, and which VER-004 states ('a match key, a relay target or a declared carrier'). So no line says a whole verifier answers the same with and without carriers under BASE: the split can refuse where it would not without them."
          "The match keys and the relay targets in the set are the glossary's (Coloured place; [NU-020], [NU-054]), not lines here: the lines fix what the carriers add and take away, relative to the set with no carrier declared, and say nothing of that set itself. So a set that colours every place in both modes, or one that under EXTENDED colours the declared carriers alone and drops every match key, meets both lines; they break the glossary's coloured set (the match keys, and under EXTENDED the relay targets), which no block states as a line: the verifier pipeline model (Verifier/Pipeline.lean, the block VER_003) does not model how a ν verifier builds the coloured set. That set is Q-tested: Rust name_fragment.rs extended_colours_relay_targets_and_the_join_carries_them and a_relay_target_no_join_consumes_is_coloured_and_its_read_arc_rejects (under EXTENDED a relay target is coloured, also one no join consumes), name_coloured_encoder.rs extended_carrier_relay_admitted_only_under_extended and a_relay_target_no_join_consumes_is_coloured_and_produced_by_the_join (the same set in Route A's plan), and Java NuNameAlignmentTest nu055_ac5_theBugVariantClassifiesOnlyWithTheMatchlessGateLifted (under EXTENDED every declared carrier is coloured and an undeclared place is not). refColourSet reads a relay target only on a matched transition, as Rust does (relays come from the match spec). A declared carrier that is not a place of the net joins the set as a name no transition touches; what the verifier does about it is the block NU_051_carrier."
  signoff "2026-11-13 c7e191c148c2ba43 ai"
  statement : ColourSet → Prop :=
    fun C =>
      (∀ (cs : List PlaceId) (net : List NuTrans) (p : PlaceId),
        C .extended cs net p = (C .extended [] net p || cs.contains p)) ∧
      (∀ (cs : List PlaceId) (net : List NuTrans), C .base cs net = C .base [] net)

/- The pinned readable form of the coloured-set lines of NU-051. -/
/--
info: def Libpetri.Spec.NU_051_colours : ColourSet → Prop :=
fun C =>
  (∀ (cs : List PlaceId) (net : List NuTrans) (p : PlaceId),
      C Mode.extended cs net p = (C Mode.extended [] net p || cs.contains p)) ∧
    ∀ (cs : List PlaceId) (net : List NuTrans), C Mode.base cs net = C Mode.base [] net
-/
#guard_msgs in #print NU_051_colours

/-- The coloured set `classify` builds is, under EXTENDED, the set it builds with no carrier
declared plus the declared carriers, and under BASE it does not read the carriers. -/
@[evidence holds NU_051_colours]
theorem NU_051_colours_reference : NU_051_colours refColourSet := by
  refine ⟨fun cs net p => ?_, fun cs net => ?_⟩
  · simp only [refColourSet, List.contains_nil]
    cases net.any (fun T => (T.keys.getD []).contains p) <;>
      cases cs.contains p <;> cases net.any (fun T => T.keys.isSome && T.relays.contains p) <;>
      decide
  · funext p
    simp [refColourSet]

/-! ### The co-mint fixture

Places: `0` and `1` are the keys of the join `J`, `2` is the carrier, `3` the join's output and
`5` the budget. The fork `m` takes a budget token and writes `0` and `2`; the consumer `r` takes
`2` and writes `1`. -/

/-- The fork: consumes the budget `5`, writes the key `0` and the carrier `2`. -/
def nu051c_fork : NuTrans where
  base := { name := "m", inputs := [inOne 5], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[0, 2], []⟩]
  keys := none
  relays := []

/-- The relay: consumes the carrier `2`, writes the key `1`. -/
def nu051c_relay : NuTrans where
  base := { name := "r", inputs := [inOne 2], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[1], []⟩]
  keys := none
  relays := []

/-- The join, keyed on `0` and `1`, writing `3`. -/
def nu051c_join : NuTrans where
  base := { name := "J", inputs := [inOne 0, inOne 1], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[3], []⟩]
  keys := some [0, 1]
  relays := []

/-- The co-mint net. -/
def nu051c_net : List NuTrans := [nu051c_fork, nu051c_relay, nu051c_join]

/-- Worked example. A fork `m` writes the join key `0` and the place `2`; `r` moves the token
from `2` to the other join key `1`. With `2` declared a carrier under EXTENDED, `2` is coloured,
so `m` is one mint writing the same fresh name into `0` and `2`, and `r` relays that name from
`2` into `1`: the join sees one name on both keys. Under BASE the declaration changes nothing,
`2` is not coloured, and `r` writes the key `1` without consuming a coloured place, which is the
shape of a mint of its own (a second, independent name) and gets no role unless declared. -/
@[evidence nonvacuous NU_051_colours]
theorem NU_051_colours_nonvacuous :
    refColourSet .extended [2] nu051c_net 2 = true ∧
    refColourSet .extended [] nu051c_net 2 = false ∧
    refColourSet .base [2] nu051c_net 2 = false ∧
    refColourSet .base [2] nu051c_net 0 = true ∧
    refClassify (refColourSet .extended [2] nu051c_net) .extended true [] nu051c_fork =
      some .mint ∧
    refClassify (refColourSet .extended [2] nu051c_net) .extended false [] nu051c_relay =
      some (.consume 2) ∧
    refClassify (refColourSet .extended [2] nu051c_net) .extended false [] nu051c_join =
      some (.join [(0, 1), (1, 1)] []) ∧
    refClassify (refColourSet .base [2] nu051c_net) .base false [] nu051c_relay = none := by
  decide

/-- A coloured set that never reads the declared carriers: the match keys alone, in both
modes. -/
def nu051c_keysOnly : ColourSet := fun _ _ net => refColourSet .base [] net

/-- ✗ Worked example: a verifier that drops the carrier declarations under EXTENDED leaves the
declared carrier `2` uncoloured, so the fork and the relay of the co-mint fixture would each mint
their own name (line 1). -/
@[evidence forbids NU_051_colours]
theorem NU_051_colours_forbids_keysOnly : ¬ NU_051_colours nu051c_keysOnly := by
  intro h
  have := h.1 [2] nu051c_net 2
  revert this; decide

/-- A coloured set that reads the declared carriers in both modes. -/
def nu051c_carriersAlways : ColourSet := fun _ cs net => refColourSet .extended cs net

/-- ✗ Worked example: a verifier that colours a declared carrier under BASE changes the BASE
fragment, which is the shipped mint → matched-join fragment, by a declaration BASE ignores
(line 2): with `2` declared, `2` becomes coloured under BASE. -/
@[evidence forbids NU_051_colours]
theorem NU_051_colours_forbids_carriersAlways : ¬ NU_051_colours nu051c_carriersAlways := by
  intro h
  have := congrFun (h.2 [2] nu051c_net) 2
  revert this; decide

/-- A coloured set that, under EXTENDED, also colours the inputs of every transition that writes a
declared carrier, as if the carrier's producer took the name in as well. -/
def nu051c_footprint : ColourSet := fun mode cs net p =>
  refColourSet mode cs net p ||
    (decide (mode = .extended) &&
      net.any (fun T => T.rows.any (fun r => r.fixed.any cs.contains) &&
        T.base.inputs.any (fun i => i.place == p)))

/-- ✗ Worked example: on the co-mint net with the carrier `2` declared under EXTENDED, a set that
also colours what the fork consumes colours the budget `5`, which is neither a declared carrier
nor coloured without the declaration. The budget would then be read as a name-carrying place,
and the fork as a consumer of it rather than a mint (line 1: the carriers are added, nothing
else). -/
@[evidence forbids NU_051_colours]
theorem NU_051_colours_forbids_footprint : ¬ NU_051_colours nu051c_footprint := by
  intro h
  have := h.1 [2] nu051c_net 5
  revert this; decide

/-- Mutant reading that weakens line 1 to "holds every declared carrier": the EXTENDED set must
contain the carriers but may colour anything else as well; line 2 is kept. -/
def NU_051_colours_mutant_holdsOnly (C : ColourSet) : Prop :=
  (∀ (cs : List PlaceId) (net : List NuTrans) (p : PlaceId), p ∈ cs →
    C .extended cs net p = true) ∧
  (∀ (cs : List PlaceId) (net : List NuTrans), C .base cs net = C .base [] net)

/-- The footprint set kills the weakened reading: it holds every declared carrier and leaves BASE
alone (the mutant holds), but colours the budget `5` once the carrier `2` is declared. -/
@[evidence mutant NU_051_colours]
theorem NU_051_colours_mutant_holdsOnly_killed :
    NU_051_colours_mutant_holdsOnly nu051c_footprint ∧ ¬ NU_051_colours nu051c_footprint := by
  refine ⟨⟨fun cs net p hp => ?_, fun cs net => ?_⟩, NU_051_colours_forbids_footprint⟩
  · simp [nu051c_footprint, refColourSet, hp]
  · funext p
    simp [nu051c_footprint, refColourSet]

/-- Mutant reading that keeps only line 2: carriers change nothing under BASE, and nothing is
asked of EXTENDED. -/
def NU_051_colours_mutant_noExtended (C : ColourSet) : Prop :=
  ∀ (cs : List PlaceId) (net : List NuTrans), C .base cs net = C .base [] net

/-- Ignoring carriers in both modes kills the first mutant: BASE is untouched (the mutant holds),
but a declared carrier is uncoloured under EXTENDED. -/
@[evidence mutant NU_051_colours]
theorem NU_051_colours_mutant_noExtended_killed :
    NU_051_colours_mutant_noExtended nu051c_keysOnly ∧ ¬ NU_051_colours nu051c_keysOnly :=
  ⟨fun _ _ => rfl, NU_051_colours_forbids_keysOnly⟩

/-- Mutant reading that keeps only line 1: under EXTENDED the declared carriers are added to the
set, and nothing is asked of BASE. -/
def NU_051_colours_mutant_noBase (C : ColourSet) : Prop :=
  ∀ (cs : List PlaceId) (net : List NuTrans) (p : PlaceId),
    C .extended cs net p = (C .extended [] net p || cs.contains p)

/-- Reading the carriers in both modes kills the second mutant: EXTENDED is the shipped set (the
mutant holds), but BASE changes with the declaration. -/
@[evidence mutant NU_051_colours]
theorem NU_051_colours_mutant_noBase_killed :
    NU_051_colours_mutant_noBase nu051c_carriersAlways ∧ ¬ NU_051_colours nu051c_carriersAlways :=
  ⟨NU_051_colours_reference.1, NU_051_colours_forbids_carriersAlways⟩

/-! ## A declared carrier that is not in the net -/

/-- The ν configuration of a verifier call, as the carrier line reads it: the fragment mode and
the declared carrier places. -/
structure NuConfig where
  /-- The fragment mode. -/
  mode : Mode
  /-- The declared carrier places, by name. -/
  carriers : List PlaceId

/-- The net of a verifier call, as the carrier line reads it: its places and its transitions. -/
structure CarrierNet where
  /-- The places of the net. -/
  places : List PlaceId
  /-- The transitions of the net. -/
  trans : List NuTrans

/-- What a verifier call yields, as the carrier line reads it: the carrier declaration is
rejected where it is made, naming a place (Java's `IllegalArgumentException`, TypeScript's
`Error`); or the call answers a verdict ([VER-003]), with the places its reason names. -/
inductive CarrierAnswer where
  /-- The declaration was rejected where it was made, naming the place. -/
  | rejected (place : PlaceId)
  /-- The call answered the verdict; `named` are the places its reason names. -/
  | answered (v : Verifier.Verdict) (named : List PlaceId)
  deriving DecidableEq

/-- A verifier call, abstractly: from the ν configuration, the net and the query (of any type
`Q`: the property, the initial marking and the other options), what the call yields. -/
abbrev CarrierVerifier (Q : Type) := NuConfig → CarrierNet → Q → CarrierAnswer

/-- A verifier, abstractly: given its routes (what the routes answer for each call, a
`CarrierVerifier`), the verifier the caller calls. A verifier that does not look at its carrier
declarations before its routes is the identity. -/
abbrev CarrierPipeline (Q : Type) := CarrierVerifier Q → CarrierVerifier Q

/-- `p` is a declared carrier that is not a place of the net. -/
def AbsentCarrier (cfg : NuConfig) (net : CarrierNet) (p : PlaceId) : Prop :=
  p ∈ cfg.carriers ∧ p ∉ net.places

instance (cfg : NuConfig) (net : CarrierNet) (p : PlaceId) :
    Decidable (AbsentCarrier cfg net p) := by
  unfold AbsentCarrier; infer_instance

/-- A loud refusal of an absent carrier: the declaration is rejected naming an absent carrier,
or the verdict is `Unknown` with a reason that names at least one place, every place it names
being an absent carrier. -/
def LoudRefusal (cfg : NuConfig) (net : CarrierNet) : CarrierAnswer → Prop
  | .rejected p => AbsentCarrier cfg net p
  | .answered (.unknown _) named => named ≠ [] ∧ ∀ p ∈ named, AbsentCarrier cfg net p
  | .answered _ _ => False

/-- A refusal: the declaration is rejected, or the verdict is `Unknown`, whatever it names. -/
def CarrierRefusal : CarrierAnswer → Prop
  | .rejected _ => True
  | .answered (.unknown _) _ => True
  | .answered _ _ => False

/-- The escape of the carrier line: the verifier `P` on routes `D` refuses the call, and the
same call with no carrier declared gets that same answer, so the refusal does not depend on the
carrier declaration. -/
def CarrierEscape {Q : Type} (P : CarrierPipeline Q) (D : CarrierVerifier Q) (cfg : NuConfig)
    (net : CarrierNet) (q : Q) : Prop :=
  CarrierRefusal (P D cfg net q) ∧ P D { cfg with carriers := [] } net q = P D cfg net q

/-- The declared carriers that are not places of the net, in declaration order. -/
def absentCarriers (cfg : NuConfig) (net : CarrierNet) : List PlaceId :=
  cfg.carriers.filter fun p => !net.places.contains p

/-- The carrier guard in front of any routes `D`: if a declared carrier is not a place of the
net, answer `Unknown` naming the first such carrier (the reason text of
`nu_scg_verifier.rs::verify_name_scg`), in both modes and for every query; otherwise the routes'
answer. It is the check [NU-010] runs for a declared mint (`unknown_mint_reason`, before any
route), applied to carriers. Registered as a witness model. -/
def refCarrierVerify {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net with
  | p :: _ => .answered (.unknown s!"declared carrier place '{p}' not in the net") [p]
  | [] => D cfg net q

#spec_witness refCarrierVerify

/-- Membership in `absentCarriers` is `AbsentCarrier`. -/
theorem nu051c_absent_mem {cfg : NuConfig} {net : CarrierNet} {p : PlaceId} :
    p ∈ absentCarriers cfg net ↔ AbsentCarrier cfg net p := by
  simp [absentCarriers, AbsentCarrier]

/-- An absent carrier makes `absentCarriers` non-empty. -/
theorem nu051c_absent_ne_nil {cfg : NuConfig} {net : CarrierNet}
    (h : ∃ p, AbsentCarrier cfg net p) : ∃ p ps, absentCarriers cfg net = p :: ps := by
  obtain ⟨p, hp⟩ := h
  have hm := nu051c_absent_mem.mpr hp
  cases hl : absentCarriers cfg net with
  | nil => rw [hl] at hm; cases hm
  | cons a l => exact ⟨a, l, rfl⟩

/-- The head of `absentCarriers` is an absent carrier. -/
theorem nu051c_absent_head {cfg : NuConfig} {net : CarrierNet} {p : PlaceId} {ps : List PlaceId}
    (h : absentCarriers cfg net = p :: ps) : AbsentCarrier cfg net p :=
  nu051c_absent_mem.mp (by rw [h]; exact List.mem_cons_self ..)

requirement NU_051_carrier
  id "NU-051"
  title "EXTENDED Coloured-Consumer Fragment"
  kind F
  scope "every ν verifier entry point that takes carrier declarations"
  source verbatim "spec/12-nu-nets.md"
  quote "A refusal that does not depend on the carrier declaration, such as a stop before the call starts ([VER-013]), an unresolved property place ([VER-003]) or a declared mint that is not a transition of the net ([NU-010]), may come first, and that refusal is then the answer."
        "*If* a declared carrier place is not a place of the net, *then* the verifier *shall* either reject the declaration, naming such a place, or answer `Unknown` with a reason that names at least one such place and no other place, in both BASE and EXTENDED and whatever the query, unless the same request with no carrier place declared gets the same refusal."
  reading "For every query type Q, routes D, ν configuration cfg, net and query q: if some declared carrier of cfg is not a place of the net, the verifier built on D either rejects the declaration naming a declared carrier that is not a place of the net, or answers Unknown with a reason that names at least one place, every place it names being a declared carrier that is not a place of the net; or its answer is a refusal (a rejection or an Unknown, CarrierRefusal) and the same call with no carrier declared gets that same answer (CarrierEscape)."
  assumes "Ruling D95 (a) decides the mode question of clash nu-c#2: an absent carrier fails in every mode, not only when a query reaches Route B. AC4 had no mode and the body said carriers are ignored under BASE; the markdown now says 'in either fragment mode and whatever the query', and the BASE sentence speaks of the fragment classifier only (NU_051_colours, line 2). D95 (a) reads 'at configuration, in every mode'; only its 'in every mode' half is a line. The line also accepts `Unknown` from verify, which the markdown has always allowed ('reject at the builder, or surface `Unknown`'), so the 'at configuration' half is deliberately not enforced: where the refusal is made is configuration (kind N, below), and Rust's verify-time `Unknown` meets it."
          "Java (SmtVerifier.carrierPlaces) and TypeScript (SmtVerifier.carrierPlaces) reject the declaration where it is made, in both modes, naming the place (NU_051_carrier_builder). Rust and Python answer `Unknown` in both modes and for every query: SmtVerifier::verify judges the declaration on the caller's net before with_arrivals (unknown_declaration_reason in rust/libpetri-verification/src/smt_verifier.rs) and verify_net answers that refusal before any route, and verify_open_net refuses a configure_smt hook's absent carrier before either route (open_net/verify_open_net.rs); the reason names every absent carrier once, in code-point order (unknown_carrier_reason in name_fragment.rs; NU_051_carrier_allAbsent). Route B keeps its own check for direct callers (nu_scg_verifier.rs verify_name_scg). A wrong shape that checks only under EXTENDED and only inside Route B ignores an absent carrier under BASE, under EXTENDED on a call that does not reach Route B, and under EXTENDED on a bounded quiescence query that Route B defers to Route A, whose build_plan skips a carrier it cannot resolve; that is the behaviour RD-27 recorded, and NU_051_carrier_forbids_routeBOnly (BASE) and NU_051_carrier_forbids_routeADeferral (EXTENDED) forbid it."
          "Order of refusals: the line does not fix which refusal wins when the carrier refusal meets one that does not depend on the carrier declaration; it asks only that such a refusal be the answer the same call gets with no carrier declared (CarrierEscape). Rust's verify_net polls the stop on entry ('net preparation'), then refuses an unresolved property place ([VER-003]), and only then answers the declaration refusal, in which unknown_declaration_reason tries the mint reason of [NU-010] before the carrier reason; verify_open_net and Python's py_encode_smt_scripts also put the mint reason first, and SmtVerifier::encode_scripts panics for a name-alignment property ([NU-055]) before it reads the declarations. On such a call the answer names no absent carrier. Java and TypeScript throw where the declaration is made, so a carrier rejection comes before any verification runs, and a mint rejection comes first only when the mint was declared first. CarrierPipeline does not model the stop, the property or the mints; they are part of the query q and of the net. preCarrierVerify takes the refusals that do not read the carrier declaration as a parameter pre and answers them first, naming no place, then answers as the Rust form: it meets the line through the escape (NU_051_carrier_preRefusal), and the line without the escape rejects it (NU_051_carrier_escape_needed), which is why the markdown carries the clause. The order inside pre, and so which of several such refusals wins, is not modelled."
          "What the escape lets through: any refusal the same call with no carrier declared also gets, so a verifier whose routes answer Unknown to every call meets the line. What the line forbids is a Proven or a Violated while a declared carrier is absent, and a refusal that the carrier declaration changes but that does not name an absent carrier alone (NU_051_carrier_forbids_unnamed, NU_051_carrier_forbids_firstDeclared, NU_051_carrier_forbids_namesAll)."
          "A verifier is modelled as a function of its routes (CarrierPipeline): the line quantifies over the routes D, which is the reading of 'MUST NOT be silently ignored' and of 'whatever the query': no Proven and no Violated while a declared carrier is absent, whatever a route would answer. A verifier that hands the call to its routes unchanged answers what they answer (NU_051_carrier_forbids_ignore). A route that refuses by itself, as Rust's Route B does, is part of the verifier here, so the Route-B-only shape is the pipeline routeBOnlyCarrierVerify, with the queries that reach Route B and the ones deferred from it to Route A as its parameters."
          "The answer is abstract: the verdict ([VER-003]) and the places its reason names, or a rejection naming a place. Which form an entry point takes (an exception where the declaration is made, Unknown from verify, Python's keyword path through Rust) is configuration (kind N), as for the declared mints of [NU-010]. The reason text ('declared carrier place 'x' not in the net (NU-051)' in Rust, 'declared carrier place 'x' not in the net' in TypeScript, 'declared carrier place 'x' is not in the net' in Java) is kind Q, and so is the tie between that text and the places the answer says it names. 'naming the offending place' is read as: the reason names at least one absent carrier and no other place. Java and TypeScript throw at the first absent carrier, and Rust names every absent one; when several are absent, which of them are named is not fixed (one, as Java and TypeScript do, or several, as Rust does and as [NU-010] names every unknown mint). Naming a declared carrier that is a place of the net is wrong, alone (NU_051_carrier_forbids_firstDeclared) or beside an absent one (NU_051_carrier_forbids_namesAll)."
          "The first sentence of the bullet ('Under EXTENDED, an author MAY declare intermediate **carrier** places (`carrierPlaces` / `carrier_place(s)`) that carry a fresh name from the minting fork ([NU-010]) onward to a ν-join input.') is an offer, and the API names in it are kind N. Offers are coverage clauses, never block lines (the convention of GlossaryExec.lean): the clause is Nu051CarrierCovers, defined next to this block, which the added sentence 'In either fragment mode, a declaration whose carrier places are all places of the net is accepted.' states: when every declared carrier is a place of the net, the carrier guard hands the call to its routes unchanged. The reference and the builder form meet it (nu051c_ref_covers, nu051c_builder_covers); a guard that refuses a present carrier under BASE, or in every mode, meets the line and fails the clause (nu051c_covers_baseRefuses, nu051c_covers_refusesAll). The clause speaks of the guard, not of the whole verifier, since under BASE the in-flight split of [VER-004] still reads the carriers (NU_051_colours assumes). The MAY sentence says 'Under EXTENDED', but declaring under BASE is allowed too: the declaration is a no-op for the classifier there (NU_051_colours, line 2), the clause covers it, and the line checks it."
          "The reason the sentence gives ('a mistyped carrier would let two fork branches mint independent names and produce a confident, spurious deadlock verdict') is the co-mint fixture of NU_051_colours_nonvacuous, where the carrier is what makes the fork and the relay share one name."
          "The open-net entry points ([VER-022], [MOD-051]) take the carriers through the configure hook on the synthetic net: the line applies to that call with the synthetic net as its net. Script encoding ([VER-013]) refuses an absent carrier too: Rust panics with the reason (SmtVerifier::encode_scripts), Python raises ValueError (py_encode_smt_scripts in rust/libpetri-py/src/verification.rs), and Java and TypeScript reject at the declaration. Its answer is scripts or a failure, not a verdict, so it is not one of the pipelines here; a line over it would take NU_010_ac6's MintAnswer form (an open item). AC4 is this line: its builder rejection names the place, as its `Unknown` does, and its 'unless a refusal that does not depend on the declaration is the answer' is the escape."
  signoff "2026-11-13 7a1b1a4383e15a26 ai"
  statement : ∀ {Q : Type}, CarrierPipeline Q → Prop :=
    fun P => ∀ (D : CarrierVerifier _) (cfg : NuConfig) (net : CarrierNet) (q : _),
      (∃ p, AbsentCarrier cfg net p) →
        LoudRefusal cfg net (P D cfg net q) ∨ CarrierEscape P D cfg net q

/- The pinned readable form of the carrier line of NU-051. -/
/--
info: def Libpetri.Spec.NU_051_carrier : {Q : Type} → CarrierPipeline Q → Prop :=
fun {Q} P =>
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    (∃ p, AbsentCarrier cfg net p) → LoudRefusal cfg net (P D cfg net q) ∨ CarrierEscape P D cfg net q
-/
#guard_msgs in #print NU_051_carrier

/-- The carrier guard refuses loudly, without the escape: when a declared carrier is missing it
answers `Unknown` naming the first missing one, and only that one. -/
theorem nu051c_ref_loud {Q : Type} (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet)
    (q : Q) (h : ∃ p, AbsentCarrier cfg net p) : LoudRefusal cfg net (refCarrierVerify D cfg net q) := by
  obtain ⟨p, ps, hl⟩ := nu051c_absent_ne_nil h
  simp only [refCarrierVerify, hl, LoudRefusal]
  refine ⟨List.cons_ne_nil _ _, fun x hx => ?_⟩
  rw [List.mem_singleton] at hx
  subst hx
  exact nu051c_absent_head hl

/-- The carrier guard satisfies the carrier line in front of any routes: when a declared
carrier is missing it answers `Unknown` naming the first missing one, and only that one, whatever
the routes would say. -/
@[evidence holds NU_051_carrier]
theorem NU_051_carrier_reference {Q : Type} : NU_051_carrier (Q := Q) refCarrierVerify :=
  fun D cfg net q h => Or.inl (nu051c_ref_loud D cfg net q h)

/-- The Java and TypeScript form: the declaration is rejected where it is made, naming the first
missing carrier. -/
def builderCarrierVerify {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net with
  | p :: _ => .rejected p
  | [] => D cfg net q

/-- ✓ The builder rejection of Java and TypeScript meets the carrier line too: declaring a place
the net does not have throws, naming it, in either mode. -/
@[evidence allows NU_051_carrier]
theorem NU_051_carrier_builder {Q : Type} : NU_051_carrier (Q := Q) builderCarrierVerify := by
  intro D cfg net q h
  obtain ⟨p, ps, hl⟩ := nu051c_absent_ne_nil h
  left
  simp only [builderCarrierVerify, hl, LoudRefusal]
  exact nu051c_absent_head hl

/-- The Rust and Python form: `Unknown` naming every absent carrier, before any route, in both
modes (`unknown_carrier_reason`, which also drops repeats and sorts the names). -/
def allAbsentCarrierVerify {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net with
  | [] => D cfg net q
  | p :: ps => .answered (.unknown "declared carrier places not in the net (NU-051)") (p :: ps)

/-- The Rust form refuses loudly, without the escape. -/
theorem nu051c_allAbsent_loud {Q : Type} (D : CarrierVerifier Q) (cfg : NuConfig)
    (net : CarrierNet) (q : Q) (h : ∃ p, AbsentCarrier cfg net p) :
    LoudRefusal cfg net (allAbsentCarrierVerify D cfg net q) := by
  obtain ⟨p, ps, hl⟩ := nu051c_absent_ne_nil h
  simp only [allAbsentCarrierVerify, hl, LoudRefusal]
  refine ⟨List.cons_ne_nil _ _, fun x hx => nu051c_absent_mem.mp ?_⟩
  rw [hl]
  exact hx

/-- ✓ Naming every absent carrier meets the carrier line: the reason names at least one place,
and every place it names is an absent carrier. -/
@[evidence allows NU_051_carrier]
theorem NU_051_carrier_allAbsent {Q : Type} : NU_051_carrier (Q := Q) allAbsentCarrierVerify := by
  intro D cfg net q h
  exact Or.inl (nu051c_allAbsent_loud D cfg net q h)

/-- Rust's order (`verify_net`): a refusal that does not read the carrier declaration (`pre`:
the stop poll on entry, the unresolved property place, the unknown mint of [NU-010], as a
function of the net and the query) answers first, as `Unknown` naming no place; otherwise the
Rust form. -/
def preCarrierVerify {Q : Type} (pre : CarrierNet → Q → Option String) : CarrierPipeline Q :=
  fun D cfg net q =>
    match pre net q with
    | some why => .answered (.unknown why) []
    | none => allAbsentCarrierVerify D cfg net q

/-- ✓ Rust's order meets the carrier line: an earlier refusal that does not read the carrier
declaration is the answer the same call with no carrier declared gets (the escape), and
otherwise the Rust form names every absent carrier. -/
@[evidence allows NU_051_carrier]
theorem NU_051_carrier_preRefusal {Q : Type} (pre : CarrierNet → Q → Option String) :
    NU_051_carrier (Q := Q) (preCarrierVerify pre) := by
  intro D cfg net q h
  cases hp : pre net q with
  | some why =>
    right
    simp only [CarrierEscape, preCarrierVerify, hp, CarrierRefusal, and_self]
  | none =>
    left
    simp only [preCarrierVerify, hp]
    exact nu051c_allAbsent_loud D cfg net q h

/-- Routes that prove everything: a stand-in for a route that answers. -/
def nu051c_proves : CarrierVerifier Bool := fun _ _ _ => .answered (.proven "fixture") []

/-- The fixture net: places `0` to `3` and `5`, the co-mint transitions. -/
def nu051c_cnet : CarrierNet := { places := [0, 1, 2, 3, 5], trans := nu051c_net }

/-- The carrier line without its escape: an absent carrier must always be refused loudly. -/
def NU_051_carrier_strict {Q : Type} (P : CarrierPipeline Q) : Prop :=
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    (∃ p, AbsentCarrier cfg net p) → LoudRefusal cfg net (P D cfg net q)

/-- The escape is needed: a call cancelled before it starts gets the stop's reason, which names
no place, so the line without its escape rejects Rust's order. -/
theorem NU_051_carrier_escape_needed :
    ¬ NU_051_carrier_strict (Q := Bool)
      (preCarrierVerify fun _ _ => some "verification cancelled during net preparation") := by
  intro h
  have := h nu051c_proves ⟨.extended, [7]⟩ nu051c_cnet true ⟨7, by decide⟩
  simp [preCarrierVerify, LoudRefusal] at this

/-- Worked example. On the co-mint net, declaring the place `7`, which the net does not have,
gives `Unknown` naming `7`, under BASE and under EXTENDED alike, even though the routes behind the
guard would have answered `Proven`; declaring only the real carrier `2` lets the routes answer. -/
@[evidence nonvacuous NU_051_carrier]
theorem NU_051_carrier_nonvacuous :
    AbsentCarrier ⟨.base, [2, 7]⟩ nu051c_cnet 7 ∧
    (∃ why, refCarrierVerify nu051c_proves ⟨.base, [2, 7]⟩ nu051c_cnet true =
      .answered (.unknown why) [7]) ∧
    (∃ why, refCarrierVerify nu051c_proves ⟨.extended, [7]⟩ nu051c_cnet false =
      .answered (.unknown why) [7]) ∧
    refCarrierVerify nu051c_proves ⟨.extended, [2]⟩ nu051c_cnet true =
      .answered (.proven "fixture") [] :=
  ⟨by decide, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩

/-- A verifier that hands every call to its routes, carriers unchecked. -/
def nu051c_ignore : CarrierPipeline Bool := fun D => D

/-- ✗ Worked example: a verifier that ignores a carrier declaration it cannot resolve answers
`Proven` on the co-mint net with the mistyped carrier `7` when its routes do, a confident verdict
about a net in which the declaration did nothing. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_ignore : ¬ NU_051_carrier nu051c_ignore := by
  intro h
  rcases h nu051c_proves ⟨.extended, [7]⟩ nu051c_cnet true ⟨7, by decide⟩ with h | ⟨h, -⟩ <;>
    exact h

/-- A wrong shape (the Rust and Python behaviour RD-27 recorded): the guard runs only under
EXTENDED, only for a query that reaches Route B (`reachesB`), and its answer stands only when the
query is not then deferred to Route A (`deferred`: a bounded quiescence query, on which the
pipeline drops any Route B `Unknown`). Everywhere else the routes answer as if the carrier had not
been declared. -/
def routeBOnlyCarrierVerify {Q : Type} (reachesB deferred : Q → Bool) : CarrierPipeline Q :=
  fun D cfg net q =>
    if cfg.mode = .extended ∧ reachesB q = true ∧ deferred q = false then
      refCarrierVerify D cfg net q
    else D cfg net q

/-- ✗ Worked example (the behaviour RD-27 recorded): with the Route-B-only shape, the mistyped
carrier `7` under BASE is ignored
and the call answers `Proven`. The query `true` stands for one that reaches Route B and is not
deferred, so even that path does not help under BASE. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_routeBOnly :
    ¬ NU_051_carrier (routeBOnlyCarrierVerify id (fun _ => false)) := by
  intro h
  rcases h nu051c_proves ⟨.base, [7]⟩ nu051c_cnet true ⟨7, by decide⟩ with h | ⟨h, -⟩ <;>
    exact h

/-- ✗ Worked example (the behaviour RD-27 recorded): under EXTENDED the Route-B-only shape still
loses the refusal on a query
that reaches Route B and is then deferred to Route A. Here every query reaches Route B and the
query `true` is deferred: Route B's `Unknown` naming `7` is dropped, Route A skips the carrier it
cannot find, and the call answers `Proven`. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_routeADeferral :
    ¬ NU_051_carrier (routeBOnlyCarrierVerify (fun _ => true) id) := by
  intro h
  rcases h nu051c_proves ⟨.extended, [7]⟩ nu051c_cnet true ⟨7, by decide⟩ with h | ⟨h, -⟩ <;>
    exact h

/-- A guard that answers `Unknown` but names no place. -/
def nu051c_unnamed {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net with
  | _ :: _ => .answered (.unknown "a declared carrier place is not in the net") []
  | [] => D cfg net q

/-- ✗ Worked example: `Unknown` with a reason that does not say which declaration is wrong
leaves the author to guess; the line asks the reason to name the missing carrier `7`. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_unnamed : ¬ NU_051_carrier (Q := Bool) nu051c_unnamed := by
  intro h
  have := h nu051c_proves ⟨.extended, [7]⟩ nu051c_cnet true ⟨7, by decide⟩
  simp [nu051c_unnamed, absentCarriers, nu051c_cnet, nu051c_proves, LoudRefusal, CarrierEscape,
    CarrierRefusal] at this

/-- A guard that names the first declared carrier, present or not. -/
def nu051c_firstDeclared {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net, cfg.carriers with
  | _ :: _, c :: _ => .answered (.unknown "a declared carrier place is not in the net") [c]
  | _, _ => D cfg net q

/-- ✗ Worked example: with carriers `2` and `7` declared on the co-mint net, naming `2`, which
is a place of the net, points the author at the wrong declaration. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_firstDeclared :
    ¬ NU_051_carrier (Q := Bool) nu051c_firstDeclared := by
  intro h
  have := h nu051c_proves ⟨.extended, [2, 7]⟩ nu051c_cnet true ⟨7, by decide⟩
  revert this
  simp [nu051c_firstDeclared, absentCarriers, nu051c_cnet, nu051c_proves, LoudRefusal,
    AbsentCarrier, CarrierEscape, CarrierRefusal]

/-- A guard that, when some declared carrier is missing, names every declared carrier. -/
def nu051c_namesAll {Q : Type} : CarrierPipeline Q := fun D cfg net q =>
  match absentCarriers cfg net with
  | _ :: _ => .answered (.unknown "declared carrier places not all in the net") cfg.carriers
  | [] => D cfg net q

/-- ✗ Worked example: with carriers `2` and `7` declared on the co-mint net, a reason that lists
both, "declared carrier places 2, 7 not all in the net", does name the missing `7`, but it also
names `2`, which is a place of the net, and leaves the author to find which of the two is wrong. -/
@[evidence forbids NU_051_carrier]
theorem NU_051_carrier_forbids_namesAll : ¬ NU_051_carrier (Q := Bool) nu051c_namesAll := by
  intro h
  have := h nu051c_proves ⟨.extended, [2, 7]⟩ nu051c_cnet true ⟨7, by decide⟩
  revert this
  simp [nu051c_namesAll, absentCarriers, nu051c_cnet, nu051c_proves, LoudRefusal, AbsentCarrier,
    CarrierEscape, CarrierRefusal]

/-- Mutant reading, option (b) of ruling D95: the carrier must fail only under EXTENDED and only
when the query reaches Route B (the escape kept). -/
def NU_051_carrier_mutant_routeB {Q : Type} (reachesB : Q → Bool) (P : CarrierPipeline Q) :
    Prop :=
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    cfg.mode = .extended → reachesB q = true →
      (∃ p, AbsentCarrier cfg net p) →
        LoudRefusal cfg net (P D cfg net q) ∨ CarrierEscape P D cfg net q

/-- The Route-B-only shape without the deferral kills the first mutant: it meets the Route B reading (the
guard runs there), but not the carrier line, which also asks for BASE and for every other
route. -/
@[evidence mutant NU_051_carrier]
theorem NU_051_carrier_mutant_routeB_killed :
    NU_051_carrier_mutant_routeB id (routeBOnlyCarrierVerify id (fun _ => false)) ∧
      ¬ NU_051_carrier (routeBOnlyCarrierVerify id (fun _ => false)) := by
  refine ⟨fun D cfg net q hm hb h => ?_, NU_051_carrier_forbids_routeBOnly⟩
  have href := nu051c_ref_loud D cfg net q h
  have hc : cfg.mode = .extended ∧ id q = true ∧ (fun _ => false) q = false := ⟨hm, hb, rfl⟩
  unfold routeBOnlyCarrierVerify
  rw [if_pos hc]
  exact Or.inl href

/-- Mutant reading: an absent carrier must give a rejection or `Unknown`, without naming it. -/
def NU_051_carrier_mutant_anyUnknown {Q : Type} (P : CarrierPipeline Q) : Prop :=
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    (∃ p, AbsentCarrier cfg net p) →
      (∃ p, P D cfg net q = .rejected p) ∨
        ∃ why named, P D cfg net q = .answered (.unknown why) named

/-- The unnamed guard kills the second mutant: it answers `Unknown` whenever a carrier is missing
(the mutant holds), but names nothing. -/
@[evidence mutant NU_051_carrier]
theorem NU_051_carrier_mutant_anyUnknown_killed :
    NU_051_carrier_mutant_anyUnknown (Q := Bool) nu051c_unnamed ∧
      ¬ NU_051_carrier (Q := Bool) nu051c_unnamed := by
  refine ⟨fun D cfg net q h => ?_, NU_051_carrier_forbids_unnamed⟩
  obtain ⟨p, ps, hl⟩ := nu051c_absent_ne_nil h
  exact Or.inr ⟨"a declared carrier place is not in the net", [], by simp [nu051c_unnamed, hl]⟩

/-- Mutant reading: `Unknown` must name some absent carrier, and may name any other place
beside it (the escape kept). -/
def NU_051_carrier_mutant_someNamed {Q : Type} (P : CarrierPipeline Q) : Prop :=
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    (∃ p, AbsentCarrier cfg net p) →
      (match P D cfg net q with
      | .rejected p => AbsentCarrier cfg net p
      | .answered (.unknown _) named => ∃ p ∈ named, AbsentCarrier cfg net p
      | .answered _ _ => False) ∨ CarrierEscape P D cfg net q

/-- The guard that names every declared carrier kills the third mutant: its reason always names
the missing carrier (the mutant holds), but also the declared carriers the net has. -/
@[evidence mutant NU_051_carrier]
theorem NU_051_carrier_mutant_someNamed_killed :
    NU_051_carrier_mutant_someNamed (Q := Bool) nu051c_namesAll ∧
      ¬ NU_051_carrier (Q := Bool) nu051c_namesAll := by
  refine ⟨fun D cfg net q h => ?_, NU_051_carrier_forbids_namesAll⟩
  obtain ⟨p, ps, hl⟩ := nu051c_absent_ne_nil h
  have hp := nu051c_absent_head hl
  left
  simp only [nu051c_namesAll, hl]
  exact ⟨p, hp.1, hp⟩

/-! ## The offer: a declaration of places the net has is accepted -/

/-- **The coverage clause of NU-051's carrier bullet** (the MAY sentence, and "In either fragment
mode, a declaration whose carrier places are all places of the net is accepted."): when every
declared carrier is a place of the net, the carrier guard hands the call to its routes unchanged,
in both modes. Offers are never a line of a block (glossary `GlossaryExec.lean`). -/
def Nu051CarrierCovers {Q : Type} (P : CarrierPipeline Q) : Prop :=
  ∀ (D : CarrierVerifier Q) (cfg : NuConfig) (net : CarrierNet) (q : Q),
    (∀ p ∈ cfg.carriers, p ∈ net.places) → P D cfg net q = D cfg net q

/-- With no declared carrier missing, `absentCarriers` is empty. -/
theorem nu051c_absent_nil {cfg : NuConfig} {net : CarrierNet}
    (h : ∀ p ∈ cfg.carriers, p ∈ net.places) : absentCarriers cfg net = [] := by
  simp only [absentCarriers, List.filter_eq_nil_iff, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, not_not]
  exact h

/-- Worked example of the offer: the carrier guard lets every call through whose declared
carriers the net has, whatever the mode and the query; on the co-mint net, declaring the real
carrier `2` under BASE or EXTENDED leaves the routes' answer as it is. -/
@[evidence cites "NU-051" "In either fragment mode, a declaration whose carrier places are all places of the net is accepted."]
theorem nu051c_ref_covers {Q : Type} : Nu051CarrierCovers (Q := Q) refCarrierVerify := by
  intro D cfg net q h
  simp only [refCarrierVerify, nu051c_absent_nil h]

/-- The builder form of Java and TypeScript makes the same offer: a declaration of places the net
has is accepted in either mode. -/
@[evidence cites "NU-051" "In either fragment mode, a declaration whose carrier places are all places of the net is accepted."]
theorem nu051c_builder_covers {Q : Type} : Nu051CarrierCovers (Q := Q) builderCarrierVerify := by
  intro D cfg net q h
  simp only [builderCarrierVerify, nu051c_absent_nil h]

/-- A guard that refuses missing carriers as the reference does, then also refuses any carrier
declared under BASE, as a builder would that reads carriers as "EXTENDED only". -/
def nu051c_baseRefuses {Q : Type} : CarrierPipeline Q := fun D =>
  refCarrierVerify (fun cfg net q =>
    match cfg.mode, cfg.carriers with
    | .base, c :: _ => .rejected c
    | _, _ => D cfg net q)

/-- A guard that refuses missing carriers as the reference does, then refuses every carrier
declaration in every mode. -/
def nu051c_refusesAll {Q : Type} : CarrierPipeline Q := fun D =>
  refCarrierVerify (fun cfg net q =>
    match cfg.carriers with
    | c :: _ => .answered (.unknown "carrier places are not supported") [c]
    | [] => D cfg net q)

/-- ✗ Worked example: a builder that throws on any carrier declared under BASE meets the carrier
line, since it refuses every missing carrier, but on the co-mint net it rejects the real carrier
`2` under BASE, where the declaration is a no-op and the routes would have answered `Proven`. It
fails the offer. -/
@[evidence cites "NU-051" "Under BASE, the fragment classifier ignores declared carriers (a documented no-op); the in-flight split of [VER-004] reads them in both modes."]
theorem nu051c_covers_baseRefuses :
    NU_051_carrier (Q := Bool) nu051c_baseRefuses ∧
      nu051c_baseRefuses nu051c_proves ⟨.base, [2]⟩ nu051c_cnet true = .rejected 2 ∧
      ¬ Nu051CarrierCovers (Q := Bool) nu051c_baseRefuses := by
  refine ⟨fun _ cfg net q h => NU_051_carrier_reference _ cfg net q h, rfl, fun hc => ?_⟩
  have := hc nu051c_proves ⟨.base, [2]⟩ nu051c_cnet true (by decide)
  revert this; decide

/-- ✗ Worked example: a verifier that answers `Unknown` for any carrier declaration meets the
carrier line, but on the co-mint net it refuses the real carrier `2` under EXTENDED, the mode in
which the markdown says an author may declare one. It fails the offer. -/
@[evidence cites "NU-051" "In either fragment mode, a declaration whose carrier places are all places of the net is accepted."]
theorem nu051c_covers_refusesAll :
    NU_051_carrier (Q := Bool) nu051c_refusesAll ∧
      (∃ why, nu051c_refusesAll nu051c_proves ⟨.extended, [2]⟩ nu051c_cnet true =
        .answered (.unknown why) [2]) ∧
      ¬ Nu051CarrierCovers (Q := Bool) nu051c_refusesAll := by
  refine ⟨fun _ cfg net q h => NU_051_carrier_reference _ cfg net q h, ⟨_, rfl⟩, fun hc => ?_⟩
  have := hc nu051c_proves ⟨.extended, [2]⟩ nu051c_cnet true (by decide)
  revert this; decide

end Libpetri.Spec
