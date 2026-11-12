import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeBuild

set_option linter.missingDocs true

/-!
# MOD-027: References to bound ports (`spec/11-modular-composition.md`)

MOD-027 is a behaviour requirement (kind B) over an abstract build script `S : ScriptFn N A`: a
list of builder calls (declare a place, add a transition, declare a terminal place, declare a
fusion set, compose an instance with port bindings or by auto-binding, compose a definition
directly), made on a new builder, gives the net `build()` returns or a rejection with a message.
Three more model parameters fix how a message prints a place (`Nm : Naming N`), the token type a
compose call checks ([MOD-022], `tyOf`) and the transition builder's check (`Build`).

A compose call *retires* a port when it binds the port to a caller place other than the port's
renamed place: the renamed place is then gone from the net, though `instance.port(...)` still hands
it out ([MOD-011]). The block says five things. A transition added to the builder that, after
fusion, names a retired place makes `build()` fail, and no transition of a built net names one
(line 1), whatever the order in which the transition and the compose call were added. A transition
that, after fusion, names exactly one retired place makes `build()` fail with the shared message
naming the first binding that retired it (line 2). A transition that, after fusion, names no
retired place does not make it fail (line 3), and neither does declaring a place (line 4). And a
retirement by itself rejects nothing: a compose call builds wherever the direct composition of the
same rewritten transitions, which retires nothing, builds and no transition names a place the call
retires (line 5).

The witness is the composition model's build script `buildScript` (`Reference/ComposeBuild.lean`);
the block holds of it for every naming, token-type check, transition-builder check and channel
merge (`mod027_ref`). The proofs run on a family of scripts that share every call and differ only
in what `build()` does after fusion (`mod027ScriptBy`: which fused transitions it keeps, its
retired check and one further check): the reference is one member, and the wrong members are the
mutants, one per line and one more for the second half of line 1, which a builder that drops an
offending transition instead of failing breaks.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## Vocabulary -/

/-- The instance and the port bindings of a composition call: an explicit `compose` with its
bindings, an auto-composition with every declared port bound to its own unrenamed body place
([MOD-024]); `none` for every other call. -/
def Op.portBinds : Op N A → Option (Instance N A × List (String × N))
  | .compose I ports _ => some (I, ports)
  | .composeAuto I _ => some (I, I.iface.map fun pt => (pt.name, pt.place))
  | _ => none

/-- **A call retires a port** ([MOD-027]): the call binds the port `r.port` of its instance (prefix
`r.pfx`) to the caller place `r.caller`, and the port's renamed place `r.place` differs from that
caller place, so the composition replaced it. -/
def RetiresPort (op : Op N A) (r : Retired N) : Prop :=
  ∃ I ports, op.portBinds = some (I, ports) ∧ (r.port, r.caller) ∈ ports ∧
    I.port r.port = some r.place ∧ r.place ≠ r.caller ∧ r.pfx = I.pfx

/-- Some call of `ops` retires the place `q`. -/
def PortRetiredBy (ops : List (Op N A)) (q : N) : Prop :=
  ∃ op ∈ ops, ∃ r, RetiresPort op r ∧ r.place = q

/-- `r` is a retirement made by the first call of `ops` that retires `r.place`. -/
def FirstRetirement (ops : List (Op N A)) (r : Retired N) : Prop :=
  ∃ l₁ op l₂, ops = l₁ ++ op :: l₂ ∧ RetiresPort op r ∧ ¬ PortRetiredBy l₁ r.place

/-- No call of `ops` binds one renamed place to two different caller places, through two ports
that expose it or through one port bound twice (ruling D35 (a): what a composition does then is
not defined). -/
def OneCallerPerPort (ops : List (Op N A)) : Prop :=
  ∀ op ∈ ops, ∀ I ports, op.portBinds = some (I, ports) → ∀ e ∈ ports, ∀ e' ∈ ports, ∀ q,
    I.port e.1 = some q → I.port e'.1 = some q → e.2 = e'.2

/-- The fusion sets the calls of `ops` declare, in order. -/
def fusionsOf (ops : List (Op N A)) : List (FusionSet N) :=
  ops.filterMap fun op => match op with
    | .fuse s => some s
    | _ => none

/-- A call that reads neither the builder's places nor its transitions: every call but an
auto-composition ([MOD-024], whose inference reads the places) and a direct composition
([MOD-025], which reads the transition names and the places). -/
def Op.Blind : Op N A → Prop
  | .composeAuto _ _ => False
  | .composeDirect _ => False
  | _ => True

/-- **The [MOD-027] message**: the retired place, its port, the instance prefix and the caller
place to use instead, names through the naming `Nm`. -/
def mod027Msg (Nm : Naming N) (r : Retired N) : String :=
  s!"place '{Nm.name r.place}' is port '{r.port}' of instance '{r.pfx}', bound to host place '{Nm.name r.caller}' at compose; reference '{Nm.name r.caller}' instead"

section Twin

variable [DecidableEq N]

/-- **The twin of a compose call**: a subnet definition, composed directly ([MOD-025]), whose
transitions are the instance's transitions rewritten through the port bindings ([MOD-020]), with
no place, terminal place, port or channel of its own. It adds to a builder what the compose call
without channel bindings adds, and retires nothing. -/
def mod027Twin (I : Instance N A) (ports : List (String × N)) : SubnetDef N A :=
  { name := I.pfx, places := [], defs := I.defs.map (rewriteDef (bindEntries I ports)),
    terminals := [], ports := [], chans := [] }

/-- **A compose call the composition accepts** ([MOD-020], [MOD-022]), but for the transition
builder's check: every port bound once, every bound port a port of the instance, every caller
place of its port's token type `tyOf`, the instance's transitions of distinct names, and no
instance transition with an input or an output collision under the bindings. -/
def mod027Accepts {T : Type} (tyOf : N → T) (I : Instance N A) (ports : List (String × N)) :
    Prop :=
  PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree tyOf I ports ∧
    (I.defs.map (·.core.name)).Nodup ∧
    ∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧ ¬ OutCollision (bindEntries I ports) d

end Twin

/-! ## MOD-027: References to Bound Ports -/

requirement MOD_027
  id "MOD-027"
  title "References to Bound Ports"
  kind B
  scope "every net builder that composes instances (Java, TypeScript, Rust; Python through Rust)"
  source verbatim "spec/11-modular-composition.md"
  quote "*If* no composition of the builder binds one renamed place to two different caller places and a transition of the builder after fusion, one added to the builder or one a composition added, names a retired place in an arc of any kind or in its output specification, *then* `build()` *shall* fail, whatever the order in which the transition and the composition that retired the place were added."
        "*If* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion consumes from or reads no terminal place and names exactly one retired place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition ([MOD-024], [MOD-025]), and no composition of the builder binds one renamed place to two different caller places, *then* `build()` *shall* fail with the message `place '<place>' is port '<port>' of instance '<instance>', bound to host place '<caller>' at compose; reference '<caller>' instead`, where `<place>` is that retired place and `<port>`, `<instance>` and `<caller>` are the port, the instance prefix and the caller place of a binding by which the first composition that retired the place retired it."
        "*When* a transition that fusion rewrites without an input-arc collision, that passes the transition builder's checks before and after fusion, and that after fusion names no retired place and consumes from or reads no terminal place, is added to a builder whose net builds and whose fusion sets share no place, before or after its other calls but after every auto-bound and direct composition, `build()` *shall* still succeed."
        "*When* one more place, a retired place included, is declared on a builder whose net builds, before or after its other calls but after every auto-bound and direct composition, `build()` *shall* still succeed."
        "*When* a `compose(instance, bindings)` call without channel bindings takes the place of a direct composition ([MOD-025]) of the instance's transitions rewritten through its bindings on a builder whose net builds, with no auto-bound or direct composition after it, and the call binds every port at most once, only ports the instance declares, each port to a caller place of its port's token type ([MOD-022]) and one renamed place to one caller place only, the instance's transitions have distinct names and no input or output collision under the bindings ([MOD-020]), and no transition of that net names a place the call retires, `build()` *shall* still succeed."
  reading "For every naming Nm, token-type map tyOf, transition-builder check Build and build script S (a list of builder calls, made on a new builder, gives the net build() returns or a rejection message), where a call retires a place q when it is an explicit compose call or MOD-024's auto-bound form and binds a port whose renamed place is q to a caller place other than q (RetiresPort; PortRetiredBy ops q: some call of ops retires q), a call is blind when it is neither an auto-composition nor a direct composition, a script has one caller per port when no call binds one renamed place to two different caller places, [add d] is the call that adds the transition definition d, d' is d after fusion (fuseDef under the substitution SubstSpec asks of the fusion sets the calls declare), the twin of compose I ports is the direct composition of I's transitions rewritten through the bindings (mod027Twin) and the composition accepts compose I ports when the MOD-020 and MOD-022 checks but the transition builder's pass (mod027Accepts tyOf):"
          "line 1: if ops has one caller per port and S ops builds the net c, no transition of c names a place some call of ops retired, in any arc or in its output specification, and no transition added by a call of ops names one after fusion, for any substitution fusion asks for;"
          "line 2: if pre ++ post has one caller per port, S (pre ++ post) builds c, every call of post is blind, the declared fusion sets are pairwise disjoint, d and d' pass Build, d' consumes from or reads no terminal place of c, d' names P, P is retired and every retired place d' names is P, then for some retirement r of P made by the first call of pre ++ post that retires P, S (pre ++ [add d] ++ post) fails with mod027Msg Nm r;"
          "line 3: if S (pre ++ post) builds c, every call of post is blind, the declared fusion sets are pairwise disjoint, d and d' pass Build, d' consumes from or reads no terminal place of c and d' names no retired place, then S (pre ++ [add d] ++ post) builds;"
          "line 4: if S (pre ++ post) builds and every call of post is blind, then S (pre ++ [declare q] ++ post) builds, for every place q;"
          "line 5: if every call of post is blind, compose I ports [] has one caller per port and the composition accepts it, S (pre ++ [twin] ++ post) builds c and no transition of c names a place compose I ports [] retires, then S (pre ++ [compose I ports []] ++ post) builds."
  assumes "Model scope. A build script is one implementation's net builder driven through its calls and then built, read as a function from the list of calls to the net or a rejection (ScriptFn, Reference/ComposeBuild.lean); a panic or exception at a call or at build() is a rejection. The runtimes record retired ports in compose and check them in build(): Rust PetriNetBuilder (rust/libpetri-core/src/petri_net.rs, recording at :1109-1130, build at :678-700, the check reject_bound_port_references at :711-731), Java PetriNet.Builder (java/src/main/java/org/libpetri/core/PetriNet.java, recording at :721-731, build at :1000-1006, checkRetiredPorts at :1016-1038, after fusion at :1186), TypeScript PetriNetBuilder (typescript/src/core/petri-net.ts, recording at :586-592, build at :732-739, rejectBoundPortReferences at :932-950, after fusion at :834). Python builds its Net through the Rust builder, so the Rust panic surfaces as StructureError, as the implementation notes say. tyOf is the token type MOD-022 checks at compose (a constant where no type is kept). The witness is the reference script buildScript; mod027_ref shows the block for every naming, token-type check, transition-builder check and channel merge (MOD-021). A script ends at its first rejected call. A caller that catches a failed compose and goes on with the same builder is out of scope: Rust consumes the builder (compose takes self by value, rust/libpetri-core/src/petri_net.rs:374) and Python makes it unusable (rust/libpetri-py/src/model.rs, PyPetriNetBuilder::take_builder), while Java (java/src/main/java/org/libpetri/core/PetriNet.java:729-734, :894-895) and TypeScript (typescript/src/core/petri-net.ts:591, :645-646) may keep the retired-port records and merged transitions of the failed call. So a retired place is one that a composition the script completed bound."
          "What is retired. RetiresPort is the paragraph 'The builder MUST remember every port place a composition retired this way' and the sentence after it: a binding of an explicit compose call, or of MOD-024's auto-bound form (every declared port bound to its own unrenamed body place, which always differs from the renamed place, pre_ne_self), whose caller place differs from the port's renamed place under the implementation's Place equality (CORE-002: the place type N, by name in Rust, TypeScript and Python, by name and token type in Java). A port bound to its own renamed place, a port that is not bound, a place that direct composition (MOD-025) merges by name, a body place that MOD-024's inference merges and a fusion member (MOD-061) are no retirements. What the builder remembers is not observable through a build script; the lines state what build() does with it, and the reference keeps exactly these records, the first one per place first (mod027Inv)."
          "Ruling D35 (a): what a composition does when it binds one renamed place to two different caller places is not defined. Rust keeps one of the two bindings in hash order and may then not retire the place (rust/libpetri-core/src/petri_net.rs:1050-1068, :1113-1124), so lines 1, 2 and 5 leave such scripts out (OneCallerPerPort); lines 3 and 4 hold without it. OneCallerPerPort also leaves out one port bound twice to two places, which the Map-based binding APIs cannot express and MOD-020 rejects. With two ports bound to one caller place, the message may name either port: Java the first in interface order (putIfAbsent over iface.ports(), java/src/main/java/org/libpetri/core/PetriNet.java:722-731), Rust and TypeScript the one their map from renamed place to port name keeps (rust/libpetri-core/src/petri_net.rs:1103-1107, typescript/src/core/petri-net.ts:578-579). So line 2 names some binding by which the first retiring call retired the place."
          "Line 1 and the built net. The second half of line 1 reads the calls: a transition added by a call of the script (Op.trans) is in every builder after it, since in the reference and in Rust a call only appends (step_prefix), so after fusion it is a transition of the net build() checks; a builder that dropped it, or rewrote its arc onto the caller place, and built would break line 1. The first half reads the built net, and covers the transitions a composition added. Ruling D42 (m): the caller-side definition of a channel binding is not already in the builder and has no arc on a port bound in the same call (MOD-021). Rust rewrites such a caller arc through the binding and builds, Java and TypeScript keep it and fail at build() (rust/libpetri-core/src/petri_net.rs:1188, java/src/main/java/org/libpetri/core/PetriNet.java:881-882, typescript/src/core/petri-net.ts:634); the caller-side definition is part of the compose call, not an added transition, so both meet line 1, and the difference is MOD-021's. A caller-side transition already added stays beside the merged one in Rust (transition() appends, rust/libpetri-core/src/petri_net.rs:319-338); Java and TypeScript replace it by the merge (java/src/main/java/org/libpetri/core/PetriNet.java:894-895, typescript/src/core/petri-net.ts:645-646), which is built from the caller side as given, with the union of the arcs and And(caller, instance) as output, so it names every place the replaced transition named, and the second half of line 1 holds in all three. Transition names are unique where a name keys something (rulings D10 and D23)."
          "What a transition names. namedPlaces holds the input, inhibitor, read and reset places and the places of every branch of the output specification, XOR branches included (outPlaces). The source of a forward output is not among them, but IO-014 requires every forward source to be an input place of the transition (WellFormedOut), so the input arc names it and the transition builder's check rejects a forward from a place with no input arc."
          "Messages (skeptic correction S3 of the composition design). Line 2 states the message of a sole offender only. Rust and Java run the EXEC-042 terminal check before the retired check (rust/libpetri-core/src/petri_net.rs:693-698, java/src/main/java/org/libpetri/core/PetriNet.java:1003-1004), TypeScript runs it after (typescript/src/core/petri-net.ts:735-739), and with several retired places named the runtimes report different ones (Rust sorts the output places, rust/libpetri-core/src/petri_net.rs:718-719). So line 2 asks that the rest of the net builds and that the transition after fusion consume from or read no terminal place and name exactly one retired place; which offender a failure names otherwise is not fixed. The message text is the same in the three runtimes (rust/libpetri-core/src/petri_net.rs:725-729, java/src/main/java/org/libpetri/core/PetriNet.java:1032-1036, typescript/src/core/petri-net.ts:937-942) and the markdown; names are printed through the naming Nm. 'When two compositions retire the same place, the first record is kept' is line 2's first retiring call: every runtime records a place once (rust/libpetri-core/src/petri_net.rs:1126-1129, Java putIfAbsent, TypeScript a has-check before set)."
          "Order and fusion. The check runs at build(), so line 1 holds for every script, whatever the order of the arc and the compose call, and lines 2 to 5 insert the transition, the place or the compose call at any position after which only blind calls follow, which covers 'before or after the compose(...) call'. An auto-composition reads the builder's places (MOD-024's inference is order-sensitive by design) and a direct composition reads its transition names and places (MOD-025), so a call inserted before one of them may change what that call does; those positions are outside lines 2 to 5. For an auto-bound composition the message of line 2 is therefore claimed only for a transition added after it, while the failure of line 1 holds in either order. A transition after fusion is d rewritten by fuseDef under the substitution of the declared sets (MOD-061 line 1); without a fusion set it is d itself (fuseDef_id). Lines 2 and 3 take the declared fusion sets pairwise disjoint and the inserted transition fused without an input-arc collision (fuseDef succeeds), as the sentences say; a builder whose net builds has disjoint sets in every runtime (Rust build() panics on an overlap, rust/libpetri-core/src/petri_net.rs:673). That the check sees the net after fusion is line 1 on the fused transitions and line 3 on a transition whose arc fusion moved off the retired place."
          "The rule rejects nothing else. Lines 3, 4 and 5 are frame lines, stated more generally than the markdown, whose matching sentences are 'A net that merely declares the retired place, without any arc naming it, is not rejected by this rule' and AC4 to AC7: no other build-time rejection of such a transition, place or compose call is allowed. This is an intended addition. It matches the runtimes: Rust build() rejects only a fusion overlap, a terminal clash and a retired reference (rust/libpetri-core/src/petri_net.rs:673-700). Line 5 says that a retirement by itself rejects nothing: the twin of a compose call adds the same transitions and places and retires nothing, so the two builders differ only in the records. Whether a net without retired places builds is the business of other blocks (CORE-040, EXEC-042, MOD-020, MOD-022, MOD-025, MOD-061); line 5 ties the net with the retirement to it. Its hypotheses are MOD-020's acceptance conditions without channel bindings, the transition builder's check on the rewritten transitions coming from the twin's direct composition, which runs it."
          "Per builder. 'A retired place is recorded per builder' and 'The record is not carried on the built net' hold by construction: a ComposedNet has no field for retired ports, and the script of a new builder that re-declares a built net (MOD-023) holds no compose call, so it retires nothing."
          "Acceptance criteria. AC1 is line 2 with the transition added last, and line 1; MOD_027_nonvacuous shows it (answer composed with in bound to A_IN, then hub_kill resetting answer/IN, fails with the message). AC2 is line 2 with the transition added before the compose call (a compose call is blind) and the second example. AC3 is lines 1 and 2, since namedPlaces holds every arc place and every place of the output specification; the examples show a read arc and an XOR branch on answer/IN failing with the message. AC4 is line 3 with the example in which hub_kill resets A_IN and the net builds (that the instance's transition now takes from A_IN is MOD-020's rewrite); the base script, answer composed with in bound to A_IN, builds by line 5 wherever its twin builds. AC5 and AC6 are line 3, since a port bound to its own renamed place and a port that is not bound are no retirements; the examples show both. AC7 is line 3 for its first half (after fusion the transition names the canonical member X, which is not retired; its base builds by line 5 as in AC4) and line 1 for its second half (after fusion the arc on the other member names the retired canonical member), with both outcomes on the reference. The test derivation is AC1, AC2 and AC4."
  signoff "pending"
  statement : ∀ {N A T : Type} [DecidableEq N], Naming N → (N → T) →
      (Trans N → Option String) → ScriptFn N A → Prop :=
    fun {N A _T} [DecidableEq N] Nm tyOf Build S =>
      (∀ ops c, OneCallerPerPort ops → S ops = .ok c → ∀ q, PortRetiredBy ops q →
        (∀ d ∈ c.trans, q ∉ d.namedPlaces) ∧
        ∀ (d : CDef N A) σ d', Op.trans d ∈ ops → SubstSpec (fusionsOf ops) σ →
          fuseDef σ d = .ok d' → q ∉ d'.namedPlaces) ∧
      (∀ pre post (d : CDef N A) c σ d' P, OneCallerPerPort (pre ++ post) →
        S (pre ++ post) = .ok c → (∀ op ∈ post, Op.Blind op) →
        FusionDisjoint (fusionsOf (pre ++ post)) → SubstSpec (fusionsOf (pre ++ post)) σ →
        Build d.toTrans = none → fuseDef σ d = .ok d' → Build d'.toTrans = none →
        (∀ p ∈ c.terminals, ¬ d'.ConsumesOrReads p) →
        P ∈ d'.namedPlaces → PortRetiredBy (pre ++ post) P →
        (∀ q ∈ d'.namedPlaces, PortRetiredBy (pre ++ post) q → q = P) →
        ∃ r, FirstRetirement (pre ++ post) r ∧ r.place = P ∧
          S (pre ++ .trans d :: post) = .error (mod027Msg Nm r)) ∧
      (∀ pre post (d : CDef N A) c σ d', S (pre ++ post) = .ok c → (∀ op ∈ post, Op.Blind op) →
        FusionDisjoint (fusionsOf (pre ++ post)) → SubstSpec (fusionsOf (pre ++ post)) σ →
        Build d.toTrans = none → fuseDef σ d = .ok d' → Build d'.toTrans = none →
        (∀ p ∈ c.terminals, ¬ d'.ConsumesOrReads p) →
        (∀ q ∈ d'.namedPlaces, ¬ PortRetiredBy (pre ++ post) q) →
        ∃ c', S (pre ++ .trans d :: post) = .ok c') ∧
      (∀ pre post q c, S (pre ++ post) = .ok c → (∀ op ∈ post, Op.Blind op) →
        ∃ c', S (pre ++ .place q :: post) = .ok c') ∧
      (∀ pre post (I : Instance N A) (ports : List (String × N)) c, (∀ op ∈ post, Op.Blind op) →
        OneCallerPerPort [Op.compose I ports []] → mod027Accepts tyOf I ports →
        S (pre ++ Op.composeDirect (mod027Twin I ports) :: post) = .ok c →
        (∀ q, PortRetiredBy [Op.compose I ports []] q → ∀ d ∈ c.trans, q ∉ d.namedPlaces) →
        ∃ c', S (pre ++ Op.compose I ports [] :: post) = .ok c')

/- The pinned readable form of MOD-027: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_027 : {N A T : Type} →
  [DecidableEq N] → Naming N → (N → T) → (Reference.Trans N → Option String) → ScriptFn N A → Prop :=
fun {N A _T} [DecidableEq N] Nm tyOf Build S =>
  (∀ (ops : List (Op N A)) (c : ComposedNet N A),
      OneCallerPerPort ops →
        S ops = Except.ok c →
          ∀ (q : N),
            PortRetiredBy ops q →
              (∀ d ∈ c.trans, q ∉ d.namedPlaces) ∧
                ∀ (d : CDef N A) (σ : N → N) (d' : CDef N A),
                  Op.trans d ∈ ops → SubstSpec (fusionsOf ops) σ → fuseDef σ d = Except.ok d' → q ∉ d'.namedPlaces) ∧
    (∀ (pre post : List (Op N A)) (d : CDef N A) (c : ComposedNet N A) (σ : N → N) (d' : CDef N A) (P : N),
        OneCallerPerPort (pre ++ post) →
          S (pre ++ post) = Except.ok c →
            (∀ op ∈ post, op.Blind) →
              FusionDisjoint (fusionsOf (pre ++ post)) →
                SubstSpec (fusionsOf (pre ++ post)) σ →
                  Build d.toTrans = none →
                    fuseDef σ d = Except.ok d' →
                      Build d'.toTrans = none →
                        (∀ p ∈ c.terminals, ¬d'.ConsumesOrReads p) →
                          P ∈ d'.namedPlaces →
                            PortRetiredBy (pre ++ post) P →
                              (∀ q ∈ d'.namedPlaces, PortRetiredBy (pre ++ post) q → q = P) →
                                ∃ r,
                                  FirstRetirement (pre ++ post) r ∧
                                    r.place = P ∧ S (pre ++ Op.trans d :: post) = Except.error (mod027Msg Nm r)) ∧
      (∀ (pre post : List (Op N A)) (d : CDef N A) (c : ComposedNet N A) (σ : N → N) (d' : CDef N A),
          S (pre ++ post) = Except.ok c →
            (∀ op ∈ post, op.Blind) →
              FusionDisjoint (fusionsOf (pre ++ post)) →
                SubstSpec (fusionsOf (pre ++ post)) σ →
                  Build d.toTrans = none →
                    fuseDef σ d = Except.ok d' →
                      Build d'.toTrans = none →
                        (∀ p ∈ c.terminals, ¬d'.ConsumesOrReads p) →
                          (∀ q ∈ d'.namedPlaces, ¬PortRetiredBy (pre ++ post) q) →
                            ∃ c', S (pre ++ Op.trans d :: post) = Except.ok c') ∧
        (∀ (pre post : List (Op N A)) (q : N) (c : ComposedNet N A),
            S (pre ++ post) = Except.ok c →
              (∀ op ∈ post, op.Blind) → ∃ c', S (pre ++ Op.place q :: post) = Except.ok c') ∧
          ∀ (pre post : List (Op N A)) (I : Instance N A) (ports : List (String × N)) (c : ComposedNet N A),
            (∀ op ∈ post, op.Blind) →
              OneCallerPerPort [Op.compose I ports []] →
                mod027Accepts tyOf I ports →
                  S (pre ++ Op.composeDirect (mod027Twin I ports) :: post) = Except.ok c →
                    (∀ (q : N), PortRetiredBy [Op.compose I ports []] q → ∀ d ∈ c.trans, q ∉ d.namedPlaces) →
                      ∃ c', S (pre ++ Op.compose I ports [] :: post) = Except.ok c'
-/
#guard_msgs in #print MOD_027

/-! ### The lines -/

section Lines

variable [DecidableEq N]

/-- Line 1: no transition of a built net names a place a call of the script retired, and no
transition a call added names one after fusion. -/
def mod027_line1 (S : ScriptFn N A) : Prop :=
  ∀ ops c, OneCallerPerPort ops → S ops = .ok c → ∀ q, PortRetiredBy ops q →
    (∀ d ∈ c.trans, q ∉ d.namedPlaces) ∧
    ∀ (d : CDef N A) σ d', Op.trans d ∈ ops → SubstSpec (fusionsOf ops) σ →
      fuseDef σ d = .ok d' → q ∉ d'.namedPlaces

/-- The first half of line 1: no transition of a built net names a retired place. -/
def mod027_line1_built (S : ScriptFn N A) : Prop :=
  ∀ ops c, OneCallerPerPort ops → S ops = .ok c →
    ∀ q, PortRetiredBy ops q → ∀ d ∈ c.trans, q ∉ d.namedPlaces

/-- The second half of line 1: when the net builds, no transition a call added names a retired
place after fusion. -/
def mod027_line1_call (S : ScriptFn N A) : Prop :=
  ∀ ops c, OneCallerPerPort ops → S ops = .ok c → ∀ q, PortRetiredBy ops q →
    ∀ (d : CDef N A) σ d', Op.trans d ∈ ops → SubstSpec (fusionsOf ops) σ →
      fuseDef σ d = .ok d' → q ∉ d'.namedPlaces

/-- Line 1 is its two halves. -/
theorem mod027_line1_iff (S : ScriptFn N A) :
    mod027_line1 S ↔ mod027_line1_built S ∧ mod027_line1_call S := by
  constructor
  · intro h
    exact ⟨fun ops c ho hc q hq => (h ops c ho hc q hq).1,
      fun ops c ho hc q hq => (h ops c ho hc q hq).2⟩
  · rintro ⟨h1, h2⟩ ops c ho hc q hq
    exact ⟨h1 ops c ho hc q hq, h2 ops c ho hc q hq⟩

/-- Line 2: a transition that, after fusion, names exactly one retired place fails `build()` with
the message on the first retirement of that place. -/
def mod027_line2 (Nm : Naming N) (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  ∀ pre post (d : CDef N A) c σ d' P, OneCallerPerPort (pre ++ post) → S (pre ++ post) = .ok c →
    (∀ op ∈ post, Op.Blind op) →
    FusionDisjoint (fusionsOf (pre ++ post)) → SubstSpec (fusionsOf (pre ++ post)) σ →
    Build d.toTrans = none → fuseDef σ d = .ok d' → Build d'.toTrans = none →
    (∀ p ∈ c.terminals, ¬ d'.ConsumesOrReads p) →
    P ∈ d'.namedPlaces → PortRetiredBy (pre ++ post) P →
    (∀ q ∈ d'.namedPlaces, PortRetiredBy (pre ++ post) q → q = P) →
    ∃ r, FirstRetirement (pre ++ post) r ∧ r.place = P ∧
      S (pre ++ .trans d :: post) = .error (mod027Msg Nm r)

/-- Line 3: a transition that, after fusion, names no retired place leaves the build
successful. -/
def mod027_line3 (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  ∀ pre post (d : CDef N A) c σ d', S (pre ++ post) = .ok c → (∀ op ∈ post, Op.Blind op) →
    FusionDisjoint (fusionsOf (pre ++ post)) → SubstSpec (fusionsOf (pre ++ post)) σ →
    Build d.toTrans = none → fuseDef σ d = .ok d' → Build d'.toTrans = none →
    (∀ p ∈ c.terminals, ¬ d'.ConsumesOrReads p) →
    (∀ q ∈ d'.namedPlaces, ¬ PortRetiredBy (pre ++ post) q) →
    ∃ c', S (pre ++ .trans d :: post) = .ok c'

/-- Line 4: declaring one more place leaves the build successful. -/
def mod027_line4 (S : ScriptFn N A) : Prop :=
  ∀ pre post (q : N) c, S (pre ++ post) = .ok c → (∀ op ∈ post, Op.Blind op) →
    ∃ c', S (pre ++ .place q :: post) = .ok c'

/-- Line 5: a compose call the composition accepts builds where its twin builds and no transition
names a place the call retires. -/
def mod027_line5 {T : Type} (tyOf : N → T) (S : ScriptFn N A) : Prop :=
  ∀ pre post (I : Instance N A) (ports : List (String × N)) c, (∀ op ∈ post, Op.Blind op) →
    OneCallerPerPort [Op.compose I ports []] → mod027Accepts tyOf I ports →
    S (pre ++ Op.composeDirect (mod027Twin I ports) :: post) = .ok c →
    (∀ q, PortRetiredBy [Op.compose I ports []] q → ∀ d ∈ c.trans, q ∉ d.namedPlaces) →
    ∃ c', S (pre ++ Op.compose I ports [] :: post) = .ok c'

end Lines

/-- MOD-027 is its five lines. -/
theorem mod027_iff [DecidableEq N] {T : Type} (Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) :
    MOD_027 Nm tyOf Build S ↔
      mod027_line1 S ∧ mod027_line2 Nm Build S ∧ mod027_line3 Build S ∧ mod027_line4 S ∧
        mod027_line5 tyOf S :=
  Iff.rfl

/-! ## A family of build scripts: the reference and its mutants -/

section Generic

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- The first retired record a definition names: its first named place that has a record, that
place's first record. The reference retired check is this, over the definitions in order. -/
def mod027HitDef (R : List (Retired N)) (d : CDef N A) : Option (Retired N) :=
  d.namedPlaces.findSome? fun p => R.find? fun r => decide (r.place = p)

omit [DecidableEq N] [ToString N] in
/-- The fused content with only the definitions `k R` keeps; the reference keeps every one. -/
def mod027Keep (k : List (Retired N) → CDef N A → Bool) (R : List (Retired N))
    (X : FuseNet N A) : FuseNet N A :=
  { X with defs := X.defs.filter (k R) }

omit [DecidableEq N] [ToString N] in
/-- Keeping every definition keeps the fused content. -/
theorem mod027Keep_all {k : List (Retired N) → CDef N A → Bool} {R : List (Retired N)}
    (hk : ∀ e, k R e = true) (X : FuseNet N A) : mod027Keep k R X = X := by
  cases X
  simp only [mod027Keep, FuseNet.mk.injEq, and_true, true_and]
  exact List.filter_eq_self.2 fun e _ => hk e

omit [DecidableEq N] [ToString N] in
/-- The reference keeps every definition. -/
theorem mod027Keep_true (R : List (Retired N)) (X : FuseNet N A) :
    mod027Keep (fun _ _ => true) R X = X :=
  mod027Keep_all (fun _ => rfl) X

/-- `build()` that keeps the fused definitions `k` keeps, then runs the reference net builder, a
per-definition retired check `g` and a further check `extra` last; the reference is
`g := mod027HitDef`, `k` keeping everything, `extra := none`. -/
def mod027FinishBy (Nm : Naming N) (Build : Trans N → Option String)
    (g : List (Retired N) → CDef N A → Option (Retired N)) (k : List (Retired N) → CDef N A → Bool)
    (extra : Bld N A → Option String) (b : Bld N A) : Except String (ComposedNet N A) :=
  match fuseStage Build b with
  | .error m => .error m
  | .ok X =>
    match refNetBuild (netOf (mod027Keep k b.retired X)) with
    | .error m => .error m
    | .ok net =>
      match (mod027Keep k b.retired X).defs.findSome? (g b.retired) with
      | some r => .error (retiredMsg Nm r)
      | none =>
        match extra b with
        | some m => .error m
        | none => .ok ⟨net, (mod027Keep k b.retired X).defs.map (·.corr), memberMap Nm b⟩

/-- The build script with `build()` given by `mod027FinishBy`. -/
def mod027ScriptBy (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) (g : List (Retired N) → CDef N A → Option (Retired N))
    (k : List (Retired N) → CDef N A → Bool) (extra : Bld N A → Option String) :
    ScriptFn N A := fun ops =>
  match ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | .error m => .error m
  | .ok b => mod027FinishBy Nm Build g k extra b

/-- The reference `build()` is the generic one with the reference check, every definition kept
and nothing more. -/
theorem mod027FinishBy_ref (Nm : Naming N) (Build : Trans N → Option String) (b : Bld N A) :
    mod027FinishBy Nm Build mod027HitDef (fun _ _ => true) (fun _ => none) b = finish Nm Build b := by
  unfold mod027FinishBy finish retiredHit mod027HitDef
  cases fuseStage Build b with
  | error m => rfl
  | ok X =>
    simp only [mod027Keep_true]
    cases refNetBuild (netOf X) with
    | error m => rfl
    | ok net =>
      simp only
      split <;> rename_i heq <;> rw [heq]

/-- The reference build script is the generic one with the reference check, every definition kept
and nothing more. -/
theorem mod027ScriptBy_ref (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) :
    mod027ScriptBy Nm tyOf Build Mg mod027HitDef (fun _ _ => true) (fun _ => none) =
      buildScript Nm tyOf Build Mg := by
  funext ops
  unfold mod027ScriptBy buildScript
  cases ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rfl
  | ok b => exact mod027FinishBy_ref Nm Build b

end Generic

/-! ### `build()` on the generic script -/

section FinishBy

variable [DecidableEq N] [ToString N] {Nm : Naming N} {Build : Trans N → Option String}
  {g : List (Retired N) → CDef N A → Option (Retired N)} {k : List (Retired N) → CDef N A → Bool}
  {extra : Bld N A → Option String}

/-- What a successful generic `build()` is. -/
theorem mod027FinishBy_ok_inv {b : Bld N A} {c : ComposedNet N A}
    (h : mod027FinishBy Nm Build g k extra b = .ok c) :
    ∃ X, fuseStage Build b = .ok X ∧ ¬ (netOf (mod027Keep k b.retired X)).TerminalClash ∧
      (mod027Keep k b.retired X).defs.findSome? (g b.retired) = none ∧ extra b = none ∧
      c = ⟨(netOf (mod027Keep k b.retired X)).collect,
        (mod027Keep k b.retired X).defs.map (·.corr), memberMap Nm b⟩ := by
  unfold mod027FinishBy at h
  cases hf : fuseStage Build b with
  | error m => rw [hf] at h; cases h
  | ok X =>
    rw [hf] at h
    simp only at h
    cases hn : refNetBuild (netOf (mod027Keep k b.retired X)) with
    | error m => rw [hn] at h; cases h
    | ok net =>
      rw [hn] at h
      simp only at h
      obtain ⟨hnc, rfl⟩ := refNetBuild_eq_ok_iff.1 hn
      cases hr : (mod027Keep k b.retired X).defs.findSome? (g b.retired) with
      | some r => rw [hr] at h; cases h
      | none =>
        rw [hr] at h
        simp only at h
        cases he : extra b with
        | some m => rw [he] at h; cases h
        | none =>
          rw [he] at h
          cases h
          exact ⟨X, rfl, hnc, hr, rfl, rfl⟩

/-- A generic `build()` whose stages all pass succeeds. -/
theorem mod027FinishBy_ok_of {b : Bld N A} {X : FuseNet N A} (hX : fuseStage Build b = .ok X)
    (hc : ¬ (netOf (mod027Keep k b.retired X)).TerminalClash)
    (hr : (mod027Keep k b.retired X).defs.findSome? (g b.retired) = none)
    (he : extra b = none) : ∃ c, mod027FinishBy Nm Build g k extra b = .ok c := by
  have hn : refNetBuild (netOf (mod027Keep k b.retired X)) =
      .ok (netOf (mod027Keep k b.retired X)).collect := refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩
  refine ⟨⟨(netOf (mod027Keep k b.retired X)).collect,
    (mod027Keep k b.retired X).defs.map (·.corr), memberMap Nm b⟩, ?_⟩
  unfold mod027FinishBy
  rw [hX]; simp only; rw [hn]; simp only; rw [hr]; simp only; rw [he]

/-- A generic `build()` whose retired check finds `r` fails with the message on `r`. -/
theorem mod027FinishBy_err_of {b : Bld N A} {X : FuseNet N A} (hX : fuseStage Build b = .ok X)
    (hc : ¬ (netOf (mod027Keep k b.retired X)).TerminalClash) {r : Retired N}
    (hr : (mod027Keep k b.retired X).defs.findSome? (g b.retired) = some r) :
    mod027FinishBy Nm Build g k extra b = .error (retiredMsg Nm r) := by
  have hn : refNetBuild (netOf (mod027Keep k b.retired X)) =
      .ok (netOf (mod027Keep k b.retired X)).collect := refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩
  unfold mod027FinishBy
  rw [hX]; simp only; rw [hn]; simp only; rw [hr]

omit [DecidableEq N] [ToString N] in
/-- The terminal clash of a fused content, read on its definitions. -/
theorem mod027_clash_iff (X : FuseNet N A) :
    (netOf X).TerminalClash ↔ ∃ p ∈ X.terminals, ∃ e ∈ X.defs, e.toTransDef.ConsumesOrReads p := by
  simp only [NetIn.TerminalClash, netOf, defBuilder, id]
  constructor
  · rintro ⟨p, hp, x, hx, h⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, e, he, h⟩
  · rintro ⟨p, hp, e, he, h⟩
    exact ⟨p, hp, _, List.mem_map.2 ⟨e, he, rfl⟩, h⟩

omit [ToString N] in
/-- The terminal places of the collected net are the fused content's, once each. -/
theorem mod027_collect_terminals (X : FuseNet N A) (p : N) :
    p ∈ (netOf X).collect.terminals ↔ p ∈ X.terminals := by
  simp [NetIn.collect, netOf, List.mem_eraseDups]

end FinishBy
/-! ### Folds -/

section Folds

variable {β α ε : Type}

/-- A successful fold over `l₁ ++ l₂` passes through a state after `l₁`. -/
theorem mod027_fold_split {f : β → α → Except ε β} {l₁ l₂ : List α} {b y : β}
    (h : (l₁ ++ l₂).foldlM f b = .ok y) : ∃ x, l₁.foldlM f b = .ok x ∧ l₂.foldlM f x = .ok y := by
  rw [List.foldlM_append] at h
  cases h1 : l₁.foldlM f b with
  | error e => rw [h1] at h; cases h
  | ok x => rw [h1] at h; exact ⟨x, rfl, h⟩

/-- Two successful folds join. -/
theorem mod027_fold_join {f : β → α → Except ε β} {l₁ l₂ : List α} {b x y : β}
    (h1 : l₁.foldlM f b = .ok x) (h2 : l₂.foldlM f x = .ok y) : (l₁ ++ l₂).foldlM f b = .ok y := by
  rw [List.foldlM_append, h1]; exact h2

end Folds

/-! ### The retired records along a script -/

section Records

variable [DecidableEq N]

/-- What the retired records of a builder are after a script `ops`: every record is a retirement
some call made; every place a call retired has a record; the first record of a place is a
retirement of the first call that retired it. -/
def mod027Inv (ops : List (Op N A)) (R : List (Retired N)) : Prop :=
  (∀ x ∈ R, ∃ op ∈ ops, RetiresPort op x) ∧
  (∀ q, PortRetiredBy ops q → ∃ x ∈ R, x.place = q) ∧
  (∀ q x, R.find? (fun r => decide (r.place = q)) = some x → FirstRetirement ops x)

/-- Before any call, nothing is retired. -/
theorem mod027Inv_nil : mod027Inv ([] : List (Op N A)) [] := by
  unfold mod027Inv
  refine ⟨fun x hx => (by cases hx), ?_, ?_⟩
  · rintro q ⟨op, hop, -⟩
    cases hop
  · intro q x h
    cases h

/-- The first record of a place after `addRetired`: the old one, else the first new one. -/
theorem mod027_find_addRetired (q : N) : ∀ (old new : List (Retired N)),
    (addRetired old new).find? (fun x => decide (x.place = q)) =
      (old.find? (fun x => decide (x.place = q))).or (new.find? (fun x => decide (x.place = q)))
  | old, [] => by simp [addRetired_nil]
  | old, r :: rs => by
    rw [addRetired_cons]
    split
    · rename_i hany
      rw [mod027_find_addRetired q old rs]
      by_cases hr : r.place = q
      · obtain ⟨x, hx, hxp⟩ := List.any_eq_true.1 hany
        have : (old.find? fun x => decide (x.place = q)).isSome := by
          rw [List.find?_isSome]; exact ⟨x, hx, by simpa [hr] using hxp⟩
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
        simp [hy]
      · simp [hr]
    · rename_i hany
      rw [mod027_find_addRetired q (old ++ [r]) rs, List.find?_append]
      by_cases hr : r.place = q
      · have hno : old.find? (fun x => decide (x.place = q)) = none := by
          rw [List.find?_eq_none]
          intro x hx hxq
          apply hany
          exact List.any_eq_true.2 ⟨x, hx, by simp only [decide_eq_true_eq] at hxq ⊢; rw [hxq, hr]⟩
        simp [hno, hr]
      · simp [hr]

/-- A call that retires nothing keeps the invariant with the same records. -/
theorem mod027Inv_none {ops : List (Op N A)} {R : List (Retired N)} {op : Op N A}
    (hop : ∀ r, ¬ RetiresPort op r) (h : mod027Inv ops R) : mod027Inv (ops ++ [op]) R := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold mod027Inv
  refine ⟨fun x hx => ?_, ?_, fun q x hx => ?_⟩
  · obtain ⟨o, ho, hr⟩ := h1 x hx
    exact ⟨o, List.mem_append_left _ ho, hr⟩
  · rintro q ⟨o, ho, r, hr, hq⟩
    rcases List.mem_append.1 ho with ho | ho
    · exact h2 q ⟨o, ho, r, hr, hq⟩
    · rw [List.mem_singleton] at ho; subst ho; exact absurd hr (hop r)
  · obtain ⟨l₁, o, l₂, he, hr, hn⟩ := h3 q x hx
    exact ⟨l₁, o, l₂ ++ [op], by rw [he]; simp, hr, hn⟩

/-- A compose call with port bindings `ports` on instance `I` keeps the invariant with its
retired records added. -/
theorem mod027Inv_compose {ops : List (Op N A)} {R : List (Retired N)} {op : Op N A}
    {I : Instance N A} {ports : List (String × N)} (hop : op.portBinds = some (I, ports))
    (h : mod027Inv ops R) :
    mod027Inv (ops ++ [op]) (addRetired R (retiredOf I.pfx (bindEntries I ports))) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hnew : ∀ x, x ∈ retiredOf I.pfx (bindEntries I ports) ↔ RetiresPort op x := by
    intro x
    rw [mem_retiredOf]
    constructor
    · rintro ⟨e, he, hne, rfl⟩
      obtain ⟨hp, hq⟩ := mem_bindEntries.1 he
      exact ⟨I, ports, hop, hp, hq, hne, rfl⟩
    · rintro ⟨I', ports', hop', hp, hq, hne, hpfx⟩
      rw [hop] at hop'
      cases hop'
      refine ⟨⟨x.place, x.port, x.caller⟩, mem_bindEntries.2 ⟨hp, hq⟩, hne, ?_⟩
      cases x; simp_all
  unfold mod027Inv
  refine ⟨fun x hx => ?_, ?_, fun q x hx => ?_⟩
  · rcases mem_addRetired hx with hx | hx
    · obtain ⟨o, ho, hr⟩ := h1 x hx
      exact ⟨o, List.mem_append_left _ ho, hr⟩
    · exact ⟨op, by simp, (hnew x).1 hx⟩
  · rintro q ⟨o, ho, r, hr, hq⟩
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨x, hx, hxq⟩ := h2 q ⟨o, ho, r, hr, hq⟩
      obtain ⟨l, hl⟩ := addRetired_prefix R (retiredOf I.pfx (bindEntries I ports))
      exact ⟨x, by rw [hl]; exact List.mem_append_left _ hx, hxq⟩
    · rw [List.mem_singleton] at ho; subst ho
      obtain ⟨x, hx, hxp⟩ := addRetired_covers (old := R) ((hnew r).2 hr)
      exact ⟨x, hx, hxp.trans hq⟩
  · rw [mod027_find_addRetired] at hx
    cases hR : R.find? (fun r => decide (r.place = q)) with
    | some y =>
      rw [hR] at hx
      simp only [Option.some_or] at hx
      have hxy : y = x := Option.some.inj hx
      subst hxy
      obtain ⟨l₁, o, l₂, he, hr, hn⟩ := h3 q y hR
      exact ⟨l₁, o, l₂ ++ [op], by rw [he]; simp, hr, hn⟩
    | none =>
      rw [hR] at hx
      simp only [Option.none_or] at hx
      have hxm := List.mem_of_find?_eq_some hx
      have hxq : x.place = q := by simpa using List.find?_some hx
      refine ⟨ops, op, [], rfl, (hnew x).1 hxm, ?_⟩
      intro hb
      obtain ⟨y, hy, hyq⟩ := h2 _ hb
      rw [List.find?_eq_none] at hR
      exact hR y hy (by simp [hyq, hxq])

variable [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- **One call keeps the invariant** of the retired records. -/
theorem mod027Inv_step {ops : List (Op N A)} {b b' : Bld N A} {op : Op N A}
    (h : mod027Inv ops b.retired) (hs : scriptStep Nm tyOf Build Mg b op = .ok b') :
    mod027Inv (ops ++ [op]) b'.retired := by
  have none_of : op.portBinds = none → ∀ r, ¬ RetiresPort op r := by
    intro hp r ⟨I, ports, hop, _⟩; rw [hp] at hop; cases hop
  cases op with
  | place p => cases hs; exact mod027Inv_none (none_of rfl) h
  | trans d =>
    simp only [scriptStep] at hs
    split at hs
    · cases hs
    · cases hs; exact mod027Inv_none (none_of rfl) h
  | terminal p => cases hs; exact mod027Inv_none (none_of rfl) h
  | fuse s =>
    simp only [scriptStep] at hs
    obtain ⟨s', -, rfl⟩ := except_map_ok_iff.1 hs
    exact mod027Inv_none (none_of rfl) h
  | compose I ports chans =>
    rw [step_compose] at hs
    rw [refCompose_retired hs]
    exact mod027Inv_compose rfl h
  | composeAuto I cs =>
    simp only [scriptStep] at hs
    unfold refAuto at hs
    split at hs
    · split at hs
      · rename_i hi
        obtain ⟨-, ms, -, rfl⟩ := applyBind_ok_iff.1 hs
        refine mod027Inv_none ?_ h
        rintro r ⟨I', ports, hop, hp, -⟩
        simp only [Op.portBinds, Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [List.isEmpty_iff] at hi
        rw [hi] at hp; cases hp
      · rw [refCompose_retired hs]
        exact mod027Inv_compose rfl h
    · cases hs
  | composeDirect S =>
    simp only [scriptStep] at hs
    split at hs
    · cases hs
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 hs
      exact mod027Inv_none (none_of rfl) h

/-- **A script keeps the invariant** of the retired records. -/
theorem mod027Inv_fold : ∀ (ops l₀ : List (Op N A)) (b₀ b : Bld N A), mod027Inv l₀ b₀.retired →
    ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok b → mod027Inv (l₀ ++ ops) b.retired
  | [], l₀, b₀, b, h, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf; simpa using h
  | op :: ops, l₀, b₀, b, h, hf => by
    rw [foldlM_except_cons] at hf
    cases hs : scriptStep Nm tyOf Build Mg b₀ op with
    | error m => rw [hs] at hf; cases hf
    | ok b₁ =>
      rw [hs] at hf
      have := mod027Inv_fold ops (l₀ ++ [op]) b₁ b (mod027Inv_step h hs) hf
      simpa using this

/-- **The fusion sets of a builder** after a call: the old ones and the one the call declared. -/
theorem mod027_step_fusions {b b' : Bld N A} {op : Op N A}
    (hs : scriptStep Nm tyOf Build Mg b op = .ok b') : b'.fusions = b.fusions ++ fusionsOf [op] := by
  cases op with
  | place p => cases hs; simp [fusionsOf]
  | trans d =>
    simp only [scriptStep] at hs
    split at hs
    · cases hs
    · cases hs; simp [fusionsOf]
  | terminal p => cases hs; simp [fusionsOf]
  | fuse s =>
    simp only [scriptStep] at hs
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 hs
    obtain ⟨-, -, rfl⟩ := (refDeclFusion_ok_iff tyOf s s').1 hs'
    simp [fusionsOf]
  | compose I ports chans =>
    rw [step_compose] at hs
    obtain ⟨ms, -, -, -, -, hf, -⟩ := refCompose_shape hs
    simp [hf, fusionsOf]
  | composeAuto I cs =>
    simp only [scriptStep] at hs
    unfold refAuto at hs
    split at hs
    · split at hs
      · obtain ⟨-, ms, -, rfl⟩ := applyBind_ok_iff.1 hs
        simp [bindAssemble, fusionsOf]
      · obtain ⟨ms, -, -, -, -, hf, -⟩ := refCompose_shape hs
        simp [hf, fusionsOf]
    · cases hs
  | composeDirect S =>
    simp only [scriptStep] at hs
    split at hs
    · cases hs
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 hs
      simp [directAssemble, fusionsOf]

/-- The fusion sets after a script: the ones its calls declared. -/
theorem mod027_fold_fusions : ∀ (ops : List (Op N A)) (b₀ b : Bld N A),
    ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok b → b.fusions = b₀.fusions ++ fusionsOf ops
  | [], b₀, b, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf; simp [fusionsOf]
  | op :: ops, b₀, b, hf => by
    rw [foldlM_except_cons] at hf
    cases hs : scriptStep Nm tyOf Build Mg b₀ op with
    | error m => rw [hs] at hf; cases hf
    | ok b₁ =>
      rw [hs] at hf
      rw [mod027_fold_fusions ops b₁ b hf, mod027_step_fusions hs]
      have : fusionsOf (op :: ops) = fusionsOf [op] ++ fusionsOf ops := by
        cases op <;> simp [fusionsOf]
      rw [this, List.append_assoc]

end Records

/-! ### Inserting a call -/

section Insert

variable [DecidableEq N]

/-- Two builders that differ by one inserted call: the second holds the places `ps` more and, when
`od = some d`, the definition `d` inserted among the first one's; everything `build()` reads but
places and definitions is the same. -/
def mod027Rel (od : Option (CDef N A)) (ps : List N) (x x' : Bld N A) : Prop :=
  x'.terminals = x.terminals ∧ x'.retired = x.retired ∧ x'.fusions = x.fusions ∧
  (∀ p, p ∈ x'.places ↔ p ∈ x.places ∨ p ∈ ps) ∧
  ∃ l₁ l₂, x.defs = l₁ ++ l₂ ∧ x'.defs = l₁ ++ od.toList ++ l₂

variable [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- **A call that reads neither places nor transitions keeps the relation**: it succeeds on the
second builder too. -/
theorem mod027Rel_step {od : Option (CDef N A)} {ps : List N} {x x' y : Bld N A} {op : Op N A}
    (hr : mod027Rel od ps x x') (hb : op.Blind) (hs : scriptStep Nm tyOf Build Mg x op = .ok y) :
    ∃ y', scriptStep Nm tyOf Build Mg x' op = .ok y' ∧ mod027Rel od ps y y' := by
  obtain ⟨ht, hR, hf, hp, l₁, l₂, hd, hd'⟩ := hr
  cases op with
  | place p =>
    cases hs
    refine ⟨_, rfl, ht, hR, hf, fun q => ?_, l₁, l₂, hd, hd'⟩
    simp only [mem_appendNew, hp]; tauto
  | trans e =>
    simp only [scriptStep] at hs ⊢
    cases hbe : Build e.toTrans with
    | some m => rw [hbe] at hs; cases hs
    | none =>
      rw [hbe] at hs; cases hs
      refine ⟨_, rfl, ht, hR, hf, fun q => ?_, l₁, l₂ ++ [e], by simp [hd], by simp [hd']⟩
      simp only [mem_appendNew, hp]; tauto
  | terminal p =>
    cases hs
    refine ⟨_, rfl, by simp [ht], hR, hf, fun q => ?_, l₁, l₂, hd, hd'⟩
    simp only [mem_appendNew, hp]; tauto
  | fuse s =>
    simp only [scriptStep] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 hs
    rw [hs']
    exact ⟨_, rfl, ht, hR, by simp [hf], hp, l₁, l₂, hd, hd'⟩
  | compose I ports chans =>
    rw [step_compose] at hs ⊢
    obtain ⟨h1, h2, h3, h4, h5, ms, hms, rfl⟩ := refCompose_ok_iff.1 hs
    refine ⟨_, refCompose_ok_iff.2 ⟨h1, h2, h3, h4, h5, ms, hms, rfl⟩, ?_⟩
    refine ⟨ht, by simp [retire, bindAssemble, hR], hf, fun q => ?_, l₁, l₂ ++ ms, ?_, ?_⟩
    · simp only [retire, mem_bindAssemble_places, hp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
    · simp [retire, bindAssemble, hd]
    · simp [retire, bindAssemble, hd']
  | composeAuto I cs => exact absurd hb id
  | composeDirect S => exact absurd hb id

/-- **A run of such calls keeps the relation.** -/
theorem mod027Rel_fold {od : Option (CDef N A)} {ps : List N} :
    ∀ (post : List (Op N A)) (x x' y : Bld N A), mod027Rel od ps x x' →
      (∀ op ∈ post, Op.Blind op) → post.foldlM (scriptStep Nm tyOf Build Mg) x = .ok y →
      ∃ y', post.foldlM (scriptStep Nm tyOf Build Mg) x' = .ok y' ∧ mod027Rel od ps y y'
  | [], x, x', y, hr, _, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    exact ⟨x', rfl, hr⟩
  | op :: post, x, x', y, hr, hb, hf => by
    rw [foldlM_except_cons] at hf
    cases hs : scriptStep Nm tyOf Build Mg x op with
    | error m => rw [hs] at hf; cases hf
    | ok x₁ =>
      rw [hs] at hf
      obtain ⟨x₁', hs', hr₁⟩ := mod027Rel_step hr (hb op (by simp)) hs
      obtain ⟨y', hy', hry⟩ := mod027Rel_fold post x₁ x₁' y hr₁
        (fun o ho => hb o (by simp [ho])) hf
      refine ⟨y', ?_, hry⟩
      rw [foldlM_except_cons, hs']
      exact hy'

/-- Adding a transition relates the builder to itself with the transition inserted. -/
theorem mod027Rel_trans {d : CDef N A} (hd : Build d.toTrans = none) (x : Bld N A) :
    ∃ x', scriptStep Nm tyOf Build Mg x (.trans d) = .ok x' ∧ mod027Rel (some d) d.namedPlaces x x' := by
  refine ⟨{ x with places := appendNew x.places d.namedPlaces, defs := x.defs ++ [d] },
    by simp only [scriptStep, hd], rfl, rfl, rfl, fun p => ?_, x.defs, [], by simp, by simp⟩
  simp only [mem_appendNew]

/-- Declaring a place relates the builder to itself with the place added. -/
theorem mod027Rel_place (q : N) (x : Bld N A) :
    ∃ x', scriptStep Nm tyOf Build Mg x (.place q) = .ok x' ∧ mod027Rel none [q] x x' :=
  ⟨_, rfl, rfl, rfl, rfl, fun p => by simp [mem_appendNew], x.defs, [], by simp, by simp⟩

/-- **A script with one call inserted** runs through the related builders. -/
theorem mod027_insert {pre post : List (Op N A)} {ins : Op N A} {od : Option (CDef N A)}
    {ps : List N} {y : Bld N A}
    (hins : ∀ x, ∃ x', scriptStep Nm tyOf Build Mg x ins = .ok x' ∧ mod027Rel od ps x x')
    (hb : ∀ op ∈ post, Op.Blind op)
    (h : (pre ++ post).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty = .ok y) :
    ∃ y', (pre ++ ins :: post).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty = .ok y' ∧
      mod027Rel od ps y y' := by
  obtain ⟨x₀, h₀, h₁⟩ := mod027_fold_split h
  obtain ⟨x₀', hs, hr⟩ := hins x₀
  obtain ⟨y', hy', hry⟩ := mod027Rel_fold post x₀ x₀' y hr hb h₁
  refine ⟨y', mod027_fold_join h₀ ?_, hry⟩
  rw [foldlM_except_cons, hs]
  exact hy'

omit [DecidableEq N] [ToString N] in
/-- With no fusion set, the substitution fusion asks for is the identity. -/
theorem mod027_substSpec_nil {σ : N → N} (h : SubstSpec ([] : List (FusionSet N)) σ) : σ = id :=
  substSpec_unique h ⟨fun s hs => (by cases hs), fun _ _ => rfl⟩

/-- **Fusion with a transition inserted**: when fusion succeeds on the first builder and the
inserted definition rewrites to `d'` that `Build` accepts, it succeeds on the second, with the
rewritten definition inserted at the same position and the same terminal places. -/
theorem mod027_fuse_trans {y y' : Bld N A} {d d' : CDef N A} {ps : List N} {Y : FuseNet N A}
    {σ : N → N} (hr : mod027Rel (some d) ps y y') (hY : fuseStage Build y = .ok Y)
    (hd : FusionDisjoint y.fusions) (hσ : SubstSpec y.fusions σ) (hfd : fuseDef σ d = .ok d')
    (hbd : Build d'.toTrans = none) :
    ∃ Y' Z₁ Z₂ e, fuseStage Build y' = .ok Y' ∧ Y.defs = Z₁ ++ Z₂ ∧ Y'.defs = Z₁ ++ e :: Z₂ ∧
      e.toTransDef = d'.toTransDef ∧ Y'.terminals = Y.terminals := by
  obtain ⟨ht, -, hf, -, l₁, l₂, hl, hl'⟩ := hr
  simp only [Option.toList_some] at hl'
  by_cases h0 : y.fusions = []
  · rw [fuseStage_nil h0] at hY
    cases hY
    have hσ' : σ = id := mod027_substSpec_nil (h0 ▸ hσ)
    subst hσ'
    rw [fuseDef_id] at hfd
    cases hfd
    refine ⟨_, l₁, l₂, d, fuseStage_nil (hf.trans h0), hl, by simp [hl'],
      (CDef.map_id_toTransDef d).symm, by simp [ht]⟩
  · rw [fuseStage_cons h0] at hY
    obtain ⟨-, hm, hbY, hYe⟩ := refFuse_ok_iff.1 hY
    have hσ' : σ = refSubst y.fusions := substSpec_unique hσ (refSubst_spec hd)
    subst hσ'
    rw [hl, List.mapM_append] at hm
    cases h1 : l₁.mapM (fuseDef (refSubst y.fusions)) with
    | error c => rw [h1] at hm; cases hm
    | ok Z₁ =>
      cases h2 : l₂.mapM (fuseDef (refSubst y.fusions)) with
      | error c => rw [h1, h2] at hm; cases hm
      | ok Z₂ =>
        rw [h1, h2] at hm
        have hZ : Y.defs = Z₁ ++ Z₂ := (Except.ok.inj hm).symm
        have hm' : y'.defs.mapM (fuseDef (refSubst y'.fusions)) = .ok (Z₁ ++ d' :: Z₂) := by
          rw [hf, hl', List.append_assoc, List.singleton_append, List.mapM_append, List.mapM_cons, h1,
            hfd, h2]; rfl
        have hb' : ∀ e ∈ Z₁ ++ d' :: Z₂, Build e.toTrans = none := by
          intro e he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact hbY e (by rw [hZ]; exact List.mem_append_left _ he)
          · exact hbd
          · exact hbY e (by rw [hZ]; exact List.mem_append_right _ he)
        have hd' : FusionDisjoint y'.fusions := hf ▸ hd
        refine ⟨fuseAssemble (refSubst y'.fusions) ⟨y'.places, y'.defs, y'.terminals⟩ (Z₁ ++ d' :: Z₂),
          Z₁, Z₂, d', ?_, hZ, rfl, rfl, ?_⟩
        · rw [fuseStage_cons (hf ▸ h0)]
          exact refFuse_accepts hd' hm' hb'
        · rw [hYe]; simp [fuseAssemble, ht, hf]

/-- **Fusion with a place inserted** succeeds with the same definitions and terminal places. -/
theorem mod027_fuse_place {y y' : Bld N A} {q : N} {Y : FuseNet N A}
    (hr : mod027Rel none [q] y y') (hY : fuseStage Build y = .ok Y) :
    ∃ Y', fuseStage Build y' = .ok Y' ∧ Y'.defs = Y.defs ∧ Y'.terminals = Y.terminals := by
  obtain ⟨ht, -, hf, -, l₁, l₂, hl, hl'⟩ := hr
  have hdefs : y'.defs = y.defs := by simp [hl, hl']
  by_cases h0 : y.fusions = []
  · rw [fuseStage_nil h0] at hY
    cases hY
    exact ⟨_, fuseStage_nil (hf.trans h0), hdefs, ht⟩
  · rw [fuseStage_cons h0] at hY
    obtain ⟨hd, hm, hbY, hYe⟩ := refFuse_ok_iff.1 hY
    have hm' : (FuseNet.mk y'.places y'.defs y'.terminals).defs.mapM
        (fuseDef (refSubst y'.fusions)) = .ok Y.defs := by
      show y'.defs.mapM _ = _
      rw [hdefs, hf]; exact hm
    refine ⟨fuseAssemble (refSubst y'.fusions) ⟨y'.places, y'.defs, y'.terminals⟩ Y.defs, ?_, rfl,
      ?_⟩
    · rw [fuseStage_cons (hf ▸ h0)]
      exact refFuse_accepts (hf ▸ hd) hm' hbY
    · rw [hYe]; simp [fuseAssemble, ht, hf]

end Insert

/-! ### A compose call and its twin -/

section TwinRel

variable [DecidableEq N]

/-- The retirements a call with port bindings `ports` on instance `I` makes are the records the
reference composition adds. -/
theorem mod027_retiresPort_iff {op : Op N A} {I : Instance N A} {ports : List (String × N)}
    (hop : op.portBinds = some (I, ports)) (x : Retired N) :
    RetiresPort op x ↔ x ∈ retiredOf I.pfx (bindEntries I ports) := by
  rw [mem_retiredOf]
  constructor
  · rintro ⟨I', ports', hop', hp, hq, hne, hpfx⟩
    rw [hop] at hop'
    cases hop'
    refine ⟨⟨x.place, x.port, x.caller⟩, mem_bindEntries.2 ⟨hp, hq⟩, hne, ?_⟩
    cases x; simp_all
  · rintro ⟨e, he, hne, rfl⟩
    obtain ⟨hp, hq⟩ := mem_bindEntries.1 he
    exact ⟨I, ports, hop, hp, hq, hne, rfl⟩

/-- The places a compose call retires. -/
def mod027RetPlaces (I : Instance N A) (ports : List (String × N)) : List N :=
  (retiredOf I.pfx (bindEntries I ports)).map (·.place)

/-- A place is retired by a compose call exactly when it is one of the call's retired places. -/
theorem mod027_retiredBy_compose {I : Instance N A} {ports : List (String × N)} {q : N} :
    PortRetiredBy [Op.compose I ports []] q ↔ q ∈ mod027RetPlaces I ports := by
  unfold PortRetiredBy mod027RetPlaces
  constructor
  · rintro ⟨op, hop, r, hr, rfl⟩
    rw [List.mem_singleton] at hop; subst hop
    exact List.mem_map.2 ⟨r, (mod027_retiresPort_iff rfl r).1 hr, rfl⟩
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    exact ⟨_, List.mem_singleton_self _, r, (mod027_retiresPort_iff rfl r).2 hr, rfl⟩

/-- Two builders that differ only in what a compose call and its twin leave differently: the same
places, definitions, terminal places and fusion sets; the same first record of every place but
the places `ps` the compose call retired, which the second builder has records of. What direct
composition records for [MOD-026] may differ too. -/
def mod027TwinRel (ps : List N) (x x' : Bld N A) : Prop :=
  x'.places = x.places ∧ x'.defs = x.defs ∧ x'.terminals = x.terminals ∧
    x'.fusions = x.fusions ∧
    (∀ q, q ∉ ps → x'.retired.find? (fun r => decide (r.place = q)) =
      x.retired.find? (fun r => decide (r.place = q))) ∧
    ∀ q ∈ ps, ∃ r ∈ x'.retired, r.place = q

variable [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

omit [ToString N] in
/-- Adding the same records to both builders keeps the record part of the relation. -/
theorem mod027TwinRel_add {ps : List N} {R R' : List (Retired N)} (new : List (Retired N))
    (h1 : ∀ q, q ∉ ps → R'.find? (fun r => decide (r.place = q)) =
      R.find? (fun r => decide (r.place = q)))
    (h2 : ∀ q ∈ ps, ∃ r ∈ R', r.place = q) :
    (∀ q, q ∉ ps → (addRetired R' new).find? (fun r => decide (r.place = q)) =
      (addRetired R new).find? (fun r => decide (r.place = q))) ∧
    ∀ q ∈ ps, ∃ r ∈ addRetired R' new, r.place = q := by
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [mod027_find_addRetired, mod027_find_addRetired, h1 q hq]
  · obtain ⟨r, hr, hrq⟩ := h2 q hq
    obtain ⟨l, hl⟩ := addRetired_prefix R' new
    exact ⟨r, by rw [hl]; exact List.mem_append_left _ hr, hrq⟩

/-- **A blind call keeps the twin relation**: it succeeds on the second builder too. -/
theorem mod027TwinRel_step {ps : List N} {x x' y : Bld N A} {op : Op N A}
    (hr : mod027TwinRel ps x x') (hb : op.Blind) (hs : scriptStep Nm tyOf Build Mg x op = .ok y) :
    ∃ y', scriptStep Nm tyOf Build Mg x' op = .ok y' ∧ mod027TwinRel ps y y' := by
  obtain ⟨hp, hd, ht, hf, h1, h2⟩ := hr
  cases op with
  | place p =>
    cases hs
    exact ⟨_, rfl, by simp [hp], hd, ht, hf, h1, h2⟩
  | trans e =>
    simp only [scriptStep] at hs ⊢
    cases hbe : Build e.toTrans with
    | some m => rw [hbe] at hs; cases hs
    | none =>
      rw [hbe] at hs; cases hs
      exact ⟨_, rfl, by simp [hp], by simp [hd], ht, hf, h1, h2⟩
  | terminal p =>
    cases hs
    exact ⟨_, rfl, by simp [hp], hd, by simp [ht], hf, h1, h2⟩
  | fuse s =>
    simp only [scriptStep] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 hs
    rw [hs']
    exact ⟨_, rfl, hp, hd, ht, by simp [hf], h1, h2⟩
  | compose I ports chans =>
    rw [step_compose] at hs ⊢
    obtain ⟨c1, c2, c3, c4, c5, ms, hms, rfl⟩ := refCompose_ok_iff.1 hs
    refine ⟨_, refCompose_ok_iff.2 ⟨c1, c2, c3, c4, c5, ms, hms, rfl⟩, ?_⟩
    obtain ⟨h1', h2'⟩ := mod027TwinRel_add (retiredOf I.pfx (bindEntries I ports)) h1 h2
    exact ⟨by simp [retire, bindAssemble, hp], by simp [retire, bindAssemble, hd],
      by simp [retire, bindAssemble, ht], by simp [retire, bindAssemble, hf], h1', h2'⟩
  | composeAuto I cs => exact absurd hb id
  | composeDirect S => exact absurd hb id

/-- **A run of blind calls keeps the twin relation.** -/
theorem mod027TwinRel_fold {ps : List N} :
    ∀ (post : List (Op N A)) (x x' y : Bld N A), mod027TwinRel ps x x' →
      (∀ op ∈ post, Op.Blind op) → post.foldlM (scriptStep Nm tyOf Build Mg) x = .ok y →
      ∃ y', post.foldlM (scriptStep Nm tyOf Build Mg) x' = .ok y' ∧ mod027TwinRel ps y y'
  | [], x, x', y, hr, _, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf
    exact ⟨x', rfl, hr⟩
  | op :: post, x, x', y, hr, hb, hf => by
    rw [foldlM_except_cons] at hf
    cases hs : scriptStep Nm tyOf Build Mg x op with
    | error m => rw [hs] at hf; cases hf
    | ok x₁ =>
      rw [hs] at hf
      obtain ⟨x₁', hs', hr₁⟩ := mod027TwinRel_step hr (hb op (by simp)) hs
      obtain ⟨y', hy', hry⟩ := mod027TwinRel_fold post x₁ x₁' y hr₁
        (fun o ho => hb o (by simp [ho])) hf
      refine ⟨y', ?_, hry⟩
      rw [foldlM_except_cons, hs']
      exact hy'

omit [DecidableEq N] [ToString N] in
/-- Merging nothing keeps every definition. -/
theorem mod027_mergeStep_nil (I : Instance N A) :
    ∀ ds : List (CDef N A), ds.mapM (mergeStep Mg I []) = .ok ds
  | [] => rfl
  | d :: ds => by
    rw [List.mapM_cons]
    have : mergeStep Mg I [] d = .ok d := rfl
    rw [this, mod027_mergeStep_nil I ds]
    rfl

/-- **The compose call where its twin succeeds**: on the same builder, a compose call the
composition accepts succeeds where its twin does, and the two builders are in the twin
relation. -/
theorem mod027_twin_start {x₀ x₁ : Bld N A} {I : Instance N A} {ports : List (String × N)}
    (hA : mod027Accepts tyOf I ports)
    (hs : scriptStep Nm tyOf Build Mg x₀ (.composeDirect (mod027Twin I ports)) = .ok x₁) :
    ∃ x₁', scriptStep Nm tyOf Build Mg x₀ (.compose I ports []) = .ok x₁' ∧
      mod027TwinRel (mod027RetPlaces I ports) x₁ x₁' := by
  obtain ⟨hA1, hA2, hA3, -, hA5⟩ := hA
  simp only [scriptStep] at hs
  split at hs
  · cases hs
  · rename_i hB
    obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 hs
    have hBuild : ∀ d ∈ I.defs, Build (rewriteDef (bindEntries I ports) d).toTrans = none := by
      intro d hd
      rw [List.findSome?_eq_none_iff] at hB
      exact hB _ (List.mem_map_of_mem hd)
    have hchan : ChansOk I ([] : List (String × CDef N A)) := by simp [ChansOk]
    rw [step_compose]
    refine ⟨_, refCompose_ok_iff.2 ⟨hA1, hA2, hA3, hchan,
      fun d hd => ⟨(hA5 d hd).1, (hA5 d hd).2, hBuild d hd⟩, _,
      mod027_mergeStep_nil I _, rfl⟩, ?_⟩
    refine ⟨by simp [retire, bindAssemble, directAssemble, mod027Twin],
      by simp [retire, bindAssemble, directAssemble, mod027Twin], by simp [retire, bindAssemble,
      directAssemble], by simp [retire, bindAssemble, directAssemble], fun q hq => ?_,
      fun q hq => ?_⟩
    · show (addRetired x₀.retired (retiredOf I.pfx (bindEntries I ports))).find? _ =
        x₀.retired.find? _
      rw [mod027_find_addRetired]
      have : (retiredOf I.pfx (bindEntries I ports)).find? (fun r => decide (r.place = q)) =
          none := by
        rw [List.find?_eq_none]
        intro r hr hrq
        exact hq (List.mem_map.2 ⟨r, hr, by simpa using hrq⟩)
      rw [this, Option.or_none]
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
      exact addRetired_covers hr

end TwinRel

/-! ### The lines on the generic script -/

section GenLines

variable [DecidableEq N]

/-- A retired check that finds nothing in a definition finds no record of a place it names. -/
def Mod027Sound (g : List (Retired N) → CDef N A → Option (Retired N)) : Prop :=
  ∀ R e, g R e = none → ∀ q ∈ e.namedPlaces, ∀ x ∈ R, x.place ≠ q

/-- A retired check finds nothing in a definition that names no recorded place. -/
def Mod027Quiet (g : List (Retired N) → CDef N A → Option (Retired N)) : Prop :=
  ∀ R e, (∀ q ∈ e.namedPlaces, ∀ x ∈ R, x.place ≠ q) → g R e = none

/-- In a definition that names exactly one recorded place `P`, a retired check finds the first
record of `P`. -/
def Mod027Names (g : List (Retired N) → CDef N A → Option (Retired N)) : Prop :=
  ∀ R e P, P ∈ e.namedPlaces → (∀ q ∈ e.namedPlaces, (∃ x ∈ R, x.place = q) → q = P) →
    g R e = R.find? (fun x => decide (x.place = P))

/-- A retired check reads only the first records of the places a definition names. -/
def Mod027Local (g : List (Retired N) → CDef N A → Option (Retired N)) : Prop :=
  ∀ R R' e, (∀ q ∈ e.namedPlaces, R'.find? (fun x => decide (x.place = q)) =
    R.find? (fun x => decide (x.place = q))) → g R' e = g R e

/-- A keep test reads only the first records of the places a definition names. -/
def Mod027KeepLocal (k : List (Retired N) → CDef N A → Bool) : Prop :=
  ∀ R R' e, (∀ q ∈ e.namedPlaces, R'.find? (fun x => decide (x.place = q)) =
    R.find? (fun x => decide (x.place = q))) → k R' e = k R e

/-- A definition a keep test drops stays dropped when more places are recorded. -/
def Mod027KeepMono (k : List (Retired N) → CDef N A → Bool) : Prop :=
  ∀ R R' e, (∀ q, (∃ x ∈ R, x.place = q) → ∃ x ∈ R', x.place = q) → k R e = false →
    k R' e = false

/-- A keep test keeps every definition that names at most one recorded place. -/
def Mod027KeepsOne (k : List (Retired N) → CDef N A → Bool) : Prop :=
  ∀ R e, (∀ q ∈ e.namedPlaces, ∀ q' ∈ e.namedPlaces, (∃ x ∈ R, x.place = q) →
    (∃ x ∈ R, x.place = q') → q = q') → k R e = true

/-- A further check that passes before a transition is inserted passes after. -/
def Mod027ExtraTrans (extra : Bld N A → Option String) : Prop :=
  ∀ x x' (d : CDef N A), mod027Rel (some d) d.namedPlaces x x' → extra x = none → extra x' = none

/-- A further check that passes before a place is declared passes after. -/
def Mod027ExtraPlace (extra : Bld N A → Option String) : Prop :=
  ∀ x x' (q : N), mod027Rel none [q] x x' → extra x = none → extra x' = none

/-- A further check that passes on a builder with a twin passes with the compose call. -/
def Mod027ExtraTwin (extra : Bld N A → Option String) : Prop :=
  ∀ ps (x x' : Bld N A), mod027TwinRel ps x x' → extra x = none → extra x' = none

variable [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}
  {g : List (Retired N) → CDef N A → Option (Retired N)} {k : List (Retired N) → CDef N A → Bool}
  {extra : Bld N A → Option String}

omit [DecidableEq N] [ToString N] in
/-- A definition and its rewrite with the same transition definition name the same places. -/
theorem mod027_namedPlaces_eq {e d : CDef N A} (h : e.toTransDef = d.toTransDef) :
    e.namedPlaces = d.namedPlaces := by
  show e.toTransDef.namedPlaces = d.toTransDef.namedPlaces
  rw [h]

omit [DecidableEq N] [ToString N] in
/-- Inserting into a list of definitions the check finds nothing in, a definition it finds nothing
in, keeps it finding nothing. -/
theorem mod027_findSome_ins {f : CDef N A → Option (Retired N)} {Z₁ Z₂ : List (CDef N A)}
    {e : CDef N A} (h : (Z₁ ++ Z₂).findSome? f = none) :
    (Z₁ ++ e :: Z₂).findSome? f = f e := by
  rw [List.findSome?_eq_none_iff] at h
  have h1 : Z₁.findSome? f = none :=
    List.findSome?_eq_none_iff.2 fun a ha => h a (List.mem_append_left _ ha)
  have h2 : Z₂.findSome? f = none :=
    List.findSome?_eq_none_iff.2 fun a ha => h a (List.mem_append_right _ ha)
  rw [List.findSome?_append, h1, List.findSome?_cons]
  cases f e <;> simp [h2]

omit [DecidableEq N] [ToString N] in
/-- An element of a list `mapM` maps successfully has an image in the result. -/
theorem mod027_mapM_mem {α β ε : Type} {f : α → Except ε β} {l : List α} {ys : List β}
    (h : l.mapM f = .ok ys) {a : α} (ha : a ∈ l) : ∃ y ∈ ys, f a = .ok y := by
  rw [mapM_except_ok_iff] at h
  revert ha
  induction h with
  | nil => intro ha; cases ha
  | cons hr _ ih =>
    intro ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hfy⟩ := ih ha
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- A transition a call of a successful script added is among the builder's definitions. -/
theorem mod027_trans_mem : ∀ (ops : List (Op N A)) (b₀ y : Bld N A) (d : CDef N A),
    Op.trans d ∈ ops → ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok y → d ∈ y.defs
  | [], _, _, _, hd, _ => by cases hd
  | op :: ops, b₀, y, d, hd, h => by
    rw [foldlM_except_cons] at h
    cases hs : scriptStep Nm tyOf Build Mg b₀ op with
    | error m => rw [hs] at h; cases h
    | ok b₁ =>
      rw [hs] at h
      rcases List.mem_cons.1 hd with he | hd
      · subst he
        simp only [scriptStep] at hs
        split at hs
        · cases hs
        · cases hs
          obtain ⟨⟨l, hl⟩, -⟩ := script_prefix h
          rw [hl]; simp
      · exact mod027_trans_mem ops b₁ y d hd h

/-- **A transition after fusion is a fused definition**: when the fusion stage succeeds, a
definition of the builder rewritten under the substitution fusion asks for names the places of
a definition the stage returns. -/
theorem mod027_fused_mem {y : Bld N A} {Y : FuseNet N A} {σ : N → N} {d d' : CDef N A}
    (hY : fuseStage Build y = .ok Y) (hσ : SubstSpec y.fusions σ) (hd : d ∈ y.defs)
    (hfd : fuseDef σ d = .ok d') : ∃ e ∈ Y.defs, e.namedPlaces = d'.namedPlaces := by
  by_cases h0 : y.fusions = []
  · rw [fuseStage_nil h0] at hY
    cases hY
    have hσ' : σ = id := mod027_substSpec_nil (h0 ▸ hσ)
    subst hσ'
    rw [fuseDef_id] at hfd
    cases hfd
    exact ⟨d, hd, mod027_namedPlaces_eq (CDef.map_id_toTransDef d).symm⟩
  · rw [fuseStage_cons h0] at hY
    obtain ⟨hdis, hm, -, -⟩ := refFuse_ok_iff.1 hY
    have hσ' : σ = refSubst y.fusions := substSpec_unique hσ (refSubst_spec hdis)
    subst hσ'
    obtain ⟨e, he, hfe⟩ := mod027_mapM_mem hm hd
    rw [hfd] at hfe
    cases hfe
    exact ⟨_, he, rfl⟩

/-- **Line 1, first half, on the generic script**: when the check is sound, no transition of a
built net names a retired place. -/
theorem mod027_gen_line1_built (hS : Mod027Sound g) :
    mod027_line1_built (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro ops c _ hc q hq d hd hqd
  unfold mod027ScriptBy at hc
  cases hy : ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, -, -, hnone, -, rfl⟩ := mod027FinishBy_ok_inv hc
    have hinv := mod027Inv_fold ops [] Bld.empty y mod027Inv_nil hy
    simp only [List.nil_append] at hinv
    obtain ⟨x, hx, hxq⟩ := hinv.2.1 q hq
    change d ∈ (netOf (mod027Keep k y.retired Y)).collect.trans at hd
    rw [netOf_collect_trans] at hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact hS _ e (List.findSome?_eq_none_iff.1 hnone e he) q hqd x hx hxq

/-- **Line 1, second half, on the generic script**: when the check is sound and every fused
definition is kept, no transition a call added names a retired place after fusion. -/
theorem mod027_gen_line1_call (hS : Mod027Sound g) (hK : ∀ R e, k R e = true) :
    mod027_line1_call (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro ops c _ hc q hq d σ d' hd hσ hfd hqd
  unfold mod027ScriptBy at hc
  cases hy : ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, hY, -, hnone, -, -⟩ := mod027FinishBy_ok_inv hc
    rw [mod027Keep_all (hK y.retired)] at hnone
    have hinv := mod027Inv_fold ops [] Bld.empty y mod027Inv_nil hy
    simp only [List.nil_append] at hinv
    obtain ⟨x, hx, hxq⟩ := hinv.2.1 q hq
    have hdy : d ∈ y.defs := mod027_trans_mem ops Bld.empty y d hd hy
    have hfus : y.fusions = fusionsOf ops := by
      simpa [Bld.empty] using mod027_fold_fusions _ _ _ hy
    obtain ⟨e, he, hne⟩ := mod027_fused_mem hY (hfus ▸ hσ) hdy hfd
    exact hS _ e (List.findSome?_eq_none_iff.1 hnone e he) q (hne ▸ hqd) x hx hxq

/-- **Line 1 on the generic script.** -/
theorem mod027_gen_line1 (hS : Mod027Sound g) (hK : ∀ R e, k R e = true) :
    mod027_line1 (mod027ScriptBy Nm tyOf Build Mg g k extra) :=
  (mod027_line1_iff _).2 ⟨mod027_gen_line1_built hS, mod027_gen_line1_call hS hK⟩

omit [DecidableEq N] [ToString N] in
/-- The keep stage with a definition inserted: the kept definitions are the old kept ones with
the inserted one, when it is kept, at its position. -/
theorem mod027_keep_ins {R : List (Retired N)} {Z₁ Z₂ : List (CDef N A)} {e : CDef N A}
    (hke : k R e = true) :
    (Z₁ ++ e :: Z₂).filter (k R) = Z₁.filter (k R) ++ e :: Z₂.filter (k R) := by
  rw [List.filter_append, List.filter_cons, if_pos hke]

/-- **Line 2 on the generic script**: when the check finds the first record of the one retired
place a definition names and a definition naming at most one recorded place is kept, a
transition naming exactly one retired place fails `build()` with the message on that record. -/
theorem mod027_gen_line2 (hN : Mod027Names g) (hK1 : Mod027KeepsOne k) :
    mod027_line2 Nm Build (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro pre post d c σ d' P _ hc hb hdis hσ hbd hfd hbd' hterm hP hPr hsole
  unfold mod027ScriptBy at hc ⊢
  cases hy : (pre ++ post).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, hY, hnc, hnone, -, rfl⟩ := mod027FinishBy_ok_inv hc
    obtain ⟨y', hy', hrel⟩ :=
      mod027_insert (mod027Rel_trans (Nm := Nm) (tyOf := tyOf) (Mg := Mg) hbd) hb hy
    have hfus : y.fusions = fusionsOf (pre ++ post) := by
      simpa [Bld.empty] using mod027_fold_fusions _ _ _ hy
    obtain ⟨Y', Z₁, Z₂, e, hY', hZ, hZ', he, hT⟩ :=
      mod027_fuse_trans hrel hY (hfus ▸ hdis) (hfus ▸ hσ) hfd hbd'
    have hinv := mod027Inv_fold (pre ++ post) [] Bld.empty y mod027Inv_nil hy
    simp only [List.nil_append] at hinv
    obtain ⟨hI1, hI2, hI3⟩ := hinv
    obtain ⟨x₀, hx₀, hx₀P⟩ := hI2 P hPr
    have hsome : (y.retired.find? fun r => decide (r.place = P)).isSome :=
      List.find?_isSome.2 ⟨x₀, hx₀, by simp [hx₀P]⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    have hxP : x.place = P := by simpa using List.find?_some hx
    refine ⟨x, hI3 P x hx, hxP, ?_⟩
    rw [hy']
    have hR : y'.retired = y.retired := hrel.2.1
    have hne := mod027_namedPlaces_eq he
    have hrec : ∀ q ∈ e.namedPlaces, (∃ z ∈ y.retired, z.place = q) → q = P := by
      rintro q hq ⟨z, hz, hzq⟩
      obtain ⟨op, hop, hr⟩ := hI1 z hz
      exact hsole q (hne ▸ hq) ⟨op, hop, z, hr, hzq⟩
    have hke : k y.retired e = true :=
      hK1 _ e fun q hq q' hq' h h' => (hrec q hq h).trans (hrec q' hq' h').symm
    have hK : (mod027Keep k y.retired Y).defs = Z₁.filter (k y.retired) ++ Z₂.filter (k y.retired) := by
      simp [mod027Keep, hZ, List.filter_append]
    have hK' : (mod027Keep k y'.retired Y').defs =
        Z₁.filter (k y.retired) ++ e :: Z₂.filter (k y.retired) := by
      simp only [mod027Keep, hR, hZ']; exact mod027_keep_ins hke
    have hge : g y'.retired e = some x := by
      rw [hR, hN y.retired e P (hne ▸ hP) hrec, hx]
    have hfind : (mod027Keep k y'.retired Y').defs.findSome? (g y'.retired) = some x := by
      rw [hK', mod027_findSome_ins (by rw [hR, ← hK]; exact hnone), hge]
    have hKT : (mod027Keep k y'.retired Y').terminals = (mod027Keep k y.retired Y).terminals := by
      simp [mod027Keep, hT]
    have hnc' : ¬ (netOf (mod027Keep k y'.retired Y')).TerminalClash := by
      rw [mod027_clash_iff] at hnc ⊢
      rintro ⟨p, hp, a, ha, hca⟩
      rw [hKT] at hp
      rw [hK'] at ha
      simp only [List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · exact hnc ⟨p, hp, a, by rw [hK]; exact List.mem_append_left _ ha, hca⟩
      · rw [he] at hca
        exact hterm p ((mod027_collect_terminals _ p).2 hp) hca
      · exact hnc ⟨p, hp, a, by rw [hK]; exact List.mem_append_right _ ha, hca⟩
    exact mod027FinishBy_err_of hY' hnc' hfind

/-- **Line 3 on the generic script**: when the check is quiet on a definition that names no
recorded place, such a definition is kept, and the further check survives an inserted transition,
a transition that names no retired place after fusion keeps the build successful. -/
theorem mod027_gen_line3 (hQ : Mod027Quiet g) (hK1 : Mod027KeepsOne k) (hE : Mod027ExtraTrans extra) :
    mod027_line3 Build (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro pre post d c σ d' hc hb hdis hσ hbd hfd hbd' hterm hnot
  unfold mod027ScriptBy at hc ⊢
  cases hy : (pre ++ post).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, hY, hnc, hnone, hex, rfl⟩ := mod027FinishBy_ok_inv hc
    obtain ⟨y', hy', hrel⟩ :=
      mod027_insert (mod027Rel_trans (Nm := Nm) (tyOf := tyOf) (Mg := Mg) hbd) hb hy
    have hfus : y.fusions = fusionsOf (pre ++ post) := by
      simpa [Bld.empty] using mod027_fold_fusions _ _ _ hy
    obtain ⟨Y', Z₁, Z₂, e, hY', hZ, hZ', he, hT⟩ :=
      mod027_fuse_trans hrel hY (hfus ▸ hdis) (hfus ▸ hσ) hfd hbd'
    have hinv := mod027Inv_fold (pre ++ post) [] Bld.empty y mod027Inv_nil hy
    simp only [List.nil_append] at hinv
    obtain ⟨hI1, -, -⟩ := hinv
    rw [hy']
    have hR : y'.retired = y.retired := hrel.2.1
    have hne := mod027_namedPlaces_eq he
    have hnrec : ∀ q ∈ e.namedPlaces, ∀ x ∈ y.retired, x.place ≠ q := by
      intro q hq x hx hxq
      obtain ⟨op, hop, hr⟩ := hI1 x hx
      exact hnot q (hne ▸ hq) ⟨op, hop, x, hr, hxq⟩
    have hke : k y.retired e = true := by
      refine hK1 _ e fun q hq q' _ h _ => ?_
      obtain ⟨x, hx, hxq⟩ := h
      exact absurd hxq (hnrec q hq x hx)
    have hK : (mod027Keep k y.retired Y).defs = Z₁.filter (k y.retired) ++ Z₂.filter (k y.retired) := by
      simp [mod027Keep, hZ, List.filter_append]
    have hK' : (mod027Keep k y'.retired Y').defs =
        Z₁.filter (k y.retired) ++ e :: Z₂.filter (k y.retired) := by
      simp only [mod027Keep, hR, hZ']; exact mod027_keep_ins hke
    have hge : g y'.retired e = none := by
      rw [hR]; exact hQ _ e hnrec
    have hfind : (mod027Keep k y'.retired Y').defs.findSome? (g y'.retired) = none := by
      rw [hK', mod027_findSome_ins (by rw [hR, ← hK]; exact hnone), hge]
    have hKT : (mod027Keep k y'.retired Y').terminals = (mod027Keep k y.retired Y).terminals := by
      simp [mod027Keep, hT]
    have hnc' : ¬ (netOf (mod027Keep k y'.retired Y')).TerminalClash := by
      rw [mod027_clash_iff] at hnc ⊢
      rintro ⟨p, hp, a, ha, hca⟩
      rw [hKT] at hp
      rw [hK'] at ha
      simp only [List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · exact hnc ⟨p, hp, a, by rw [hK]; exact List.mem_append_left _ ha, hca⟩
      · rw [he] at hca
        exact hterm p ((mod027_collect_terminals _ p).2 hp) hca
      · exact hnc ⟨p, hp, a, by rw [hK]; exact List.mem_append_right _ ha, hca⟩
    exact mod027FinishBy_ok_of hY' hnc' hfind (hE y y' d hrel hex)

/-- **Line 4 on the generic script**: when the further check survives a declared place, declaring
one more place keeps the build successful. -/
theorem mod027_gen_line4 (hE : Mod027ExtraPlace extra) :
    mod027_line4 (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro pre post q c hc hb
  unfold mod027ScriptBy at hc ⊢
  cases hy : (pre ++ post).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, hY, hnc, hnone, hex, rfl⟩ := mod027FinishBy_ok_inv hc
    obtain ⟨y', hy', hrel⟩ :=
      mod027_insert (mod027Rel_place (Nm := Nm) (tyOf := tyOf) (Build := Build) (Mg := Mg) q) hb hy
    obtain ⟨Y', hY', hD, hT⟩ := mod027_fuse_place hrel hY
    rw [hy']
    have hR : y'.retired = y.retired := hrel.2.1
    have hKd : (mod027Keep k y'.retired Y').defs = (mod027Keep k y.retired Y).defs := by
      simp [mod027Keep, hD, hR]
    have hKT : (mod027Keep k y'.retired Y').terminals = (mod027Keep k y.retired Y).terminals := by
      simp [mod027Keep, hT]
    have hnc' : ¬ (netOf (mod027Keep k y'.retired Y')).TerminalClash := by
      rw [mod027_clash_iff] at hnc ⊢
      rw [hKd, hKT]; exact hnc
    exact mod027FinishBy_ok_of hY' hnc' (by rw [hKd, hR]; exact hnone) (hE y y' q hrel hex)

/-- **Line 5 on the generic script**: when the check and the keep test read only the first records
of the places a definition names, a dropped definition stays dropped when more places are
recorded, and the further check survives the twin relation, a compose call the composition
accepts builds where its twin builds and no transition names a place the call retires. -/
theorem mod027_gen_line5 (hG : Mod027Local g) (hKL : Mod027KeepLocal k) (hKM : Mod027KeepMono k)
    (hE : Mod027ExtraTwin extra) :
    mod027_line5 tyOf (mod027ScriptBy Nm tyOf Build Mg g k extra) := by
  intro pre post I ports c hb _ hA hc hnot
  unfold mod027ScriptBy at hc ⊢
  cases hy : (pre ++ Op.composeDirect (mod027Twin I ports) :: post).foldlM
      (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => rw [hy] at hc; cases hc
  | ok y =>
    rw [hy] at hc
    obtain ⟨Y, hY, hnc, hnone, hex, rfl⟩ := mod027FinishBy_ok_inv hc
    obtain ⟨x₀, h₀, h₁⟩ := mod027_fold_split hy
    rw [foldlM_except_cons] at h₁
    cases hs : scriptStep Nm tyOf Build Mg x₀ (.composeDirect (mod027Twin I ports)) with
    | error m => rw [hs] at h₁; cases h₁
    | ok x₁ =>
      rw [hs] at h₁
      obtain ⟨x₁', hs', hr₁⟩ := mod027_twin_start hA hs
      obtain ⟨y', hy', hr⟩ := mod027TwinRel_fold post x₁ x₁' y hr₁ hb h₁
      have hfold : (pre ++ Op.compose I ports [] :: post).foldlM (scriptStep Nm tyOf Build Mg)
          Bld.empty = .ok y' := by
        refine mod027_fold_join h₀ ?_
        rw [foldlM_except_cons, hs']
        exact hy'
      rw [hfold]
      have hrel := hr
      obtain ⟨hp, hd, ht, hf, hfind, hcov⟩ := hr
      have hY' : fuseStage Build y' = .ok Y := by
        rw [← hY]; unfold fuseStage; rw [hp, hd, ht, hf]
      have hav : ∀ e ∈ (mod027Keep k y.retired Y).defs, ∀ q ∈ e.namedPlaces,
          q ∉ mod027RetPlaces I ports := by
        intro e he q hq hqp
        refine hnot q (mod027_retiredBy_compose.2 hqp) e.toTransDef ?_ hq
        change _ ∈ (netOf (mod027Keep k y.retired Y)).collect.trans
        rw [netOf_collect_trans]
        exact List.mem_map_of_mem he
      have hmono : ∀ q, (∃ x ∈ y.retired, x.place = q) → ∃ x ∈ y'.retired, x.place = q := by
        intro q hq
        by_cases hqp : q ∈ mod027RetPlaces I ports
        · exact hcov q hqp
        · have h1 : (y.retired.find? fun r => decide (r.place = q)).isSome := by
            obtain ⟨x, hx, hxq⟩ := hq
            exact List.find?_isSome.2 ⟨x, hx, by simp [hxq]⟩
          rw [← hfind q hqp] at h1
          obtain ⟨x, hx, hxq⟩ := List.find?_isSome.1 h1
          exact ⟨x, hx, by simpa using hxq⟩
      have hkeq : mod027Keep k y'.retired Y = mod027Keep k y.retired Y := by
        unfold mod027Keep
        congr 1
        apply List.filter_congr
        intro e he
        cases hke : k y.retired e with
        | false => exact hKM _ _ e hmono hke
        | true =>
          have hin : e ∈ (mod027Keep k y.retired Y).defs := List.mem_filter.2 ⟨he, hke⟩
          rw [hKL _ _ e fun q hq => hfind q (hav e hin q hq), hke]
      have hnone' : (mod027Keep k y'.retired Y).defs.findSome? (g y'.retired) = none := by
        rw [hkeq, List.findSome?_eq_none_iff]
        intro e he
        rw [hG _ _ e fun q hq => hfind q (hav e he q hq)]
        exact List.findSome?_eq_none_iff.1 hnone e he
      exact mod027FinishBy_ok_of hY' (by rw [hkeq]; exact hnc) hnone' (hE _ y y' hrel hex)

end GenLines
/-! ### The reference check -/

section RefCheck

variable [DecidableEq N]

/-- The reference check finds nothing only where no named place has a record. -/
theorem mod027HitDef_sound : Mod027Sound (mod027HitDef (N := N) (A := A)) := by
  intro R e h q hq x hx hxq
  rw [mod027HitDef, List.findSome?_eq_none_iff] at h
  have := h q hq
  rw [List.find?_eq_none] at this
  exact this x hx (by simp [hxq])

/-- The reference check finds nothing where no named place has a record. -/
theorem mod027HitDef_quiet : Mod027Quiet (mod027HitDef (N := N) (A := A)) := by
  intro R e h
  rw [mod027HitDef, List.findSome?_eq_none_iff]
  intro q hq
  rw [List.find?_eq_none]
  intro x hx hxq
  exact h q hq x hx (by simpa using hxq)

/-- Over the places of a list that has one recorded place `P`, the first record found is `P`'s. -/
theorem mod027_findSome_one (R : List (Retired N)) (P : N) :
    ∀ l : List N, P ∈ l → (∀ q ∈ l, (∃ x ∈ R, x.place = q) → q = P) →
      l.findSome? (fun p => R.find? fun r => decide (r.place = p)) =
        R.find? (fun r => decide (r.place = P))
  | [], h, _ => by cases h
  | a :: l, h, hs => by
    have hoth : ∀ q ∈ a :: l, q ≠ P → R.find? (fun r => decide (r.place = q)) = none := by
      intro q hq hne
      rw [List.find?_eq_none]
      intro x hx hxq
      exact hne (hs q hq ⟨x, hx, by simpa using hxq⟩)
    rw [List.findSome?_cons]
    by_cases ha : a = P
    · subst ha
      cases hf : R.find? (fun r => decide (r.place = a)) with
      | some x => rfl
      | none =>
        simp only
        rw [List.findSome?_eq_none_iff]
        intro q hq
        by_cases hqa : q = a
        · rw [hqa, hf]
        · exact hoth q (List.mem_cons_of_mem _ hq) hqa
    · rw [hoth a List.mem_cons_self ha]
      simp only
      exact mod027_findSome_one R P l ((List.mem_cons.1 h).resolve_left (Ne.symm ha))
        (fun q hq => hs q (List.mem_cons_of_mem _ hq))

/-- In a definition that names exactly one recorded place, the reference check finds its first
record. -/
theorem mod027HitDef_names : Mod027Names (mod027HitDef (N := N) (A := A)) :=
  fun R e P hP hs => mod027_findSome_one R P e.namedPlaces hP hs

omit [DecidableEq N] in
/-- `findSome?` over a list on whose elements two functions agree. -/
theorem mod027_findSome_congr {α β : Type} {f f' : α → Option β} :
    ∀ l : List α, (∀ a ∈ l, f' a = f a) → l.findSome? f' = l.findSome? f
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h a List.mem_cons_self,
      mod027_findSome_congr l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The reference check reads only the first records of the places a definition names. -/
theorem mod027HitDef_local : Mod027Local (mod027HitDef (N := N) (A := A)) :=
  fun _ _ e h => mod027_findSome_congr e.namedPlaces h

/-- The reference keeps every definition: its keep test reads nothing. -/
theorem mod027KeepAll_local : Mod027KeepLocal (fun (_ : List (Retired N)) (_ : CDef N A) => true) :=
  fun _ _ _ _ => rfl

omit [DecidableEq N] in
/-- The reference keep test drops nothing. -/
theorem mod027KeepAll_mono : Mod027KeepMono (fun (_ : List (Retired N)) (_ : CDef N A) => true) :=
  fun _ _ _ _ h => h

omit [DecidableEq N] in
/-- The reference keep test keeps every definition. -/
theorem mod027KeepAll_one : Mod027KeepsOne (fun (_ : List (Retired N)) (_ : CDef N A) => true) :=
  fun _ _ _ => rfl

end RefCheck

/-! ## Example vocabulary -/

section Examples

/-- The channel merge of the examples: the reference merge with the caller's action first. -/
def mod027ExMg : MergeFn String Unit :=
  refMerge refBuild (seqAct fun a _ => a) (fun _ _ => .ok none)

/-- The rejection message a script ends with, if any. -/
def mod027Err (S : ScriptFn String Unit) (ops : List (Op String Unit)) : Option String :=
  match S ops with
  | .error m => some m
  | .ok _ => none

/-- A host transition `nm` that takes a token from `go`, with read arcs `rd` and output `out`. -/
def mod027ExHost (nm : String) (rd : List String) (out : Option (Out String)) : CDef String Unit :=
  { core := ⟨nm, [⟨"go", .one⟩], [], rd, []⟩, out := out, timing := .immediate, priority := 0,
    action := .passthrough }

/-- Compose `answer` with its port `in` bound to the caller place `X`. -/
def mod027ExBind (X : String) : Op String Unit := .compose buildExInst [("in", X)] []

/-- The message that names `answer/IN`, port `in`, instance `answer` and caller place `X`. -/
def mod027ExMsg (X : String) : String :=
  s!"place 'answer/IN' is port 'in' of instance 'answer', bound to host place '{X}' at compose; reference '{X}' instead"

end Examples

/-! ## The reference -/

section Reference

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- The reference build script meets MOD-027 for every naming, token-type check,
transition-builder check and channel merge. -/
theorem mod027_ref (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) : MOD_027 Nm tyOf Build (buildScript Nm tyOf Build Mg) := by
  rw [← mod027ScriptBy_ref]
  exact ⟨mod027_gen_line1 mod027HitDef_sound (fun _ _ => rfl),
    mod027_gen_line2 mod027HitDef_names mod027KeepAll_one,
    mod027_gen_line3 mod027HitDef_quiet mod027KeepAll_one (fun _ _ _ _ h => h),
    mod027_gen_line4 (fun _ _ _ _ h => h),
    mod027_gen_line5 mod027HitDef_local mod027KeepAll_local mod027KeepAll_mono
      (fun _ _ _ _ h => h)⟩

end Reference

/-- ✓ The reference build script satisfies MOD-027 for every naming, every token-type check and
every transition-builder check. Compose the instance `answer` with its port `in` bound to the
caller place `A_IN`. A host transition that names `answer/IN`, added before or after the compose
call, makes `build()` fail with the message that points at `A_IN`; one that names `A_IN` instead
builds; declaring `answer/IN` without naming it builds; and the compose call builds wherever the
same instance transitions, composed directly with their arcs already on `A_IN`, build. -/
@[evidence holds MOD_027]
theorem MOD_027_reference {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String) :
    MOD_027 Nm tyOf Build (buildScript (A := A) Nm tyOf Build
      (refMerge Build (seqAct fun a _ => a) (fun _ _ => .ok none))) :=
  mod027_ref Nm tyOf Build _

/-! ## Worked examples on the reference -/

/-- ✓ Every line of MOD-027 is exercised by the reference. The subnet `ans` has an input port `in`
over its place `IN` and a transition `work` from `IN` to `OUT`; `answer` is its instance.
Composing `answer` with `in` bound to `A_IN`, a host transition `hub_kill` that takes a token from
`go` and resets `answer/IN` makes `build()` fail with "place 'answer/IN' is port 'in' of instance
'answer', bound to host place 'A_IN' at compose; reference 'A_IN' instead", whether it is added
after or before the compose call (lines 1 and 2, AC1 and AC2). A read arc or an XOR branch on
`answer/IN` fails with the same message (lines 1 and 2, AC3). Resetting `A_IN` instead builds
(line 3, AC4). Binding `in` to `answer/IN` itself, or not binding it, retires nothing, and
`hub_kill` on `answer/IN` builds (line 3, AC5, AC6). With a fusion set that lists `X` first and
`answer/IN` second, `hub_kill` on `answer/IN` builds, since fusion moves its arc to `X` (line 3,
AC7); with `answer/IN` first and `Y` second, `hub_kill` on `Y` fails, since fusion moves its arc
onto `answer/IN` (line 1, AC7). Declaring `answer/IN` builds (line 4). The instance's `work`
rewritten to take from `A_IN` and composed directly builds, and so does the compose call
(line 5). Composing `answer` a second time with `in` bound to `B_IN` keeps the first record, so
the message still points at `A_IN` (line 2). The auto-bound form binds `in` to the unrenamed place
`IN` and retires `answer/IN` too ([MOD-024]). -/
@[evidence nonvacuous MOD_027]
theorem MOD_027_nonvacuous :
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .trans (buildExKill "answer/IN")] = some (mod027ExMsg "A_IN") ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [.trans (buildExKill "answer/IN"), mod027ExBind "A_IN"] = some (mod027ExMsg "A_IN") ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .trans (mod027ExHost "peek" ["answer/IN"] none)] =
        some (mod027ExMsg "A_IN") ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN",
          .trans (mod027ExHost "pick" [] (some (.xor (.place "done") (.place "answer/IN"))))] =
        some (mod027ExMsg "A_IN") ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .trans (buildExKill "A_IN")] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "answer/IN", .trans (buildExKill "answer/IN")] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [.compose buildExInst [] [], .trans (buildExKill "answer/IN")] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .trans (buildExKill "answer/IN"), .fuse ⟨"f", ["X", "answer/IN"]⟩]
        = none ∧
    (mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .trans (buildExKill "Y"), .fuse ⟨"f", ["answer/IN", "Y"]⟩]).isSome
        = true ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", .place "answer/IN"] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [.composeDirect (mod027Twin buildExInst [("in", "A_IN")])] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN"] = none ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [mod027ExBind "A_IN", mod027ExBind "B_IN", .trans (buildExKill "answer/IN")] =
        some (mod027ExMsg "A_IN") ∧
    mod027Err (buildScript strNaming (fun _ => ()) refBuild mod027ExMg)
        [.composeAuto buildExInst [], .trans (buildExKill "answer/IN")] = some (mod027ExMsg "IN") := by
  decide
/-! ## Facts about the examples -/

section ExFacts

/-- A script whose every compose call binds at most one port. -/
def mod027SingleBinds (ops : List (Op N A)) : Bool :=
  ops.all fun op => match op.portBinds with
    | some (_, ports) => decide (ports.length ≤ 1)
    | none => true

/-- A script whose every compose call binds at most one port has one caller per port. -/
theorem mod027_oneCaller_of_single {ops : List (Op N A)} (h : mod027SingleBinds ops = true) :
    OneCallerPerPort ops := by
  intro op hop I ports hp e he e' he' q _ _
  have hl : ports.length ≤ 1 := by
    have := List.all_eq_true.1 h op hop
    rw [hp] at this
    simpa using this
  match ports, he, he', hl with
  | [x], he, he', _ =>
    rw [List.mem_singleton] at he he'
    rw [he, he']

/-- The only retirement `answer` bound to `X` makes is its port `in` over `answer/IN`. -/
theorem mod027_ex_retires {X : String} {r : Retired String} (h : RetiresPort (mod027ExBind X) r) :
    r = ⟨"answer/IN", "in", "answer", X⟩ := by
  obtain ⟨I, ports, hb, hp, hq, -, hpfx⟩ := h
  simp only [mod027ExBind, Op.portBinds, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [List.mem_singleton, Prod.mk.injEq] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [h1] at hq
  have hin : buildExInst.port "in" = some "answer/IN" := by decide
  rw [hin, Option.some.injEq] at hq
  obtain ⟨pl, po, pf, ca⟩ := r
  simp only at h1 h2 hq hpfx
  subst h1 h2 hq
  rw [hpfx]
  rfl

/-- In a script of such compose calls and calls that bind nothing, only `answer/IN` is
retired. -/
theorem mod027_ex_retiredBy {ops : List (Op String Unit)} {X : String}
    (h : ∀ op ∈ ops, op = mod027ExBind X ∨ op.portBinds = none) {q : String}
    (hq : PortRetiredBy ops q) : q = "answer/IN" := by
  obtain ⟨op, hop, r, hr, rfl⟩ := hq
  rcases h op hop with rfl | hn
  · rw [mod027_ex_retires hr]
  · obtain ⟨I, ports, hb, -⟩ := hr
    rw [hn] at hb; cases hb

/-- `answer` bound to `X` retires `answer/IN`. -/
theorem mod027_ex_retired {ops : List (Op String Unit)} {X : String} (hX : X ≠ "answer/IN")
    (h : mod027ExBind X ∈ ops) : PortRetiredBy ops "answer/IN" :=
  ⟨_, h, ⟨"answer/IN", "in", "answer", X⟩,
    ⟨buildExInst, [("in", X)], rfl, by simp, rfl, fun e => hX e.symm, rfl⟩, rfl⟩

end ExFacts

/-! ## Wrong build scripts -/

section WrongChecks

variable [DecidableEq N]

/-- A place has a record exactly when its first record exists. -/
theorem mod027_any_find (R : List (Retired N)) (q : N) :
    R.any (fun x => decide (x.place = q)) = (R.find? fun x => decide (x.place = q)).isSome := by
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true, List.find?_isSome]

/-- The recorded places a definition names, in order. -/
def mod027Recorded (R : List (Retired N)) (e : CDef N A) : List N :=
  e.namedPlaces.filter fun q => R.any fun x => decide (x.place = q)

/-- The recorded places a definition names depend only on the first records of the places it
names. -/
theorem mod027Recorded_local {R R' : List (Retired N)} {e : CDef N A}
    (h : ∀ q ∈ e.namedPlaces, R'.find? (fun x => decide (x.place = q)) =
      R.find? (fun x => decide (x.place = q))) :
    mod027Recorded R' e = mod027Recorded R e := by
  unfold mod027Recorded
  apply List.filter_congr
  intro q hq
  rw [mod027_any_find, mod027_any_find, h q hq]

/-- A place is among the recorded places a definition names when the definition names it and it
has a record. -/
theorem mem_mod027Recorded {R : List (Retired N)} {e : CDef N A} {q : N} :
    q ∈ mod027Recorded R e ↔ q ∈ e.namedPlaces ∧ ∃ x ∈ R, x.place = q := by
  unfold mod027Recorded
  rw [List.mem_filter, List.any_eq_true]
  simp

/-- A retired check that reports only a definition naming one retired place: one naming two is
let through. -/
def mod027HitOne (R : List (Retired N)) (e : CDef N A) : Option (Retired N) :=
  match e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) with
  | [] => none
  | q :: rest => if rest.all (fun q' => decide (q' = q)) then R.find? (fun x => decide (x.place = q))
    else none

/-- The one-place check is quiet where nothing is recorded. -/
theorem mod027HitOne_quiet : Mod027Quiet (mod027HitOne (N := N) (A := A)) := by
  intro R e h
  have hf : e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq hany
    obtain ⟨x, hx, hxq⟩ := List.any_eq_true.1 hany
    exact h q hq x hx (by simpa using hxq)
  unfold mod027HitOne
  rw [hf]

/-- The one-place check finds the first record of the one recorded place a definition names. -/
theorem mod027HitOne_names : Mod027Names (mod027HitOne (N := N) (A := A)) := by
  intro R e P hP hs
  have hmem : ∀ q, q ∈ e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) →
      q = P := by
    intro q hq
    rw [List.mem_filter] at hq
    obtain ⟨x, hx, hxq⟩ := List.any_eq_true.1 hq.2
    exact hs q hq.1 ⟨x, hx, by simpa using hxq⟩
  unfold mod027HitOne
  cases hL : e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) with
  | nil =>
    symm
    rw [List.find?_eq_none]
    intro x hx hxP
    have : P ∈ e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) :=
      List.mem_filter.2 ⟨hP, List.any_eq_true.2 ⟨x, hx, hxP⟩⟩
    rw [hL] at this; cases this
  | cons q rest =>
    have hq : q = P := hmem q (by rw [hL]; exact List.mem_cons_self)
    have hall : rest.all (fun q' => decide (q' = q)) = true := by
      rw [List.all_eq_true]
      intro q' hq'
      have := hmem q' (by rw [hL]; exact List.mem_cons_of_mem _ hq')
      simp [this, hq]
    subst hq
    simp only
    rw [if_pos hall]

/-- The one-place check reads only the first records of the places a definition names. -/
theorem mod027HitOne_local : Mod027Local (mod027HitOne (N := N) (A := A)) := by
  intro R R' e h
  have hf := mod027Recorded_local (e := e) h
  unfold mod027Recorded at hf
  unfold mod027HitOne
  rw [hf]
  cases hL : e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) with
  | nil => rfl
  | cons q rest =>
    have hq : q ∈ e.namedPlaces := by
      have : q ∈ e.namedPlaces.filter (fun q => R.any fun x => decide (x.place = q)) := by
        rw [hL]; exact List.mem_cons_self
      exact (List.mem_filter.1 this).1
    simp only
    rw [h q hq]

/-- A retired check that reports the right record with the caller place replaced by the retired
place: the message then points back at the place it rejects. -/
def mod027HitBack (R : List (Retired N)) (e : CDef N A) : Option (Retired N) :=
  (mod027HitDef R e).map fun r => { r with caller := r.place }

/-- The pointing-back check finds nothing exactly where the reference check finds nothing. -/
theorem mod027HitBack_none {R : List (Retired N)} {e : CDef N A} :
    mod027HitBack R e = none ↔ mod027HitDef R e = none := by
  unfold mod027HitBack
  cases mod027HitDef R e <;> simp

/-- The pointing-back check is sound. -/
theorem mod027HitBack_sound : Mod027Sound (mod027HitBack (N := N) (A := A)) :=
  fun R e h => mod027HitDef_sound R e (mod027HitBack_none.1 h)

/-- The pointing-back check is quiet where nothing is recorded. -/
theorem mod027HitBack_quiet : Mod027Quiet (mod027HitBack (N := N) (A := A)) :=
  fun R e h => mod027HitBack_none.2 (mod027HitDef_quiet R e h)

/-- The pointing-back check reads only the first records of the places a definition names. -/
theorem mod027HitBack_local : Mod027Local (mod027HitBack (N := N) (A := A)) := by
  intro R R' e h
  show (mod027HitDef R' e).map _ = (mod027HitDef R e).map _
  rw [mod027HitDef_local R R' e h]

/-- A list of places is one place, possibly repeated, or empty. -/
def mod027AllEq (L : List N) : Bool :=
  match L with
  | [] => true
  | q :: rest => rest.all fun q' => decide (q' = q)

/-- `mod027AllEq` holds when any two places of the list are equal. -/
theorem mod027AllEq_iff (L : List N) : mod027AllEq L = true ↔ ∀ a ∈ L, ∀ b ∈ L, a = b := by
  cases L with
  | nil => simp [mod027AllEq]
  | cons q rest =>
    simp only [mod027AllEq, List.all_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · intro h a ha b hb
      have ha' : a = q := by
        rcases ha with rfl | ha
        · rfl
        · exact h a ha
      have hb' : b = q := by
        rcases hb with rfl | hb
        · rfl
        · exact h b hb
      rw [ha', hb']
    · intro h a ha
      exact h a (Or.inr ha) q (Or.inl rfl)

/-- A keep test that drops a fused definition naming two different recorded places: `build()`
then succeeds without it. -/
def mod027KeepOne (R : List (Retired N)) (e : CDef N A) : Bool :=
  mod027AllEq (mod027Recorded R e)

/-- The dropping test keeps a definition naming at most one recorded place. -/
theorem mod027KeepOne_one : Mod027KeepsOne (mod027KeepOne (N := N) (A := A)) := by
  intro R e h
  unfold mod027KeepOne
  rw [mod027AllEq_iff]
  intro a ha b hb
  rw [mem_mod027Recorded] at ha hb
  exact h a ha.1 b hb.1 ha.2 hb.2

/-- The dropping test reads only the first records of the places a definition names. -/
theorem mod027KeepOne_local : Mod027KeepLocal (mod027KeepOne (N := N) (A := A)) := by
  intro R R' e h
  unfold mod027KeepOne
  rw [mod027Recorded_local h]

/-- A definition the dropping test drops stays dropped when more places are recorded. -/
theorem mod027KeepOne_mono : Mod027KeepMono (mod027KeepOne (N := N) (A := A)) := by
  intro R R' e hm hk
  cases h' : mod027KeepOne R' e with
  | false => rfl
  | true =>
    exfalso
    unfold mod027KeepOne at hk h'
    rw [mod027AllEq_iff] at h'
    have : mod027AllEq (mod027Recorded R e) = true := by
      rw [mod027AllEq_iff]
      intro a ha b hb
      rw [mem_mod027Recorded] at ha hb
      exact h' a (mem_mod027Recorded.2 ⟨ha.1, hm a ha.2⟩) b
        (mem_mod027Recorded.2 ⟨hb.1, hm b hb.2⟩)
    rw [this] at hk
    cases hk

variable [ToString N]

/-- A further check that fails as soon as the builder holds a retired record, with the message on
the first one. -/
def mod027ExtraAny (Nm : Naming N) (b : Bld N A) : Option String :=
  b.retired.head?.map (retiredMsg Nm)

omit [DecidableEq N] [ToString N] in
/-- The check reads only the retired records, which an inserted transition does not change. -/
theorem mod027ExtraAny_trans (Nm : Naming N) : Mod027ExtraTrans (mod027ExtraAny (A := A) Nm) := by
  intro x x' d hr hx; unfold mod027ExtraAny at *; rw [hr.2.1]; exact hx

omit [DecidableEq N] [ToString N] in
/-- The check reads only the retired records, which a declared place does not change. -/
theorem mod027ExtraAny_place (Nm : Naming N) : Mod027ExtraPlace (mod027ExtraAny (A := A) Nm) := by
  intro x x' q hr hx; unfold mod027ExtraAny at *; rw [hr.2.1]; exact hx

omit [ToString N] in
/-- A further check that rejects a transition naming, before fusion, a place a fusion set merges
into another. -/
def mod027ExtraMoved (b : Bld N A) : Option String :=
  if b.defs.any (fun e => e.namedPlaces.any fun p => decide (refSubst b.fusions p ≠ p)) then
    some "an arc names a place a fusion set merges away"
  else none

omit [ToString N] in
/-- The fusion check does not read the places, so declaring one keeps it passing. -/
theorem mod027ExtraMoved_place : Mod027ExtraPlace (mod027ExtraMoved (N := N) (A := A)) := by
  intro x x' q hr hx
  obtain ⟨-, -, hf, -, l₁, l₂, hl, hl'⟩ := hr
  have hd : x'.defs = x.defs := by simp [hl, hl']
  unfold mod027ExtraMoved at hx ⊢
  rw [hd, hf]; exact hx

omit [ToString N] in
/-- The fusion check reads the definitions and fusion sets, which a compose call and its twin
leave alike. -/
theorem mod027ExtraMoved_twin : Mod027ExtraTwin (mod027ExtraMoved (N := N) (A := A)) := by
  intro ps x x' hr hx
  obtain ⟨-, hd, -, hf, -, -⟩ := hr
  unfold mod027ExtraMoved at hx ⊢
  rw [hd, hf]; exact hx

omit [ToString N] in
/-- A further check that rejects a declared place that is not terminal and that no transition
names. -/
def mod027ExtraOrphan (b : Bld N A) : Option String :=
  if b.places.any (fun p => decide (p ∉ b.terminals) &&
      b.defs.all (fun e => decide (p ∉ e.namedPlaces))) then
    some "a declared place is used by no transition"
  else none

omit [ToString N] in
/-- Adding a transition keeps the unused-place check passing: a place it adds is one it names. -/
theorem mod027ExtraOrphan_trans : Mod027ExtraTrans (mod027ExtraOrphan (N := N) (A := A)) := by
  intro x x' d hr hx
  obtain ⟨ht, -, -, hp, l₁, l₂, hl, hl'⟩ := hr
  simp only [Option.toList_some] at hl'
  unfold mod027ExtraOrphan at hx ⊢
  have hnx : ¬ (x.places.any (fun p => decide (p ∉ x.terminals) &&
      x.defs.all (fun e => decide (p ∉ e.namedPlaces)))) = true := by
    intro h; rw [if_pos h] at hx; cases hx
  rw [if_neg]
  intro h
  obtain ⟨p, hpl, hc⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hnt, hnd⟩ := hc
  rw [ht] at hnt
  have hdx : ∀ e ∈ x.defs, e ∈ x'.defs := by
    intro e he; rw [hl] at he; rw [hl']
    simp only [List.mem_append, List.mem_cons] at he ⊢
    rcases he with he | he
    · exact Or.inl (Or.inl he)
    · exact Or.inr he
  rcases (hp _).1 hpl with hpl | hpl
  · apply hnx
    refine List.any_eq_true.2 ⟨p, hpl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hnt, fun e he => hnd e (hdx e he)⟩
  · exact hnd d (by rw [hl']; simp) hpl

omit [ToString N] in
/-- The unused-place check reads the places, definitions and terminal places, which a compose
call and its twin leave alike. -/
theorem mod027ExtraOrphan_twin : Mod027ExtraTwin (mod027ExtraOrphan (N := N) (A := A)) := by
  intro ps x x' hr hx
  obtain ⟨hp, hd, ht, -, -, -⟩ := hr
  unfold mod027ExtraOrphan at hx ⊢
  rw [hp, hd, ht]; exact hx

omit [ToString N] in
/-- A further check that rejects a fusion set listing a retired place. -/
def mod027ExtraFuseRetired (b : Bld N A) : Option String :=
  if b.fusions.any (fun s => s.members.any fun m => b.retired.any fun r => decide (r.place = m))
  then some "fusion member is not a place of the net" else none

omit [DecidableEq N] [ToString N] in
/-- Two places of one binding entry list of length at most one never clash. -/
theorem mod027_noClash_single [DecidableEq N] {bm : List (BindEntry N)} (h : bm.length ≤ 1)
    (a b : N) : ¬ BindClash bm a b := by
  rintro ⟨hab, e, e', ha, hb, -⟩
  unfold bindLookup at ha hb
  have hea : e.place = a := by simpa using List.find?_some ha
  have heb : e'.place = b := by simpa using List.find?_some hb
  have hme := List.mem_of_find?_eq_some ha
  have hme' := List.mem_of_find?_eq_some hb
  match bm, h, hme, hme' with
  | [], _, hme, _ => cases hme
  | [x], _, hme, hme' =>
    rw [List.mem_singleton] at hme hme'
    subst hme hme'
    exact hab (hea.symm.trans heb)
  | _ :: _ :: _, h, _, _ => simp at h

end WrongChecks

/-- `answer` composed with `in` bound to `A_IN` is a call the composition accepts, with no token
type. -/
theorem mod027_ex_accepts : mod027Accepts (fun _ : String => ()) buildExInst [("in", "A_IN")] := by
  refine ⟨by unfold PortsDistinct; decide, by unfold PortsKnown; decide, fun _ _ _ _ => rfl,
    by decide, fun d _ => ⟨?_, ?_⟩⟩
  · rintro ⟨a, -, b, -, hc⟩
    exact mod027_noClash_single (by decide) a b hc
  · rintro ⟨o, -, br, -, a, -, b, -, hc⟩
    exact mod027_noClash_single (by decide) a b hc

/-- The script without any retired check. -/
def mod027Sc0 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg (fun _ _ => none) (fun _ _ => true)
    (fun _ => none)

/-- The script whose check reports only a transition naming one retired place. -/
def mod027Sc1 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitOne (fun _ _ => true)
    (fun _ => none)

/-- The script that drops a fused transition naming two retired places and builds without it. -/
def mod027ScD : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitDef mod027KeepOne
    (fun _ => none)

/-- The script whose message points back at the retired place. -/
def mod027Sc2 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitBack (fun _ _ => true)
    (fun _ => none)

/-- The script that also rejects a transition naming, before fusion, a place fusion merges
away. -/
def mod027Sc3 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitDef (fun _ _ => true)
    mod027ExtraMoved

/-- The script that also rejects a declared place no transition names. -/
def mod027Sc4 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitDef (fun _ _ => true)
    mod027ExtraOrphan

/-- The script that fails as soon as a compose call retired a port. -/
def mod027Sc5 : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitDef (fun _ _ => true)
    (mod027ExtraAny strNaming)

/-- The script that rejects a fusion set listing a retired place. -/
def mod027Sc5b : ScriptFn String Unit :=
  mod027ScriptBy strNaming (fun _ => ()) refBuild mod027ExMg mod027HitDef (fun _ _ => true)
    mod027ExtraFuseRetired

/-- A built net whose transitions name a retired place breaks line 1. -/
theorem mod027_not_line1 {S : ScriptFn String Unit} {ops : List (Op String Unit)} {q : String}
    (hone : mod027SingleBinds ops = true) (hq : PortRetiredBy ops q)
    (h : (S ops).toOption.map (fun c => c.trans.any fun d => decide (q ∈ d.namedPlaces)) =
      some true) : ¬ mod027_line1 S := by
  intro h1
  cases hc : S ops with
  | error m => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h
    simp only [Except.toOption, Option.map_some, Option.some.injEq, List.any_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨d, hd, hqd⟩ := h
    exact (h1 ops c (mod027_oneCaller_of_single hone) hc q hq).1 d hd hqd

/-- A script that builds the twin of `answer` bound to `A_IN` followed by `post`, with no
transition naming `answer/IN`, and fails the compose call followed by `post`, breaks line 5. -/
theorem mod027_not_line5 {S : ScriptFn String Unit} {post : List (Op String Unit)}
    (hb : ∀ op ∈ post, Op.Blind op)
    (htw : (S (Op.composeDirect (mod027Twin buildExInst [("in", "A_IN")]) :: post)).toOption.map
      (fun c => c.trans.all fun d => decide ("answer/IN" ∉ d.namedPlaces)) = some true)
    (hbad : (S (mod027ExBind "A_IN" :: post)).toOption = none) :
    ¬ mod027_line5 (fun _ : String => ()) S := by
  intro h5
  cases hc : S (Op.composeDirect (mod027Twin buildExInst [("in", "A_IN")]) :: post) with
  | error m => rw [hc] at htw; cases htw
  | ok c =>
    rw [hc] at htw
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at htw
    obtain ⟨c', hc'⟩ := h5 [] post buildExInst [("in", "A_IN")] c hb
      (mod027_oneCaller_of_single (by decide)) mod027_ex_accepts hc
      (by
        intro q hq d hd
        have hq' := mod027_ex_retiredBy (X := "A_IN")
          (fun op hop => Or.inl (List.mem_singleton.1 hop)) hq
        subst hq'
        exact of_decide_eq_true (List.all_eq_true.1 htw d hd))
    have : S (mod027ExBind "A_IN" :: post) = .ok c' := hc'
    rw [this] at hbad
    cases hbad

/-- `answer` and a second instance `other` of the same subnet, `in` bound to `A_IN` and `B_IN`, and
a host transition that resets both retired places. -/
def mod027ExTwo : List (Op String Unit) :=
  [mod027ExBind "A_IN", .compose (renamedInstance strNaming buildExAns "other") [("in", "B_IN")] [],
    .trans (buildExDef "hub_kill" [⟨"go", .one⟩] none ["answer/IN", "other/IN"])]

/-! ## Mutants, one per line -/

/-- Mutant reading: MOD-027 without line 1. -/
def MOD_027_mutant_noLine1 [DecidableEq N] {T : Type} (Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line2 Nm Build S ∧ mod027_line3 Build S ∧ mod027_line4 S ∧ mod027_line5 tyOf S

/-- Mutant reading: MOD-027 with line 1 reading the built net only, not the transitions the calls
added. -/
def MOD_027_mutant_builtOnly [DecidableEq N] {T : Type} (Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line1_built S ∧ mod027_line2 Nm Build S ∧ mod027_line3 Build S ∧ mod027_line4 S ∧
    mod027_line5 tyOf S

/-- Mutant reading: MOD-027 without line 2. -/
def MOD_027_mutant_noLine2 [DecidableEq N] {T : Type} (_Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line1 S ∧ mod027_line3 Build S ∧ mod027_line4 S ∧ mod027_line5 tyOf S

/-- Mutant reading: MOD-027 without line 3. -/
def MOD_027_mutant_noLine3 [DecidableEq N] {T : Type} (Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line1 S ∧ mod027_line2 Nm Build S ∧ mod027_line4 S ∧ mod027_line5 tyOf S

/-- Mutant reading: MOD-027 without line 4. -/
def MOD_027_mutant_noLine4 [DecidableEq N] {T : Type} (Nm : Naming N) (tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line1 S ∧ mod027_line2 Nm Build S ∧ mod027_line3 Build S ∧ mod027_line5 tyOf S

/-- Mutant reading: MOD-027 without line 5. -/
def MOD_027_mutant_noLine5 [DecidableEq N] {T : Type} (Nm : Naming N) (_tyOf : N → T)
    (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  mod027_line1 S ∧ mod027_line2 Nm Build S ∧ mod027_line3 Build S ∧ mod027_line4 S

set_option maxRecDepth 20000 in
/-- The mutant without line 1 is killed by a check that lets a transition through when it names two
retired places. Bind `answer`'s port to `A_IN` and `other`'s to `B_IN`; a host transition that
resets both `answer/IN` and `other/IN` builds, though both places are retired. A transition that
names one retired place still fails with the right message, so lines 2 to 5 hold. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_noLine1_killed :
    MOD_027_mutant_noLine1 strNaming (fun _ : String => ()) refBuild mod027Sc1 ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc1 := by
  refine ⟨⟨mod027_gen_line2 mod027HitOne_names mod027KeepAll_one,
    mod027_gen_line3 mod027HitOne_quiet mod027KeepAll_one (fun _ _ _ _ h => h),
    mod027_gen_line4 (fun _ _ _ _ h => h),
    mod027_gen_line5 mod027HitOne_local mod027KeepAll_local mod027KeepAll_mono
      (fun _ _ _ _ h => h)⟩, fun h => ?_⟩
  exact mod027_not_line1 (ops := mod027ExTwo) (q := "answer/IN") (by decide)
    (mod027_ex_retired (X := "A_IN") (by decide) (by simp [mod027ExTwo])) (by decide) h.1

set_option maxRecDepth 20000 in
/-- The mutant that reads only the built net in line 1 is killed by a builder that silently drops a
transition naming two retired places. Bind `answer`'s port to `A_IN` and `other`'s to `B_IN`, and
add a host transition that resets both `answer/IN` and `other/IN`: the build succeeds, the built
net has no transition on a retired place, but the transition the caller added is gone instead of
being rejected. A transition that names one retired place is kept and fails with the right
message, so the rest of the block holds. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_builtOnly_killed :
    MOD_027_mutant_builtOnly strNaming (fun _ : String => ()) refBuild mod027ScD ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027ScD := by
  refine ⟨⟨mod027_gen_line1_built mod027HitDef_sound,
    mod027_gen_line2 mod027HitDef_names mod027KeepOne_one,
    mod027_gen_line3 mod027HitDef_quiet mod027KeepOne_one (fun _ _ _ _ h => h),
    mod027_gen_line4 (fun _ _ _ _ h => h),
    mod027_gen_line5 mod027HitDef_local mod027KeepOne_local mod027KeepOne_mono
      (fun _ _ _ _ h => h)⟩, fun h => ?_⟩
  have hok : (mod027ScD mod027ExTwo).toOption.isSome = true := by decide
  cases hS : mod027ScD mod027ExTwo with
  | error m => rw [hS] at hok; cases hok
  | ok c =>
    have hnil : fusionsOf mod027ExTwo = [] := rfl
    have hid : SubstSpec ([] : List (FusionSet String)) id :=
      ⟨fun s hs => (by cases hs), fun _ _ => rfl⟩
    exact (h.1 mod027ExTwo c (mod027_oneCaller_of_single (by decide)) hS "answer/IN"
      (mod027_ex_retired (X := "A_IN") (by decide) (by simp [mod027ExTwo]))).2
      (buildExDef "hub_kill" [⟨"go", .one⟩] none ["answer/IN", "other/IN"]) id _
      (by simp [mod027ExTwo]) (hnil ▸ hid) (fuseDef_id _) (by decide)

set_option maxRecDepth 20000 in
/-- The mutant without line 2 is killed by a check whose message points back at the retired place.
Compose `answer` with `in` bound to `A_IN` and add `hub_kill` resetting `answer/IN`: the build fails,
but the message says "bound to host place 'answer/IN' ... reference 'answer/IN' instead" instead of
pointing at `A_IN`. It still rejects every retired place and nothing else, so lines 1, 3, 4 and 5
hold. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_noLine2_killed :
    MOD_027_mutant_noLine2 strNaming (fun _ : String => ()) refBuild mod027Sc2 ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc2 := by
  refine ⟨⟨mod027_gen_line1 mod027HitBack_sound (fun _ _ => rfl),
    mod027_gen_line3 mod027HitBack_quiet mod027KeepAll_one (fun _ _ _ _ h => h),
    mod027_gen_line4 (fun _ _ _ _ h => h),
    mod027_gen_line5 mod027HitBack_local mod027KeepAll_local mod027KeepAll_mono
      (fun _ _ _ _ h => h)⟩, fun h => ?_⟩
  have hc : (mod027Sc2 [mod027ExBind "A_IN"]).toOption.map (·.terminals) = some [] := by decide
  cases hS : mod027Sc2 [mod027ExBind "A_IN"] with
  | error m => rw [hS] at hc; cases hc
  | ok c =>
    rw [hS] at hc
    have ht : c.terminals = [] := by simpa [Except.toOption] using hc
    have hnil : fusionsOf ([mod027ExBind "A_IN"] ++ ([] : List (Op String Unit))) = [] := rfl
    have hid : SubstSpec ([] : List (FusionSet String)) id :=
      ⟨fun s hs => (by cases hs), fun _ _ => rfl⟩
    obtain ⟨r, hfr, -, he⟩ := h.2.1 [mod027ExBind "A_IN"] [] (buildExKill "answer/IN") c id
      ((buildExKill "answer/IN").map id id) "answer/IN" (mod027_oneCaller_of_single (by decide))
      hS (by simp) (hnil ▸ List.Pairwise.nil) (hnil ▸ hid)
      (by decide) (fuseDef_id _) (by decide) (by simp [ht]) (by decide)
      (mod027_ex_retired (X := "A_IN") (by decide) (by simp))
      (fun q _ hq => mod027_ex_retiredBy (X := "A_IN") (by simp) hq)
    obtain ⟨l₁, op, l₂, hops, hr, -⟩ := hfr
    have hop : op = mod027ExBind "A_IN" := by
      have : op ∈ l₁ ++ op :: l₂ := by simp
      rw [← hops] at this
      simpa using this
    subst hop
    rw [mod027_ex_retires hr] at he
    have hbad : mod027Err mod027Sc2 [mod027ExBind "A_IN", .trans (buildExKill "answer/IN")] =
        some (mod027ExMsg "answer/IN") := by decide
    have hne : mod027Msg strNaming ⟨"answer/IN", "in", "answer", "A_IN"⟩ ≠ mod027ExMsg "answer/IN" := by
      decide
    have he' : mod027Sc2 [mod027ExBind "A_IN", .trans (buildExKill "answer/IN")] =
        .error (mod027Msg strNaming ⟨"answer/IN", "in", "answer", "A_IN"⟩) := he
    rw [mod027Err, he'] at hbad
    exact hne (Option.some.inj hbad)

set_option maxRecDepth 20000 in
/-- The mutant without line 3 is killed by a script that also rejects a transition naming, before
fusion, a place that fusion merges away. Compose `answer` with `in` bound to `A_IN`, declare a
fusion set that lists `X` first and `answer/IN` second, and add `hub_kill` resetting `answer/IN`:
after fusion the reset is on `X`, which is not retired, so the net must build, but the extra check
rejects it (AC7, first half). It still rejects every arc the fused net has on a retired place, and
it reads only transitions and fusion sets, so lines 1, 2, 4 and 5 hold. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_noLine3_killed :
    MOD_027_mutant_noLine3 strNaming (fun _ : String => ()) refBuild mod027Sc3 ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc3 := by
  refine ⟨⟨mod027_gen_line1 mod027HitDef_sound (fun _ _ => rfl),
    mod027_gen_line2 mod027HitDef_names mod027KeepAll_one,
    mod027_gen_line4 mod027ExtraMoved_place,
    mod027_gen_line5 mod027HitDef_local mod027KeepAll_local mod027KeepAll_mono
      mod027ExtraMoved_twin⟩, fun h => ?_⟩
  have hok : (mod027Sc3 [mod027ExBind "A_IN", .fuse ⟨"f", ["X", "answer/IN"]⟩]).toOption.map
      (·.terminals) = some [] := by decide
  cases hS : mod027Sc3 [mod027ExBind "A_IN", .fuse ⟨"f", ["X", "answer/IN"]⟩] with
  | error m => rw [hS] at hok; cases hok
  | ok c =>
    rw [hS] at hok
    have ht : c.terminals = [] := by simpa [Except.toOption] using hok
    have hfus : fusionsOf ([mod027ExBind "A_IN"] ++ [.fuse ⟨"f", ["X", "answer/IN"]⟩]) =
        [(⟨"f", ["X", "answer/IN"]⟩ : FusionSet String)] := rfl
    have hdis : FusionDisjoint [(⟨"f", ["X", "answer/IN"]⟩ : FusionSet String)] :=
      List.pairwise_singleton _ _
    have hσ := refSubst_spec hdis
    have hfd : fuseDef (refSubst [⟨"f", ["X", "answer/IN"]⟩]) (buildExKill "answer/IN") =
        .ok ((buildExKill "answer/IN").map (refSubst [⟨"f", ["X", "answer/IN"]⟩]) id) :=
      fuseDef_untouched _ _ (by decide)
    obtain ⟨c', hc'⟩ := h.2.2.1 [mod027ExBind "A_IN"] [.fuse ⟨"f", ["X", "answer/IN"]⟩]
      (buildExKill "answer/IN") c _ _ hS (by simp [Op.Blind]) (hfus ▸ hdis) (hfus ▸ hσ)
      (by decide) hfd (by decide) (by simp [ht])
      (by
        intro q hq hr
        have := mod027_ex_retiredBy (X := "A_IN") (by simp [Op.portBinds]) hr
        subst this
        revert hq
        decide)
    have hbad : (mod027Sc3 ([mod027ExBind "A_IN"] ++
        .trans (buildExKill "answer/IN") :: [.fuse ⟨"f", ["X", "answer/IN"]⟩])).toOption =
        none := by decide
    rw [hc'] at hbad
    cases hbad

set_option maxRecDepth 20000 in
/-- The mutant without line 4 is killed by a script that rejects a declared place that is not
terminal and that no transition names. Compose `answer` with `in` bound to `A_IN`: the net builds;
declaring `answer/IN` on it must still build, but this script rejects it. It still rejects exactly
the arcs on retired places, and a compose call and its twin declare the same places, so lines 1,
2, 3 and 5 hold. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_noLine4_killed :
    MOD_027_mutant_noLine4 strNaming (fun _ : String => ()) refBuild mod027Sc4 ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc4 := by
  refine ⟨⟨mod027_gen_line1 mod027HitDef_sound (fun _ _ => rfl),
    mod027_gen_line2 mod027HitDef_names mod027KeepAll_one,
    mod027_gen_line3 mod027HitDef_quiet mod027KeepAll_one mod027ExtraOrphan_trans,
    mod027_gen_line5 mod027HitDef_local mod027KeepAll_local mod027KeepAll_mono
      mod027ExtraOrphan_twin⟩, fun h => ?_⟩
  have hok : (mod027Sc4 [mod027ExBind "A_IN"]).toOption.isSome = true := by decide
  cases hS : mod027Sc4 [mod027ExBind "A_IN"] with
  | error m => rw [hS] at hok; cases hok
  | ok c =>
    obtain ⟨c', hc'⟩ := h.2.2.2.1 [mod027ExBind "A_IN"] [] "answer/IN" c (by simpa using hS)
      (by simp)
    have hbad : (mod027Sc4 ([mod027ExBind "A_IN"] ++ [.place "answer/IN"])).toOption = none := by
      decide
    rw [hc'] at hbad
    cases hbad

set_option maxRecDepth 20000 in
/-- The mutant without line 5 is killed by a builder whose retired check walks the instance's
transitions before the rewrite (the renamed body names every port place), so `build()` fails as
soon as a compose call retired a port. Compose `answer` with `in` bound to `A_IN` and nothing
else: the same transition, written directly with its arc on `A_IN`, builds, and nothing names
`answer/IN`, so the compose call must build too, but this builder fails with the message on
`answer/IN`. It still rejects every arc on a retired place with the right message, and an added
transition or place changes no record, so lines 1 to 4 hold. -/
@[evidence mutant MOD_027]
theorem MOD_027_mutant_noLine5_killed :
    MOD_027_mutant_noLine5 strNaming (fun _ : String => ()) refBuild mod027Sc5 ∧
      ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc5 :=
  ⟨⟨mod027_gen_line1 mod027HitDef_sound (fun _ _ => rfl),
    mod027_gen_line2 mod027HitDef_names mod027KeepAll_one,
    mod027_gen_line3 mod027HitDef_quiet mod027KeepAll_one (mod027ExtraAny_trans strNaming),
    mod027_gen_line4 (mod027ExtraAny_place strNaming)⟩,
    fun h => mod027_not_line5 (post := []) (by simp) (by decide) (by decide) h.2.2.2.2⟩

set_option maxRecDepth 20000 in
/-- ✗ A builder without the retired check violates MOD-027 (line 1): composing `answer` with `in`
bound to `A_IN` and adding `hub_kill` resetting `answer/IN` builds, and the built net resets a
place no transition of the instance uses any more, so the reset silently does nothing. -/
@[evidence forbids MOD_027]
theorem MOD_027_forbids_noCheck : ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc0 :=
  fun h =>
  mod027_not_line1 (ops := [mod027ExBind "A_IN", .trans (buildExKill "answer/IN")])
    (q := "answer/IN") (by decide) (mod027_ex_retired (X := "A_IN") (by decide) (by simp)) (by decide)
    h.1

set_option maxRecDepth 20000 in
/-- ✗ A builder whose fusion check rejects a fusion set listing a retired place violates MOD-027
(line 5, AC7 first half): composing `answer` with `in` bound to `A_IN`, adding `hub_kill`
resetting `answer/IN` and fusing `X` with `answer/IN` must build, because the same transitions
written directly on `A_IN` build with that fusion set and after fusion nothing names
`answer/IN`; this builder fails instead. -/
@[evidence forbids MOD_027]
theorem MOD_027_forbids_fuseRetired :
    ¬ MOD_027 strNaming (fun _ : String => ()) refBuild mod027Sc5b := fun h =>
  mod027_not_line5 (post := [.trans (buildExKill "answer/IN"), .fuse ⟨"f", ["X", "answer/IN"]⟩])
    (by simp [Op.Blind]) (by decide) (by decide) h.2.2.2.2

end Libpetri.Spec
