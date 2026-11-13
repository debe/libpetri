import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Reference.ComposeBind

set_option linter.missingDocs true

/-!
# MOD-020: Composition operation (`spec/11-modular-composition.md`)

MOD-020 is a behaviour requirement (kind B) over an abstract composition function
`C : ComposeFn N A`: what an enclosing builder holds (`Bld`), a module instance, the port bindings
of one `compose(instance, bindings)` call (port name, caller place; a list, so that a port can be
named twice) and its channel bindings (channel name, caller-side transition definition) give the
builder after the call, or a rejection with a message. Three further model parameters are shared
with neighbouring blocks: `tyOf`, the token type of a place where the place model keeps one
([MOD-022]); `Build`, the transition builder's check ([CORE-030], [IO-011], [IO-012],
[EXEC-012]); and `Mg`, the channel merge ([MOD-021]).

The block says what a successful call leaves in the builder (every instance transition that no
channel binding names, rewritten through the binding; for every channel binding, the merge of its
caller-side transition with the rewritten instance transition it names; and the places their arcs
name), when a call fails (a port bound twice, with an error naming it; an unknown port; an input or
output collision; ill-formed channel bindings), which message a failure carries when every other
transition is fine (the two collision messages, the transition builder's message), and when a
call succeeds. The witness is the reference composition `refCompose tyOf Build Mg`
(`Reference/ComposeBind.lean`); the block holds for every `tyOf`, `Build` and `Mg`.

Wrong compositions are killed: one that rejects everything, and one per line that meets a
plausible wrong reading of that line (a lazy composition that leaves the arcs on the port places,
one that accepts a re-bound port, one that ignores an unknown port, one that accepts an input or an
output collision, one that drops the collision messages or the transition builder's message, one
that rejects an empty instance, one that ignores an unknown channel). Further wrong compositions
are forbidden outright: one that drops the channel bindings, one that sends a three-port collision
to the rebuild, and one that fails a re-bound port with a message that names no port.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary of the block -/

section Vocabulary

variable {N A T : Type}

/-- **A coherent call** (ruling D35 (a)): any two port bindings whose ports expose one renamed
place bind it to one caller place. The lines that assume it claim nothing about any other call:
the runtimes keep one of the two bindings, Rust in hash order. -/
def mod020_coherent (I : Instance N A) (ports : List (String × N)) : Prop :=
  ∀ e ∈ ports, ∀ e' ∈ ports, I.port e.1 ≠ none → I.port e.1 = I.port e'.1 → e.2 = e'.2

/-- **The caller obligations of a call** (rulings D72 (ii)(b), D42 (m) and D10): the instance's
transitions and the caller-side transitions of the channel bindings have pairwise distinct names,
so no caller-side transition is bound to two channels (every runtime rejects such a call when it
records the second binding; the reference composition does not, so the lines that need the
obligation leave that call out); no caller-side transition is already a transition of the builder;
and no caller-side transition names a bound port place of the instance (Rust rewrites the caller
side through the binding before the merge, Java and TypeScript do not). -/
def mod020_fresh (b : Bld N A) (I : Instance N A) (ports : List (String × N))
    (chans : List (String × CDef N A)) : Prop :=
  (I.defs.map (·.core.name) ++ chans.map (·.2.core.name)).Nodup ∧
    (∀ c ∈ chans, c.2.core.name ∉ b.defs.map (·.core.name)) ∧
    ∀ c ∈ chans, ∀ e ∈ bindEntries I ports, e.place ∉ c.2.namedPlaces

/-- **A plain call**: no caller place it binds is a place an instance transition names, no
instance transition has two input arcs on one place ([CORE-030]), and no AND branch of an
instance transition's output specification names one place twice ([IO-011]); the last two are
true of every built body. On a call that is not plain, TypeScript reports a collision message
where Rust and Java report the transition builder's message, and Rust and Java can miss a
collision behind a place named twice in one branch. -/
def mod020_plain (I : Instance N A) (ports : List (String × N)) : Prop :=
  (∀ e ∈ ports, ∀ d ∈ I.defs, e.2 ∉ d.namedPlaces) ∧
    (∀ d ∈ I.defs, (d.core.inputs.map (·.place)).Nodup) ∧
    ∀ d ∈ I.defs, ∀ br ∈ (d.out.map Out.branches).getD [], br.Nodup

/-- **The binding checks pass**: every port is bound at most once, every bound port is a port of
the instance, every caller place has its port's token type ([MOD-022]), and the channel bindings
are well formed (no channel bound twice, every channel known, its transition a transition of the
instance, no two channels on one instance transition). -/
def mod020_checks (tyOf : N → T) (I : Instance N A) (ports : List (String × N))
    (chans : List (String × CDef N A)) : Prop :=
  PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree tyOf I ports ∧ ChansOk I chans

/-- An instance transition that no channel binding names. -/
def mod020_unchanneled (I : Instance N A) (chans : List (String × CDef N A)) (d : CDef N A) :
    Bool :=
  chans.all fun c => I.chan c.1 != some d.core.name

/-- The ports `pa` and `pb` expose the places `x` and `y`, in either order. -/
def mod020_portsOf (I : Instance N A) (x y : N) (pa pb : String) : Prop :=
  (I.port pa = some x ∧ I.port pb = some y) ∨ (I.port pa = some y ∧ I.port pb = some x)

variable [DecidableEq N]

/-- Plainness is decidable where place names are. -/
instance mod020_plain_decidable (I : Instance N A) (ports : List (String × N)) :
    Decidable (mod020_plain I ports) :=
  inferInstanceAs (Decidable ((∀ e ∈ ports, ∀ d ∈ I.defs, e.2 ∉ d.namedPlaces) ∧
    (∀ d ∈ I.defs, (d.core.inputs.map (·.place)).Nodup) ∧
    ∀ d ∈ I.defs, ∀ br ∈ (d.out.map Out.branches).getD [], br.Nodup))

/-- A definition without an input or an output collision under the resolved bindings `bm`. -/
def mod020_clean (bm : List (BindEntry N)) (d : CDef N A) : Prop :=
  ¬ InCollision bm d ∧ ¬ OutCollision bm d

end Vocabulary

section Messages

variable {N : Type} [ToString N]

/-- The input collision message of MOD-020 (the text of all three runtimes). -/
def mod020_inMsg (pfx pa pb : String) (X : N) (t : String) : String :=
  s!"ports '{pa}' and '{pb}' of instance '{pfx}' are both bound to host place '{X}'; transition '{t}' would consume from '{X}' through two input arcs. Bind them to distinct places or use one port."

/-- The output collision message of MOD-020 (the text of all three runtimes). -/
def mod020_outMsg (pfx pa pb : String) (X : N) (t : String) : String :=
  s!"ports '{pa}' and '{pb}' of instance '{pfx}' are both bound to host place '{X}'; transition '{t}' would produce into '{X}' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port."

end Messages

/-! ## MOD-020: Composition Operation (port mapping by structural rewrite) -/

requirement MOD_020
  id "MOD-020"
  title "Composition Operation (port mapping by structural rewrite)"
  kind B
  scope "every compose(instance, bindings) call of an enclosing net builder"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* a coherent `compose(instance, bindings)` call that meets the caller obligations succeeds, the enclosing builder *shall* hold its earlier transitions followed by one transition per instance transition, among them, in the instance's order, every instance transition that no channel binding names with each bound port place replaced by its caller place in every arc and in the output specification and its name, timing, priority and action unchanged, and, for every channel binding, the [MOD-021] merge of its caller-side transition with the instance transition it names after the rewrite, and its places *shall* be its earlier places and the places its new transitions name."
        "*If* one `compose(...)` call binds a port name more than once, no channel name more than once and no caller-side transition to more than one channel, *then* the call *shall* fail with an error naming a port it binds more than once."
        "*If* a `compose(...)` call binds a port name that the instance does not declare, *then* the call *shall* fail."
        "*If* a coherent `compose(...)` call gives a transition of the instance an input collision, *then* the call *shall* fail."
        "*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an input collision and no output collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the input collision message above, naming the instance prefix, a port exposing each of two places on which input arcs of `t` collide, in either order, their caller place and `t`."
        "*If* a coherent `compose(...)` call gives a transition of the instance an output collision, *then* the call *shall* fail."
        "*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an output collision and no input collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the output collision message above, naming the instance prefix, a port exposing each of two places that collide in one AND branch of the output specification of `t`, in either order, their caller place and `t`."
        "*If* a coherent and plain `compose(...)` call passes the binding checks and has no collision, every instance transition before a transition `t` passes the checks of the transition builder after the rewrite, and `t` after the rewrite does not, *then* the call *shall* fail with the transition builder's message for `t` after the rewrite."
        "*When* a coherent `compose(...)` call that meets the caller obligations passes the binding checks, has no collision, every instance transition passes the checks of the transition builder after the rewrite, and every channel merge of [MOD-021] succeeds, the call *shall* succeed."
        "*If* a `compose(...)` call binds a channel name more than once, binds a channel that the instance does not declare, binds a channel whose transition is not a transition of the instance, or binds two channels to one instance transition, *then* the call *shall* fail."
  reading "For every token-type map tyOf, transition-builder check Build, channel merge Mg and composition function C (a builder b, an instance I, port bindings ports and channel bindings chans give the builder after the call, or a rejection), where bm is bindEntries I ports (each bound port's renamed place, port name and caller place), bindSubst bm sends a bound port place to its caller place and keeps every other place, rewriteDef bm d is d with every place sent through bindSubst bm, 'coherent' is mod020_coherent, 'fresh' (the caller obligations) is mod020_fresh, 'plain' is mod020_plain, 'the binding checks pass' is mod020_checks and 'clean' is mod020_clean (no input and no output collision):"
          "line 1: on a coherent, fresh call, if C succeeds with b', then b'.defs is b.defs followed by a list ms with one entry per instance definition, the instance definitions no channel names, each with its TransDef mapped through bindSubst bm (TransDef.map (bindSubst bm) id: every arc and output place through the map, name, timing, priority and action kept), form a sublist of ms (as TransDef, in order), for every channel binding c and instance definition d that c's channel names, Mg merges c's caller-side definition with rewriteDef bm d into some entry of ms, and a place is a place of b' exactly when it is a place of b or a place some definition of ms names;"
          "line 2: if no channel name is bound twice, no caller-side transition is bound to two channels (the caller-side definitions of the channel bindings have pairwise distinct names) and some port name is bound twice, C fails with a message that contains a port name bound at least twice;"
          "line 3: if some binding names a port the instance does not declare, C fails;"
          "line 4: on a coherent call, if some instance definition has an input collision (InCollision bm d), C fails;"
          "line 5: on a coherent, plain call whose binding checks pass, if the instance definitions are pre ++ d :: post, every definition of pre is clean and passes Build after the rewrite, every definition of post is clean, and d has an input collision and no output collision, then C fails with mod020_inMsg I.pfx pa pb (bindSubst bm x) d.core.name for two input places x and y of d that collide (BindClash bm x y) and ports pa and pb exposing x and y in either order;"
          "line 6: on a coherent call, if some instance definition has an output collision (OutCollision bm d), C fails;"
          "line 7: as line 5 for an output collision of d (d has an output collision and no input collision), with mod020_outMsg, for two places x and y of one AND branch of d's output specification that collide;"
          "line 8: on a coherent, plain call whose binding checks pass, if the instance definitions are pre ++ d :: post, every definition of pre is clean and passes Build after the rewrite, d and every definition of post are clean, and Build rejects d after the rewrite with message m, then C fails with m;"
          "line 9: on a coherent, fresh call whose binding checks pass, if every instance definition is clean and passes Build after the rewrite, and Mg merges the caller-side definition of every channel binding with the rewritten instance definition it names, C succeeds;"
          "line 10: if the channel bindings are ill formed (not ChansOk: a channel bound twice, an unknown channel, a channel whose transition is not an instance definition, or two channels on one instance definition), C fails."
  assumes "Model scope. Bld (Reference/ComposeBind.lean) is what the enclosing builder holds: its places and transition definitions (CDef) in the order added, and what composition leaves for build() (retired ports, contributions, fusion sets). The composition rejects by failing; Rust panics, Java throws IllegalArgumentException or IllegalStateException, TypeScript throws an Error, Python raises through the Rust panic. The runtimes compose in rust/libpetri-core/src/petri_net.rs (compose_internal, apply_composition, reject_port_collision) with compose.rs (bind_port, bind_channel), java/src/main/java/org/libpetri/core/PetriNet.java (composeInternal, rejectPortCollisions, applyComposition) with ComposeBindings.java, and typescript/src/core/petri-net.ts (applyComposition, rejectPortBindingCollision) with compose-bindings.ts. Item 1 (each binding maps a port name, resolved on the instance, to a caller place) is the binding list ports and bindEntries. A script ends at its first rejected call. A caller that catches a failed compose and goes on with the same builder is out of scope: Rust consumes the builder (PetriNetBuilder::compose takes self by value, rust/libpetri-core/src/petri_net.rs) and Python makes it unusable (rust/libpetri-py/src/model.rs, PyPetriNetBuilder::take_builder), while Java (composeInternal records the retired ports before applyComposition runs, and applyComposition adds each channel merge as it goes, java/src/main/java/org/libpetri/core/PetriNet.java) and TypeScript (applyComposition records the retired ports and adds each channel merge as it goes, typescript/src/core/petri-net.ts) may keep the retired-port records and merged transitions of the failed call."
          "Ruling D35 (a): two ports may expose one body place (MOD-003). A call that binds two such ports to different caller places has no defined outcome: Rust keeps one binding in hash order and Java the last one put (compose_internal in rust/libpetri-core/src/petri_net.rs, composeInternal in java/src/main/java/org/libpetri/core/PetriNet.java), and the reference keeps the first. Lines 1 and 4 to 9 are stated on coherent calls only (mod020_coherent); lines 2, 3 and 10 hold of every call. The prose of the spec says so in the definition of a coherent call."
          "The caller obligations (mod020_fresh), assumed by line 1 and line 9. Ruling D72 (ii)(b): binding one caller-side transition to two channels of one instance in one call is a compose-time error naming the transition and both channels (AC6). Every runtime rejects it when it records the second channel binding, with the message Transition '<t>' is already bound to channel '<c1>'; it cannot also be bound to channel '<c2>' (MOD-020) (rust/libpetri-core/src/compose.rs bind_channel, java/src/main/java/org/libpetri/core/ComposeBindings.java bindChannel, typescript/src/core/compose-bindings.ts bindChannel; Python raises it through the Rust panic). The runtimes compare the caller transition by identity (Rust by its id, Java by ==, TypeScript by ===); the block reads one transition as one name (ruling D23). The reference composition refCompose (Reference/ComposeBind.lean) does not reject such a call, so no line states the rejection; lines 1 and 9 treat it as a caller obligation: the instance's transitions and the caller-side transitions of the channel bindings have pairwise distinct names, and the block claims nothing about the outcome of a call that breaks it. That premise is the part of ruling D10 (transition names are assumed distinct, ruling D23; no builder checks them) that the name-keyed staging maps of one call need; it does not exclude an instance transition whose name the builder already holds, so composing one instance twice is covered, and every runtime then appends the second copy (Java holds transitions in a LinkedHashSet of objects without a structural equals, the transitions field of PetriNet.Builder, java/src/main/java/org/libpetri/core/PetriNet.java). Ruling D42 (m): a caller-side transition already in the builder is replaced by the merge in Java and TypeScript and kept beside it in Rust, so the caller obligations also exclude it. Rust rewrites the caller-side transition through the binding before the merge (petri_net.rs apply_composition, substitute_places) and Java and TypeScript merge it as given, so the caller obligations also exclude a caller-side transition that names a bound port place of the instance."
          "Ruling D72 (i)(a): a port re-bound in one call fails with an error naming the port. Every runtime rejects at the second binding with the message Port '<name>' is already bound (rust/libpetri-core/src/compose.rs bind_port, java/src/main/java/org/libpetri/core/ComposeBindings.java bindPort, typescript/src/core/compose-bindings.ts bindPort); Java's Map overload cannot name a port twice. Line 2 reads 'naming' as 'the message contains the text of the port name' (MsgNames, as in MOD-006); so a message that happens to contain a short port name meets it, and an empty port name is contained in every message. MOD_020_forbids_genericDup shows the line rejects a message that does not contain the port. With several re-bound ports the runtimes name the first one re-bound, and line 2 asks for one of them. The sentence and line 2 are premised on no channel being bound twice: a call is a list of bindings that every runtime records through one binding builder in the caller's order (bind_port and bind_channel in rust/libpetri-core/src/compose.rs, bindPort and bindChannel in java/src/main/java/org/libpetri/core/ComposeBindings.java and typescript/src/core/compose-bindings.ts), so when a channel is also bound twice and its duplicate comes first, the call fails with Channel '<name>' is already bound, which names no port. A call that binds a channel twice fails by line 10. For the same reason the sentence and line 2 are premised on no caller-side transition being bound to more than one channel: the binding builder rejects the second channel binding of one caller transition when it records it (bind_channel, bindChannel), so when that binding comes before the re-bound port the call fails with a message that names the transition and two channels and no port. Line 2 reads that premise as pairwise distinct names of the caller-side definitions, the block's reading of one transition (ruling D23)."
          "Line 3 (an unknown port fails) is the new EARS sentence for what every runtime does (Rust compose_internal panics with the known ports, Java and TypeScript resolve the port through instance.port, which fails, MOD-011 AC4). Line 10 (ill-formed channel bindings fail) is what every runtime does: a channel bound twice fails in bind_channel / bindChannel (rust/libpetri-core/src/compose.rs, java/src/main/java/org/libpetri/core/ComposeBindings.java, typescript/src/core/compose-bindings.ts); an unknown channel fails in apply_composition with the known channels (rust/libpetri-core/src/petri_net.rs) and through instance.channel in Java and TypeScript; a second channel on one instance transition finds that transition already merged away and fails (the internal-invariant panic of Rust apply_composition, the IllegalStateException of Java applyComposition, the Error of TypeScript applyComposition in typescript/src/core/petri-net.ts); a channel whose transition is missing cannot come from a built subnet definition. The messages are not stated. Line 9 assumes the binding checks pass (mod020_checks): a caller place of another token type than its port's is MOD-022's line."
          "Clauses 2 to 5 and the reworded clauses 3 and 4 (ruling D20, clashes mod-b#7 and mod-b#9) are line 1. Clause 2 is the rewrite TransDef.map (bindSubst bm) id, which renames every input, inhibitor, read and reset place and every output-specification place, and keeps the name, the timing, the priority and the action. Clause 3: every runtime adds the places the arcs of the new transitions name (builder auto-collection: the transition() calls that end apply_composition in rust/libpetri-core/src/petri_net.rs and applyComposition in java/src/main/java/org/libpetri/core/PetriNet.java and typescript/src/core/petri-net.ts), so an internal place no arc names is not added. The place clause compares places by the place model's equality; TypeScript keys its builder's places by name and keeps the first Place object of a name (the _places map of PetriNetBuilder and its addPlace, typescript/src/core/petri-net.ts), so a caller Place object that has the name of a place the builder holds adds no second place. Clause 4: a transition a channel binding names is replaced by its merge with the caller-side transition; line 1 says the merge Mg of the caller side with the rewritten instance transition is among the new transitions, and fixes the number of new transitions and the order of the unmerged ones. The slot of a merge differs (Rust the instance transition's slot, Java and TypeScript the merges first, ruling D42 (3) unspecified) and is not stated; what the merge holds is MOD-021's (over Mg). Line 1 compares TransDef, not CDef: the declared-to-actual correspondence is MOD-031's. The MOD-021 rules (c) and (d) that a merge MUST be rejected at compose time are line 1 with MOD-021's Mg: a call whose merge fails cannot succeed (mod020_mergeFails)."
          "Clause 5 (eager) is line 1: the state the call returns already holds the rewritten transitions. Its consequence mod020_eager states that no unmerged new transition names a bound port place when no caller place is itself a bound port place; that build() rejects an arc on a retired port place is MOD-027's. The sentence 'The result of composition over the enclosing builder MUST be observationally indistinguishable from a hand-written flat net' and AC4 are MOD-023's (composition wave W8)."
          "The input and output collision lines (4 to 7) are stated for two different bound port places sent to one caller place (InCollision, OutCollision), as Rust and Java check (reject_port_collision in rust/libpetri-core/src/petri_net.rs, rejectPortCollisions in java/src/main/java/org/libpetri/core/PetriNet.java). An output collision is taken inside one AND branch of Out.branches, which flattens nested Ands (the sentence 'A branch is taken after flattening nested `And`s, as in [IO-011].'), and two places in different Xor alternatives are in different branches, so they are no collision (the sentence 'Two ports that land in **different** `Xor` alternatives are not a port-binding collision, because each alternative still names the place once.'). TypeScript compares every input place after the substitution (rejectPortBindingCollision in typescript/src/core/petri-net.ts), so it also prints the collision message for a caller place that an instance transition already names under its own name, or for two input arcs on one unbound place; Rust and Java skip a pair of one place named twice in one AND branch and can then miss a collision in that branch. Lines 5, 7 and 8 assume a plain call (mod020_plain), where the three checks agree and which every built body meets but for the caller places. Lines 4 and 6 claim rejection only: the accepted set is the same in every runtime, since a collision makes the rewritten transition fail CORE-030 or IO-011 when the rebuild meets it."
          "Lines 5, 7 and 8 state a message only when every other transition is fine (skeptic correction S3 of the composition design). Rust and TypeScript check transition by transition, collision first and then the rebuild (the loop over the renamed body in apply_composition, rust/libpetri-core/src/petri_net.rs, and in applyComposition, typescript/src/core/petri-net.ts); Java checks every port pair for collisions before any rebuild (composeInternal calls rejectPortCollisions before applyComposition, java/src/main/java/org/libpetri/core/PetriNet.java). So the lines assume every transition before t passes, every transition after t has no collision, and t has a collision of one kind only. When several pairs of t collide, the runtimes name different pairs (Rust and TypeScript the first input arc whose caller place repeats, Java the first port pair in code-point order of the port names), so the lines ask for some colliding pair of t; MOD_020_forbids_threePortToBuild shows they reject a check that only reports a pair of two ports and sends three to the rebuild. Rust and TypeScript name the two ports in input-arc order, Java in code-point order of the port names (clash mod-b#15), so the lines accept either order. Where two ports expose one place, TypeScript names the last port of the instance on that place, which need not be a bound one, so the lines name some port exposing each place (mod020_portsOf), and the spec's MUST says the same."
          "Line 8 delegates the message to Build (skeptic correction S6): the block holds for every Build. With the reference builder refBuild, Xor(a, b) bound to Xor(X, X) fails with the IO-012 ambiguity message and an input arc and a read arc bound to one place with the EXEC-012 message; those messages are IO-012's and EXEC-012's lines. So the sentence 'If the substitution makes two distinct alternatives claim the same set of places, such as `Xor(a, b)` becoming `Xor(X, X)`, then rebuilding the transition shall fail with the [IO-012] ambiguity message, which names the transition, the two output branches and the places.' is line 8 with IO-012, shown on the reference by MOD_020_nonvacuous (bindEx_xorAmbiguous). The sentence 'Other effects of binding two ports to one place (an input and an output, an input and an inhibitor) are unchanged: they are legal arcs with their usual semantics.' is line 9 where Build accepts the rewritten transition, and line 8 where it does not: whether such arcs are legal is Build's (CORE-030, IO-011, EXEC-012). The sentence 'The checks apply wherever [MOD-020] bindings are processed, so the auto-bound form of [MOD-024] is covered too.' is MOD-024's (its lines over refAuto). The sentence 'Without this check the rebuild would fail on [CORE-030] AC3 with a message that names only the rewritten transition, not the binding that caused it.' is informative."
          "AC1 (every arc that referenced the port's renamed place now references P) is line 1 and mod020_eager; MOD_020_nonvacuous shows it on the reference (Join under s with a, b and out bound to X, Y and P gives s/join over X, Y and P). AC2 (internal places that an arc names appear under their renamed names) is line 1's place clause. AC3 (transition count after a call without channel bindings is the prior count plus the instance's) is line 1's length clause (mod020_count). AC5 (a port bound twice is rejected with an error naming the port) is line 2 (MOD_020_nonvacuous: Port 'a' is already bound). AC6 (one caller transition bound to two channels is rejected) is what every runtime does (the caller obligations above) and is not stated: the reference composition accepts such a call, so a line for it needs refCompose to reject it first. AC7 (ports a and b of s bound to X with join consuming from both is rejected with the collision message; with no transition consuming from both it is accepted) is lines 4, 5 and 9 (MOD_020_nonvacuous). AC8 (And(a, b) rejected with the output collision message; Xor(a, b) rejected with the IO-012 message) is lines 6, 7 and 8 (MOD_020_nonvacuous). The channel merge of clause 4 is line 1 (MOD_020_nonvacuous: channel go of C bound to host leaves the one transition host)."
  signoff "2026-11-13 f5810a9e911aa811 ai"
  statement : ∀ {N A T : Type} [DecidableEq N] [ToString N], (N → T) →
      (Trans N → Option String) → (CDef N A → CDef N A → Except String (CDef N A)) →
      ComposeFn N A → Prop :=
    fun {N A _T} [DecidableEq N] [ToString N] tyOf Build Mg C =>
      (∀ b I ports chans b', mod020_coherent I ports → mod020_fresh b I ports chans →
        C b I ports chans = .ok b' →
        ∃ ms, b'.defs = b.defs ++ ms ∧ ms.length = I.defs.length ∧
          ((I.defs.filter (mod020_unchanneled I chans)).map
              (fun d => d.toTransDef.map (bindSubst (bindEntries I ports)) id)).Sublist
            (ms.map CDef.toTransDef) ∧
          (∀ d ∈ I.defs, ∀ c ∈ chans, I.chan c.1 = some d.core.name →
            ∃ m ∈ ms, Mg c.2 (rewriteDef (bindEntries I ports) d) = .ok m) ∧
          ∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ ∃ d ∈ ms, p ∈ d.namedPlaces) ∧
      (∀ b I ports chans, (chans.map (·.1)).Nodup → ¬ PortsDistinct ports →
        (chans.map (·.2.core.name)).Nodup →
        ∃ n m, 2 ≤ (ports.map (·.1)).count n ∧ C b I ports chans = .error m ∧
          MsgNames m n) ∧
      (∀ b I ports chans, ¬ PortsKnown I ports → ∃ m, C b I ports chans = .error m) ∧
      (∀ b I ports chans, ∀ d ∈ I.defs, mod020_coherent I ports →
        InCollision (bindEntries I ports) d → ∃ m, C b I ports chans = .error m) ∧
      (∀ (b : Bld N A) (I : Instance N A) ports chans (pre : List (CDef N A)) (d : CDef N A)
          (post : List (CDef N A)), mod020_checks tyOf I ports chans →
        mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
        (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
          Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
        (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
        ¬ OutCollision (bindEntries I ports) d → InCollision (bindEntries I ports) d →
        ∃ x ∈ d.core.inputs.map (·.place), ∃ y ∈ d.core.inputs.map (·.place),
          BindClash (bindEntries I ports) x y ∧ ∃ pa pb, mod020_portsOf I x y pa pb ∧
            C b I ports chans =
              .error (mod020_inMsg I.pfx pa pb (bindSubst (bindEntries I ports) x) d.core.name)) ∧
      (∀ b I ports chans, ∀ d ∈ I.defs, mod020_coherent I ports →
        OutCollision (bindEntries I ports) d → ∃ m, C b I ports chans = .error m) ∧
      (∀ (b : Bld N A) (I : Instance N A) ports chans (pre : List (CDef N A)) (d : CDef N A)
          (post : List (CDef N A)), mod020_checks tyOf I ports chans →
        mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
        (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
          Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
        (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
        ¬ InCollision (bindEntries I ports) d → OutCollision (bindEntries I ports) d →
        ∃ o, d.out = some o ∧ ∃ br ∈ o.branches, ∃ x ∈ br, ∃ y ∈ br,
          BindClash (bindEntries I ports) x y ∧ ∃ pa pb, mod020_portsOf I x y pa pb ∧
            C b I ports chans =
              .error (mod020_outMsg I.pfx pa pb (bindSubst (bindEntries I ports) x) d.core.name)) ∧
      (∀ (b : Bld N A) (I : Instance N A) ports chans (pre : List (CDef N A)) (d : CDef N A)
          (post : List (CDef N A)) m, mod020_checks tyOf I ports chans →
        mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
        (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
          Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
        (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
        mod020_clean (bindEntries I ports) d →
        Build (rewriteDef (bindEntries I ports) d).toTrans = some m →
        C b I ports chans = .error m) ∧
      (∀ b I ports chans, mod020_checks tyOf I ports chans → mod020_coherent I ports →
        mod020_fresh b I ports chans →
        (∀ d ∈ I.defs, mod020_clean (bindEntries I ports) d ∧
          Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
        (∀ d ∈ I.defs, ∀ c ∈ chans, I.chan c.1 = some d.core.name →
          ∃ m, Mg c.2 (rewriteDef (bindEntries I ports) d) = .ok m) →
        ∃ b', C b I ports chans = .ok b') ∧
      (∀ b I ports chans, ¬ ChansOk I chans → ∃ m, C b I ports chans = .error m)

/- The pinned readable form of MOD-020: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_020 : {N A T : Type} →
  [DecidableEq N] →
    [ToString N] →
      (N → T) →
        (Reference.Trans N → Option String) → (CDef N A → CDef N A → Except String (CDef N A)) → ComposeFn N A → Prop :=
fun {N A _T} [DecidableEq N] [ToString N] tyOf Build Mg C =>
  (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)) (b' : Bld N A),
      mod020_coherent I ports →
        mod020_fresh b I ports chans →
          C b I ports chans = Except.ok b' →
            ∃ ms,
              b'.defs = b.defs ++ ms ∧
                ms.length = I.defs.length ∧
                  (List.map (fun d => TransDef.map (bindSubst (bindEntries I ports)) id d.toTransDef)
                          (List.filter (mod020_unchanneled I chans) I.defs)).Sublist
                      (List.map CDef.toTransDef ms) ∧
                    (∀ d ∈ I.defs,
                        ∀ c ∈ chans,
                          I.chan c.1 = some d.core.name →
                            ∃ m ∈ ms, Mg c.2 (rewriteDef (bindEntries I ports) d) = Except.ok m) ∧
                      ∀ (p : N), p ∈ b'.places ↔ p ∈ b.places ∨ ∃ d ∈ ms, p ∈ d.namedPlaces) ∧
    (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
        (List.map (fun x => x.1) chans).Nodup →
          ¬PortsDistinct ports →
            (List.map (fun x => x.2.core.name) chans).Nodup →
              ∃ n m,
                2 ≤ List.count n (List.map (fun x => x.1) ports) ∧ C b I ports chans = Except.error m ∧ MsgNames m n) ∧
      (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
          ¬PortsKnown I ports → ∃ m, C b I ports chans = Except.error m) ∧
        (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
            ∀ d ∈ I.defs,
              mod020_coherent I ports → InCollision (bindEntries I ports) d → ∃ m, C b I ports chans = Except.error m) ∧
          (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A))
              (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)),
              mod020_checks tyOf I ports chans →
                mod020_coherent I ports →
                  mod020_plain I ports →
                    I.defs = pre ++ d :: post →
                      (∀ e ∈ pre,
                          mod020_clean (bindEntries I ports) e ∧
                            Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
                        (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
                          ¬OutCollision (bindEntries I ports) d →
                            InCollision (bindEntries I ports) d →
                              ∃ x ∈ List.map (fun x => x.place) d.core.inputs,
                                ∃ y ∈ List.map (fun x => x.place) d.core.inputs,
                                  BindClash (bindEntries I ports) x y ∧
                                    ∃ pa pb,
                                      mod020_portsOf I x y pa pb ∧
                                        C b I ports chans =
                                          Except.error
                                            (mod020_inMsg I.pfx pa pb (bindSubst (bindEntries I ports) x)
                                              d.core.name)) ∧
            (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
                ∀ d ∈ I.defs,
                  mod020_coherent I ports →
                    OutCollision (bindEntries I ports) d → ∃ m, C b I ports chans = Except.error m) ∧
              (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A))
                  (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)),
                  mod020_checks tyOf I ports chans →
                    mod020_coherent I ports →
                      mod020_plain I ports →
                        I.defs = pre ++ d :: post →
                          (∀ e ∈ pre,
                              mod020_clean (bindEntries I ports) e ∧
                                Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
                            (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
                              ¬InCollision (bindEntries I ports) d →
                                OutCollision (bindEntries I ports) d →
                                  ∃ o,
                                    d.out = some o ∧
                                      ∃ br ∈ o.branches,
                                        ∃ x ∈ br,
                                          ∃ y ∈ br,
                                            BindClash (bindEntries I ports) x y ∧
                                              ∃ pa pb,
                                                mod020_portsOf I x y pa pb ∧
                                                  C b I ports chans =
                                                    Except.error
                                                      (mod020_outMsg I.pfx pa pb (bindSubst (bindEntries I ports) x)
                                                        d.core.name)) ∧
                (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A))
                    (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)) (m : String),
                    mod020_checks tyOf I ports chans →
                      mod020_coherent I ports →
                        mod020_plain I ports →
                          I.defs = pre ++ d :: post →
                            (∀ e ∈ pre,
                                mod020_clean (bindEntries I ports) e ∧
                                  Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
                              (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
                                mod020_clean (bindEntries I ports) d →
                                  Build (rewriteDef (bindEntries I ports) d).toTrans = some m →
                                    C b I ports chans = Except.error m) ∧
                  (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
                      mod020_checks tyOf I ports chans →
                        mod020_coherent I ports →
                          mod020_fresh b I ports chans →
                            (∀ d ∈ I.defs,
                                mod020_clean (bindEntries I ports) d ∧
                                  Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
                              (∀ d ∈ I.defs,
                                  ∀ c ∈ chans,
                                    I.chan c.1 = some d.core.name →
                                      ∃ m, Mg c.2 (rewriteDef (bindEntries I ports) d) = Except.ok m) →
                                ∃ b', C b I ports chans = Except.ok b') ∧
                    ∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
                      ¬ChansOk I chans → ∃ m, C b I ports chans = Except.error m
-/
#guard_msgs in #print MOD_020

/-! ### The ten lines, named (for the mutants) -/

section Lines

variable {N A T : Type} [DecidableEq N] [ToString N]

/-- What line 1 asks of the outcome `r` of one call: the shape of a success. -/
def mod020_P1 (Mg : CDef N A → CDef N A → Except String (CDef N A)) (b : Bld N A)
    (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  ∀ b', mod020_coherent I ports → mod020_fresh b I ports chans → r = .ok b' →
    ∃ ms, b'.defs = b.defs ++ ms ∧ ms.length = I.defs.length ∧
      ((I.defs.filter (mod020_unchanneled I chans)).map
          (fun d => d.toTransDef.map (bindSubst (bindEntries I ports)) id)).Sublist
        (ms.map CDef.toTransDef) ∧
      (∀ d ∈ I.defs, ∀ c ∈ chans, I.chan c.1 = some d.core.name →
        ∃ m ∈ ms, Mg c.2 (rewriteDef (bindEntries I ports) d) = .ok m) ∧
      ∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ ∃ d ∈ ms, p ∈ d.namedPlaces

/-- What line 2 asks of the outcome of one call: on a call that binds no channel twice and no
caller-side transition to two channels, a port bound twice fails, naming such a port. -/
def mod020_P2 (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  (chans.map (·.1)).Nodup → ¬ PortsDistinct ports → (chans.map (·.2.core.name)).Nodup →
    ∃ n m, 2 ≤ (ports.map (·.1)).count n ∧ r = .error m ∧ MsgNames m n

/-- What line 3 asks of the outcome of one call: an unknown port fails. -/
def mod020_P3 (I : Instance N A) (ports : List (String × N)) (r : Except String (Bld N A)) :
    Prop :=
  ¬ PortsKnown I ports → ∃ m, r = .error m

/-- What line 4 asks of the outcome of one call: an input collision fails. -/
def mod020_P4 (I : Instance N A) (ports : List (String × N)) (r : Except String (Bld N A)) :
    Prop :=
  ∀ d ∈ I.defs, mod020_coherent I ports → InCollision (bindEntries I ports) d → ∃ m, r = .error m

/-- What line 5 asks of the outcome of one call: the input collision message, when every other
transition is fine. -/
def mod020_P5 (tyOf : N → T) (Build : Trans N → Option String) (I : Instance N A)
    (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  ∀ (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)),
    mod020_checks tyOf I ports chans →
    mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
    (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
      Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
    (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
    ¬ OutCollision (bindEntries I ports) d → InCollision (bindEntries I ports) d →
    ∃ x ∈ d.core.inputs.map (·.place), ∃ y ∈ d.core.inputs.map (·.place),
      BindClash (bindEntries I ports) x y ∧ ∃ pa pb, mod020_portsOf I x y pa pb ∧
        r = .error (mod020_inMsg I.pfx pa pb (bindSubst (bindEntries I ports) x) d.core.name)

/-- What line 6 asks of the outcome of one call: an output collision fails. -/
def mod020_P6 (I : Instance N A) (ports : List (String × N)) (r : Except String (Bld N A)) :
    Prop :=
  ∀ d ∈ I.defs, mod020_coherent I ports → OutCollision (bindEntries I ports) d → ∃ m, r = .error m

/-- What line 7 asks of the outcome of one call: the output collision message, when every other
transition is fine. -/
def mod020_P7 (tyOf : N → T) (Build : Trans N → Option String) (I : Instance N A)
    (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  ∀ (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)),
    mod020_checks tyOf I ports chans →
    mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
    (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
      Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
    (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
    ¬ InCollision (bindEntries I ports) d → OutCollision (bindEntries I ports) d →
    ∃ o, d.out = some o ∧ ∃ br ∈ o.branches, ∃ x ∈ br, ∃ y ∈ br,
      BindClash (bindEntries I ports) x y ∧ ∃ pa pb, mod020_portsOf I x y pa pb ∧
        r = .error (mod020_outMsg I.pfx pa pb (bindSubst (bindEntries I ports) x) d.core.name)

/-- What line 8 asks of the outcome of one call: the transition builder's message of a single
cause. -/
def mod020_P8 (tyOf : N → T) (Build : Trans N → Option String) (I : Instance N A)
    (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  ∀ (pre : List (CDef N A)) (d : CDef N A) (post : List (CDef N A)) m,
    mod020_checks tyOf I ports chans →
    mod020_coherent I ports → mod020_plain I ports → I.defs = pre ++ d :: post →
    (∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
      Build (rewriteDef (bindEntries I ports) e).toTrans = none) →
    (∀ e ∈ post, mod020_clean (bindEntries I ports) e) →
    mod020_clean (bindEntries I ports) d →
    Build (rewriteDef (bindEntries I ports) d).toTrans = some m →
    r = .error m

/-- What line 9 asks of the outcome of one call: acceptance. -/
def mod020_P9 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (b : Bld N A) (I : Instance N A)
    (ports : List (String × N)) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  mod020_checks tyOf I ports chans → mod020_coherent I ports → mod020_fresh b I ports chans →
    (∀ d ∈ I.defs, mod020_clean (bindEntries I ports) d ∧
      Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
    (∀ d ∈ I.defs, ∀ c ∈ chans, I.chan c.1 = some d.core.name →
      ∃ m, Mg c.2 (rewriteDef (bindEntries I ports) d) = .ok m) →
    ∃ b', r = .ok b'

/-- What line 10 asks of the outcome of one call: ill-formed channel bindings fail. -/
def mod020_P10 (I : Instance N A) (chans : List (String × CDef N A))
    (r : Except String (Bld N A)) : Prop :=
  ¬ ChansOk I chans → ∃ m, r = .error m

/-- Line 1 of MOD-020: the shape of a success. -/
def mod020_line1 (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) :
    Prop :=
  ∀ b I ports chans, mod020_P1 Mg b I ports chans (C b I ports chans)
/-- Line 2 of MOD-020: a port bound twice. -/
def mod020_line2 (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P2 ports chans (C b I ports chans)
/-- Line 3 of MOD-020: an unknown port. -/
def mod020_line3 (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P3 I ports (C b I ports chans)
/-- Line 4 of MOD-020: an input collision. -/
def mod020_line4 (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P4 I ports (C b I ports chans)
/-- Line 5 of MOD-020: the input collision message. -/
def mod020_line5 (tyOf : N → T) (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P5 tyOf Build I ports chans (C b I ports chans)
/-- Line 6 of MOD-020: an output collision. -/
def mod020_line6 (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P6 I ports (C b I ports chans)
/-- Line 7 of MOD-020: the output collision message. -/
def mod020_line7 (tyOf : N → T) (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P7 tyOf Build I ports chans (C b I ports chans)
/-- Line 8 of MOD-020: the transition builder's message. -/
def mod020_line8 (tyOf : N → T) (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P8 tyOf Build I ports chans (C b I ports chans)
/-- Line 9 of MOD-020: acceptance. -/
def mod020_line9 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P9 tyOf Build Mg b I ports chans (C b I ports chans)
/-- Line 10 of MOD-020: ill-formed channel bindings. -/
def mod020_line10 (C : ComposeFn N A) : Prop :=
  ∀ b I ports chans, mod020_P10 I chans (C b I ports chans)

/-- MOD-020 is its ten lines. -/
theorem mod020_iff (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) :
    MOD_020 tyOf Build Mg C ↔
      mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
      mod020_line5 tyOf Build C ∧ mod020_line6 C ∧ mod020_line7 tyOf Build C ∧
      mod020_line8 tyOf Build C ∧ mod020_line9 tyOf Build Mg C ∧ mod020_line10 C :=
  Iff.rfl

end Lines


/-! ### The reference -/

section Reference

/-- A `Forall₂`-related pair of lists: the related partners of the left elements that satisfy `p`
appear, in order, among the right elements, when the relation fixes them. -/
theorem mod020_forall₂_filter_sublist {α β γ : Type} {R : α → β → Prop} {p : α → Bool}
    {f : α → γ} {g : β → γ} (h : ∀ x y, p x = true → R x y → g y = f x) :
    ∀ {l : List α} {ms : List β}, List.Forall₂ R l ms → ((l.filter p).map f).Sublist (ms.map g)
  | _, _, .nil => by simp
  | _, _, .cons (a := x) (b := y) hxy hrest => by
    have ih := mod020_forall₂_filter_sublist h hrest
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.map_cons, h x y hp hxy]
      exact ih.cons_cons _
    · rw [List.filter_cons_of_neg hp, List.map_cons]
      exact ih.cons _

/-- Two members of a list on which `f` gives one `some` value are one member, when the `some`
values of `f` over the list are pairwise distinct. -/
theorem mod020_filterMap_inj {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (l.filterMap f).Nodup → ∀ {x y : α} {t : β}, x ∈ l → y ∈ l →
      f x = some t → f y = some t → x = y
  | [], _, _, _, _, hx, _, _, _ => nomatch hx
  | a :: l, hn, x, y, t, hx, hy, hfx, hfy => by
    have ht : (l.filterMap f).Nodup :=
      hn.sublist ((List.sublist_cons_self a l).filterMap f)
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · rw [List.filterMap_cons, hfx] at hn
      exact absurd (List.mem_filterMap.2 ⟨y, hy', hfy⟩) (List.nodup_cons.1 hn).1
    · rw [List.filterMap_cons, hfy] at hn
      exact absurd (List.mem_filterMap.2 ⟨x, hx', hfx⟩) (List.nodup_cons.1 hn).1
    · exact mod020_filterMap_inj ht hx' hy' hfx hfy

/-- The first element of a list that occurs again later in it occurs at least twice. -/
theorem mod020_bindDup_count : ∀ {l : List String} {x : String}, bindDup l = some x →
    2 ≤ l.count x
  | [], _, h => by simp [bindDup] at h
  | y :: ys, x, h => by
    unfold bindDup at h
    split at h
    · rename_i hy
      cases h
      rw [List.count_cons_self]
      have := List.count_pos_iff.2 hy
      omega
    · have := mod020_bindDup_count h
      rw [List.count_cons]
      split <;> omega

/-- The message for a port bound twice names the port. -/
theorem mod020_dupPortMsg_names (n : String) : MsgNames (dupPortMsg n) n :=
  msgNames_mid "Port '" n "' is already bound"

variable {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]
  {tyOf : N → T} {Build : Trans N → Option String}
  {Mg : CDef N A → CDef N A → Except String (CDef N A)}

omit [DecidableEq N] [ToString N] in
theorem mod020_unchanneled_iff {I : Instance N A} {chans : List (String × CDef N A)}
    {d : CDef N A} :
    mod020_unchanneled I chans d = true ↔ ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name := by
  simp [mod020_unchanneled, List.all_eq_true]

omit [DecidableEq N] [ToString N] in
/-- Under well-formed channel bindings, the channel bindings that name one instance transition are
one binding. -/
theorem mod020_chan_unique {I : Instance N A} {chans : List (String × CDef N A)}
    (h : ChansOk I chans) {c c' : String × CDef N A} {t : String} (hc : c ∈ chans)
    (hc' : c' ∈ chans) (ht : I.chan c.1 = some t) (ht' : I.chan c'.1 = some t) : c = c' :=
  mod020_filterMap_inj (f := fun c => I.chan c.1) h.2.2.2 hc hc' ht ht'

/-- The reference composition meets line 1. -/
theorem mod020_ref_line1 : mod020_line1 Mg (refCompose tyOf Build Mg) := by
  intro b I ports chans b' _ _ h
  obtain ⟨ms, hd, hp, -, -, -, hf⟩ := refCompose_shape h
  obtain ⟨-, -, -, hchk, -⟩ := refCompose_ok_iff.1 h
  refine ⟨ms, hd, hf.length_eq.symm, ?_, ?_, hp⟩
  · refine mod020_forall₂_filter_sublist (fun d m hu hm => ?_) hf
    have hn : ∀ c ∈ chans, I.chan c.1 ≠ some (rewriteDef (bindEntries I ports) d).core.name :=
      mod020_unchanneled_iff.1 hu
    rw [mergeStep_none hn] at hm
    cases hm
    rfl
  · intro d hd c hc hcn
    obtain ⟨m, hm, hmm⟩ := forall₂_mem_left hf d hd
    obtain ⟨c', hc', hcn', hs⟩ := mergeStep_some (Mg := Mg) (I := I) (chans := chans)
      (d := rewriteDef (bindEntries I ports) d) ⟨c, hc, by rw [rewriteDef_name]; exact hcn⟩
    rw [rewriteDef_name] at hcn'
    obtain rfl := mod020_chan_unique hchk hc' hc hcn' hcn
    rw [hs] at hmm
    exact ⟨m, hm, hmm⟩

/-- The reference composition meets line 2. -/
theorem mod020_ref_line2 : mod020_line2 (refCompose tyOf Build Mg) := by
  intro b I ports chans _ h _
  cases hn : bindDup (ports.map (·.1)) with
  | none => exact absurd ((bindDup_eq_none_iff _).1 hn) h
  | some n =>
    exact ⟨n, _, mod020_bindDup_count hn, refCompose_dupPort_msg hn, mod020_dupPortMsg_names n⟩

/-- The reference composition meets line 3. -/
theorem mod020_ref_line3 : mod020_line3 (refCompose tyOf Build Mg) :=
  fun _ _ _ _ h => refCompose_unknownPort h

/-- The reference composition meets line 4. -/
theorem mod020_ref_line4 : mod020_line4 (refCompose tyOf Build Mg) :=
  fun _ _ _ _ _ hd _ h => refCompose_inCollision hd h

/-- The reference composition meets line 6. -/
theorem mod020_ref_line6 : mod020_line6 (refCompose tyOf Build Mg) :=
  fun _ _ _ _ _ hd _ h => refCompose_outCollision hd h

/-- The reference composition meets line 10. -/
theorem mod020_ref_line10 : mod020_line10 (refCompose tyOf Build Mg) :=
  fun _ _ _ _ h => refCompose_chans h

omit [DecidableEq N] in
/-- The binding checks pass exactly when the reference's port and channel checks find nothing. -/
theorem mod020_checks_none {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : mod020_checks tyOf I ports chans) :
    portCheck tyOf I ports = none ∧ chanCheck I chans = none :=
  ⟨portCheck_eq_none_iff.2 ⟨h.1, h.2.1, h.2.2.1⟩, chanCheck_eq_none_iff.2 h.2.2.2⟩

/-- A clean definition the transition builder accepts goes through the binding. -/
theorem mod020_bindStep_ok {I : Instance N A} {ports : List (String × N)} {pre : List (CDef N A)}
    (h : ∀ e ∈ pre, mod020_clean (bindEntries I ports) e ∧
      Build (rewriteDef (bindEntries I ports) e).toTrans = none) :
    ∀ e ∈ pre, ∃ z, bindStep Build I.pfx (bindEntries I ports) e = .ok z := fun e he =>
  ⟨_, bindStep_ok_iff.2 ⟨(h e he).1.1, (h e he).1.2, (h e he).2, rfl⟩⟩

omit [DecidableEq N] in
/-- The input collision message of the reference is MOD-020's. -/
theorem mod020_inCollMsg (pfx : String) (e e' : BindEntry N) (t : String) :
    inCollMsg pfx e e' t = mod020_inMsg pfx e.port e'.port e.caller t := rfl

omit [DecidableEq N] in
/-- The output collision message of the reference is MOD-020's. -/
theorem mod020_outCollMsg (pfx : String) (e e' : BindEntry N) (t : String) :
    outCollMsg pfx e e' t = mod020_outMsg pfx e.port e'.port e.caller t := rfl

omit [ToString N] in
/-- Two bound places `x` and `y`, looked up to `e` and `e'`: the ports of `e` and `e'` expose
`x` and `y`, and `e`'s caller is where the binding sends `x`. -/
theorem mod020_pair {I : Instance N A} {ports : List (String × N)} {x y : N}
    {e e' : BindEntry N} (ha : bindLookup (bindEntries I ports) x = some e)
    (hb : bindLookup (bindEntries I ports) y = some e') :
    mod020_portsOf I x y e.port e'.port ∧ e.caller = bindSubst (bindEntries I ports) x := by
  obtain ⟨hea, hpa⟩ := bindLookup_some ha
  obtain ⟨heb, hpb⟩ := bindLookup_some hb
  have hia := (mem_bindEntries.1 hea).2
  have hib := (mem_bindEntries.1 heb).2
  exact ⟨Or.inl ⟨hpa ▸ hia, hpb ▸ hib⟩, (bindSubst_of_lookup ha).symm⟩

/-- The reference composition meets line 5. -/
theorem mod020_ref_line5 : mod020_line5 tyOf Build (refCompose tyOf Build Mg) := by
  intro b I ports chans pre d post hch _ _ hI hpre _ hout hin
  obtain ⟨hp, hc⟩ := mod020_checks_none hch
  obtain ⟨⟨e, e'⟩, hhead⟩ : ∃ q, (inPairs (bindEntries I ports) d).head? = some q := by
    cases h : (inPairs (bindEntries I ports) d).head? with
    | none => exact absurd hin (inPairs_eq_nil_iff.1 (List.head?_eq_none_iff.1 h))
    | some q => exact ⟨q, rfl⟩
  obtain ⟨x, hx, y, hy, hclash, hla, hlb⟩ := inPairs_head hhead
  obtain ⟨hports, hcaller⟩ := mod020_pair hla hlb
  refine ⟨x, hx, y, hy, hclash, e.port, e'.port, hports, ?_⟩
  rw [refCompose_step_error hp hc hI (mod020_bindStep_ok hpre) (bindStep_inColl hhead),
    mod020_inCollMsg, hcaller]

/-- The reference composition meets line 7. -/
theorem mod020_ref_line7 : mod020_line7 tyOf Build (refCompose tyOf Build Mg) := by
  intro b I ports chans pre d post hch _ _ hI hpre _ hin hout
  obtain ⟨hp, hc⟩ := mod020_checks_none hch
  obtain ⟨⟨e, e'⟩, hhead⟩ : ∃ q, (outPairs (bindEntries I ports) d).head? = some q := by
    cases h : (outPairs (bindEntries I ports) d).head? with
    | none => exact absurd hout (outPairs_eq_nil_iff.1 (List.head?_eq_none_iff.1 h))
    | some q => exact ⟨q, rfl⟩
  obtain ⟨o, ho, br, hbr, x, hx, y, hy, hclash, hla, hlb⟩ := outPairs_head hhead
  obtain ⟨hports, hcaller⟩ := mod020_pair hla hlb
  refine ⟨o, ho, br, hbr, x, hx, y, hy, hclash, e.port, e'.port, hports, ?_⟩
  rw [refCompose_step_error hp hc hI (mod020_bindStep_ok hpre) (bindStep_outColl hin hhead),
    mod020_outCollMsg, hcaller]

/-- The reference composition meets line 8. -/
theorem mod020_ref_line8 : mod020_line8 tyOf Build (refCompose tyOf Build Mg) := by
  intro b I ports chans pre d post m hch _ _ hI hpre _ hd hm
  obtain ⟨hp, hc⟩ := mod020_checks_none hch
  exact refCompose_step_error hp hc hI (mod020_bindStep_ok hpre) (bindStep_build hd.1 hd.2 hm)

/-- The reference composition meets line 9. -/
theorem mod020_ref_line9 : mod020_line9 tyOf Build Mg (refCompose tyOf Build Mg) := by
  intro b I ports chans hch _ _ hall hmg
  exact refCompose_accepts hch.1 hch.2.1 hch.2.2.1 hch.2.2.2
    (fun d hd => ⟨(hall d hd).1.1, (hall d hd).1.2, (hall d hd).2⟩) hmg

end Reference

/-- ✓ The reference composition satisfies MOD-020 for every token-type map, transition builder
and channel merge. Binding port `a` of an instance `s` to `X` rewrites every arc on `s/a` to `X`;
binding `a` twice fails with `Port 'a' is already bound`; binding two ports a transition consumes
from to one place fails with the input collision message; binding an unknown channel fails; and a
call with no fault succeeds. -/
@[evidence holds MOD_020]
theorem MOD_020_reference {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    MOD_020 tyOf Build Mg (refCompose tyOf Build Mg) :=
  ⟨mod020_ref_line1, mod020_ref_line2, mod020_ref_line3, mod020_ref_line4, mod020_ref_line5,
    mod020_ref_line6, mod020_ref_line7, mod020_ref_line8, mod020_ref_line9, mod020_ref_line10⟩


/-! ### Consequences for every model of the block -/

section Consequences

variable {N A T : Type} [DecidableEq N] [ToString N]

omit [DecidableEq N] [ToString N] in
/-- Split a list at its first element with a decidable property. -/
theorem mod020_first {P : CDef N A → Prop} [DecidablePred P] :
    ∀ {l : List (CDef N A)}, (∃ d ∈ l, P d) →
      ∃ pre d post, l = pre ++ d :: post ∧ (∀ e ∈ pre, ¬ P e) ∧ P d
  | [], h => by simp at h
  | x :: l, h => by
    by_cases hx : P x
    · exact ⟨[], x, l, rfl, by simp, hx⟩
    · obtain ⟨y, hy, hpy⟩ := h
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hpy hx
      · obtain ⟨pre, d, post, rfl, hpre, hd⟩ := mod020_first ⟨y, hy, hpy⟩
        refine ⟨x :: pre, d, post, rfl, ?_, hd⟩
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hx, hpre⟩

omit [ToString N] in
/-- **AC3: the transition count.** In every model of line 1, a coherent call whose caller
obligations hold leaves the builder's earlier transitions and adds exactly one transition per
instance transition: composing a two-transition instance into a builder with three transitions
gives five. -/
theorem mod020_count {Mg : CDef N A → CDef N A → Except String (CDef N A)} {C : ComposeFn N A}
    (h1 : mod020_line1 Mg C) {b b' : Bld N A}
    {I : Instance N A} {ports : List (String × N)} {chans : List (String × CDef N A)}
    (hc : mod020_coherent I ports) (hf : mod020_fresh b I ports chans)
    (h : C b I ports chans = .ok b') : b'.defs.length = b.defs.length + I.defs.length := by
  obtain ⟨ms, hd, hl, -, -, -⟩ := h1 b I ports chans b' hc hf h
  rw [hd, List.length_append, hl]

omit [ToString N] in
/-- **Item 5, eager: the port place is gone at once.** In every model of line 1, after a coherent
call whose caller obligations hold, every instance transition that no channel binding names is in
the builder with its arcs through the binding, and, when no caller place is itself a bound port
place, it names no bound port place: binding port `out` of `s` to `P` leaves no arc on `s/out`
as soon as `compose` returns. -/
theorem mod020_eager {Mg : CDef N A → CDef N A → Except String (CDef N A)} {C : ComposeFn N A}
    (h1 : mod020_line1 Mg C) {b b' : Bld N A}
    {I : Instance N A} {ports : List (String × N)} {chans : List (String × CDef N A)}
    (hc : mod020_coherent I ports) (hf : mod020_fresh b I ports chans)
    (h : C b I ports chans = .ok b')
    (hcp : ∀ e₁ ∈ bindEntries I ports, ∀ e₂ ∈ bindEntries I ports, e₁.caller ≠ e₂.place)
    {d : CDef N A} (hd : d ∈ I.defs) (hu : mod020_unchanneled I chans d = true) :
    ∃ m ∈ b'.defs, m.toTransDef = d.toTransDef.map (bindSubst (bindEntries I ports)) id ∧
      ∀ e ∈ bindEntries I ports, e.place ∉ m.namedPlaces := by
  obtain ⟨ms, hdefs, -, hsub, -, -⟩ := h1 b I ports chans b' hc hf h
  have hm : d.toTransDef.map (bindSubst (bindEntries I ports)) id ∈ ms.map CDef.toTransDef :=
    hsub.subset (List.mem_map_of_mem (List.mem_filter.2 ⟨hd, hu⟩))
  obtain ⟨m, hm, he⟩ := List.mem_map.1 hm
  refine ⟨m, by rw [hdefs]; exact List.mem_append_right _ hm, he, fun e hep hin => ?_⟩
  have hnp : m.namedPlaces = (rewriteDef (bindEntries I ports) d).namedPlaces := by
    show m.toTransDef.namedPlaces = (rewriteDef (bindEntries I ports) d).toTransDef.namedPlaces
    rw [he]; rfl
  rw [hnp] at hin
  exact rewriteDef_clears hep hcp d hin

omit [ToString N] in
/-- **A failing channel merge fails the call** ([MOD-021] rules (c) and (d)). In every model of
line 1, a coherent call whose caller obligations hold cannot succeed when the merge of some
channel binding's caller-side transition with the rewritten instance transition it names fails:
binding channel `go` to a caller transition whose timing does not merge with `go`'s fails the
call. -/
theorem mod020_mergeFails {Mg : CDef N A → CDef N A → Except String (CDef N A)}
    {C : ComposeFn N A} (h1 : mod020_line1 Mg C) {b : Bld N A} {I : Instance N A}
    {ports : List (String × N)} {chans : List (String × CDef N A)}
    (hc : mod020_coherent I ports) (hf : mod020_fresh b I ports chans) {d : CDef N A}
    (hd : d ∈ I.defs) {c : String × CDef N A} (hcm : c ∈ chans) (hcn : I.chan c.1 = some d.core.name)
    {m : String} (hm : Mg c.2 (rewriteDef (bindEntries I ports) d) = .error m) :
    ∃ m', C b I ports chans = .error m' := by
  cases hr : C b I ports chans with
  | error m' => exact ⟨m', rfl⟩
  | ok b' =>
    obtain ⟨ms, -, -, -, hmg, -⟩ := h1 b I ports chans b' hc hf hr
    obtain ⟨m', -, hm'⟩ := hmg d hd c hcm hcn
    rw [hm] at hm'
    cases hm'

omit [ToString N] in
/-- **A rewritten transition the transition builder rejects fails the call.** In every model of
line 8 there is no partial success: on a coherent, plain call whose binding checks pass and
that has no collision, if the transition builder rejects some instance transition after the
rewrite, the call fails, with the builder's message for the first such transition. -/
theorem mod020_buildFails {tyOf : N → T} {Build : Trans N → Option String}
    {C : ComposeFn N A} (h8 : mod020_line8 tyOf Build C) {b : Bld N A}
    {I : Instance N A} {ports : List (String × N)} {chans : List (String × CDef N A)}
    (hch : mod020_checks tyOf I ports chans) (hc : mod020_coherent I ports)
    (hp : mod020_plain I ports) (hcl : ∀ d ∈ I.defs, mod020_clean (bindEntries I ports) d)
    (hb : ∃ d ∈ I.defs, Build (rewriteDef (bindEntries I ports) d).toTrans ≠ none) :
    ∃ m, C b I ports chans = .error m := by
  obtain ⟨pre, d, post, hI, hpre, hd⟩ := mod020_first hb
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hd
  have hmem : ∀ e ∈ pre, e ∈ I.defs := fun e he => by rw [hI]; exact List.mem_append_left _ he
  have hdm : d ∈ I.defs := by rw [hI]; simp
  have hpm : ∀ e ∈ post, e ∈ I.defs := fun e he => by rw [hI]; simp [he]
  exact ⟨m, h8 b I ports chans pre d post m hch hc hp hI
    (fun e he => ⟨hcl e (hmem e he), not_not.1 (hpre e he)⟩) (fun e he => hcl e (hpm e he))
    (hcl d hdm) hm⟩

end Consequences

/-! ### Examples on the reference -/

section Examples

/-- The token-type map of the examples: no token types (TypeScript, Rust, Python). -/
abbrev mod020_ty : String → Unit := fun _ => ()

/-- The channel merge of the examples: keep the caller side. -/
abbrev mod020_mg : CDef String Unit → CDef String Unit → Except String (CDef String Unit) :=
  fun c _ => .ok c

/-- The empty subnet definition `E`. -/
def mod020_emptyS : SubnetDef String Unit :=
  { name := "E", places := [], defs := [], ports := [], chans := [] }

/-- The instance of `E` under `s`: no places, no transitions, no ports. -/
def mod020_emptyI : Instance String Unit := renamedInstance strNaming mod020_emptyS "s"

/-- An empty instance with no bindings passes every premise of line 9. -/
theorem mod020_empty_premises :
    mod020_checks mod020_ty mod020_emptyI [] [] ∧ mod020_coherent mod020_emptyI [] ∧
      mod020_fresh (Bld.empty : Bld String Unit) mod020_emptyI [] [] := by
  simp [mod020_checks, PortsDistinct, PortsKnown, PortTypesAgree, ChansOk, mod020_coherent,
    mod020_fresh, mod020_emptyI, renamedInstance, mod020_emptyS]

/-- A message that does not contain the letter `a` does not name port `a`. -/
theorem mod020_names_a {m : String} (h : 'a' ∉ m.toList) : ¬ MsgNames m "a" :=
  not_msgNames (by decide) h

end Examples

set_option maxRecDepth 20000 in
/-- ✓ Every line of MOD-020 is exercised by the reference, on a subnet `Join` whose transition
`join` takes from ports `a` and `b` and puts into port `out`, instantiated under `s`. Binding
`a`, `b` and `out` to `X`, `Y` and `P` gives one transition `s/join` from `X` and `Y` into `P`,
and the builder's places are exactly `X`, `Y` and `P` (line 1, AC1, AC2). Binding `a` twice fails
with `Port 'a' is already bound` (line 2, AC5). Binding `a` and `b` both to `X` fails with the
input collision message naming `a`, `b`, `s`, `X` and `s/join` (lines 4 and 5, AC7), while on a
subnet whose two transitions each take from one of the two ports the same binding succeeds (line
9, AC7). On a transition `split` writing `And(a, b)` the same binding fails with the output
collision message, and on one writing `Xor(a, b)` with the IO-012 message of the transition
builder (lines 6, 7 and 8, AC8). Binding channel `go` of a subnet `C` to a caller transition
`host`, with a merge that keeps the caller side, leaves the one transition `host` and no `s/go`
(line 1, clause 4). -/
@[evidence nonvacuous MOD_020]
theorem MOD_020_nonvacuous :
    (refInst strNaming bindExJoin "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I
          [("a", "X"), ("b", "Y"), ("out", "P")] []).toOption.map
        (fun b => (b.defs.map fun d => (d.core.name, d.namedPlaces), b.places)) =
      some ([("s/join", ["X", "Y", "P"])], ["X", "Y", "P"]) ∧
    bindExErr (refInst strNaming bindExJoin "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X"), ("a", "Y")] []) =
      some "Port 'a' is already bound" ∧
    bindExErr (refInst strNaming bindExJoin "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X"), ("b", "X")] []) =
      some "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join' would consume from 'X' through two input arcs. Bind them to distinct places or use one port." ∧
    (refInst strNaming bindExTwo "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X"), ("b", "X")] []).toOption.map
        (fun b => b.defs.map fun d => d.namedPlaces) = some [["X", "s/x"], ["X", "s/y"]] ∧
    bindExErr (refInst strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X"), ("b", "X")] []) =
      some "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/split' would produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port." ∧
    bindExErr (refInst strNaming (bindExSplit (.xor (.place "a") (.place "b"))) "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X"), ("b", "X")] []) =
      some "output spec of transition 's/split' is ambiguous: output branches 0 and 1 both claim {X}; no write can tell them apart (IO-012)" ∧
    (refInst strNaming bindExChan "s" >>= fun I =>
        refCompose mod020_ty refBuild mod020_mg Bld.empty I [("a", "X")]
          [("go", bindExDef "host" [] none)]).toOption.map
        (fun b => b.defs.map (·.core.name)) = some ["host"] :=
  ⟨bindEx_rewrite, bindEx_dupPort, bindEx_inCollision, bindEx_noCollision, bindEx_outCollision,
    bindEx_xorAmbiguous, bindEx_channel⟩

/-! ### Wrong compositions -/

/-- ✗ A composition that rejects every call violates MOD-020 (line 9): composing the empty
instance `s` of `E` with no binding passes every check and must succeed. -/
@[evidence forbids MOD_020]
theorem MOD_020_forbids_rejectAll :
    ¬ MOD_020 mod020_ty refBuild mod020_mg (fun _ _ _ _ => .error "rejected") := by
  intro h
  obtain ⟨hch, hco, hfr⟩ := mod020_empty_premises
  obtain ⟨b', hb'⟩ := h.2.2.2.2.2.2.2.2.1 Bld.empty mod020_emptyI [] [] hch hco hfr
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  cases hb'


/-! ### Tools for the mutants -/

section MutantTools

variable {N A : Type} [DecidableEq N] [ToString N]

/-- The composition `C`, except on the calls `cond` picks, where it is `alt`: the shape of every
wrong composition below. -/
def mod020_ite (cond : Bld N A → Instance N A → List (String × N) → List (String × CDef N A) → Bool)
    (alt C : ComposeFn N A) : ComposeFn N A := fun b I ports chans =>
  if cond b I ports chans then alt b I ports chans else C b I ports chans

omit [DecidableEq N] [ToString N] in
/-- Every line asks something of the outcome of one call at a time; so a line `C` meets and `alt`
meets on the calls `cond` picks holds of `mod020_ite cond alt C`. -/
theorem mod020_lift
    {cond : Bld N A → Instance N A → List (String × N) → List (String × CDef N A) → Bool}
    {alt C : ComposeFn N A}
    (Q : Bld N A → Instance N A → List (String × N) → List (String × CDef N A) →
      Except String (Bld N A) → Prop)
    (hC : ∀ b I ports chans, Q b I ports chans (C b I ports chans))
    (ha : ∀ b I ports chans, cond b I ports chans = true → Q b I ports chans (alt b I ports chans)) :
    ∀ b I ports chans, Q b I ports chans (mod020_ite cond alt C b I ports chans) := by
  intro b I ports chans
  unfold mod020_ite
  split
  · exact ha b I ports chans ‹_›
  · exact hC b I ports chans

/-- The composition `C` with every rejection message replaced by `rejected`. -/
def mod020_hush (C : ComposeFn N A) : ComposeFn N A := fun b I ports chans =>
  match C b I ports chans with
  | .ok x => .ok x
  | .error _ => .error "rejected"

omit [DecidableEq N] [ToString N] in
theorem mod020_hush_ok {C : ComposeFn N A} {b : Bld N A} {I : Instance N A}
    {ports : List (String × N)} {chans : List (String × CDef N A)} {x : Bld N A} :
    mod020_hush C b I ports chans = .ok x ↔ C b I ports chans = .ok x := by
  unfold mod020_hush
  cases C b I ports chans <;> simp

omit [DecidableEq N] [ToString N] in
theorem mod020_hush_err {C : ComposeFn N A} {b : Bld N A} {I : Instance N A}
    {ports : List (String × N)} {chans : List (String × CDef N A)} {m : String}
    (h : C b I ports chans = .error m) : mod020_hush C b I ports chans = .error "rejected" := by
  simp [mod020_hush, h]

omit [DecidableEq N] [ToString N] in
theorem mod020_map_err {r : Except String (Bld N A)} {f : Bld N A → Bld N A} {m : String}
    (h : r = .error m) : r.map f = .error m := by
  subst h; rfl

/-- Three places of a list, every two of them a colliding pair under `bm`. -/
def mod020_three (bm : List (BindEntry N)) (l : List N) : Bool :=
  l.any fun x => l.any fun y => l.any fun z =>
    (clashPair bm x y).isSome && (clashPair bm y z).isSome && (clashPair bm x z).isSome

omit [ToString N] in
theorem mod020_clash_of_isSome {bm : List (BindEntry N)} {x y : N}
    (h : (clashPair bm x y).isSome = true) : BindClash bm x y := by
  by_contra hc
  rw [← clashPair_eq_none_iff] at hc
  simp [hc] at h

omit [ToString N] in
theorem mod020_noIn {bm : List (BindEntry N)} {l : List (CDef N A)}
    (h : l.all (fun d => (inPairs bm d).isEmpty) = true) : ∀ d ∈ l, ¬ InCollision bm d :=
  fun d hd => inPairs_eq_nil_iff.1 (List.isEmpty_iff.1 (List.all_eq_true.1 h d hd))

omit [ToString N] in
theorem mod020_noOut {bm : List (BindEntry N)} {l : List (CDef N A)}
    (h : l.all (fun d => (outPairs bm d).isEmpty) = true) : ∀ d ∈ l, ¬ OutCollision bm d :=
  fun d hd => outPairs_eq_nil_iff.1 (List.isEmpty_iff.1 (List.all_eq_true.1 h d hd))

omit [ToString N] in
theorem mod020_someIn {bm : List (BindEntry N)} {l : List (CDef N A)}
    (h : l.any (fun d => !(inPairs bm d).isEmpty) = true) : ∃ d ∈ l, InCollision bm d := by
  obtain ⟨d, hd, hn⟩ := List.any_eq_true.1 h
  refine ⟨d, hd, ?_⟩
  by_contra hc
  rw [← inPairs_eq_nil_iff] at hc
  simp [hc] at hn

omit [ToString N] in
theorem mod020_someOut {bm : List (BindEntry N)} {l : List (CDef N A)}
    (h : l.any (fun d => !(outPairs bm d).isEmpty) = true) : ∃ d ∈ l, OutCollision bm d := by
  obtain ⟨d, hd, hn⟩ := List.any_eq_true.1 h
  refine ⟨d, hd, ?_⟩
  by_contra hc
  rw [← outPairs_eq_nil_iff] at hc
  simp [hc] at hn

omit [DecidableEq N] [ToString N] in
theorem mod020_split_mem {l pre post : List (CDef N A)} {d e : CDef N A}
    (hI : l = pre ++ d :: post) (he : e ∈ l) : e ∈ pre ∨ e = d ∨ e ∈ post := by
  subst hI
  simp only [List.mem_append, List.mem_cons] at he
  tauto

omit [DecidableEq N] [ToString N] in
theorem mod020_mem_of_split {l pre post : List (CDef N A)} {d : CDef N A}
    (hI : l = pre ++ d :: post) : d ∈ l := by
  rw [hI]; simp

omit [ToString N] in
theorem mod020_subst_congr {bm bm' : List (BindEntry N)} (h : bindLookup bm = bindLookup bm') :
    bindSubst bm = bindSubst bm' := by
  funext q; simp only [bindSubst, h]

omit [ToString N] in
theorem mod020_rewrite_congr {bm bm' : List (BindEntry N)} (h : bindLookup bm = bindLookup bm')
    (d : CDef N A) : rewriteDef bm d = rewriteDef bm' d := by
  unfold rewriteDef; rw [mod020_subst_congr h]

omit [ToString N] in
theorem mod020_inColl_congr {bm bm' : List (BindEntry N)} (h : bindLookup bm = bindLookup bm')
    {d : CDef N A} : InCollision bm d ↔ InCollision bm' d := by
  simp only [InCollision, BindClash, h]

omit [ToString N] in
theorem mod020_outColl_congr {bm bm' : List (BindEntry N)} (h : bindLookup bm = bindLookup bm')
    {d : CDef N A} : OutCollision bm d ↔ OutCollision bm' d := by
  simp only [OutCollision, BindClash, h]

omit [DecidableEq N] [ToString N] in
/-- The caller obligations of a call hold of a call with fewer bound ports. -/
theorem mod020_fresh_ports {b : Bld N A} {I : Instance N A} {ports ports' : List (String × N)}
    {chans : List (String × CDef N A)}
    (hs : ∀ e ∈ bindEntries I ports', e ∈ bindEntries I ports)
    (h : mod020_fresh b I ports chans) : mod020_fresh b I ports' chans :=
  ⟨h.1, h.2.1, fun c hc e he => h.2.2 c hc e (hs e he)⟩

omit [ToString N] in
/-- Every rewritten definition, unmerged, has the shape line 1 asks for, on a call without
channel bindings. -/
theorem mod020_assemble_P1 (Mg : CDef N A → CDef N A → Except String (CDef N A)) (b : Bld N A)
    (I : Instance N A) (ports : List (String × N)) :
    mod020_P1 Mg b I ports []
      (.ok (bindAssemble b (I.defs.map (rewriteDef (bindEntries I ports))))) := by
  intro b' _ _ h
  cases h
  refine ⟨I.defs.map (rewriteDef (bindEntries I ports)), rfl, by simp, ?_, ?_,
    fun p => mem_bindAssemble_places⟩
  · rw [List.map_map]
    exact (List.filter_sublist).map _
  · intro _ _ _ hc
    exact absurd hc List.not_mem_nil

end MutantTools

/-! ### Mutants: one per line -/

section Mutants

variable {N A T : Type} [DecidableEq N] [ToString N]

/-- Mutant reading: MOD-020 without line 1, so a success may hold anything. -/
def MOD_020_mutant_noShape (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧ mod020_line5 tyOf Build C ∧
    mod020_line6 C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 2, so a port may be bound twice. -/
def MOD_020_mutant_noDup (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line3 C ∧ mod020_line4 C ∧ mod020_line5 tyOf Build C ∧
    mod020_line6 C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 3, so an unknown port may be ignored. -/
def MOD_020_mutant_noUnknown (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line4 C ∧ mod020_line5 tyOf Build C ∧
    mod020_line6 C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 4, so an input collision need fail only on a plain
call. -/
def MOD_020_mutant_noInCollision (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line5 tyOf Build C ∧
    mod020_line6 C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 5, so an input collision may fail with any message. -/
def MOD_020_mutant_noInMessage (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line6 C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 6, so an output collision need fail only on a plain
call. -/
def MOD_020_mutant_noOutCollision (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line5 tyOf Build C ∧ mod020_line7 tyOf Build C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 7, so an output collision may fail with any message. -/
def MOD_020_mutant_noOutMessage (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line5 tyOf Build C ∧ mod020_line6 C ∧ mod020_line8 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 8, so a rewritten transition the transition builder
rejects may fail the call with any message. -/
def MOD_020_mutant_noBuildMessage (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line5 tyOf Build C ∧ mod020_line6 C ∧ mod020_line7 tyOf Build C ∧
    mod020_line9 tyOf Build Mg C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 9, the rejections and the shape of a success only
(skeptic correction S2 of the composition design). -/
def MOD_020_mutant_noAcceptance (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line5 tyOf Build C ∧ mod020_line6 C ∧ mod020_line7 tyOf Build C ∧
    mod020_line8 tyOf Build C ∧ mod020_line10 C

/-- Mutant reading: MOD-020 without line 10, so an unknown channel may be ignored. -/
def MOD_020_mutant_noChans (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) (C : ComposeFn N A) : Prop :=
  mod020_line1 Mg C ∧ mod020_line2 C ∧ mod020_line3 C ∧ mod020_line4 C ∧
    mod020_line5 tyOf Build C ∧ mod020_line6 C ∧ mod020_line7 tyOf Build C ∧
    mod020_line8 tyOf Build C ∧ mod020_line9 tyOf Build Mg C

end Mutants


/-! ### Wrong compositions for the mutants, and the examples they are killed on -/

section Models

/-- The reference composition of the examples: no token types, the reference transition builder,
a merge that keeps the caller side. -/
abbrev mod020_R : ComposeFn String Unit := refCompose mod020_ty refBuild mod020_mg

/-- The instance `s` of `Join` (transition `join` from ports `a` and `b` into port `out`). -/
def mod020_I0 : Instance String Unit := renamedInstance strNaming bindExJoin "s"

/-- The transition `s/join` of `mod020_I0`. -/
def mod020_d0 : CDef String Unit :=
  CDef.map (strNaming.pre "s") (preS "s") (bindExDef "join" [⟨"a", .one⟩, ⟨"b", .one⟩] (some (.place "out")))

/-- A subnet whose transition `join` takes from ports `a`, `b` and `c`. -/
def mod020_join3 : SubnetDef String Unit :=
  { name := "Join3", places := ["a", "b", "c", "out"],
    defs := [bindExDef "join" [⟨"a", .one⟩, ⟨"b", .one⟩, ⟨"c", .one⟩] (some (.place "out"))],
    ports := [⟨"a", .input, "a"⟩, ⟨"b", .input, "b"⟩, ⟨"c", .input, "c"⟩], chans := [] }

/-- The transition `s/join` of `Join3` instantiated under `s`. -/
def mod020_join3d : CDef String Unit :=
  CDef.map (strNaming.pre "s") (preS "s")
    (bindExDef "join" [⟨"a", .one⟩, ⟨"b", .one⟩, ⟨"c", .one⟩] (some (.place "out")))

/-- The transition `s/split` of `Split` with the output specification `o`, instantiated under
`s`. -/
def mod020_splitDef (o : Out String) : CDef String Unit :=
  CDef.map (strNaming.pre "s") (preS "s") (bindExDef "split" [⟨"in", .one⟩] (some o))

/-- A lazy composition: the checks of the reference, but a success adds the instance's
transitions as they are, with their arcs still on the port places, as if the rewrite were left to
`build()`. -/
def mod020_lazy : ComposeFn String Unit := fun b I ports chans =>
  (mod020_R b I ports chans).map fun b' => { b' with defs := b.defs ++ I.defs }

/-- A composition that accepts the one call binding port `a` to `X` twice, as if bound once. -/
def mod020_dupOnce : ComposeFn String Unit :=
  mod020_ite (fun _ _ ports _ => ports == [("a", "X"), ("a", "X")])
    (fun b I _ chans => mod020_R b I [("a", "X")] chans) mod020_R

/-- A composition that ignores a binding of an unknown port `zz`. -/
def mod020_skipUnknown : ComposeFn String Unit :=
  mod020_ite (fun _ I ports _ => ports == [("zz", "X")] && (I.port "zz").isNone)
    (fun b I _ chans => mod020_R b I [] chans) mod020_R

/-- A composition that checks a call's ports and its output collisions, and accepts an input
collision on a call that is not plain (a caller place that an instance transition already names),
adding every rewritten transition: the slip of a collision check that only looks at caller places
from outside the instance. -/
def mod020_acceptIn : ComposeFn String Unit :=
  mod020_ite (fun _ I ports chans => chans.isEmpty && (portCheck mod020_ty I ports).isNone &&
      !decide (mod020_plain I ports) &&
      I.defs.all (fun d => (outPairs (bindEntries I ports) d).isEmpty) &&
      I.defs.any (fun d => !(inPairs (bindEntries I ports) d).isEmpty))
    (fun b I ports _ => .ok (bindAssemble b (I.defs.map (rewriteDef (bindEntries I ports)))))
    mod020_R

/-- A composition that checks a call's ports and its input collisions, and accepts an output
collision on a call that is not plain, adding every rewritten transition. -/
def mod020_acceptOut : ComposeFn String Unit :=
  mod020_ite (fun _ I ports chans => chans.isEmpty && (portCheck mod020_ty I ports).isNone &&
      !decide (mod020_plain I ports) &&
      I.defs.all (fun d => (inPairs (bindEntries I ports) d).isEmpty) &&
      I.defs.any (fun d => !(outPairs (bindEntries I ports) d).isEmpty))
    (fun b I ports _ => .ok (bindAssemble b (I.defs.map (rewriteDef (bindEntries I ports)))))
    mod020_R

/-- The reference, except that a call with an input collision fails with the message
`rejected`. -/
def mod020_noInMsg : ComposeFn String Unit :=
  mod020_ite (fun _ I ports _ => (portCheck mod020_ty I ports).isNone &&
      I.defs.any (fun d => !(inPairs (bindEntries I ports) d).isEmpty))
    (mod020_hush mod020_R) mod020_R

/-- The reference, except that a call with an output collision fails with the message
`rejected`. -/
def mod020_noOutMsg : ComposeFn String Unit :=
  mod020_ite (fun _ I ports _ => (portCheck mod020_ty I ports).isNone &&
      I.defs.any (fun d => !(outPairs (bindEntries I ports) d).isEmpty))
    (mod020_hush mod020_R) mod020_R

/-- The reference, except that a call without a collision whose rewritten transition the
transition builder rejects fails with the message `rejected`. -/
def mod020_noBuildMsg : ComposeFn String Unit :=
  mod020_ite (fun _ I ports _ => (portCheck mod020_ty I ports).isNone &&
      I.defs.all (fun d => (inPairs (bindEntries I ports) d).isEmpty) &&
      I.defs.all (fun d => (outPairs (bindEntries I ports) d).isEmpty) &&
      I.defs.any (fun d => (refBuild (rewriteDef (bindEntries I ports) d).toTrans).isSome))
    (mod020_hush mod020_R) mod020_R

/-- The reference, except that composing an instance without transitions with no binding is
rejected. -/
def mod020_rejectEmpty : ComposeFn String Unit :=
  mod020_ite (fun _ I ports chans => ports.isEmpty && chans.isEmpty && I.defs.isEmpty)
    (fun _ _ _ _ => .error "rejected") mod020_R

/-- The channel bindings of a call without those whose channel the instance does not declare. -/
def mod020_knownChans (I : Instance String Unit) (chans : List (String × CDef String Unit)) :
    List (String × CDef String Unit) :=
  chans.filter fun c => (I.chan c.1).isSome

/-- A composition that ignores the channel bindings whose channel the instance does not
declare. -/
def mod020_skipUnknownChan : ComposeFn String Unit :=
  mod020_ite (fun _ I _ chans => chans.any fun c => (I.chan c.1).isNone)
    (fun b I ports chans => mod020_R b I ports (mod020_knownChans I chans)) mod020_R

end Models

section ModelLemmas

theorem mod020_portCheck_spec {I : Instance String Unit} {ports : List (String × String)}
    (h : (portCheck mod020_ty I ports).isNone = true) :
    PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree mod020_ty I ports :=
  portCheck_eq_none_iff.1 (Option.isNone_iff_eq_none.1 h)

theorem mod020_lookup_dup (I : Instance String Unit) :
    bindLookup (bindEntries I [("a", "X"), ("a", "X")]) =
      bindLookup (bindEntries I [("a", "X")]) := by
  funext q
  cases hp : I.port "a" with
  | none => simp [bindEntries, bindLookup, hp]
  | some v => by_cases hv : v = q <;> simp [bindEntries, bindLookup, hp, List.find?, hv]

theorem mod020_coherent_one (I : Instance String Unit) (e : String × String) :
    mod020_coherent I [e] := by
  intro x hx y hy _ _
  simp only [List.mem_singleton] at hx hy
  rw [hx, hy]

theorem mod020_coherent_nil (I : Instance String Unit) : mod020_coherent I [] :=
  fun _ h => nomatch h

/-- The input collision message is never a message of at most eight characters, such as
`rejected` or `CORE-030`: it is longer. -/
theorem mod020_inMsg_ne {N : Type} [ToString N] (pfx pa pb : String) (X : N) (t : String)
    {s : String} (hs : s.length ≤ 8) : mod020_inMsg pfx pa pb X t ≠ s := by
  intro h
  have := congrArg String.length h
  simp only [mod020_inMsg, String.length_append] at this
  have hL : 9 ≤ (toString "' through two input arcs. Bind them to distinct places or use one port.").length := by decide
  omega

/-- The output collision message is never a message of at most eight characters: it is
longer. -/
theorem mod020_outMsg_ne {N : Type} [ToString N] (pfx pa pb : String) (X : N) (t : String)
    {s : String} (hs : s.length ≤ 8) : mod020_outMsg pfx pa pb X t ≠ s := by
  intro h
  have := congrArg String.length h
  simp only [mod020_outMsg, String.length_append] at this
  have hL : 9 ≤ (toString "' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port.").length := by decide
  omega

theorem mod020_R_line1 : mod020_line1 mod020_mg mod020_R := mod020_ref_line1
theorem mod020_R_line2 : mod020_line2 mod020_R := mod020_ref_line2
theorem mod020_R_line3 : mod020_line3 mod020_R := mod020_ref_line3
theorem mod020_R_line4 : mod020_line4 mod020_R := mod020_ref_line4
theorem mod020_R_line5 : mod020_line5 mod020_ty refBuild mod020_R := mod020_ref_line5
theorem mod020_R_line6 : mod020_line6 mod020_R := mod020_ref_line6
theorem mod020_R_line7 : mod020_line7 mod020_ty refBuild mod020_R := mod020_ref_line7
theorem mod020_R_line8 : mod020_line8 mod020_ty refBuild mod020_R := mod020_ref_line8
theorem mod020_R_line9 : mod020_line9 mod020_ty refBuild mod020_mg mod020_R := mod020_ref_line9
theorem mod020_R_line10 : mod020_line10 mod020_R := mod020_ref_line10

end ModelLemmas


/-! ### Mutant 1: line 1 dropped (a lazy composition) -/

theorem mod020_lazy_meets : MOD_020_mutant_noShape mod020_ty refBuild mod020_mg mod020_lazy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b I ports chans hu h hcn
    obtain ⟨n, m, hc, he, hn⟩ := mod020_R_line2 b I ports chans hu h hcn
    exact ⟨n, m, hc, mod020_map_err he, hn⟩
  · intro b I ports chans h
    obtain ⟨m, he⟩ := mod020_R_line3 b I ports chans h
    exact ⟨m, mod020_map_err he⟩
  · intro b I ports chans d hd hc h
    obtain ⟨m, he⟩ := mod020_R_line4 b I ports chans d hd hc h
    exact ⟨m, mod020_map_err he⟩
  · intro b I ports chans pre d post h1 h2 h3 h4 h5 h6 h7 h8
    obtain ⟨x, hx, y, hy, hxy, pa, pb, hp, he⟩ :=
      mod020_R_line5 b I ports chans pre d post h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨x, hx, y, hy, hxy, pa, pb, hp, mod020_map_err he⟩
  · intro b I ports chans d hd hc h
    obtain ⟨m, he⟩ := mod020_R_line6 b I ports chans d hd hc h
    exact ⟨m, mod020_map_err he⟩
  · intro b I ports chans pre d post h1 h2 h3 h4 h5 h6 h7 h8
    obtain ⟨o, ho, br, hbr, x, hx, y, hy, hxy, pa, pb, hp, he⟩ :=
      mod020_R_line7 b I ports chans pre d post h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨o, ho, br, hbr, x, hx, y, hy, hxy, pa, pb, hp, mod020_map_err he⟩
  · intro b I ports chans pre d post m h1 h2 h3 h4 h5 h6 h7 h8
    exact mod020_map_err (mod020_R_line8 b I ports chans pre d post m h1 h2 h3 h4 h5 h6 h7 h8)
  · intro b I ports chans h1 h2 h3 h4 h5
    obtain ⟨b', hb⟩ := mod020_R_line9 b I ports chans h1 h2 h3 h4 h5
    exact ⟨_, by unfold mod020_lazy; rw [hb]; rfl⟩
  · intro b I ports chans h
    obtain ⟨m, he⟩ := mod020_R_line10 b I ports chans h
    exact ⟨m, mod020_map_err he⟩

set_option maxRecDepth 20000 in
/-- ✗ A lazy composition kills the mutant without line 1: it checks and rejects exactly as the
reference does, so it meets every other line, but binding `a`, `b` and `out` of `Join` under `s`
to `X`, `Y` and `P` leaves `s/join` taking from `s/a` and `s/b` and putting into `s/out`, where
line 1 asks for `X`, `Y` and `P` as soon as `compose` returns. -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noShape_killed :
    MOD_020_mutant_noShape mod020_ty refBuild mod020_mg mod020_lazy ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_lazy := by
  refine ⟨mod020_lazy_meets, fun h => ?_⟩
  have hok : (mod020_R Bld.empty mod020_I0 [("a", "X"), ("b", "Y"), ("out", "P")] []).toOption.isSome
      = true := by decide
  cases hr : mod020_R Bld.empty mod020_I0 [("a", "X"), ("b", "Y"), ("out", "P")] [] with
  | error m => rw [hr] at hok; cases hok
  | ok b0 =>
    obtain ⟨ms, hd, -, hsub, -, -⟩ := h.1 Bld.empty mod020_I0
      [("a", "X"), ("b", "Y"), ("out", "P")] []
      { b0 with defs := (Bld.empty : Bld String Unit).defs ++ mod020_I0.defs }
      (by unfold mod020_coherent; decide) (by unfold mod020_fresh; decide)
      (by show (mod020_R _ _ _ _).map _ = _; rw [hr]; rfl)
    simp only [Bld.empty, List.nil_append] at hd
    subst hd
    have := hsub.map TransDef.namedPlaces
    revert this
    decide


/-! ### Mutant 2: line 2 dropped (a port bound twice accepted) -/

theorem mod020_dupOnce_meets :
    MOD_020_mutant_noDup mod020_ty refBuild mod020_mg mod020_dupOnce := by
  have hcond : ∀ {ports : List (String × String)},
      (ports == [("a", "X"), ("a", "X")]) = true → ports = [("a", "X"), ("a", "X")] := by
    intro ports h; simpa using h
  have hnd : ¬ PortsDistinct [("a", "X"), ("a", "X")] := by simp [PortsDistinct]
  have hsub : ∀ (I : Instance String Unit), ∀ e ∈ bindEntries I [("a", "X")],
      e ∈ bindEntries I [("a", "X"), ("a", "X")] := by
    intro I e he
    rw [mem_bindEntries] at he ⊢
    exact ⟨List.mem_cons_of_mem _ he.1, he.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans hc b' _ hfr h
    obtain rfl := hcond hc
    obtain ⟨ms, hd, hl, hs, hmg, hp⟩ := mod020_R_line1 b I [("a", "X")] chans b'
      (mod020_coherent_one I _) (mod020_fresh_ports (hsub I) hfr) h
    refine ⟨ms, hd, hl, ?_, ?_, hp⟩
    · rw [mod020_subst_congr (mod020_lookup_dup I)]
      exact hs
    · intro d hd c hc hcn
      rw [mod020_rewrite_congr (mod020_lookup_dup I)]
      exact hmg d hd c hc hcn
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    obtain rfl := hcond hc
    exact mod020_R_line3 b I [("a", "X")] chans (by simpa [PortsKnown] using hk)
  · refine mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4 ?_
    intro b I ports chans hc d hd _ hin
    obtain rfl := hcond hc
    exact mod020_R_line4 b I [("a", "X")] chans d hd (mod020_coherent_one I _)
      ((mod020_inColl_congr (mod020_lookup_dup I)).1 hin)
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc _ _ _ hch
    obtain rfl := hcond hc
    exact absurd hch.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6 ?_
    intro b I ports chans hc d hd _ hout
    obtain rfl := hcond hc
    exact mod020_R_line6 b I [("a", "X")] chans d hd (mod020_coherent_one I _)
      ((mod020_outColl_congr (mod020_lookup_dup I)).1 hout)
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc _ _ _ hch
    obtain rfl := hcond hc
    exact absurd hch.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc _ _ _ _ hch
    obtain rfl := hcond hc
    exact absurd hch.1 hnd
  · refine mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 ?_
    intro b I ports chans hc hch
    obtain rfl := hcond hc
    exact absurd hch.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10 ?_
    intro b I ports chans _ h
    exact mod020_R_line10 b I [("a", "X")] chans h

set_option maxRecDepth 20000 in
/-- ✗ A composition that accepts port `a` bound to `X` twice, as if bound once, kills the mutant
without line 2: it meets every other line, but binding `a` of `Join` under `s` to `X` twice
succeeds, where line 2 asks for an error naming `a` (AC5). -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noDup_killed :
    MOD_020_mutant_noDup mod020_ty refBuild mod020_mg mod020_dupOnce ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_dupOnce := by
  refine ⟨mod020_dupOnce_meets, fun h => ?_⟩
  obtain ⟨n, m, -, he, -⟩ := h.2.1 Bld.empty mod020_I0 [("a", "X"), ("a", "X")] []
    List.nodup_nil (by simp [PortsDistinct]) List.nodup_nil
  have hok : (mod020_dupOnce Bld.empty mod020_I0 [("a", "X"), ("a", "X")] []).toOption.isSome
      = true := by decide
  rw [he] at hok
  cases hok

/-! ### Mutant 3: line 3 dropped (an unknown port ignored) -/

theorem mod020_skipUnknown_meets :
    MOD_020_mutant_noUnknown mod020_ty refBuild mod020_mg mod020_skipUnknown := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)},
      (ports == [("zz", "X")] && (I.port "zz").isNone) = true →
        ports = [("zz", "X")] ∧ I.port "zz" = none := by
    intro I ports h; simpa using h
  have hb : ∀ {I : Instance String Unit}, I.port "zz" = none →
      bindEntries I [("zz", "X")] = [] := by
    intro I hz; simp [bindEntries, hz]
  have hk : ∀ {I : Instance String Unit}, I.port "zz" = none → ¬ PortsKnown I [("zz", "X")] := by
    intro I hz h; exact h ("zz", "X") (by simp) hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans hc b' _ hfr h
    obtain ⟨rfl, hz⟩ := hcond hc
    rw [hb hz]
    exact mod020_R_line1 b I [] chans b' (mod020_coherent_nil I)
      (mod020_fresh_ports (by simp [bindEntries]) hfr) h
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    obtain ⟨rfl, -⟩ := hcond hc
    exact absurd (by simp [PortsDistinct]) hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4 ?_
    intro b I ports chans hc d hd _ hin
    obtain ⟨rfl, hz⟩ := hcond hc
    rw [hb hz] at hin
    exact mod020_R_line4 b I [] chans d hd (mod020_coherent_nil I) hin
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc _ _ _ hch
    obtain ⟨rfl, hz⟩ := hcond hc
    exact absurd hch.2.1 (hk hz)
  · refine mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6 ?_
    intro b I ports chans hc d hd _ hout
    obtain ⟨rfl, hz⟩ := hcond hc
    rw [hb hz] at hout
    exact mod020_R_line6 b I [] chans d hd (mod020_coherent_nil I) hout
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc _ _ _ hch
    obtain ⟨rfl, hz⟩ := hcond hc
    exact absurd hch.2.1 (hk hz)
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc _ _ _ _ hch
    obtain ⟨rfl, hz⟩ := hcond hc
    exact absurd hch.2.1 (hk hz)
  · refine mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 ?_
    intro b I ports chans hc hch
    obtain ⟨rfl, hz⟩ := hcond hc
    exact absurd hch.2.1 (hk hz)
  · refine mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10 ?_
    intro b I ports chans _ h
    exact mod020_R_line10 b I [] chans h

set_option maxRecDepth 20000 in
/-- ✗ A composition that ignores a binding of the unknown port `zz` kills the mutant without
line 3: it meets every other line, but binding `zz` of `Join` under `s` to `X` succeeds, where
line 3 asks for a failure. -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noUnknown_killed :
    MOD_020_mutant_noUnknown mod020_ty refBuild mod020_mg mod020_skipUnknown ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_skipUnknown := by
  refine ⟨mod020_skipUnknown_meets, fun h => ?_⟩
  obtain ⟨m, he⟩ := h.2.2.1 Bld.empty mod020_I0 [("zz", "X")] []
    (fun hk => hk ("zz", "X") (by simp) (by decide))
  have hok : (mod020_skipUnknown Bld.empty mod020_I0 [("zz", "X")] []).toOption.isSome = true := by
    decide
  rw [he] at hok
  cases hok


/-! ### Mutants 4 and 6: a collision accepted on a call that is not plain -/

/-- What the condition of `mod020_acceptIn` and `mod020_acceptOut` gives: no channel binding,
the ports bound once each and known, and a call that is not plain. -/
theorem mod020_acceptCond {I : Instance String Unit} {ports : List (String × String)}
    {chans : List (String × CDef String Unit)} {p : Bool}
    (h : (chans.isEmpty && (portCheck mod020_ty I ports).isNone &&
      !decide (mod020_plain I ports) && p) = true) :
    chans = [] ∧ (PortsDistinct ports ∧ PortsKnown I ports) ∧ ¬ mod020_plain I ports ∧
      p = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨hc, hp⟩, hn⟩, hq⟩ := h
  have hp' := mod020_portCheck_spec hp
  exact ⟨hc, ⟨hp'.1, hp'.2.1⟩, hn, hq⟩

theorem mod020_acceptIn_meets :
    MOD_020_mutant_noInCollision mod020_ty refBuild mod020_mg mod020_acceptIn := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)}
      {chans : List (String × CDef String Unit)},
      (chans.isEmpty && (portCheck mod020_ty I ports).isNone &&
        !decide (mod020_plain I ports) &&
        I.defs.all (fun d => (outPairs (bindEntries I ports) d).isEmpty) &&
        I.defs.any (fun d => !(inPairs (bindEntries I ports) d).isEmpty)) = true →
      chans = [] ∧ (PortsDistinct ports ∧ PortsKnown I ports) ∧ ¬ mod020_plain I ports ∧
        ∀ d ∈ I.defs, ¬ OutCollision (bindEntries I ports) d := by
    intro I ports chans h
    rw [Bool.and_eq_true] at h
    obtain ⟨hc, hk, hn, ho⟩ := mod020_acceptCond h.1
    exact ⟨hc, hk, hn, mod020_noOut ho⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans hc
    obtain ⟨rfl, -⟩ := hcond hc
    exact mod020_assemble_P1 mod020_mg b I ports
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    exact absurd (hcond hc).2.1.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    exact absurd (hcond hc).2.1.2 hk
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6 ?_
    intro b I ports chans hc d hd _ hout
    exact absurd hout ((hcond hc).2.2.2 d hd)
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc _ _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 ?_
    intro b I ports chans _ _ _ _ _ _
    exact ⟨_, rfl⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10 ?_
    intro b I ports chans hc hch
    obtain ⟨rfl, -⟩ := hcond hc
    exact absurd (by simp [ChansOk]) hch

set_option maxRecDepth 20000 in
/-- ✗ A composition that accepts an input collision on a call that is not plain kills the mutant
without line 4: it fails every plain call as the reference does, so it meets line 5 and every
other line, but binding ports `a` and `b` of `Join` under `s`, whose `s/join` takes from both,
to `s/out`, a place `s/join` already names, succeeds, where line 4 asks for a failure. -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noInCollision_killed :
    MOD_020_mutant_noInCollision mod020_ty refBuild mod020_mg mod020_acceptIn ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_acceptIn := by
  refine ⟨mod020_acceptIn_meets, fun h => ?_⟩
  obtain ⟨m, he⟩ := h.2.2.2.1 Bld.empty mod020_I0 [("a", "s/out"), ("b", "s/out")] [] mod020_d0
    (by rw [show mod020_I0.defs = [mod020_d0] from rfl]; exact List.mem_singleton_self _) (by unfold mod020_coherent; decide)
    ⟨"s/a", by decide, "s/b", by decide, mod020_clash_of_isSome (by decide)⟩
  have hok : (mod020_acceptIn Bld.empty mod020_I0 [("a", "s/out"), ("b", "s/out")]
      []).toOption.isSome = true := by decide
  rw [he] at hok
  cases hok

theorem mod020_acceptOut_meets :
    MOD_020_mutant_noOutCollision mod020_ty refBuild mod020_mg mod020_acceptOut := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)}
      {chans : List (String × CDef String Unit)},
      (chans.isEmpty && (portCheck mod020_ty I ports).isNone &&
        !decide (mod020_plain I ports) &&
        I.defs.all (fun d => (inPairs (bindEntries I ports) d).isEmpty) &&
        I.defs.any (fun d => !(outPairs (bindEntries I ports) d).isEmpty)) = true →
      chans = [] ∧ (PortsDistinct ports ∧ PortsKnown I ports) ∧ ¬ mod020_plain I ports ∧
        ∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d := by
    intro I ports chans h
    rw [Bool.and_eq_true] at h
    obtain ⟨hc, hk, hn, hi⟩ := mod020_acceptCond h.1
    exact ⟨hc, hk, hn, mod020_noIn hi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans hc
    obtain ⟨rfl, -⟩ := hcond hc
    exact mod020_assemble_P1 mod020_mg b I ports
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    exact absurd (hcond hc).2.1.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    exact absurd (hcond hc).2.1.2 hk
  · refine mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4 ?_
    intro b I ports chans hc d hd _ hin
    exact absurd hin ((hcond hc).2.2.2 d hd)
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc _ _ _ _ _ _ hp
    exact absurd hp (hcond hc).2.2.1
  · refine mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 ?_
    intro b I ports chans _ _ _ _ _ _
    exact ⟨_, rfl⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10 ?_
    intro b I ports chans hc hch
    obtain ⟨rfl, -⟩ := hcond hc
    exact absurd (by simp [ChansOk]) hch

set_option maxRecDepth 20000 in
/-- ✗ A composition that accepts an output collision on a call that is not plain kills the
mutant without line 6: it fails every plain call as the reference does, so it meets line 7 and
every other line, but binding ports `a` and `b` of a `Split` under `s`, whose `s/split` writes
`And(a, b)`, to `s/in`, the place `s/split` takes from, succeeds, where line 6 asks for a
failure. -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noOutCollision_killed :
    MOD_020_mutant_noOutCollision mod020_ty refBuild mod020_mg mod020_acceptOut ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_acceptOut := by
  refine ⟨mod020_acceptOut_meets, fun h => ?_⟩
  have hdo : (mod020_splitDef (.and (.place "a") (.place "b"))).out =
      some (.and (.place "s/a") (.place "s/b")) := rfl
  obtain ⟨m, he⟩ := h.2.2.2.2.2.1 Bld.empty
    (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s")
    [("a", "s/in"), ("b", "s/in")] [] (mod020_splitDef (.and (.place "a") (.place "b")))
    (by rw [show (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b")))
      "s").defs = [mod020_splitDef (.and (.place "a") (.place "b"))] from rfl]
        exact List.mem_singleton_self _) (by unfold mod020_coherent; decide)
    ⟨_, hdo, ["s/a", "s/b"], by decide, "s/a", by decide, "s/b", by decide,
      mod020_clash_of_isSome (by decide)⟩
  have hok : (mod020_acceptOut Bld.empty
      (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s")
      [("a", "s/in"), ("b", "s/in")] []).toOption.isSome = true := by decide
  rw [he] at hok
  cases hok

/-! ### Mutant 9: line 9 dropped (an empty instance rejected) -/

theorem mod020_rejectEmpty_meets :
    MOD_020_mutant_noAcceptance mod020_ty refBuild mod020_mg mod020_rejectEmpty := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)}
      {chans : List (String × CDef String Unit)},
      (ports.isEmpty && chans.isEmpty && I.defs.isEmpty) = true → ports = [] ∧ I.defs = [] := by
    intro I ports chans h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨h.1.1, h.2⟩
  have hnil : ∀ {l pre post : List (CDef String Unit)} {d : CDef String Unit},
      l = [] → l = pre ++ d :: post → False := by
    intro l pre post d h1 h2; rw [h1] at h2; simp at h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans _ b' _ _ h
    cases h
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    obtain ⟨rfl, -⟩ := hcond hc
    exact absurd List.nodup_nil hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans _ _
    exact ⟨_, rfl⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4 ?_
    intro b I ports chans _ _ _ _ _
    exact ⟨_, rfl⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc pre d post _ _ _ hI
    exact (hnil (hcond hc).2 hI).elim
  · refine mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6 ?_
    intro b I ports chans _ _ _ _ _
    exact ⟨_, rfl⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc pre d post _ _ _ hI
    exact (hnil (hcond hc).2 hI).elim
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc pre d post m _ _ _ hI
    exact (hnil (hcond hc).2 hI).elim
  · refine mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10 ?_
    intro b I ports chans _ _
    exact ⟨_, rfl⟩

/-- ✗ A composition that rejects an instance without transitions composed with no binding kills
the mutant without line 9: every rejection and shape line holds of it, but composing the empty
instance `s` of `E` passes every check and must succeed (skeptic correction S2). -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noAcceptance_killed :
    MOD_020_mutant_noAcceptance mod020_ty refBuild mod020_mg mod020_rejectEmpty ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_rejectEmpty := by
  refine ⟨mod020_rejectEmpty_meets, fun h => ?_⟩
  obtain ⟨hch, hco, hfr⟩ := mod020_empty_premises
  obtain ⟨b', hb'⟩ := h.2.2.2.2.2.2.2.2.1 Bld.empty mod020_emptyI [] [] hch hco hfr
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  have he : mod020_rejectEmpty Bld.empty mod020_emptyI [] [] = .error "rejected" := by
    unfold mod020_rejectEmpty mod020_ite
    rw [if_pos (by decide)]
  rw [he] at hb'
  cases hb'


/-! ### Mutant 10: line 10 dropped (an unknown channel ignored) -/

theorem mod020_knownChans_unchanneled (I : Instance String Unit)
    (chans : List (String × CDef String Unit)) :
    mod020_unchanneled I (mod020_knownChans I chans) = mod020_unchanneled I chans := by
  funext d
  simp only [mod020_unchanneled, mod020_knownChans, List.all_filter]
  congr 1
  funext c
  cases I.chan c.1 <;> simp

theorem mod020_knownChans_fresh {b : Bld String Unit} {I : Instance String Unit}
    {ports : List (String × String)} {chans : List (String × CDef String Unit)}
    (h : mod020_fresh b I ports chans) : mod020_fresh b I ports (mod020_knownChans I chans) := by
  refine ⟨h.1.sublist ?_, fun c hc => h.2.1 c (List.mem_of_mem_filter hc),
    fun c hc => h.2.2 c (List.mem_of_mem_filter hc)⟩
  exact (List.filter_sublist.map _).append_left _

theorem mod020_skipUnknownChan_meets :
    MOD_020_mutant_noChans mod020_ty refBuild mod020_mg mod020_skipUnknownChan := by
  have hcond : ∀ {I : Instance String Unit} {chans : List (String × CDef String Unit)},
      (chans.any fun c => (I.chan c.1).isNone) = true → ¬ ChansOk I chans := by
    intro I chans h hok
    obtain ⟨c, hc, hn⟩ := List.any_eq_true.1 h
    exact hok.2.1 c hc (Option.isNone_iff_eq_none.1 hn)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 ?_
    intro b I ports chans _ b' hco hfr h
    obtain ⟨ms, hd, hl, hs, hmg, hp⟩ :=
      mod020_R_line1 b I ports (mod020_knownChans I chans) b' hco (mod020_knownChans_fresh hfr) h
    refine ⟨ms, hd, hl, ?_, fun d hd c hc hcn => hmg d hd c ?_ hcn, hp⟩
    · rw [mod020_knownChans_unchanneled] at hs
      exact hs
    · exact List.mem_filter.2 ⟨hc, by simp [hcn]⟩
  · exact mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2
      (fun b I ports chans _ hu hd hcn => mod020_R_line2 b I ports _
        (hu.sublist (List.filter_sublist.map _)) hd (hcn.sublist (List.filter_sublist.map _)))
  · exact mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3
      (fun b I ports chans _ => mod020_R_line3 b I ports _)
  · exact mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4
      (fun b I ports chans _ => mod020_R_line4 b I ports _)
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc _ _ _ hch
    exact absurd hch.2.2.2 (hcond hc)
  · exact mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6
      (fun b I ports chans _ => mod020_R_line6 b I ports _)
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc _ _ _ hch
    exact absurd hch.2.2.2 (hcond hc)
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc _ _ _ _ hch
    exact absurd hch.2.2.2 (hcond hc)
  · refine mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 ?_
    intro b I ports chans hc hch
    exact absurd hch.2.2.2 (hcond hc)

set_option maxRecDepth 20000 in
/-- ✗ A composition that ignores a binding of an unknown channel kills the mutant without line
10: it meets every other line, but binding the channel `nope`, which `Join` does not declare, to a
caller transition `host` succeeds, where line 10 asks for a failure. -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noChans_killed :
    MOD_020_mutant_noChans mod020_ty refBuild mod020_mg mod020_skipUnknownChan ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_skipUnknownChan := by
  refine ⟨mod020_skipUnknownChan_meets, fun h => ?_⟩
  obtain ⟨m, he⟩ := h.2.2.2.2.2.2.2.2.2 Bld.empty mod020_I0 [] [("nope", bindExDef "host" [] none)]
    (fun hok => hok.2.1 ("nope", bindExDef "host" [] none) (by simp) (by decide))
  have hok : (mod020_skipUnknownChan Bld.empty mod020_I0 []
      [("nope", bindExDef "host" [] none)]).toOption.isSome = true := by decide
  rw [he] at hok
  cases hok


/-! ### Mutants 5, 7 and 8: a message line dropped (the message replaced by `rejected`) -/

section HushLines

/-- A hushed reference meets line 1 on every call. -/
theorem mod020_hush_P1 (b : Bld String Unit) (I : Instance String Unit)
    (ports : List (String × String)) (chans : List (String × CDef String Unit)) :
    mod020_P1 mod020_mg b I ports chans (mod020_hush mod020_R b I ports chans) :=
  fun b' hco hfr h => mod020_R_line1 b I ports chans b' hco hfr (mod020_hush_ok.1 h)

/-- A hushed reference meets line 4 on every call. -/
theorem mod020_hush_P4 (b : Bld String Unit) (I : Instance String Unit)
    (ports : List (String × String)) (chans : List (String × CDef String Unit)) :
    mod020_P4 I ports (mod020_hush mod020_R b I ports chans) := fun d hd hco hin => by
  obtain ⟨m, he⟩ := mod020_R_line4 b I ports chans d hd hco hin
  exact ⟨_, mod020_hush_err he⟩

/-- A hushed reference meets line 6 on every call. -/
theorem mod020_hush_P6 (b : Bld String Unit) (I : Instance String Unit)
    (ports : List (String × String)) (chans : List (String × CDef String Unit)) :
    mod020_P6 I ports (mod020_hush mod020_R b I ports chans) := fun d hd hco hout => by
  obtain ⟨m, he⟩ := mod020_R_line6 b I ports chans d hd hco hout
  exact ⟨_, mod020_hush_err he⟩

/-- A hushed reference meets line 9 on every call. -/
theorem mod020_hush_P9 (b : Bld String Unit) (I : Instance String Unit)
    (ports : List (String × String)) (chans : List (String × CDef String Unit)) :
    mod020_P9 mod020_ty refBuild mod020_mg b I ports chans (mod020_hush mod020_R b I ports chans) :=
  fun h1 h2 h3 h4 h5 => by
    obtain ⟨b', hb⟩ := mod020_R_line9 b I ports chans h1 h2 h3 h4 h5
    exact ⟨b', mod020_hush_ok.2 hb⟩

/-- A hushed reference meets line 10 on every call. -/
theorem mod020_hush_P10 (b : Bld String Unit) (I : Instance String Unit)
    (ports : List (String × String)) (chans : List (String × CDef String Unit)) :
    mod020_P10 I chans (mod020_hush mod020_R b I ports chans) := fun h => by
  obtain ⟨m, he⟩ := mod020_R_line10 b I ports chans h
  exact ⟨_, mod020_hush_err he⟩

end HushLines

theorem mod020_noInMsg_meets :
    MOD_020_mutant_noInMessage mod020_ty refBuild mod020_mg mod020_noInMsg := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)},
      ((portCheck mod020_ty I ports).isNone &&
        I.defs.any (fun d => !(inPairs (bindEntries I ports) d).isEmpty)) = true →
      (PortsDistinct ports ∧ PortsKnown I ports) ∧
        ∃ d ∈ I.defs, InCollision (bindEntries I ports) d := by
    intro I ports h
    simp only [Bool.and_eq_true] at h
    have hp' := mod020_portCheck_spec h.1
    exact ⟨⟨hp'.1, hp'.2.1⟩, mod020_someIn h.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 (fun b I ports chans _ => mod020_hush_P1 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    exact absurd (hcond hc).1.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    exact absurd (hcond hc).1.2 hk
  · exact mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4
      (fun b I ports chans _ => mod020_hush_P4 b I ports chans)
  · exact mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6
      (fun b I ports chans _ => mod020_hush_P6 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc pre d post _ _ _ hI hpre hpost hnin
    obtain ⟨-, d3, hd3, hin⟩ := hcond hc
    rcases mod020_split_mem hI hd3 with h | rfl | h
    · exact absurd hin (hpre _ h).1.1
    · exact absurd hin hnin
    · exact absurd hin (hpost _ h).1
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc pre d post m _ _ _ hI hpre hpost hd
    obtain ⟨-, d3, hd3, hin⟩ := hcond hc
    rcases mod020_split_mem hI hd3 with h | rfl | h
    · exact absurd hin (hpre _ h).1.1
    · exact absurd hin hd.1
    · exact absurd hin (hpost _ h).1
  · exact mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 (fun b I ports chans _ => mod020_hush_P9 b I ports chans)
  · exact mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10
      (fun b I ports chans _ => mod020_hush_P10 b I ports chans)

theorem mod020_noOutMsg_meets :
    MOD_020_mutant_noOutMessage mod020_ty refBuild mod020_mg mod020_noOutMsg := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)},
      ((portCheck mod020_ty I ports).isNone &&
        I.defs.any (fun d => !(outPairs (bindEntries I ports) d).isEmpty)) = true →
      (PortsDistinct ports ∧ PortsKnown I ports) ∧
        ∃ d ∈ I.defs, OutCollision (bindEntries I ports) d := by
    intro I ports h
    simp only [Bool.and_eq_true] at h
    have hp' := mod020_portCheck_spec h.1
    exact ⟨⟨hp'.1, hp'.2.1⟩, mod020_someOut h.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 (fun b I ports chans _ => mod020_hush_P1 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    exact absurd (hcond hc).1.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    exact absurd (hcond hc).1.2 hk
  · exact mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4
      (fun b I ports chans _ => mod020_hush_P4 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc pre d post _ _ _ hI hpre hpost hnout
    obtain ⟨-, d3, hd3, hout⟩ := hcond hc
    rcases mod020_split_mem hI hd3 with h | rfl | h
    · exact absurd hout (hpre _ h).1.2
    · exact absurd hout hnout
    · exact absurd hout (hpost _ h).2
  · exact mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6
      (fun b I ports chans _ => mod020_hush_P6 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P8 mod020_ty refBuild I ports chans r)
      mod020_R_line8 ?_
    intro b I ports chans hc pre d post m _ _ _ hI hpre hpost hd
    obtain ⟨-, d3, hd3, hout⟩ := hcond hc
    rcases mod020_split_mem hI hd3 with h | rfl | h
    · exact absurd hout (hpre _ h).1.2
    · exact absurd hout hd.2
    · exact absurd hout (hpost _ h).2
  · exact mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 (fun b I ports chans _ => mod020_hush_P9 b I ports chans)
  · exact mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10
      (fun b I ports chans _ => mod020_hush_P10 b I ports chans)

theorem mod020_noBuildMsg_meets :
    MOD_020_mutant_noBuildMessage mod020_ty refBuild mod020_mg mod020_noBuildMsg := by
  have hcond : ∀ {I : Instance String Unit} {ports : List (String × String)},
      ((portCheck mod020_ty I ports).isNone &&
        I.defs.all (fun d => (inPairs (bindEntries I ports) d).isEmpty) &&
        I.defs.all (fun d => (outPairs (bindEntries I ports) d).isEmpty) &&
        I.defs.any (fun d => (refBuild (rewriteDef (bindEntries I ports) d).toTrans).isSome))
        = true →
      (PortsDistinct ports ∧ PortsKnown I ports) ∧
        (∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d) ∧
        (∀ d ∈ I.defs, ¬ OutCollision (bindEntries I ports) d) := by
    intro I ports h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp, hi⟩, ho⟩, -⟩ := h
    have hp' := mod020_portCheck_spec hp
    exact ⟨⟨hp'.1, hp'.2.1⟩, mod020_noIn hi, mod020_noOut ho⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mod020_lift (fun b I ports chans r => mod020_P1 mod020_mg b I ports chans r)
      mod020_R_line1 (fun b I ports chans _ => mod020_hush_P1 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P2 ports chans r) mod020_R_line2 ?_
    intro b I ports chans hc _ hnd
    exact absurd (hcond hc).1.1 hnd
  · refine mod020_lift (fun b I ports chans r => mod020_P3 I ports r) mod020_R_line3 ?_
    intro b I ports chans hc hk
    exact absurd (hcond hc).1.2 hk
  · exact mod020_lift (fun b I ports chans r => mod020_P4 I ports r) mod020_R_line4
      (fun b I ports chans _ => mod020_hush_P4 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P5 mod020_ty refBuild I ports chans r)
      mod020_R_line5 ?_
    intro b I ports chans hc pre d post _ _ _ hI _ _ _ hin
    exact absurd hin ((hcond hc).2.1 d (mod020_mem_of_split hI))
  · exact mod020_lift (fun b I ports chans r => mod020_P6 I ports r) mod020_R_line6
      (fun b I ports chans _ => mod020_hush_P6 b I ports chans)
  · refine mod020_lift (fun b I ports chans r => mod020_P7 mod020_ty refBuild I ports chans r)
      mod020_R_line7 ?_
    intro b I ports chans hc pre d post _ _ _ hI _ _ _ hout
    exact absurd hout ((hcond hc).2.2 d (mod020_mem_of_split hI))
  · exact mod020_lift
      (fun b I ports chans r => mod020_P9 mod020_ty refBuild mod020_mg b I ports chans r)
      mod020_R_line9 (fun b I ports chans _ => mod020_hush_P9 b I ports chans)
  · exact mod020_lift (fun b I ports chans r => mod020_P10 I chans r) mod020_R_line10
      (fun b I ports chans _ => mod020_hush_P10 b I ports chans)

set_option maxRecDepth 20000 in
/-- ✗ A composition that fails an input collision with the message `rejected` kills the mutant
without line 5: it fails every call the reference fails, but binding `a` and `b` of `Join` under
`s` to `X`, where `s/join` takes from both and nothing else is wrong, gives `rejected` instead of
the input collision message naming `a`, `b`, `s`, `X` and `s/join` (AC7). -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noInMessage_killed :
    MOD_020_mutant_noInMessage mod020_ty refBuild mod020_mg mod020_noInMsg ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_noInMsg := by
  refine ⟨mod020_noInMsg_meets, fun h => ?_⟩
  have hI : mod020_I0.defs = [] ++ mod020_d0 :: [] := rfl
  obtain ⟨_, -, _, -, -, pa, pb, -, he⟩ := h.2.2.2.2.1 Bld.empty mod020_I0 [("a", "X"), ("b", "X")]
    [] [] mod020_d0 []
    ⟨by simp [PortsDistinct], by unfold PortsKnown; decide, fun _ _ _ _ => rfl, by simp [ChansOk]⟩
    (by unfold mod020_coherent; decide) (by decide) hI
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (outPairs_eq_nil_iff.1 (by decide))
    ⟨"s/a", by decide, "s/b", by decide, mod020_clash_of_isSome (by decide)⟩
  have hr : bindExErr (mod020_noInMsg Bld.empty mod020_I0 [("a", "X"), ("b", "X")] []) =
      some "rejected" := by decide
  rw [he] at hr
  exact mod020_inMsg_ne _ _ _ _ _ (by decide) (Option.some.inj hr)

set_option maxRecDepth 20000 in
/-- ✗ A composition that fails an output collision with the message `rejected` kills the
mutant without line 7: it fails every call the reference fails, but binding `a` and `b` of a
`Split` whose `split` writes `And(a, b)` to `X` gives `rejected` instead of the output collision
message naming `a`, `b`, `s`, `X` and `s/split` (AC8). -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noOutMessage_killed :
    MOD_020_mutant_noOutMessage mod020_ty refBuild mod020_mg mod020_noOutMsg ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_noOutMsg := by
  refine ⟨mod020_noOutMsg_meets, fun h => ?_⟩
  have hI : (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s").defs =
      [] ++ mod020_splitDef (.and (.place "a") (.place "b")) :: [] := rfl
  have hdo : (mod020_splitDef (.and (.place "a") (.place "b"))).out =
      some (.and (.place "s/a") (.place "s/b")) := rfl
  obtain ⟨_, -, _, -, _, -, _, -, -, pa, pb, -, he⟩ := h.2.2.2.2.2.2.1 Bld.empty
    (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s")
    [("a", "X"), ("b", "X")] [] [] (mod020_splitDef (.and (.place "a") (.place "b"))) []
    ⟨by simp [PortsDistinct], by unfold PortsKnown; decide, fun _ _ _ _ => rfl, by simp [ChansOk]⟩
    (by unfold mod020_coherent; decide) (by decide) hI
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (inPairs_eq_nil_iff.1 (by decide))
    ⟨_, hdo, ["s/a", "s/b"], by decide, "s/a", by decide, "s/b", by decide,
      mod020_clash_of_isSome (by decide)⟩
  have hr : bindExErr (mod020_noOutMsg Bld.empty
      (renamedInstance strNaming (bindExSplit (.and (.place "a") (.place "b"))) "s")
      [("a", "X"), ("b", "X")] []) = some "rejected" := by decide
  rw [he] at hr
  exact mod020_outMsg_ne _ _ _ _ _ (by decide) (Option.some.inj hr)

set_option maxRecDepth 20000 in
/-- ✗ A composition that fails a transition-builder rejection with the message `rejected` kills
the mutant without line 8: it fails every call the reference fails, but binding `a` and `b` of a
`Split` whose `split` writes `Xor(a, b)` to `X` gives `rejected` instead of the transition
builder's IO-012 message for `Xor(X, X)` (AC8). -/
@[evidence mutant MOD_020]
theorem MOD_020_mutant_noBuildMessage_killed :
    MOD_020_mutant_noBuildMessage mod020_ty refBuild mod020_mg mod020_noBuildMsg ∧
      ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_noBuildMsg := by
  refine ⟨mod020_noBuildMsg_meets, fun h => ?_⟩
  have hI : (renamedInstance strNaming (bindExSplit (.xor (.place "a") (.place "b"))) "s").defs =
      [] ++ mod020_splitDef (.xor (.place "a") (.place "b")) :: [] := rfl
  have he := h.2.2.2.2.2.2.2.1 Bld.empty
    (renamedInstance strNaming (bindExSplit (.xor (.place "a") (.place "b"))) "s")
    [("a", "X"), ("b", "X")] [] [] (mod020_splitDef (.xor (.place "a") (.place "b"))) []
    "output spec of transition 's/split' is ambiguous: output branches 0 and 1 both claim {X}; no write can tell them apart (IO-012)"
    ⟨by simp [PortsDistinct], by unfold PortsKnown; decide, fun _ _ _ _ => rfl, by simp [ChansOk]⟩
    (by unfold mod020_coherent; decide) (by decide) hI
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    ⟨inPairs_eq_nil_iff.1 (by decide), outPairs_eq_nil_iff.1 (by decide)⟩ (by decide)
  have hr : bindExErr (mod020_noBuildMsg Bld.empty
      (renamedInstance strNaming (bindExSplit (.xor (.place "a") (.place "b"))) "s")
      [("a", "X"), ("b", "X")] []) = some "rejected" := by decide
  rw [he] at hr
  exact absurd hr (by decide)


/-! ### Further wrong compositions, forbidden outright -/

/-- The transition `s/go` of `C` instantiated under `s`. -/
def mod020_goDef : CDef String Unit :=
  CDef.map (strNaming.pre "s") (preS "s") (bindExDef "go" [⟨"a", .one⟩] (some (.place "x")))

/-- A composition that drops the channel bindings: every instance transition is rewritten and
added, and no merge is made, as if the staged merges were keyed by one name and looked up by
another. -/
def mod020_dropChans : ComposeFn String Unit := fun b I ports _ => mod020_R b I ports []

set_option maxRecDepth 20000 in
/-- ✗ A composition that drops the channel bindings violates MOD-020 (line 1): binding channel
`go` of a subnet `C` under `s` to a caller transition `host` leaves the unmerged `s/go` in the
builder and no `host`, where line 1 asks for the merge of `host` with the rewritten `s/go` among
the new transitions. -/
@[evidence forbids MOD_020]
theorem MOD_020_forbids_dropChannels :
    ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_dropChans := by
  intro h
  have hnames : (mod020_dropChans Bld.empty (renamedInstance strNaming bindExChan "s")
      [("a", "X")] [("go", bindExDef "host" [] none)]).toOption.map
        (fun b => b.defs.map (·.core.name)) = some ["s/go"] := by decide
  cases hr : mod020_dropChans Bld.empty (renamedInstance strNaming bindExChan "s")
      [("a", "X")] [("go", bindExDef "host" [] none)] with
  | error m => rw [hr] at hnames; cases hnames
  | ok b0 =>
    rw [hr] at hnames
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at hnames
    obtain ⟨ms, hd, -, -, hmg, -⟩ := h.1 Bld.empty (renamedInstance strNaming bindExChan "s")
      [("a", "X")] [("go", bindExDef "host" [] none)] b0
      (by unfold mod020_coherent; decide) (by unfold mod020_fresh; decide) hr
    have hI : (renamedInstance strNaming bindExChan "s").defs = [mod020_goDef] := rfl
    obtain ⟨m, hm, hmm⟩ := hmg mod020_goDef (by rw [hI]; exact List.mem_singleton_self _)
      ("go", bindExDef "host" [] none) (List.mem_singleton_self _) (by decide)
    cases hmm
    have hmem : (bindExDef "host" [] none).core.name ∈ b0.defs.map (·.core.name) := by
      rw [hd]; exact List.mem_map_of_mem (List.mem_append_right _ hm)
    rw [hnames] at hmem
    revert hmem
    decide

set_option maxRecDepth 20000 in
/-- A composition whose collision check only reports a caller place that exactly two bound ports
reach: three ports that one transition consumes from fall through to the rebuild and fail with the
transition builder's message, which names only the transition. -/
def mod020_threeToBuild : ComposeFn String Unit :=
  mod020_ite (fun _ I ports _ => (portCheck mod020_ty I ports).isNone &&
      I.defs.any (fun d => mod020_three (bindEntries I ports) (d.core.inputs.map (·.place))))
    (fun _ I ports _ => .error ((I.defs.findSome? fun d =>
      refBuild (rewriteDef (bindEntries I ports) d).toTrans).getD "rejected"))
    mod020_R

set_option maxRecDepth 20000 in
/-- ✗ A collision check that only reports two ports on one caller place violates MOD-020 (line
5): binding ports `a`, `b` and `c` of `Join3` under `s`, whose `s/join` takes from all three, to
`X` fails with the transition builder's CORE-030 message, where line 5 asks for the input
collision message naming a colliding pair of the three ports, `s`, `X` and `s/join`, as every
runtime gives. -/
@[evidence forbids MOD_020]
theorem MOD_020_forbids_threePortToBuild :
    ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_threeToBuild := by
  intro h
  have hI : (renamedInstance strNaming mod020_join3 "s").defs = [] ++ mod020_join3d :: [] := rfl
  obtain ⟨_, -, _, -, -, pa, pb, -, he⟩ := h.2.2.2.2.1 Bld.empty
    (renamedInstance strNaming mod020_join3 "s") [("a", "X"), ("b", "X"), ("c", "X")] []
    [] mod020_join3d []
    ⟨by simp [PortsDistinct], by unfold PortsKnown; decide, fun _ _ _ _ => rfl, by simp [ChansOk]⟩
    (by unfold mod020_coherent; decide) (by decide) hI
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (outPairs_eq_nil_iff.1 (by decide))
    ⟨"s/a", by decide, "s/b", by decide, mod020_clash_of_isSome (by decide)⟩
  have hr : bindExErr (mod020_threeToBuild Bld.empty (renamedInstance strNaming mod020_join3 "s")
      [("a", "X"), ("b", "X"), ("c", "X")] []) = some "CORE-030" := by decide
  rw [he] at hr
  exact mod020_inMsg_ne _ _ _ _ _ (by decide) (Option.some.inj hr)

/-- A composition that fails a re-bound port with a message that names no port. -/
def mod020_genericDup : ComposeFn String Unit :=
  mod020_ite (fun _ _ ports _ => (bindDup (ports.map (·.1))).isSome)
    (fun _ _ _ _ => .error "rejected") mod020_R

set_option maxRecDepth 20000 in
/-- ✗ A composition that fails a re-bound port with a generic message violates MOD-020 (line 2):
binding port `a` of `Join` under `s` to `X` and again to `Y` fails with `rejected`, which does not
contain `a`, where line 2 asks for an error naming `a` (AC5). -/
@[evidence forbids MOD_020]
theorem MOD_020_forbids_genericDup :
    ¬ MOD_020 mod020_ty refBuild mod020_mg mod020_genericDup := by
  intro h
  obtain ⟨n, m, hc, he, hn⟩ := h.2.1 Bld.empty mod020_I0 [("a", "X"), ("a", "Y")] []
    List.nodup_nil (by simp [PortsDistinct]) List.nodup_nil
  have hna : n = "a" := by
    by_contra hne
    have : List.count n (List.map (fun x => x.1) [("a", "X"), ("a", "Y")]) = 0 := by
      simp only [List.map_cons, List.map_nil, List.count_eq_zero, List.mem_cons,
        List.not_mem_nil, or_false, or_self]
      exact fun h => hne h
    omega
  subst hna
  have hr : bindExErr (mod020_genericDup Bld.empty mod020_I0 [("a", "X"), ("a", "Y")] []) =
      some "rejected" := by decide
  rw [he] at hr
  cases hr
  exact mod020_names_a (by decide) hn

end Libpetri.Spec
