import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.GlossaryAction
import Libpetri.Reference.ComposeBind
import Libpetri.Spec.Req.MOD_006

set_option linter.missingDocs true

/-!
# MOD-025: Direct composition (`spec/11-modular-composition.md`)

MOD-025 is a builder requirement (kind B) over an abstract direct-composition function
`D : DirectFn N A` (an enclosing builder and a subnet definition give the builder after the call,
or a rejection with a message), a naming model `Nm : Naming N` and a run-time token type
`tyOf : N → T` of places. Places are keys of the place model: by name in TypeScript, Rust and
Python (`strNaming`, and `tyOf` constant, so the type line says nothing there), by name and token
type in Java (`typedNaming`, `tyOf := Prod.snd`).

The block says what a successful direct composition leaves in the builder (the earlier
transitions followed by the body's, unchanged and under their own names; every body place and
every place a body arc names, merged by equality with the places the builder holds), when it
fails (a body transition name the builder already holds, with a message naming it; a declared
channel; a same-named place of another token type; a terminal place the body declares), when it
succeeds, and that two direct compositions give the same places and the same transitions in
either order.

The witness is the reference direct composition `refDirect Nm tyOf`
(`Reference/ComposeBind.lean`); the block holds for every naming model and every token type
map. The order line follows from the others for every model (`mod025_line6_of`), and so do
the same for any number of definitions in any order (`mod025_perm`) and the no-op of an empty
subnet (`mod025_empty`). Wrong compositions are killed, one per line: one
that reverses the body's transitions, one that adds a body place the builder already holds a
second time, one without the name check, one whose rejection names nothing, one without the
channel check, one without the type check (the name-only check of Rust on Java's places), one
that rejects everything, and one without the terminal check, which drops the body's terminal
declarations without a word. Two more are forbidden: one that prefixes the body's transition
names (as instantiation would), and one that keeps the first of two same-named places and
renames the second, which is order-sensitive.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary of the order line -/

section Vocab

variable {N A : Type}

/-- Every place a body transition of `S` names is a body place of `S`: true of every subnet
definition the subnet builder builds, whose body holds every place an arc names ([MOD-006],
[CORE-040]). -/
def DirectClosed (S : SubnetDef N A) : Prop :=
  ∀ d ∈ S.defs, ∀ p ∈ d.namedPlaces, p ∈ S.places

/-- Two builders hold the same flat net: the same places (as a set), the same transition
definitions (in some order), and the same terminal places, retired ports and fusion sets. -/
def DirectSame (c c' : Bld N A) : Prop :=
  (∀ p, p ∈ c.places ↔ p ∈ c'.places) ∧ c.defs.Perm c'.defs ∧ c.terminals = c'.terminals ∧
    c.retired = c'.retired ∧ c.fusions = c'.fusions

end Vocab

/-! ## MOD-025: Direct Composition (compose a subnet without instantiation) -/

requirement MOD_025
  id "MOD-025"
  title "Direct Composition (compose a subnet without instantiation)"
  kind B
  scope "every direct composition of a subnet definition into an enclosing builder (Java, TypeScript, Rust, Python); the token-type line where place identity carries the token type (Java)"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* direct composition of a subnet definition into an enclosing builder succeeds, the builder *shall* hold its earlier transitions followed by the body's transitions in the body's order, each unchanged and under its original name, and its earlier places together with every body place and every place a body transition names, a body place equal to a place it already holds being that place, no place added twice, and nothing else of the builder changed but the subnet membership of [MOD-026]."
        "*If* a body transition's name is the name of a transition already in the enclosing builder, *then* direct composition *shall* fail at the call."
        "*If* the subnet definition declares no terminal place and no channel and exactly one name of its body transitions is the name of a transition already in the enclosing builder, *then* the error *shall* name that transition and the subnet definition."
        "*If* the interface of a subnet definition declares a channel, *then* direct composition of that definition *shall* fail at the call."
        "*Where* place identity carries the token type ([CORE-002]), *if* a body place has the name of a place the enclosing builder holds and a different token type, *then* direct composition *shall* fail at the call."
        "*When* a subnet definition that declares no terminal place ([EXEC-042]) and no channel is composed directly into an enclosing builder that holds no transition with the name of a body transition and, where place identity carries the token type, no place with the name of a body place and a different token type, direct composition *shall* succeed."
        "*If* two subnet definitions that declare no terminal place, and whose body transitions name only their own body places, are composed directly one after the other into one builder and both calls succeed, *then* composing them in the other order *shall* also succeed in both calls and give a builder with the same places and the same transitions, each with its arcs, timing, priority and action."
        "*If* the body of a subnet definition declares a terminal place ([EXEC-042]), *then* direct composition of that definition *shall* fail at the call."
  reading "For every naming model Nm, every token type map tyOf on places and every direct-composition function D:"
          "if D b S returns the builder b', then the definitions of b' are those of b followed by those of S (the same values, so name, arcs, output specification, timing, priority and action unchanged); a place is in b' exactly when it is in b, is a place of S, or is named by a definition of S; the places of b' are, in some order, those of b (each as often as in b) and some new places, each once and none of them a place of b; and the terminal places, retired ports and fusion sets of b' are those of b;"
          "if some definition of S has the name of a definition of b, D b S fails; if moreover S declares no terminal place and no channel and every such definition of S has the name n, D b S fails with a message that contains n and contains the name of S;"
          "if S declares a channel, D b S fails;"
          "if some place x of S and some place h of b have the same name (Nm.name) and tyOf h differs from tyOf x, D b S fails;"
          "if S declares no terminal place and no channel, no definition of S has the name of a definition of b, and no place of S has the name of a place of b with another tyOf, D b S succeeds;"
          "if S1 and S2 declare no terminal place, every place a definition of S1 (of S2) names is a place of S1 (of S2), D b S1 returns b1 and D b1 S2 returns c, then D b S2 returns some b2 and D b2 S1 returns some c' with the same places as c (as a set), the same definitions (as a permutation), and the same terminal places, retired ports and fusion sets;"
          "if S declares a terminal place, D b S fails."
  assumes "The builder is the composition model's Bld (Reference/ComposeBind.lean): its places, its transition definitions in the order added, its declared terminal places, retired ports (MOD-027), direct-composition contributions (MOD-026) and fusion sets (MOD-060). A direct-composition function (DirectFn) is one implementation's compose(SubnetDef) call read as a function of the builder at the call and the definition: Rust compose_direct (rust/libpetri-core/src/petri_net.rs:536-607), Java Builder.compose(SubnetDef) (java/src/main/java/org/libpetri/core/PetriNet.java:576-645), TypeScript composeDirect (typescript/src/core/petri-net.ts:341-402), Python through the Rust call. A panic or exception is a rejection (.error msg); 'at the call' is that D b S itself fails, which is 'at compose time' and item 4 (composition is eager, MOD-020): nothing waits for build(). That the builder offers a direct-composition operation at all is an existence clause, not a safety line: it belongs in a coverage theorem (as ExecCoversW5 does for the execution blocks), not in this block."
          "Places are the abstract N, the key type of the place model (CORE-002), so 'merge purely by name equality' is equality of keys: a body place equal to a place the builder holds is that place. Under strNaming (TypeScript, Rust, Python) a key is the name; under typedNaming (Java) it is the name and the token type, and a same-named place of another type is the type line's rejection, so no two places of one name arise either way. Line 4 is the token-type sentence for the implementations whose place identity carries the token type (Java, ruling D36 (a)): tyOf is the token type there (Prod.snd on typedNaming keys). Rust and TypeScript compare places by name and document the name-only merge (petri_net.rs:525-527, petri-net.ts:334-336), the MAY carve-out of the markdown: for them tyOf is constant and line 4 asks nothing. The markdown's MUST that such implementations document the name-only merge contract in their API surface is a documentation obligation, not behaviour, and no line states it; those doc comments are where it is met. The compile-time half of a token type is not modelled."
          "Line 1 is items 1 to 3. 'Unchanged' is equality of the definition values (CDef), so arcs, output specification, timing, priority and action tag are those of the body; that the action is shared by reference is MOD-030's line, and that a directly-composed definition carries no correspondence is MOD-031's. The order of places is not normative (ruling D32), so the places are compared up to order: 'no place added twice' is that the places after the call are the earlier ones, each as often as before, and some new ones, each once and none held before (AC1's single output place). The definitions are compared as a list: the body's transitions follow the builder's in the body's order in all three runtimes, which is the declaration order EXEC-002 uses as its last tie-break. The subnet membership a direct composition records (the contrib field) is MOD-026's line, not this block's. The places a body arc names are added too: every runtime's transition() collects them (petri_net.rs:597-599, PetriNet.java:639-641, petri-net.ts:397-398), and every built body already holds them (DirectClosed)."
          "Line 2 is the paragraph on transition name collisions. The check is against the transitions the builder holds at the call (petri_net.rs:559-575, PetriNet.java:595-606, petri-net.ts:363-374): a host transition of the same name added after the call is not rejected by direct composition. That case falls under the shared unique-names assumption (ruling D10; RD-10 in spec/runtime-defects.md records that no builder checks transition names). For the same reason no line asks anything of two body transitions of one name, or of two transitions of one name the builder already holds: line 5 accepts such a call and line 1 adds both, as all three runtimes do, since they take the host's names once before the loop; such nets are RD-10's. The message part has a sole-offender premise (skeptic correction S3 of the composition design): all three runtimes check terminal places, then channels, then transition names, then (Java) token types, and stop at the first failure, so with several offending names the message names one of them, and with a terminal place or a channel it is that check's message. To name is to contain as a substring (MsgNames, as in MOD-006), so a message that lists every body transition, the offending one among them, also meets the message part; that the message names the offending transition and no innocent one is tested, not proven. The markdown asks the message to name both nets and to point at instantiate(prefix); the model's builder carries no net name, so the line asks for the transition and the subnet definition only, and the enclosing net's name and the pointer, which all three runtimes write, are tested, not proven."
          "Line 3 is the channel paragraph's rejection (all three runtimes: petri_net.rs:542-553, PetriNet.java:582-589, petri-net.ts:348-357). That the message names the channels and points at instantiation with explicit binding is tested, not proven: the reference's stand-in text does not list the channels. Line 4 is the token-type paragraph's rejection (PetriNet.java:608-622); that the message names the place and both token types is likewise tested, not proven. Java compares each body place with one host place per name, the one put last into a name-keyed map (PetriNet.java:611-615), so when the builder already holds two places of one name with different token types and the last one has the body place's type, Java accepts where line 4 rejects; this is runtime defect RD-24 (spec/runtime-defects.md)."
          "Line 5 is the acceptance line every partial composition function needs (skeptic correction S2: a function that rejects everything meets lines 2 to 4). Its premise on terminal places is line 7. Interface ports are advisory (MOD-004): no line reads the ports, so a port's place merges by equality like any other body place, and a model that consulted the ports could not meet line 1 and line 5 at once on a definition whose port places are its body places."
          "Line 6 is the order-independence paragraph as reworded under ruling D20 (clash mod-b#12): the two builders hold the same places, transitions and arcs, while the declaration order of the places and of the transitions follows the order of the calls (line 1). It is stated for two definitions (AC3); the body's 'any order' of any number of definitions follows for every model of the block (mod025_perm: a sequence of direct compositions that succeeds in one order succeeds in every reordering with the same flat net), since by lines 1 to 5 a later call depends on the builder only through its places and transition names as sets (mod025_congr). Its premises hold of every built subnet definition (DirectClosed, above) except the terminal places, which line 7 rejects in every order. Line 6 follows from lines 1 to 5 for every model (mod025_line6_of): a successful first call shows the second definition clashes with neither the builder nor the first definition, and the clash checks read only set membership. So it has no mutant of its own (as for MOD-010 AC2, skeptic correction S4); without its premise on body places it would not follow, since the type check reads the body places only (Reference/ComposeBind.lean, notes of the model step)."
          "Line 7 is EXEC-042 AC6 for direct composition, which EXEC-042's block leaves to the composition model: a subnet body that declares terminal places is rejected by compose. All three runtimes reject it before any other check (petri_net.rs:539, PetriNet.java:578, petri-net.ts:345), so the body's terminal declarations are never dropped without a word. That the message names the place is tested, not proven: the reference's stand-in text names the subnet only (all three runtimes name the first terminal place through the helper instantiate uses). The same rejection by instantiate, with the message naming the place, is MOD-010 line 4."
          "AC1 (one output place, the body arc on the host place) is line 1 and MOD_025_nonvacuous. AC2 (body transitions under their original names, no prefix/ separator introduced) is line 1: the definitions are the body's own values; MOD_025_forbids_prefixes kills a composition that prefixes them. AC3 (two subnets in opposite orders give the same place set, transition set and arc topology) is line 6, with its example in MOD_025_nonvacuous. AC4 (a transition name collision is rejected at compose time, naming the transition and pointing at instantiation) is line 2. AC5 (a declared channel is rejected) is line 3. AC6 (token-typed implementations reject a same-named body place of another type) is line 4. AC7 (an empty subnet is a no-op) follows from lines 1 and 5 (mod025_empty), up to the order of the places and the membership records of MOD-026. AC8 (direct and instance composition may be mixed, un-prefixed and prefix/ names coexist) is line 5: a direct composition is rejected only for a name the builder holds, and a renamed name p/x is not the body's name x; that instance composition then accepts the result is MOD-020's. AC9 (direct composition then build() is indistinguishable from a hand-written net) and the sentence 'The result MUST satisfy [MOD-023]' are MOD-023's line that a built net passes the build checks and is flat (composition wave W8), with its DOT clause reworded under ruling D20 (clash mod-b#11). The sentences on when to use direct composition and that it is additive are guidance, not behaviour."
  signoff "pending"
  statement : ∀ {N A T : Type}, Naming N → (N → T) → DirectFn N A → Prop :=
    fun {N A T} Nm (tyOf : N → T) D =>
      (∀ (b b' : Bld N A) (S : SubnetDef N A), D b S = .ok b' →
        b'.defs = b.defs ++ S.defs ∧
        (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
        (∃ new : List N, b'.places.Perm (b.places ++ new) ∧ new.Nodup ∧ ∀ p ∈ new, p ∉ b.places) ∧
        b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions) ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), DirectNameClash b S →
        (∃ m, D b S = .error m) ∧
        ∀ n, S.terminals = [] → S.chans = [] →
          (∀ d ∈ S.defs, d.core.name ∈ b.defs.map (·.core.name) → d.core.name = n) →
          ∃ m, D b S = .error m ∧ MsgNames m n ∧ MsgNames m S.name) ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), S.chans ≠ [] → ∃ m, D b S = .error m) ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), DirectTypeClash Nm tyOf b S → ∃ m, D b S = .error m) ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), S.terminals = [] → S.chans = [] →
        ¬ DirectNameClash b S → ¬ DirectTypeClash Nm tyOf b S → ∃ b', D b S = .ok b') ∧
      (∀ (b b₁ c : Bld N A) (S₁ S₂ : SubnetDef N A), DirectClosed S₁ → DirectClosed S₂ →
        S₁.terminals = [] → S₂.terminals = [] → D b S₁ = .ok b₁ → D b₁ S₂ = .ok c →
        ∃ b₂ c', D b S₂ = .ok b₂ ∧ D b₂ S₁ = .ok c' ∧ DirectSame c c') ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), S.terminals ≠ [] → ∃ m, D b S = .error m)

/- The pinned readable form of MOD-025: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_025 : {N A T : Type} → Naming N → (N → T) → DirectFn N A → Prop :=
fun {N A T} Nm tyOf D =>
  (∀ (b b' : Bld N A) (S : SubnetDef N A),
      D b S = Except.ok b' →
        b'.defs = b.defs ++ S.defs ∧
          (∀ (p : N), p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
            (∃ new, b'.places.Perm (b.places ++ new) ∧ new.Nodup ∧ ∀ p ∈ new, p ∉ b.places) ∧
              b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions) ∧
    (∀ (b : Bld N A) (S : SubnetDef N A),
        DirectNameClash b S →
          (∃ m, D b S = Except.error m) ∧
            ∀ (n : String),
              S.terminals = [] →
                S.chans = [] →
                  (∀ d ∈ S.defs, d.core.name ∈ List.map (fun x => x.core.name) b.defs → d.core.name = n) →
                    ∃ m, D b S = Except.error m ∧ MsgNames m n ∧ MsgNames m S.name) ∧
      (∀ (b : Bld N A) (S : SubnetDef N A), S.chans ≠ [] → ∃ m, D b S = Except.error m) ∧
        (∀ (b : Bld N A) (S : SubnetDef N A), DirectTypeClash Nm tyOf b S → ∃ m, D b S = Except.error m) ∧
          (∀ (b : Bld N A) (S : SubnetDef N A),
              S.terminals = [] →
                S.chans = [] → ¬DirectNameClash b S → ¬DirectTypeClash Nm tyOf b S → ∃ b', D b S = Except.ok b') ∧
            (∀ (b b₁ c : Bld N A) (S₁ S₂ : SubnetDef N A),
                DirectClosed S₁ →
                  DirectClosed S₂ →
                    S₁.terminals = [] →
                      S₂.terminals = [] →
                        D b S₁ = Except.ok b₁ →
                          D b₁ S₂ = Except.ok c →
                            ∃ b₂ c', D b S₂ = Except.ok b₂ ∧ D b₂ S₁ = Except.ok c' ∧ DirectSame c c') ∧
              ∀ (b : Bld N A) (S : SubnetDef N A), S.terminals ≠ [] → ∃ m, D b S = Except.error m
-/
#guard_msgs in #print MOD_025

/-! ### The seven lines, named (for the mutants) -/

section Lines

variable {N A T : Type}

/-- Line 1 of MOD-025: what a success leaves in the builder. -/
def mod025_line1 (D : DirectFn N A) : Prop :=
  ∀ (b b' : Bld N A) (S : SubnetDef N A), D b S = .ok b' →
    b'.defs = b.defs ++ S.defs ∧
    (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
    (∃ new : List N, b'.places.Perm (b.places ++ new) ∧ new.Nodup ∧ ∀ p ∈ new, p ∉ b.places) ∧
    b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions

/-- Line 2 of MOD-025: a transition name the builder holds rejects, and a sole offender is
named. -/
def mod025_line2 (D : DirectFn N A) : Prop :=
  ∀ (b : Bld N A) (S : SubnetDef N A), DirectNameClash b S →
    (∃ m, D b S = .error m) ∧
    ∀ n, S.terminals = [] → S.chans = [] →
      (∀ d ∈ S.defs, d.core.name ∈ b.defs.map (·.core.name) → d.core.name = n) →
      ∃ m, D b S = .error m ∧ MsgNames m n ∧ MsgNames m S.name

/-- Line 3 of MOD-025: a declared channel rejects. -/
def mod025_line3 (D : DirectFn N A) : Prop :=
  ∀ (b : Bld N A) (S : SubnetDef N A), S.chans ≠ [] → ∃ m, D b S = .error m

/-- Line 4 of MOD-025: a same-named place of another token type rejects. -/
def mod025_line4 (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  ∀ (b : Bld N A) (S : SubnetDef N A), DirectTypeClash Nm tyOf b S → ∃ m, D b S = .error m

/-- Line 5 of MOD-025: no terminal place, no channel and no clash give success. -/
def mod025_line5 (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  ∀ (b : Bld N A) (S : SubnetDef N A), S.terminals = [] → S.chans = [] →
    ¬ DirectNameClash b S → ¬ DirectTypeClash Nm tyOf b S → ∃ b', D b S = .ok b'

/-- Line 6 of MOD-025: two direct compositions in either order. -/
def mod025_line6 (D : DirectFn N A) : Prop :=
  ∀ (b b₁ c : Bld N A) (S₁ S₂ : SubnetDef N A), DirectClosed S₁ → DirectClosed S₂ →
    S₁.terminals = [] → S₂.terminals = [] → D b S₁ = .ok b₁ → D b₁ S₂ = .ok c →
    ∃ b₂ c', D b S₂ = .ok b₂ ∧ D b₂ S₁ = .ok c' ∧ DirectSame c c'

/-- Line 7 of MOD-025: a terminal place the body declares rejects ([EXEC-042] AC6). -/
def mod025_line7 (D : DirectFn N A) : Prop :=
  ∀ (b : Bld N A) (S : SubnetDef N A), S.terminals ≠ [] → ∃ m, D b S = .error m

/-- MOD-025 is its seven lines. -/
theorem mod025_iff (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) :
    MOD_025 Nm tyOf D ↔ mod025_line1 D ∧ mod025_line2 D ∧ mod025_line3 D ∧
      mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧ mod025_line6 D ∧ mod025_line7 D :=
  Iff.rfl

end Lines

/-! ### Line 6 from the others -/

section Order

variable {N A T : Type}

/-- What line 6 needs of a success: the definitions are the old ones and the body's in some
order, the places are the old ones, the body's and those a body definition names, and the rest
is unchanged. -/
def DirectWeak (b : Bld N A) (S : SubnetDef N A) (b' : Bld N A) : Prop :=
  b'.defs.Perm (b.defs ++ S.defs) ∧
  (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
  b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions

/-- Five propositions: adding `b₁ ∨ c₁` then `b₂ ∨ c₂` to `a` is adding them in the other
order. -/
theorem mod025_or_swap (a b₁ c₁ b₂ c₂ : Prop) :
    ((a ∨ b₁ ∨ c₁) ∨ b₂ ∨ c₂) ↔ ((a ∨ b₂ ∨ c₂) ∨ b₁ ∨ c₁) := by
  tauto

/-- **Order independence of any check-based direct composition.** A direct composition that
succeeds exactly when the subnet declares no terminal place and the checks it runs pass (the
channel check when `cc`, the name check when `nc`, the type check when `tc`), and whose success
has the weak shape, gives the same places and the same transitions in either order. -/
theorem mod025_order_generic {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A} (nc tc cc : Bool)
    (hrej : ∀ b S b', D b S = .ok b' →
      (cc = true → S.chans = []) ∧ (nc = true → ¬ DirectNameClash b S) ∧
      (tc = true → ¬ DirectTypeClash Nm tyOf b S) ∧ DirectWeak b S b')
    (hacc : ∀ b S, S.terminals = [] → (cc = true → S.chans = []) →
      (nc = true → ¬ DirectNameClash b S) → (tc = true → ¬ DirectTypeClash Nm tyOf b S) →
      ∃ b', D b S = .ok b') :
    mod025_line6 D := by
  intro b b₁ c S₁ S₂ hc₁ hc₂ ht₁ ht₂ h₁ h₂
  obtain ⟨c1, n1, t1, w1⟩ := hrej _ _ _ h₁
  obtain ⟨c2, n2, t2, w2⟩ := hrej _ _ _ h₂
  have defs1 : ∀ d, d ∈ b₁.defs ↔ d ∈ b.defs ∨ d ∈ S₁.defs := fun d => by
    rw [w1.1.mem_iff, List.mem_append]
  obtain ⟨b₂, hb₂⟩ := hacc b S₂ ht₂ c2
    (fun hn ⟨d, hd, d', hd', he⟩ => n2 hn ⟨d, hd, d', (defs1 d').2 (.inl hd'), he⟩)
    (fun ht ⟨x, hx, h, hh, hn, hty⟩ => t2 ht ⟨x, hx, h, (w1.2.1 h).2 (.inl hh), hn, hty⟩)
  obtain ⟨-, -, -, w3⟩ := hrej _ _ _ hb₂
  have defs2 : ∀ d, d ∈ b₂.defs ↔ d ∈ b.defs ∨ d ∈ S₂.defs := fun d => by
    rw [w3.1.mem_iff, List.mem_append]
  obtain ⟨c', hc'⟩ := hacc b₂ S₁ ht₁ c1
    (fun hn ⟨d, hd, d', hd', he⟩ => by
      rcases (defs2 d').1 hd' with hb | hs
      · exact n1 hn ⟨d, hd, d', hb, he⟩
      · exact n2 hn ⟨d', hs, d, (defs1 d).2 (.inr hd), he.symm⟩)
    (fun ht ⟨x, hx, h, hh, hn, hty⟩ => by
      rcases (w3.2.1 h).1 hh with hb | hs | ⟨d, hd, hp⟩
      · exact t1 ht ⟨x, hx, h, hb, hn, hty⟩
      · exact t2 ht ⟨h, hs, x, (w1.2.1 x).2 (.inr (.inl hx)), hn.symm, Ne.symm hty⟩
      · exact t2 ht ⟨h, hc₂ d hd h hp, x, (w1.2.1 x).2 (.inr (.inl hx)), hn.symm, Ne.symm hty⟩)
  obtain ⟨-, -, -, w4⟩ := hrej _ _ _ hc'
  refine ⟨b₂, c', hb₂, hc', fun p => ?_, ?_, ?_, ?_, ?_⟩
  · rw [w2.2.1, w1.2.1, w4.2.1, w3.2.1]
    exact mod025_or_swap _ _ _ _ _
  · refine w2.1.trans ((w1.1.append_right _).trans ?_)
    refine List.Perm.trans ?_ ((w3.1.append_right _).symm.trans w4.1.symm)
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · rw [w2.2.2.1, w1.2.2.1, w4.2.2.1, w3.2.2.1]
  · rw [w2.2.2.2.1, w1.2.2.2.1, w4.2.2.2.1, w3.2.2.2.1]
  · rw [w2.2.2.2.2, w1.2.2.2.2, w4.2.2.2.2, w3.2.2.2.2]

/-- **Line 6 follows from lines 1 to 5.** Every direct composition that meets lines 1 to 5
composes two definitions in either order to the same places and transitions: if `Producer` then
`Consumer` succeeds, the first call shows `Consumer` clashes neither with the builder nor with
`Producer`, so `Consumer` then `Producer` succeeds as well, with the transitions in the other
order. -/
theorem mod025_line6_of {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A}
    (h1 : mod025_line1 D) (h2 : mod025_line2 D) (h3 : mod025_line3 D)
    (h4 : mod025_line4 Nm tyOf D) (h5 : mod025_line5 Nm tyOf D) : mod025_line6 D := by
  have notErr : ∀ {b S b'} {P : Prop}, D b S = .ok b' → (P → ∃ m, D b S = .error m) → ¬ P :=
    fun hb hP p => by obtain ⟨m, hm⟩ := hP p; rw [hb] at hm; cases hm
  refine mod025_order_generic (Nm := Nm) (tyOf := tyOf) true true true
    (fun b S b' hb => ⟨fun _ => ?_, fun _ => notErr hb (fun h => (h2 b S h).1),
      fun _ => notErr hb (h4 b S), ?_⟩)
    (fun b S ht hc hn hty => h5 b S ht (hc rfl) (hn rfl) (hty rfl))
  · by_contra hc
    exact notErr hb (h3 b S) hc
  · obtain ⟨hd, hp, -, ht, hr, hf⟩ := h1 b b' S hb
    exact ⟨List.Perm.of_eq hd, hp, ht, hr, hf⟩

end Order

/-! ### The reference -/

section Reference

variable {N A T : Type} [DecidableEq N] [DecidableEq T]

/-- Appending new places keeps the old ones as they were and adds each new one once. -/
theorem mod025_appendNew_shape {ps new : List N} :
    ∃ nw : List N, (appendNew ps new).Perm (ps ++ nw) ∧ nw.Nodup ∧ ∀ p ∈ nw, p ∉ ps := by
  refine ⟨(new.filter fun p => decide (p ∉ ps)).eraseDups, List.Perm.refl _, eraseDups_nodup _,
    fun p hp => ?_⟩
  have := List.mem_eraseDups.1 hp
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact this.2

/-- A message `m` whose characters are `a`, then those of `s`, then `c`, names `s`. -/
theorem mod025_msgNames {m s : String} (a c : List Char) (h : m.toList = a ++ s.toList ++ c) :
    MsgNames m s :=
  ⟨a, c, h.symm⟩

/-- **The reference names a sole offending transition.** When the subnet declares no terminal
place and no channel and every body transition the builder already holds is named `n`, the
reference direct composition fails with a message containing `n` and the subnet's name. -/
theorem mod025_ref_msg {Nm : Naming N} {tyOf : N → T} {b : Bld N A} {S : SubnetDef N A}
    {n : String} (ht : S.terminals = []) (hc : S.chans = []) (hx : DirectNameClash b S)
    (hs : ∀ d ∈ S.defs, d.core.name ∈ b.defs.map (·.core.name) → d.core.name = n) :
    ∃ m, refDirect Nm tyOf b S = .error m ∧ MsgNames m n ∧ MsgNames m S.name := by
  unfold refDirect
  simp only [ht, hc, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
  cases hf : S.defs.find? (fun d => b.defs.any fun d' => d'.core.name == d.core.name) with
  | none => exact absurd (directNameClash_find_iff.1 hf) (not_not.2 hx)
  | some d =>
    have hd := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [List.any_eq_true, beq_iff_eq] at hp
    obtain ⟨d', hd', he⟩ := hp
    have hn : d.core.name = n := hs d hd (List.mem_map.2 ⟨d', hd', he⟩)
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [← hn]
      apply mod025_msgNames "compose(SubnetDef): transition '".toList
        ("' from subnet '" ++ S.name ++
          "' collides with a transition already in the net").toList
      simp only [String.toList_append, List.append_assoc]
      rfl
    · apply mod025_msgNames
        ("compose(SubnetDef): transition '" ++ d.core.name ++ "' from subnet '").toList
        "' collides with a transition already in the net".toList
      simp only [String.toList_append, List.append_assoc]
      rfl

/-- Line 1 of the reference: `directAssemble`'s shape. -/
theorem mod025_ref_line1 (Nm : Naming N) (tyOf : N → T) :
    mod025_line1 (A := A) (refDirect Nm tyOf) := by
  intro b b' S hb
  obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 hb
  exact ⟨directAssemble_defs b S, fun p => mem_directAssemble_places,
    mod025_appendNew_shape, rfl, rfl, rfl⟩

/-- ✓ The reference direct composition satisfies MOD-025 for every naming model and every token
type map: it appends the body unrenamed and merges places by equality, rejects a terminal place
the body declares, a channel, a transition name the builder holds (naming it) and a same-named
place of another type, and accepts otherwise. -/
@[evidence holds MOD_025]
theorem MOD_025_reference {N A T : Type} [DecidableEq N] [DecidableEq T] (Nm : Naming N)
    (tyOf : N → T) : MOD_025 Nm tyOf (refDirect (A := A) Nm tyOf) := by
  have l1 := mod025_ref_line1 (A := A) Nm tyOf
  have l2 : mod025_line2 (A := A) (refDirect Nm tyOf) := fun b S hx =>
    ⟨refDirect_error_of (fun h => h.2.2.1 hx), fun _ ht hc hs => mod025_ref_msg ht hc hx hs⟩
  have l3 : mod025_line3 (A := A) (refDirect Nm tyOf) := fun b S hc =>
    refDirect_error_of (fun h => hc h.2.1)
  have l4 : mod025_line4 (A := A) Nm tyOf (refDirect Nm tyOf) := fun b S hx =>
    refDirect_error_of (fun h => h.2.2.2 hx)
  have l5 : mod025_line5 (A := A) Nm tyOf (refDirect Nm tyOf) := fun b S ht hc hn hty =>
    ⟨_, refDirect_accepts ht hc hn hty⟩
  have l7 : mod025_line7 (A := A) (refDirect Nm tyOf) := fun b S ht =>
    refDirect_error_of (fun h => ht h.1)
  exact ⟨l1, l2, l3, l4, l5, mod025_line6_of l1 l2 l3 l4 l5, l7⟩

end Reference

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A T : Type}

/-- **AC7: an empty subnet is a no-op.** In every model of MOD-025, direct-composing a subnet with
no places, no transitions, no terminal places and no channels succeeds and leaves the builder's
places and transitions as they were. -/
theorem mod025_empty {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A} (h : MOD_025 Nm tyOf D)
    (b : Bld N A) (nm : String) (ps : List (Port N)) :
    ∃ b', D b ⟨nm, [], [], [], ps, []⟩ = .ok b' ∧ (∀ p, p ∈ b'.places ↔ p ∈ b.places) ∧
      b'.defs = b.defs := by
  obtain ⟨b', hb'⟩ := h.2.2.2.2.1 b ⟨nm, [], [], [], ps, []⟩ rfl rfl
    (fun ⟨_, hd, _⟩ => nomatch hd) (fun ⟨_, hx, _⟩ => nomatch hx)
  obtain ⟨hd, hp, -⟩ := h.1 b b' _ hb'
  refine ⟨b', hb', fun p => ?_, by simpa using hd⟩
  rw [hp]
  simp

/-- Holding the same flat net is reflexive. -/
theorem directSame_refl (b : Bld N A) : DirectSame b b :=
  ⟨fun _ => Iff.rfl, List.Perm.refl _, rfl, rfl, rfl⟩

/-- Holding the same flat net is symmetric. -/
theorem DirectSame.symm {b b' : Bld N A} (h : DirectSame b b') : DirectSame b' b :=
  ⟨fun p => (h.1 p).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- Holding the same flat net is transitive. -/
theorem DirectSame.trans {b b' b'' : Bld N A} (h : DirectSame b b') (h' : DirectSame b' b'') :
    DirectSame b b'' :=
  ⟨fun p => (h.1 p).trans (h'.1 p), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

/-- A bind in `Except` succeeds when its first part does and the rest does. -/
theorem mod025_bind_ok {α β : Type} {e : Except String α} {g : α → Except String β} {c : β} :
    (e >>= g) = .ok c ↔ ∃ a, e = .ok a ∧ g a = .ok c := by
  cases e with
  | error m => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

/-- **A later call sees only the flat net.** In every model of MOD-025, a definition without
terminal places that composes into a builder composes into every builder that holds the same flat
net, to the same flat net. -/
theorem mod025_congr {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A} (h : MOD_025 Nm tyOf D)
    {b b' c : Bld N A} {S : SubnetDef N A} (ht : S.terminals = []) (hs : DirectSame b b')
    (hc : D b S = .ok c) : ∃ c', D b' S = .ok c' ∧ DirectSame c c' := by
  have notErr : ∀ {P : Prop}, (P → ∃ m, D b S = .error m) → ¬ P :=
    fun hP p => by obtain ⟨m, hm⟩ := hP p; rw [hc] at hm; cases hm
  have hch : S.chans = [] := by
    by_contra hn
    exact notErr (h.2.2.1 b S) hn
  have hn : ¬ DirectNameClash b S := notErr (fun x => (h.2.1 b S x).1)
  have hty : ¬ DirectTypeClash Nm tyOf b S := notErr (h.2.2.2.1 b S)
  obtain ⟨c', hc'⟩ := h.2.2.2.2.1 b' S ht hch
    (fun ⟨d, hd, d', hd', he⟩ => hn ⟨d, hd, d', hs.2.1.mem_iff.2 hd', he⟩)
    (fun ⟨x, hx, y, hy, he, hne⟩ => hty ⟨x, hx, y, (hs.1 y).2 hy, he, hne⟩)
  obtain ⟨d1, p1, -, t1, r1, f1⟩ := h.1 b c S hc
  obtain ⟨d2, p2, -, t2, r2, f2⟩ := h.1 b' c' S hc'
  refine ⟨c', hc', fun p => ?_, ?_, ?_, ?_, ?_⟩
  · rw [p1, p2, hs.1 p]
  · rw [d1, d2]
    exact hs.2.1.append_right _
  · rw [t1, t2, hs.2.2.1]
  · rw [r1, r2, hs.2.2.2.1]
  · rw [f1, f2, hs.2.2.2.2]

/-- The same sequence of direct compositions from two builders that hold the same flat net gives
the same flat net. -/
theorem mod025_foldl_congr {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A}
    (h : MOD_025 Nm tyOf D) :
    ∀ (l : List (SubnetDef N A)), (∀ S ∈ l, S.terminals = []) →
      ∀ {b b' c : Bld N A}, DirectSame b b' → l.foldlM D b = .ok c →
        ∃ c', l.foldlM D b' = .ok c' ∧ DirectSame c c'
  | [], _, b, b', c, hs, hc => by
    simp only [List.foldlM_nil] at hc ⊢
    cases hc
    exact ⟨b', rfl, hs⟩
  | S :: l, hl, b, b', c, hs, hc => by
    simp only [List.foldlM_cons] at hc ⊢
    obtain ⟨b₁, h₁, hr⟩ := mod025_bind_ok.1 hc
    obtain ⟨b₁', h₁', hs₁⟩ := mod025_congr h (hl S List.mem_cons_self) hs h₁
    obtain ⟨c', hc', hs'⟩ :=
      mod025_foldl_congr h l (fun S' hS' => hl S' (List.mem_cons_of_mem _ hS')) hs₁ hr
    exact ⟨c', mod025_bind_ok.2 ⟨b₁', h₁', hc'⟩, hs'⟩

/-- **Any order of any number of direct compositions** ([MOD-025] body: "composing the same set
of subnets into one builder in any order"). In every model of MOD-025, a sequence of direct
compositions of definitions without terminal places, whose body transitions name only their own
body places, that succeeds in one order succeeds in every reordering, with the same flat net:
`Producer`, `Consumer`, `Logger` in any of their six orders give one set of places and one set of
transitions. -/
theorem mod025_perm {Nm : Naming N} {tyOf : N → T} {D : DirectFn N A} (h : MOD_025 Nm tyOf D)
    {l l' : List (SubnetDef N A)} (hp : l.Perm l')
    (hl : ∀ S ∈ l, DirectClosed S ∧ S.terminals = []) {b c : Bld N A}
    (hc : l.foldlM D b = .ok c) : ∃ c', l'.foldlM D b = .ok c' ∧ DirectSame c c' := by
  suffices key : ∀ {l l' : List (SubnetDef N A)}, l.Perm l' →
      (∀ S ∈ l, DirectClosed S ∧ S.terminals = []) → ∀ {b b' c : Bld N A}, DirectSame b b' →
        l.foldlM D b = .ok c → ∃ c', l'.foldlM D b' = .ok c' ∧ DirectSame c c' from
    key hp hl (directSame_refl b) hc
  intro l l' hp
  induction hp with
  | nil =>
    intro _ b b' c hs hc
    simp only [List.foldlM_nil] at hc ⊢
    cases hc
    exact ⟨b', rfl, hs⟩
  | cons S _ ih =>
    intro hl b b' c hs hc
    simp only [List.foldlM_cons] at hc ⊢
    obtain ⟨b₁, h₁, hr⟩ := mod025_bind_ok.1 hc
    obtain ⟨b₁', h₁', hs₁⟩ := mod025_congr h (hl S List.mem_cons_self).2 hs h₁
    obtain ⟨c', hc', hs'⟩ := ih (fun S' hS' => hl S' (List.mem_cons_of_mem _ hS')) hs₁ hr
    exact ⟨c', mod025_bind_ok.2 ⟨b₁', h₁', hc'⟩, hs'⟩
  | swap x y l =>
    intro hl b b' c hs hc
    simp only [List.foldlM_cons] at hc ⊢
    obtain ⟨b₁, h₁, hr⟩ := mod025_bind_ok.1 hc
    obtain ⟨b₂, h₂, hr'⟩ := mod025_bind_ok.1 hr
    have hy := hl y List.mem_cons_self
    have hx := hl x (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨e₁, e₂, he₁, he₂, hse⟩ := h.2.2.2.2.2.1 b b₁ b₂ y x hy.1 hx.1 hy.2 hx.2 h₁ h₂
    obtain ⟨f₁, hf₁, hsf₁⟩ := mod025_congr h hx.2 hs he₁
    obtain ⟨f₂, hf₂, hsf₂⟩ := mod025_congr h hy.2 hsf₁ he₂
    obtain ⟨c', hc', hs'⟩ := mod025_foldl_congr h l
      (fun S hS => (hl S (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hS))).2)
      (hse.trans hsf₂) hr'
    exact ⟨c', mod025_bind_ok.2 ⟨f₁, hf₁, mod025_bind_ok.2 ⟨f₂, hf₂, hc'⟩⟩, hs'⟩
  | trans h₁₂ _ ih₁ ih₂ =>
    intro hl b b' c hs hc
    obtain ⟨c₁, hc₁, hs₁⟩ := ih₁ hl hs hc
    obtain ⟨c₂, hc₂, hs₂⟩ := ih₂ (fun S hS => hl S (h₁₂.mem_iff.2 hS)) (directSame_refl b') hc₁
    exact ⟨c₂, hc₂, hs₁.trans hs₂⟩

end Consequences

/-! ### Worked examples -/

/-- An example transition definition: name, input places (one token each) and output
specification; `Immediate`, priority 0, passthrough action. -/
def mod025_def (nm : String) (ins : List String) (out : Option (Out String)) : CDef String Unit :=
  { core := ⟨nm, ins.map fun p => ⟨p, .one⟩, [], [], []⟩, out := out, timing := .immediate,
    priority := 0, action := .passthrough }

/-- The subnet `Producer`: the transition `produce` puts a token into its body place `output`,
which its port `out` exposes. -/
def mod025_producer : SubnetDef String Unit :=
  { name := "Producer", places := ["output"],
    defs := [mod025_def "produce" [] (some (.place "output"))],
    ports := [⟨"out", .output, "output"⟩], chans := [] }

/-- The subnet `Consumer`: the transition `consume` takes a token from `output` and puts one into
`done`. -/
def mod025_consumer : SubnetDef String Unit :=
  { name := "Consumer", places := ["output", "done"],
    defs := [mod025_def "consume" ["output"] (some (.place "done"))], ports := [], chans := [] }

/-- The subnet `Pair`: the transitions `t1` (into `x`) and `t2` (from `x`), in that order. -/
def mod025_pair : SubnetDef String Unit :=
  { name := "Pair", places := ["x"],
    defs := [mod025_def "t1" [] (some (.place "x")), mod025_def "t2" ["x"] none],
    ports := [], chans := [] }

/-- The subnet `Go`: `Producer`'s body, with `produce` exposed as the channel `go`. -/
def mod025_chan : SubnetDef String Unit :=
  { mod025_producer with name := "Go", chans := [⟨"go", "produce"⟩] }

/-- The subnet `Ending`: `Producer`'s body, with its place `output` declared terminal. -/
def mod025_termProducer : SubnetDef String Unit :=
  { mod025_producer with name := "Ending", terminals := ["output"] }

/-- A host builder that declares the place `output`. -/
def mod025_host : Bld String Unit := { places := ["output"], defs := [] }

/-- The host builder after a hand-written transition `produce` was added. -/
def mod025_hostT : Bld String Unit :=
  { places := ["output"], defs := [mod025_def "produce" [] (some (.place "output"))] }

/-- A subnet over places keyed by name and token type, with one place `("output", k)`. -/
def mod025_typed (k : Nat) : SubnetDef (String × Nat) Unit :=
  { name := "Typed", places := [("output", k)], defs := [], ports := [], chans := [] }

/-- A host builder over places keyed by name and token type, declaring `("output", 1)`. -/
def mod025_hostTyped : Bld (String × Nat) Unit := { places := [("output", 1)], defs := [] }

/-- The reference on places by name (TypeScript, Rust, Python). -/
abbrev mod025_refS : DirectFn String Unit := refDirect strNaming (fun _ => ())

/-- The places and transition names of a builder, for the examples. -/
def mod025_view (b : Bld String Unit) : List String × List String :=
  (b.places, b.defs.map (·.core.name))

/-- ✓ Every line of MOD-025 is exercised by the reference. Composing `Producer` into a host that
declares `output` leaves one place `output`, and `produce` puts into it (AC1, line 1). `Producer`
then `Consumer` gives the places `output`, `done` and the transitions `produce`, `consume`;
`Consumer` then `Producer` gives the same places and the transitions `consume`, `produce` (AC3,
line 6). A host that already holds `produce` rejects `Producer` with a message naming `produce`
and `Producer` (AC4, line 2). The subnet `Go`, which declares a channel, is rejected (AC5, line
3). With places keyed by name and token type, a body place `output` of type 2 is rejected in a
host holding `output` of type 1, and one of type 1 is accepted (AC6, lines 4 and 5). An empty
subnet leaves the host as it was (AC7). The subnet `Ending`, whose body declares `output` a
terminal place, is rejected (line 7). -/
@[evidence nonvacuous MOD_025]
theorem MOD_025_nonvacuous :
    ((mod025_refS mod025_host mod025_producer).toOption.map fun b =>
        (mod025_view b, b.defs.map (·.namedPlaces))) =
      some ((["output"], ["produce"]), [["output"]]) ∧
    ((mod025_refS mod025_host mod025_producer >>= fun b => mod025_refS b mod025_consumer).toOption.map
        mod025_view) = some (["output", "done"], ["produce", "consume"]) ∧
    ((mod025_refS mod025_host mod025_consumer >>= fun b => mod025_refS b mod025_producer).toOption.map
        mod025_view) = some (["output", "done"], ["consume", "produce"]) ∧
    bindExErr (mod025_refS mod025_hostT mod025_producer) =
      some "compose(SubnetDef): transition 'produce' from subnet 'Producer' collides with a transition already in the net" ∧
    (mod025_refS mod025_host mod025_chan).toOption.isNone = true ∧
    (refDirect (typedNaming Nat) Prod.snd mod025_hostTyped (mod025_typed 2)).toOption.isNone = true ∧
    (refDirect (typedNaming Nat) Prod.snd mod025_hostTyped (mod025_typed 1)).toOption.map
      (·.places) = some [("output", 1)] ∧
    ((mod025_refS mod025_host ⟨"Empty", [], [], [], [], []⟩).toOption.map mod025_view) =
      some (["output"], []) ∧
    (mod025_refS mod025_host mod025_termProducer).toOption.isNone = true := by
  decide

/-! ### Reading results off a computed composition -/

section Read

variable {α β : Type}

/-- A composition whose computed view is `some y` succeeded, with a result of that view. -/
theorem mod025_ok_of_map {e : Except String α} {f : α → β} {y : β}
    (h : e.toOption.map f = some y) : ∃ x, e = .ok x ∧ f x = y := by
  cases e with
  | error m => simp [Except.toOption] at h
  | ok x => exact ⟨x, rfl, by simpa [Except.toOption] using h⟩

/-- A composition whose computed result is `none` did not succeed. -/
theorem mod025_not_ok {e : Except String α} (h : e.toOption = none) (x : α) : e ≠ .ok x := by
  intro he
  rw [he] at h
  cases h

/-- A composition that succeeded did not fail. -/
theorem mod025_not_err {e : Except String α} {x : α} (h : e = .ok x) (m : String) :
    e ≠ .error m := by
  intro he
  rw [h] at he
  cases he

end Read

/-! ### Wrong compositions -/

section Wrong

variable {N A T : Type} [DecidableEq N] [DecidableEq T]

/-- A direct composition that runs the reference's checks and, on success, replaces the builder
the reference returns by `f b S`. -/
def mod025Post (Nm : Naming N) (tyOf : N → T) (f : Bld N A → SubnetDef N A → Bld N A) :
    DirectFn N A := fun b S =>
  match refDirect Nm tyOf b S with
  | .ok _ => .ok (f b S)
  | .error m => .error m

theorem mod025Post_ok {Nm : Naming N} {tyOf : N → T} {f : Bld N A → SubnetDef N A → Bld N A}
    {b c : Bld N A} {S : SubnetDef N A} :
    mod025Post Nm tyOf f b S = .ok c ↔ (∃ b', refDirect Nm tyOf b S = .ok b') ∧ c = f b S := by
  unfold mod025Post
  cases refDirect Nm tyOf b S with
  | ok b' => simp [eq_comm]
  | error m => simp

theorem mod025Post_err {Nm : Naming N} {tyOf : N → T} {f : Bld N A → SubnetDef N A → Bld N A}
    {b : Bld N A} {S : SubnetDef N A} {m : String} :
    mod025Post Nm tyOf f b S = .error m ↔ refDirect Nm tyOf b S = .error m := by
  unfold mod025Post
  cases refDirect Nm tyOf b S with
  | ok b' => simp
  | error m => simp

/-- Lines 2 to 7 hold of a post-processed reference whose result has the weak shape. -/
theorem mod025Post_lines {Nm : Naming N} {tyOf : N → T} {f : Bld N A → SubnetDef N A → Bld N A}
    (hw : ∀ b S, DirectWeak b S (f b S)) :
    mod025_line2 (mod025Post Nm tyOf f) ∧ mod025_line3 (mod025Post Nm tyOf f) ∧
      mod025_line4 Nm tyOf (mod025Post Nm tyOf f) ∧ mod025_line5 Nm tyOf (mod025Post Nm tyOf f) ∧
      mod025_line6 (mod025Post Nm tyOf f) ∧ mod025_line7 (mod025Post Nm tyOf f) := by
  have R := MOD_025_reference (A := A) Nm tyOf
  have err : ∀ {b S}, (∃ m, refDirect Nm tyOf b S = .error m) →
      ∃ m, mod025Post Nm tyOf f b S = .error m :=
    fun ⟨m, hm⟩ => ⟨m, mod025Post_err.2 hm⟩
  refine ⟨fun b S hx => ⟨err (R.2.1 b S hx).1, fun n ht hc hs => ?_⟩,
    fun b S hc => err (R.2.2.1 b S hc), fun b S hx => err (R.2.2.2.1 b S hx),
    fun b S ht hc hn hty => ⟨_, mod025Post_ok.2 ⟨R.2.2.2.2.1 b S ht hc hn hty, rfl⟩⟩,
    mod025_order_generic (Nm := Nm) (tyOf := tyOf) true true true ?_ ?_,
    fun b S ht => err (R.2.2.2.2.2.2 b S ht)⟩
  · obtain ⟨m, hm, h1, h2⟩ := (R.2.1 b S hx).2 n ht hc hs
    exact ⟨m, mod025Post_err.2 hm, h1, h2⟩
  · intro b S c hc
    obtain ⟨⟨b', hb'⟩, rfl⟩ := mod025Post_ok.1 hc
    obtain ⟨-, h2, h3, h4, -⟩ := refDirect_ok_iff.1 hb'
    exact ⟨fun _ => h2, fun _ => h3, fun _ => h4, hw b S⟩
  · intro b S ht hc hn hty
    exact ⟨_, mod025Post_ok.2 ⟨R.2.2.2.2.1 b S ht (hc rfl) (hn rfl) (hty rfl), rfl⟩⟩

/-- A direct composition that appends the body's transitions in reverse order. -/
def revDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A :=
  mod025Post Nm tyOf fun b S => { directAssemble Nm b S with defs := b.defs ++ S.defs.reverse }

/-- A direct composition that appends every body place, also one the builder already holds. -/
def dupDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A :=
  mod025Post Nm tyOf fun b S =>
    { directAssemble Nm b S with places := b.places ++ (S.places ++ S.defs.flatMap (·.namedPlaces)) }

/-- A direct composition without the transition-name check. -/
def noNameDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  match refDirect Nm tyOf { b with defs := [] } S with
  | .ok _ => .ok (directAssemble Nm b S)
  | .error m => .error m

/-- A direct composition whose every rejection says only "rejected". -/
def constMsgDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  match refDirect Nm tyOf b S with
  | .ok b' => .ok b'
  | .error _ => .error "rejected"

/-- A direct composition without the channel check. -/
def noChanDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  refDirect Nm tyOf b { S with chans := [] }

/-- A direct composition that rejects everything, with the reference's message where the
reference rejects. -/
def rejectOkDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  match refDirect Nm tyOf b S with
  | .ok _ => .error "rejected"
  | .error m => .error m

/-- A direct composition without the terminal check: the body's terminal declarations are
dropped and the rest is the reference. -/
def noTermDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  refDirect Nm tyOf b { S with terminals := [] }

end Wrong

/-- A direct composition (places by name) that prefixes every body transition name with the
subnet's name, as instantiation would. -/
def prefixDirect : DirectFn String Unit :=
  mod025Post strNaming (fun _ => ()) fun b S =>
    { directAssemble strNaming b S with
      defs := b.defs ++ S.defs.map fun d => { d with core := { d.core with name := preS S.name d.core.name } } }

/-- A direct composition (places by name) that merges a body place only into a place the builder
does not hold yet: a body place the builder already holds is renamed under the subnet's name,
everywhere in the body. -/
def firstKeepsDirect : DirectFn String Unit := fun b S =>
  let σ := fun x => if x ∈ b.places then preS S.name x else x
  refDirect strNaming (fun _ => ()) b
    { S with places := S.places.map σ, defs := S.defs.map (CDef.map σ id) }

/-- ✗ A direct composition that prefixes the body's transition names violates MOD-025 (line 1,
AC2): composing `Producer` into the host gives the transition `Producer/produce`, not
`produce`. -/
@[evidence forbids MOD_025]
theorem MOD_025_forbids_prefixes : ¬ MOD_025 strNaming (fun _ : String => ()) prefixDirect := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod025_ok_of_map (f := mod025_view)
    (show (prefixDirect mod025_host mod025_producer).toOption.map mod025_view =
      some (["output"], ["Producer/produce"]) by decide)
  have := congrArg (List.map (·.core.name)) (h.1 _ _ _ hc).1
  rw [show c.defs.map (·.core.name) = ["Producer/produce"] from congrArg Prod.snd hv] at this
  exact absurd this (by decide)

/-- ✗ A direct composition that keeps the first of two same-named places violates MOD-025 (line
6, AC3): `Producer` then `Consumer` leaves `output` and `Consumer/output`, while `Consumer` then
`Producer` leaves `output` and `Producer/output`, so the order of the calls changes the net. -/
@[evidence forbids MOD_025]
theorem MOD_025_forbids_firstKeeps :
    ¬ MOD_025 strNaming (fun _ : String => ()) firstKeepsDirect := by
  intro h
  let get : Except String (Bld String Unit) → Bld String Unit := fun e => e.toOption.getD Bld.empty
  have h₁ : firstKeepsDirect Bld.empty mod025_producer =
      .ok (get (firstKeepsDirect Bld.empty mod025_producer)) := rfl
  have h₂ : firstKeepsDirect (get (firstKeepsDirect Bld.empty mod025_producer)) mod025_consumer =
      .ok (get (firstKeepsDirect (get (firstKeepsDirect Bld.empty mod025_producer))
        mod025_consumer)) := rfl
  obtain ⟨b₂, c', hb₂, hc', hs⟩ := h.2.2.2.2.2.1 _ _ _ _ _ (by unfold DirectClosed; decide)
    (by unfold DirectClosed; decide) rfl rfl h₁ h₂
  have e₂ : b₂ = get (firstKeepsDirect Bld.empty mod025_consumer) := by rw [hb₂]; rfl
  subst e₂
  have e₃ : c' = get (firstKeepsDirect (get (firstKeepsDirect Bld.empty mod025_consumer))
      mod025_producer) := by rw [hc']; rfl
  subst e₃
  have := (hs.1 "Producer/output").2 (by decide)
  exact absurd this (by decide)

/-! ### Mutants, one per line -/

section Mutants

variable {N A T : Type}

/-- Mutant reading of line 1: the transitions of the builder after the call are the old ones and
the body's in any order (the declaration order left open). Lines 2 to 7 as in MOD-025. -/
def MOD_025_mutant_anyOrder (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  (∀ (b b' : Bld N A) (S : SubnetDef N A), D b S = .ok b' →
    b'.defs.Perm (b.defs ++ S.defs) ∧
    (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
    (∃ new : List N, b'.places.Perm (b.places ++ new) ∧ new.Nodup ∧ ∀ p ∈ new, p ∉ b.places) ∧
    b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions) ∧
  mod025_line2 D ∧ mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧
  mod025_line6 D ∧ mod025_line7 D

/-- Mutant reading of line 1 without "no place added twice": the places as a set only. Lines 2 to
7 as in MOD-025. -/
def MOD_025_mutant_dupPlaces (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  (∀ (b b' : Bld N A) (S : SubnetDef N A), D b S = .ok b' →
    b'.defs = b.defs ++ S.defs ∧
    (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces) ∧
    b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.fusions = b.fusions) ∧
  mod025_line2 D ∧ mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧
  mod025_line6 D ∧ mod025_line7 D

/-- Mutant reading: MOD-025 without line 2 (no transition-name check). -/
def MOD_025_mutant_noNameCheck (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧ mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧
  mod025_line6 D ∧ mod025_line7 D

/-- Mutant reading of line 2 as a rejection only: a transition name the builder holds rejects,
with any message. -/
def MOD_025_mutant_noNaming (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧
  (∀ (b : Bld N A) (S : SubnetDef N A), DirectNameClash b S → ∃ m, D b S = .error m) ∧
  mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧ mod025_line6 D ∧
  mod025_line7 D

/-- Mutant reading: MOD-025 without line 3 (no channel check). -/
def MOD_025_mutant_noChannelCheck (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧ mod025_line2 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line5 Nm tyOf D ∧
  mod025_line6 D ∧ mod025_line7 D

/-- Mutant reading: MOD-025 without line 4 (no token-type check). -/
def MOD_025_mutant_noTypeCheck (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧ mod025_line2 D ∧ mod025_line3 D ∧ mod025_line5 Nm tyOf D ∧ mod025_line6 D ∧
  mod025_line7 D

/-- Mutant reading: MOD-025 without line 5 (no acceptance; skeptic correction S2). -/
def MOD_025_mutant_noAcceptance (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧ mod025_line2 D ∧ mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧ mod025_line6 D ∧
  mod025_line7 D

/-- Mutant reading: MOD-025 without line 7 (no terminal check; [EXEC-042] AC6). -/
def MOD_025_mutant_noTerminalCheck (Nm : Naming N) (tyOf : N → T) (D : DirectFn N A) : Prop :=
  mod025_line1 D ∧ mod025_line2 D ∧ mod025_line3 D ∧ mod025_line4 Nm tyOf D ∧
  mod025_line5 Nm tyOf D ∧ mod025_line6 D

end Mutants

/-! ### What the wrong compositions do -/

section WrongLemmas

variable {N A T : Type} [DecidableEq N] [DecidableEq T] {Nm : Naming N} {tyOf : N → T}

/-- A composition whose computed result is some value succeeded. -/
theorem mod025_ok_of_isSome {α : Type} {e : Except String α} (h : e.toOption.isSome = true) :
    ∃ x, e = .ok x := by
  cases e with
  | error m => simp [Except.toOption] at h
  | ok x => exact ⟨x, rfl⟩

omit [DecidableEq T] in
/-- The weak shape of the reversed assembly. -/
theorem revDirect_weak (b : Bld N A) (S : SubnetDef N A) :
    DirectWeak b S { directAssemble Nm b S with defs := b.defs ++ S.defs.reverse } :=
  ⟨List.Perm.append_left _ (List.reverse_perm _), fun _ => mem_directAssemble_places (Nm := Nm),
    rfl, rfl, rfl⟩

omit [DecidableEq T] in
/-- The weak shape of the assembly that appends every body place. -/
theorem dupDirect_weak (b : Bld N A) (S : SubnetDef N A) :
    DirectWeak b S { directAssemble Nm b S with
      places := b.places ++ (S.places ++ S.defs.flatMap (·.namedPlaces)) } :=
  ⟨List.Perm.of_eq rfl, fun _ => by simp [List.mem_flatMap], rfl, rfl, rfl⟩

theorem noNameDirect_ok {b c : Bld N A} {S : SubnetDef N A} :
    noNameDirect Nm tyOf b S = .ok c ↔
      (∃ b', refDirect Nm tyOf { b with defs := [] } S = .ok b') ∧ c = directAssemble Nm b S := by
  unfold noNameDirect
  cases refDirect Nm tyOf { b with defs := [] } S with
  | ok b' => simp [eq_comm]
  | error m => simp

theorem noNameDirect_err {b : Bld N A} {S : SubnetDef N A}
    (h : ∃ m, refDirect Nm tyOf { b with defs := [] } S = .error m) :
    ∃ m, noNameDirect Nm tyOf b S = .error m := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by unfold noNameDirect; rw [hm]⟩

theorem constMsgDirect_ok {b c : Bld N A} {S : SubnetDef N A} :
    constMsgDirect Nm tyOf b S = .ok c ↔ refDirect Nm tyOf b S = .ok c := by
  unfold constMsgDirect
  cases refDirect Nm tyOf b S with
  | ok b' => simp
  | error m => simp

theorem constMsgDirect_err {b : Bld N A} {S : SubnetDef N A}
    (h : ∃ m, refDirect Nm tyOf b S = .error m) : ∃ m, constMsgDirect Nm tyOf b S = .error m := by
  obtain ⟨m, hm⟩ := h
  exact ⟨"rejected", by unfold constMsgDirect; rw [hm]⟩

theorem rejectOkDirect_not_ok {b c : Bld N A} {S : SubnetDef N A} :
    rejectOkDirect Nm tyOf b S ≠ .ok c := by
  unfold rejectOkDirect
  cases refDirect Nm tyOf b S <;> simp

theorem rejectOkDirect_err {b : Bld N A} {S : SubnetDef N A} {m : String}
    (h : refDirect Nm tyOf b S = .error m) : rejectOkDirect Nm tyOf b S = .error m := by
  unfold rejectOkDirect
  rw [h]

end WrongLemmas

/-! ### The mutants killed -/

/-- The composition that appends the body's transitions in reverse order kills the mutant: it
meets lines 2 to 6 and has the old transitions and the body's in some order, but composing `Pair`
gives `t2`, `t1` where the body declares `t1`, `t2` (line 1: declaration order). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_anyOrder_killed :
    MOD_025_mutant_anyOrder strNaming (fun _ : String => ()) (revDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (revDirect (A := Unit) strNaming (fun _ => ())) := by
  refine ⟨⟨fun b b' S hb => ?_, mod025Post_lines revDirect_weak⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := mod025Post_ok.1 hb
    exact ⟨List.Perm.append_left _ (List.reverse_perm _),
      fun _ => mem_directAssemble_places (Nm := strNaming), mod025_appendNew_shape, rfl, rfl, rfl⟩
  · obtain ⟨c, hc, hv⟩ := mod025_ok_of_map (f := mod025_view)
      (show (revDirect strNaming (fun _ => ()) mod025_host mod025_pair).toOption.map mod025_view =
        some (["output", "x"], ["t2", "t1"]) by decide)
    have := congrArg (List.map (·.core.name)) (h.1 _ _ _ hc).1
    rw [show c.defs.map (·.core.name) = ["t2", "t1"] from congrArg Prod.snd hv] at this
    exact absurd this (by decide)

/-- The composition that appends every body place, also one the builder already holds, kills the
mutant: it meets lines 2 to 6 and holds the right places as a set, but composing `Producer` into
a host that holds `output` once leaves `output` three times, adding a place the host already
holds (line 1, AC1's single place). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_dupPlaces_killed :
    MOD_025_mutant_dupPlaces strNaming (fun _ : String => ()) (dupDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (dupDirect (A := Unit) strNaming (fun _ => ())) := by
  refine ⟨⟨fun b b' S hb => ?_, mod025Post_lines dupDirect_weak⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := mod025Post_ok.1 hb
    exact ⟨rfl, fun _ => by simp [List.mem_flatMap], rfl, rfl, rfl⟩
  · obtain ⟨c, hc, hv⟩ := mod025_ok_of_map (f := fun b : Bld String Unit => b.places)
      (show (dupDirect strNaming (fun _ => ()) mod025_host mod025_producer).toOption.map (·.places) =
        some ["output", "output", "output"] by decide)
    obtain ⟨nw, hperm, -, hnot⟩ := (h.1 _ _ _ hc).2.2.1
    rw [hv] at hperm
    cases nw with
    | nil => exact absurd hperm.length_eq (by decide)
    | cons x xs =>
      have hx : x ∈ ["output", "output", "output"] := hperm.mem_iff.2 (by simp)
      have hxo : x = "output" := by simpa using hx
      exact hnot x List.mem_cons_self (by simp [mod025_host, hxo])

/-- The composition without the name check kills the mutant: it meets lines 1 and 3 to 6, but
composes `Producer` into a host that already holds a transition `produce` (line 2, AC4). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noNameCheck_killed :
    MOD_025_mutant_noNameCheck strNaming (fun _ : String => ()) (noNameDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (noNameDirect (A := Unit) strNaming (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) strNaming (fun _ : String => ())
  have hacc : ∀ (b : Bld String Unit) (S : SubnetDef String Unit), S.terminals = [] →
      S.chans = [] → ¬ DirectTypeClash strNaming (fun _ : String => ()) b S →
      ∃ b', noNameDirect strNaming (fun _ => ()) b S = .ok b' := fun b S ht hc hty =>
    ⟨_, noNameDirect_ok.2 ⟨R.2.2.2.2.1 { b with defs := [] } S ht hc
      (fun ⟨_, _, _, hd', _⟩ => by simp at hd') hty, rfl⟩⟩
  refine ⟨⟨fun b b' S hb => ?_, fun b S hc => noNameDirect_err (R.2.2.1 _ S hc),
    fun b S hx => noNameDirect_err (R.2.2.2.1 _ S hx),
    fun b S ht hc _ hty => hacc b S ht hc hty,
    mod025_order_generic (Nm := strNaming) (tyOf := fun _ : String => ()) false true true ?_
      (fun b S ht hc _ hty => hacc b S ht (hc rfl) (hty rfl)),
    fun b S ht => noNameDirect_err (R.2.2.2.2.2.2 _ S ht)⟩, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := noNameDirect_ok.1 hb
    exact ⟨directAssemble_defs b S, fun _ => mem_directAssemble_places, mod025_appendNew_shape,
      rfl, rfl, rfl⟩
  · intro b S c hc
    obtain ⟨⟨b', hb'⟩, rfl⟩ := noNameDirect_ok.1 hc
    obtain ⟨-, h2, -, h4, -⟩ := refDirect_ok_iff.1 hb'
    exact ⟨fun _ => h2, fun h => absurd h Bool.false_ne_true, fun _ => h4,
      List.Perm.of_eq (directAssemble_defs b S), fun _ => mem_directAssemble_places, rfl, rfl, rfl⟩
  · obtain ⟨c, hc⟩ := mod025_ok_of_isSome
      (show (noNameDirect strNaming (fun _ => ()) mod025_hostT mod025_producer).toOption.isSome =
        true by decide)
    obtain ⟨m, hm⟩ := (h.2.1 mod025_hostT mod025_producer (by unfold DirectNameClash; decide)).1
    exact mod025_not_err hc m hm

/-- The composition whose rejections say only "rejected" kills the mutant: it rejects exactly
where the reference does, but its message for a host that already holds `produce` does not name
`produce` (line 2, AC4). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noNaming_killed :
    MOD_025_mutant_noNaming strNaming (fun _ : String => ()) (constMsgDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (constMsgDirect (A := Unit) strNaming (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) strNaming (fun _ : String => ())
  refine ⟨⟨fun b b' S hb => R.1 b b' S (constMsgDirect_ok.1 hb),
    fun b S hx => constMsgDirect_err (R.2.1 b S hx).1,
    fun b S hc => constMsgDirect_err (R.2.2.1 b S hc),
    fun b S hx => constMsgDirect_err (R.2.2.2.1 b S hx),
    fun b S ht hc hn hty => ?_, fun b b₁ c S₁ S₂ hc₁ hc₂ ht₁ ht₂ h₁ h₂ => ?_,
    fun b S ht => constMsgDirect_err (R.2.2.2.2.2.2 b S ht)⟩, fun h => ?_⟩
  · obtain ⟨b', hb'⟩ := R.2.2.2.2.1 b S ht hc hn hty
    exact ⟨b', constMsgDirect_ok.2 hb'⟩
  · obtain ⟨b₂, c', hb₂, hc', hs⟩ := R.2.2.2.2.2.1 b b₁ c S₁ S₂ hc₁ hc₂ ht₁ ht₂
      (constMsgDirect_ok.1 h₁) (constMsgDirect_ok.1 h₂)
    exact ⟨b₂, c', constMsgDirect_ok.2 hb₂, constMsgDirect_ok.2 hc', hs⟩
  · obtain ⟨m, hm, hn, -⟩ := (h.2.1 mod025_hostT mod025_producer
      (by unfold DirectNameClash; decide)).2 "produce" rfl rfl (by decide)
    have he : bindExErr (constMsgDirect strNaming (fun _ => ()) mod025_hostT mod025_producer) =
        some "rejected" := by decide
    rw [hm] at he
    cases he
    exact absurd (msgNames_chars hn (ch := 'p') (by decide)) (by decide)

/-- The composition without the channel check kills the mutant: it meets every other line, but
composes `Go`, whose interface declares the channel `go` (line 3, AC5). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noChannelCheck_killed :
    MOD_025_mutant_noChannelCheck strNaming (fun _ : String => ()) (noChanDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (noChanDirect (A := Unit) strNaming (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) strNaming (fun _ : String => ())
  refine ⟨⟨fun b b' S hb => R.1 b b' { S with chans := [] } hb,
    fun b S hx => ⟨(R.2.1 b { S with chans := [] } hx).1,
      fun n ht _ hs => (R.2.1 b { S with chans := [] } hx).2 n ht rfl hs⟩,
    fun b S hx => R.2.2.2.1 b { S with chans := [] } hx,
    fun b S ht _ hn hty => R.2.2.2.2.1 b { S with chans := [] } ht rfl hn hty,
    mod025_order_generic (Nm := strNaming) (tyOf := fun _ : String => ()) true true false ?_
      (fun b S ht _ hn hty => R.2.2.2.2.1 b { S with chans := [] } ht rfl (hn rfl) (hty rfl)),
    fun b S ht => R.2.2.2.2.2.2 b { S with chans := [] } ht⟩,
    fun h => ?_⟩
  · intro b S c hc
    obtain ⟨-, -, h3, h4, rfl⟩ := refDirect_ok_iff.1 hc
    exact ⟨fun h => absurd h Bool.false_ne_true, fun _ => h3, fun _ => h4,
      List.Perm.of_eq (directAssemble_defs b _), fun _ => mem_directAssemble_places, rfl, rfl, rfl⟩
  · obtain ⟨c, hc⟩ := mod025_ok_of_isSome
      (show (noChanDirect strNaming (fun _ => ()) mod025_host mod025_chan).toOption.isSome =
        true by decide)
    obtain ⟨m, hm⟩ := h.2.2.1 mod025_host mod025_chan (by decide)
    exact mod025_not_err hc m hm

/-- The name-only check of Rust and TypeScript, run on Java's places (keyed by name and token
type), kills the mutant: it meets every other line, but composes a body place `output` of type 2
into a host holding `output` of type 1 (line 4, AC6). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noTypeCheck_killed :
    MOD_025_mutant_noTypeCheck (typedNaming Nat) Prod.snd
        (refDirect (A := Unit) (typedNaming Nat) (fun _ => ())) ∧
      ¬ MOD_025 (typedNaming Nat) Prod.snd (refDirect (A := Unit) (typedNaming Nat) (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) (typedNaming Nat) (fun _ : String × Nat => ())
  refine ⟨⟨R.1, R.2.1, R.2.2.1,
    fun b S ht hc hn _ => R.2.2.2.2.1 b S ht hc hn (fun ⟨_, _, _, _, _, hty⟩ => hty rfl),
    R.2.2.2.2.2⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := mod025_ok_of_isSome
    (show (refDirect (typedNaming Nat) (fun _ => ()) mod025_hostTyped (mod025_typed 2)).toOption.isSome =
      true by decide)
  obtain ⟨m, hm⟩ := h.2.2.2.1 mod025_hostTyped (mod025_typed 2)
    (by unfold DirectTypeClash; decide)
  exact mod025_not_err hc m hm

/-- The composition that rejects everything (with the reference's message where the reference
rejects) kills the mutant: it meets lines 1 to 4, 6 and 7, but rejects even an empty subnet (line 5,
AC7). -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noAcceptance_killed :
    MOD_025_mutant_noAcceptance strNaming (fun _ : String => ()) (rejectOkDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (rejectOkDirect (A := Unit) strNaming (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) strNaming (fun _ : String => ())
  have err : ∀ {b S}, (∃ m, refDirect (A := Unit) strNaming (fun _ : String => ()) b S = .error m) →
      ∃ m, rejectOkDirect strNaming (fun _ => ()) b S = .error m :=
    fun ⟨m, hm⟩ => ⟨m, rejectOkDirect_err hm⟩
  refine ⟨⟨fun b b' S hb => absurd hb rejectOkDirect_not_ok,
    fun b S hx => ⟨err (R.2.1 b S hx).1, fun n ht hc hs => ?_⟩,
    fun b S hc => err (R.2.2.1 b S hc), fun b S hx => err (R.2.2.2.1 b S hx),
    fun b b₁ c S₁ S₂ _ _ _ _ h₁ _ => absurd h₁ rejectOkDirect_not_ok,
    fun b S ht => err (R.2.2.2.2.2.2 b S ht)⟩, fun h => ?_⟩
  · obtain ⟨m, hm, h1, h2⟩ := (R.2.1 b S hx).2 n ht hc hs
    exact ⟨m, rejectOkDirect_err hm, h1, h2⟩
  · obtain ⟨b', hb'⟩ := h.2.2.2.2.1 mod025_host ⟨"Empty", [], [], [], [], []⟩ rfl rfl
      (fun ⟨_, hd, _⟩ => nomatch hd) (fun ⟨_, hx, _⟩ => nomatch hx)
    exact rejectOkDirect_not_ok hb'

/-- The composition without the terminal check kills the mutant: it meets lines 1 to 6, but
composes `Ending`, whose body declares `output` a terminal place, into the host and drops that
declaration without a word, where line 7 ([EXEC-042] AC6) asks for a rejection. -/
@[evidence mutant MOD_025]
theorem MOD_025_mutant_noTerminalCheck_killed :
    MOD_025_mutant_noTerminalCheck strNaming (fun _ : String => ())
        (noTermDirect (A := Unit) strNaming (fun _ => ())) ∧
      ¬ MOD_025 strNaming (fun _ : String => ()) (noTermDirect (A := Unit) strNaming (fun _ => ())) := by
  have R := MOD_025_reference (A := Unit) strNaming (fun _ : String => ())
  let D := noTermDirect (A := Unit) strNaming (fun _ : String => ())
  have l1 : mod025_line1 D := fun b b' S hb => R.1 b b' { S with terminals := [] } hb
  have l2 : mod025_line2 D := fun b S hx =>
    ⟨(R.2.1 b { S with terminals := [] } hx).1,
      fun n _ hc hs => (R.2.1 b { S with terminals := [] } hx).2 n rfl hc hs⟩
  have l3 : mod025_line3 D := fun b S hc => R.2.2.1 b { S with terminals := [] } hc
  have l4 : mod025_line4 strNaming (fun _ : String => ()) D := fun b S hx =>
    R.2.2.2.1 b { S with terminals := [] } hx
  have l5 : mod025_line5 strNaming (fun _ : String => ()) D := fun b S _ hc hn hty =>
    R.2.2.2.2.1 b { S with terminals := [] } rfl hc hn hty
  refine ⟨⟨l1, l2, l3, l4, l5, mod025_line6_of l1 l2 l3 l4 l5⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := mod025_ok_of_isSome
    (show (noTermDirect (A := Unit) strNaming (fun _ => ()) mod025_host
      mod025_termProducer).toOption.isSome = true by decide)
  obtain ⟨m, hm⟩ := h.2.2.2.2.2.2 mod025_host mod025_termProducer (by decide)
  exact mod025_not_err hc m hm

end Libpetri.Spec
