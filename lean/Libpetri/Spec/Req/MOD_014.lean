import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Req.MOD_006

set_option linter.missingDocs true

/-!
# MOD-014: SubnetDef.fromNet retrofit utility (`spec/11-modular-composition.md`)

MOD-014 is a behaviour requirement (kind B) over one abstract function: the retrofit utility
`F : FromNetFn N A`, which takes a net that is already built (`ClosedNet`: its name, places,
transition definitions in order and terminal places) and an interface (ports and channels) and
returns a subnet definition or a rejection with a message.

The block says when `fromNet` fails: a port on a place the net does not hold, a channel on a
transition name the net does not hold, two ports of one name, two channels of one name. It says
that `fromNet` succeeds otherwise, that a success wraps the net unchanged (its name, places,
transitions in order and terminal places) with the interface as given, and that the message of a
failure names an offending port or channel. Which offender is named when there are several is not
stated, nor the order of the checks.

The witness is the reference `refFromNet`, which is MOD-006's reference subnet builder run with a
net builder that returns the supplied net as it is (`refFromNet_eq`): the validation of
[MOD-006] applied to a net that needs no building. The block pins `fromNet` up to the message:
two models of the block succeed and fail on the same inputs and return the same definition
(`mod014_determined`). Wrong utilities are killed, one per load-bearing line.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-! ## The utility's types -/

section Types

variable (N A : Type)

/-- A net as `fromNet` receives it: an existing closed net, already built ([CORE-040]), read as
its name, its places, its transitions' definitions in declaration order and its terminal places
([EXEC-042]). The definitions are composition's (`CDef`), so a net built by composition keeps the
correspondence of [MOD-031] on its transitions. -/
structure ClosedNet where
  /-- The net's name. -/
  name      : String
  /-- The net's places. -/
  places    : List N
  /-- The net's transition definitions, in declaration order. -/
  defs      : List (CDef N A)
  /-- The net's terminal places ([EXEC-042]). -/
  terminals : List N := []

/-- A retrofit utility ([MOD-014]): a closed net, the interface's ports and its channels give a
subnet definition or a rejection with a message (a panic or an exception, read as `.error msg`). -/
abbrev FromNetFn := ClosedNet N A → List (Port N) → List Chan → Except String (SubnetDef N A)

end Types

variable {N A : Type}

/-- The subnet definition that wraps the net `X` with the ports `ps` and the channels `cs`: the
net's name, its places, its transitions in order and its terminal places as the body, the given
ports and channels as the interface. -/
def ClosedNet.wrap (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) : SubnetDef N A :=
  { name := X.name, places := X.places, defs := X.defs, terminals := X.terminals,
    ports := ps, chans := cs }

/-! ## MOD-014: SubnetDef.fromNet retrofit utility -/

requirement MOD_014
  id "MOD-014"
  title "SubnetDef.fromNet retrofit utility"
  kind B
  scope "every retrofit utility fromNet"
  source verbatim "spec/11-modular-composition.md"
  quote "*If* a port of the interface exposes a place that is not a place of the net, *then* `fromNet` *shall* fail."
        "*If* a channel of the interface exposes a transition whose name is not the name of a transition of the net, *then* `fromNet` *shall* fail."
        "*If* two ports of the interface have the same name, *then* `fromNet` *shall* fail."
        "*If* two channels of the interface have the same name, *then* `fromNet` *shall* fail."
        "*When* every port of the interface exposes a place of the net, every channel exposes a transition of the net, and no two ports and no two channels have the same name, `fromNet` *shall* succeed."
        "*When* `fromNet` succeeds, the subnet definition *shall* have the net's name, the net's places, transitions and terminal places as its body, with the transitions in the net's order, and the given ports and channels as its interface."
        "*When* `fromNet` fails, the error message *shall* contain the name of a port or channel that meets one of the four rejection cases above."
  reading "For every retrofit utility F:"
          "if some port of ps exposes a place that is not a place of the net X, F fails on X, ps and cs;"
          "if some channel of cs names a transition that is not the name of a transition of X, F fails on X, ps and cs;"
          "if two ports of ps have the same name, F fails;"
          "if two channels of cs have the same name, F fails;"
          "if every port exposes a place of X, every channel names a transition of X, and the port names and the channel names are each pairwise distinct, F succeeds;"
          "if F succeeds with the definition D, then D is X.wrap ps cs: the name, places, transition definitions (in order) and terminal places of X, the ports ps and the channels cs;"
          "if F fails with the message msg, then msg contains the name of a port whose place is not in X or whose name two ports carry, or the name of a channel whose transition is not the name of a transition of X or whose name two channels carry."
  assumes "A retrofit utility (FromNetFn) is the fromNet call of one implementation (rust/libpetri-core/src/subnet_def.rs:232-293, java/src/main/java/org/libpetri/core/SubnetDef.java:507-552, typescript/src/core/subnet-def.ts fromNet; Python's SubnetDef.from_net calls the Rust function, rust/libpetri-py/src/model.rs:880-883), read as a function from a built net (ClosedNet: its name, places, transition definitions in declaration order and terminal places) and an interface (the ports and the channels) to a subnet definition or a rejection with a message (a panic or an exception, read as .error msg). The sentence 'Implementations MUST provide a utility' (raised from MAY by ruling D57 (a)) is the existence of the model: the block's argument is the implementation's fromNet, and all four implementations provide one. It is no block line."
          "The net is already built, so no net builder runs and MOD-006's case 5 (a body the net builder rejects) does not arise. The reference refFromNet is MOD-006's reference subnet builder over a net builder that returns the net unchanged (refFromNet_eq), which is the design's 'the same check applied to an already built net'. A net that declares terminal places is accepted (line 5, MOD_014_nonvacuous) and refused when the definition is instantiated (EXEC-042 AC6, MOD-010 line 2's premise); all three runtimes keep the net, terminal places included, as the body."
          "Line 1 and line 5 compare a port's place with the net's places by equality on the place type N (CORE-002: by name in TypeScript, typescript/src/core/subnet-def.ts placeNames, and in Rust and Python, whose Place equality is name-only; by name and token type in Java, java/src/main/java/org/libpetri/core/SubnetDef.java:527)."
          "Line 2 and line 5 match a channel to a net transition by name (ruling D23, settled by D10, and R-MA3 (a)), as MOD-006 lines 2 and 6 do: the model's channel carries the transition's name. Rust and Python compare names (rust/libpetri-core/src/subnet_def.rs:236-240, :272); Java and TypeScript compare transition objects (java/src/main/java/org/libpetri/core/SubnetDef.java:543, typescript/src/core/subnet-def.ts bodyTransitions.has), so a channel over a second transition object that has the name of a net transition is rejected there and accepted in Rust. The model's channel carries only the transition's name, not a transition object, so it cannot tell that second object from the net's own transition: the case is outside what the block can state, the formula (lines 2 and 5) reads it as Rust does, and the markdown calls it implementation-defined. The shared unique-names assumption (D10, D23; no builder checks names) concerns the transitions inside one net and does not settle this case, since the second object is not in the net. After a composition the net holds rewritten transition objects, so in Java and TypeScript a caller exposes the transition it fetches from the net."
          "Lines 3 and 4 are reached only by the model. An interface value of every runtime holds at most one port and one channel of each name: Rust and TypeScript key them by name in a map (rust/libpetri-core/src/interface.rs:104-107, typescript/src/core/interface.ts:57-59), Java keeps sets built only by its interface builder (java/src/main/java/org/libpetri/core/Interface.java:29-37), and every interface builder rejects a second declaration of a name at the port() or channel() call (rust/libpetri-core/src/interface.rs:164-170, java/src/main/java/org/libpetri/core/Interface.java:183-190, typescript/src/core/interface.ts:107-113). The model's interface is two lists, which can carry a repeated name, and all three runtimes' fromNet check the names again (rust/libpetri-core/src/subnet_def.rs:243-251, :264-270, java/src/main/java/org/libpetri/core/SubnetDef.java:520-525, :537-542); the lines state that check. Port names and channel names are two namespaces, as in MOD-006."
          "Line 5 is implied by line 7 (mod014_line5_of_line7): when no port or channel offends, line 7 leaves no message a failure could carry. It is kept as the acceptance line (skeptic correction S2 of the composition design) and has no mutant of its own, as MOD-006 line 6. Lines 1 to 5 together fix exactly when fromNet succeeds, and line 6 fixes what it returns, so two models of the block agree on every input up to the message (mod014_determined)."
          "Line 6 is AC1: 'body equals the supplied net (modulo immutability semantics)' reads as the definition holding the net's places, its transition definitions as a list in the net's order (correspondence included) and its terminal places; Lean values are immutable. The name is the net's name in all three runtimes (rust/libpetri-core/src/subnet_def.rs:285, java/src/main/java/org/libpetri/core/SubnetDef.java:551, typescript/src/core/subnet-def.ts new SubnetDef(SUBNET_DEF_KEY, net.name, ...)), which the markdown now states. The interface is the given one: Rust and Java keep the interface value, and the model's lists stand for it; the runtimes' interface has no order to keep, so line 6 returning the lists as given asks nothing of an order."
          "The markdown's sentences 'This allows pre-existing nets to be wrapped as reusable subnet fragments without rebuilding them.' and 'It is also how a subnet definition whose body holds a composed instance is built, which nested instantiation needs ([MOD-013]).' are motivation with no shall or MUST: the first is line 6 (the body is the net, not a rebuild), and the second is covered by line 6 with the CDef correspondence the ClosedNet keeps ([MOD-031]); nested instantiation itself is stated by MOD-013's block."
          "Line 7 is the sentence of MOD-006 'Each failure MUST produce an error identifying the offending element by name.', which AC2 brings in: to name a port or channel is for the message to contain its name as a substring (List.IsInfix on the characters), with the weakness MOD-006 records (a blank name is named by every message). All three runtimes name the port or channel and also its place or transition and the net (subnet_def.rs:246-280, SubnetDef.java:522-547, subnet-def.ts fromNet). The line is existential over the offenders: Rust walks the interface's hash maps (rust/libpetri-core/src/subnet_def.rs:244, :264), so which offender is named when there are several is not stated, nor whether ports are checked before channels."
          "AC2 (the interface validation rules of MOD-006 apply) is lines 1 to 4 and 7, MOD-006's cases 1 to 4 and its message rule stated of fromNet; case 5 does not arise (above). AC3 (the result is unparameterised, its parameter type the unit or void type) is API typing, kind Q: the model's SubnetDef carries no parameter type, and the runtimes' result types are SubnetDef<()> (rust/libpetri-core/src/subnet_def.rs:232), SubnetDef<Void> (java/src/main/java/org/libpetri/core/SubnetDef.java:507) and SubnetDef<void> (typescript/src/core/subnet-def.ts fromNet); tested, not proven. The test derivation (a net with places a and b, the port in on a) is MOD_014_nonvacuous."
  signoff "2026-11-13 9f29ec20e2b63a3f ai"
  statement : ∀ {N A : Type}, FromNetFn N A → Prop :=
    fun {N A} F =>
      (∀ (X : ClosedNet N A) ps cs, ∀ q ∈ ps, q.place ∉ X.places → ∃ msg, F X ps cs = .error msg) ∧
      (∀ (X : ClosedNet N A) ps cs, ∀ c ∈ cs, c.trans ∉ X.defs.map (·.core.name) →
        ∃ msg, F X ps cs = .error msg) ∧
      (∀ (X : ClosedNet N A) ps cs, ¬ (ps.map (·.name)).Nodup → ∃ msg, F X ps cs = .error msg) ∧
      (∀ (X : ClosedNet N A) ps cs, ¬ (cs.map (·.name)).Nodup → ∃ msg, F X ps cs = .error msg) ∧
      (∀ (X : ClosedNet N A) ps cs, (∀ q ∈ ps, q.place ∈ X.places) →
        (∀ c ∈ cs, c.trans ∈ X.defs.map (·.core.name)) →
        (ps.map (·.name)).Nodup → (cs.map (·.name)).Nodup → ∃ D, F X ps cs = .ok D) ∧
      (∀ (X : ClosedNet N A) ps cs D, F X ps cs = .ok D → D = X.wrap ps cs) ∧
      (∀ (X : ClosedNet N A) ps cs msg, F X ps cs = .error msg →
        (∃ q ∈ ps, (q.place ∉ X.places ∨ 2 ≤ (ps.map (·.name)).count q.name) ∧
          q.name.toList <:+: msg.toList) ∨
        ∃ c ∈ cs, (c.trans ∉ X.defs.map (·.core.name) ∨ 2 ≤ (cs.map (·.name)).count c.name) ∧
          c.name.toList <:+: msg.toList)

/- The pinned readable form of MOD-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_014 : {N A : Type} → FromNetFn N A → Prop :=
fun {N A} F =>
  (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan),
      ∀ q ∈ ps, q.place ∉ X.places → ∃ msg, F X ps cs = Except.error msg) ∧
    (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan),
        ∀ c ∈ cs, c.trans ∉ List.map (fun x => x.core.name) X.defs → ∃ msg, F X ps cs = Except.error msg) ∧
      (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan),
          ¬(List.map (fun x => x.name) ps).Nodup → ∃ msg, F X ps cs = Except.error msg) ∧
        (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan),
            ¬(List.map (fun x => x.name) cs).Nodup → ∃ msg, F X ps cs = Except.error msg) ∧
          (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan),
              (∀ q ∈ ps, q.place ∈ X.places) →
                (∀ c ∈ cs, c.trans ∈ List.map (fun x => x.core.name) X.defs) →
                  (List.map (fun x => x.name) ps).Nodup →
                    (List.map (fun x => x.name) cs).Nodup → ∃ D, F X ps cs = Except.ok D) ∧
            (∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) (D : SubnetDef N A),
                F X ps cs = Except.ok D → D = X.wrap ps cs) ∧
              ∀ (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) (msg : String),
                F X ps cs = Except.error msg →
                  (∃ q ∈ ps,
                      (q.place ∉ X.places ∨ 2 ≤ List.count q.name (List.map (fun x => x.name) ps)) ∧
                        q.name.toList <:+: msg.toList) ∨
                    ∃ c ∈ cs,
                      (c.trans ∉ List.map (fun x => x.core.name) X.defs ∨
                          2 ≤ List.count c.name (List.map (fun x => x.name) cs)) ∧
                        c.name.toList <:+: msg.toList
-/
#guard_msgs in #print MOD_014

/-! ### The seven lines, named (for the mutants) -/

section Lines

/-- The transition names of a closed net. -/
def ClosedNet.transNames (X : ClosedNet N A) : List String := X.defs.map (·.core.name)

/-- Line 1 of MOD-014: a port on a place the net does not hold fails. -/
def mod014_line1 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs, ∀ q ∈ ps, q.place ∉ X.places → ∃ msg, F X ps cs = .error msg

/-- Line 2 of MOD-014: a channel on a transition name the net does not hold fails. -/
def mod014_line2 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs, ∀ c ∈ cs, c.trans ∉ X.defs.map (·.core.name) →
    ∃ msg, F X ps cs = .error msg

/-- Line 3 of MOD-014: two ports of one name fail. -/
def mod014_line3 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs, ¬ (ps.map (·.name)).Nodup → ∃ msg, F X ps cs = .error msg

/-- Line 4 of MOD-014: two channels of one name fail. -/
def mod014_line4 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs, ¬ (cs.map (·.name)).Nodup → ∃ msg, F X ps cs = .error msg

/-- Line 5 of MOD-014: otherwise `fromNet` succeeds. -/
def mod014_line5 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs, (∀ q ∈ ps, q.place ∈ X.places) →
    (∀ c ∈ cs, c.trans ∈ X.defs.map (·.core.name)) →
    (ps.map (·.name)).Nodup → (cs.map (·.name)).Nodup → ∃ D, F X ps cs = .ok D

/-- Line 6 of MOD-014: a success wraps the net unchanged with the interface as given. -/
def mod014_line6 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs D, F X ps cs = .ok D → D = X.wrap ps cs

/-- What line 7 asks of the message `msg` of a failure on `X`, `ps`, `cs`: it contains the name of
a port whose place `X` does not hold or whose name two ports carry, or of a channel whose
transition name `X` does not hold or whose name two channels carry. -/
def Mod014Named (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) (msg : String) : Prop :=
  (∃ q ∈ ps, (q.place ∉ X.places ∨ 2 ≤ (ps.map (·.name)).count q.name) ∧ MsgNames msg q.name) ∨
  ∃ c ∈ cs, (c.trans ∉ X.defs.map (·.core.name) ∨ 2 ≤ (cs.map (·.name)).count c.name) ∧
    MsgNames msg c.name

/-- Line 7 of MOD-014: a failure's message names an offending port or channel. -/
def mod014_line7 (F : FromNetFn N A) : Prop :=
  ∀ (X : ClosedNet N A) ps cs msg, F X ps cs = .error msg → Mod014Named X ps cs msg

/-- MOD-014 is its seven lines. -/
theorem mod014_iff (F : FromNetFn N A) :
    MOD_014 F ↔ mod014_line1 F ∧ mod014_line2 F ∧ mod014_line3 F ∧ mod014_line4 F ∧
      mod014_line5 F ∧ mod014_line6 F ∧ mod014_line7 F :=
  Iff.rfl

/-- **Line 5 follows from line 7.** When no port or channel offends, a failure would need a
message naming an offender, and there is none; so `fromNet` succeeds. -/
theorem mod014_line5_of_line7 {F : FromNetFn N A} (h7 : mod014_line7 F) : mod014_line5 F := by
  intro X ps cs hp hc hpn hcn
  cases hF : F X ps cs with
  | ok D => exact ⟨D, rfl⟩
  | error msg =>
    exfalso
    rcases h7 X ps cs msg hF with ⟨q, hq, hoff | hoff, -⟩ | ⟨c, hc', hoff | hoff, -⟩
    · exact hoff (hp q hq)
    · have := List.nodup_iff_count_le_one.1 hpn q.name; omega
    · exact hoff (hc c hc')
    · have := List.nodup_iff_count_le_one.1 hcn c.name; omega

/-- An input is good when every port exposes a place of the net, every channel names a
transition of the net, and the port names and the channel names are each distinct. -/
def FromNetGood (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) : Prop :=
  (∀ q ∈ ps, q.place ∈ X.places) ∧ (∀ c ∈ cs, c.trans ∈ X.defs.map (·.core.name)) ∧
    (ps.map (·.name)).Nodup ∧ (cs.map (·.name)).Nodup

/-- Under MOD-014, `fromNet` succeeds exactly on the good inputs, and then returns the wrapped
net. -/
theorem mod014_result {F : FromNetFn N A} (h : MOD_014 F) (X : ClosedNet N A)
    (ps : List (Port N)) (cs : List Chan) :
    (FromNetGood X ps cs → F X ps cs = .ok (X.wrap ps cs)) ∧
      (¬ FromNetGood X ps cs → ∃ msg, F X ps cs = .error msg) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  refine ⟨fun ⟨hp, hc, hpn, hcn⟩ => ?_, fun hn => ?_⟩
  · obtain ⟨D, hD⟩ := h5 X ps cs hp hc hpn hcn
    rw [hD, h6 X ps cs D hD]
  · unfold FromNetGood at hn
    by_cases hp : ∀ q ∈ ps, q.place ∈ X.places
    · by_cases hc : ∀ c ∈ cs, c.trans ∈ X.defs.map (·.core.name)
      · by_cases hpn : (ps.map (·.name)).Nodup
        · exact h4 X ps cs fun hcn => hn ⟨hp, hc, hpn, hcn⟩
        · exact h3 X ps cs hpn
      · obtain ⟨c, hcm⟩ := Classical.not_forall.1 hc
        exact h2 X ps cs c (Classical.not_imp.1 hcm).1 (Classical.not_imp.1 hcm).2
    · obtain ⟨q, hqm⟩ := Classical.not_forall.1 hp
      exact h1 X ps cs q (Classical.not_imp.1 hqm).1 (Classical.not_imp.1 hqm).2

/-- **The block pins `fromNet` up to the message.** Two retrofit utilities that both meet MOD-014
succeed on the same inputs, return the same subnet definition, and fail on the same inputs. -/
theorem mod014_determined {F G : FromNetFn N A} (hF : MOD_014 F) (hG : MOD_014 G)
    (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) :
    (F X ps cs).toOption = (G X ps cs).toOption := by
  by_cases hg : FromNetGood X ps cs
  · rw [(mod014_result hF X ps cs).1 hg, (mod014_result hG X ps cs).1 hg]
  · obtain ⟨m, hm⟩ := (mod014_result hF X ps cs).2 hg
    obtain ⟨m', hm'⟩ := (mod014_result hG X ps cs).2 hg
    rw [hm, hm']; rfl

end Lines

/-! ### The reference: MOD-006's subnet build over a net that is already built -/

section Via

/-- The net `X` as MOD-006's built body: its places, its definitions' `TransDef` parts in order,
its terminal places. -/
def ClosedNet.toBuilt (X : ClosedNet N A) : BuiltNet N A :=
  ⟨X.places, X.defs.map (·.toTransDef), X.terminals⟩

/-- The net `X` with the interface `ps`, `cs` as MOD-006's subnet input. -/
def ClosedNet.toIn (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) : SubnetIn N A :=
  { name := X.name, places := X.places, defs := X.defs, terminals := X.terminals,
    ports := ps, chans := cs }

/-- The net builder that builds nothing: it returns the net `b` as it is. -/
def alreadyBuilt (b : BuiltNet N A) : NetBuilder (defsTB N A) := fun _ => .ok b

/-- The shape of a retrofit utility: MOD-006's subnet build `subnetVia` with the port check `cp`
and the channel check `cc`, over the net builder that returns the supplied net as it is. -/
def fromNetVia (cp cc : SubnetIn N A → BuiltNet N A → Option String) : FromNetFn N A :=
  fun X ps cs => subnetVia (alreadyBuilt X.toBuilt) cp cc (X.toIn ps cs)

/-- The transition names of the net as a built body are the net's transition names. -/
theorem transNames_toBuilt (X : ClosedNet N A) :
    transNames X.toBuilt = X.defs.map (·.core.name) := by
  simp [transNames, ClosedNet.toBuilt, List.map_map]

/-- The subnet definition MOD-006 builds from the net and its interface is the wrapped net. -/
theorem builtDef_toIn (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) :
    builtDef (X.toIn ps cs) X.toBuilt = X.wrap ps cs := rfl

variable {cp cc : SubnetIn N A → BuiltNet N A → Option String}

/-- A `fromNetVia` utility fails unless both checks pass on the net. -/
theorem fromNetVia_fails {X : ClosedNet N A} {ps : List (Port N)} {cs : List Chan}
    (h : cp (X.toIn ps cs) X.toBuilt = none → cc (X.toIn ps cs) X.toBuilt = none → False) :
    ∃ m, fromNetVia cp cc X ps cs = .error m :=
  subnetVia_fails fun b hb hp hc => by
    simp only [alreadyBuilt, Except.ok.injEq] at hb
    subst hb
    exact h hp hc

/-- A `fromNetVia` utility fails only through one of its checks. -/
theorem fromNetVia_error {X : ClosedNet N A} {ps : List (Port N)} {cs : List Chan} {m : String}
    (h : fromNetVia cp cc X ps cs = .error m) :
    cp (X.toIn ps cs) X.toBuilt = some m ∨
      (cp (X.toIn ps cs) X.toBuilt = none ∧ cc (X.toIn ps cs) X.toBuilt = some m) := by
  rcases subnetVia_error.1 h with he | ⟨b, hb, hb'⟩
  · cases he
  · simp only [alreadyBuilt, Except.ok.injEq] at hb
    subst hb
    exact hb'

/-- When both checks pass, a `fromNetVia` utility returns the wrapped net. -/
theorem fromNetVia_succeeds {X : ClosedNet N A} {ps : List (Port N)} {cs : List Chan}
    (hp : cp (X.toIn ps cs) X.toBuilt = none) (hc : cc (X.toIn ps cs) X.toBuilt = none) :
    fromNetVia cp cc X ps cs = .ok (X.wrap ps cs) :=
  subnetVia_ok rfl hp hc

/-- A success of a `fromNetVia` utility is the wrapped net. -/
theorem fromNetVia_ok {X : ClosedNet N A} {ps : List (Port N)} {cs : List Chan}
    {D : SubnetDef N A} (h : fromNetVia cp cc X ps cs = .ok D) : D = X.wrap ps cs := by
  unfold fromNetVia subnetVia at h
  simp only [alreadyBuilt] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- Line 1 for a `fromNetVia` utility whose passing port check means every port place is in the
body. -/
theorem via14_line1 (hP : ∀ S b, cp S b = none → ∀ q ∈ S.ports, q.place ∈ b.places) :
    mod014_line1 (fromNetVia cp cc) := fun _ _ _ q hq hn =>
  fromNetVia_fails fun hp _ => hn (hP _ _ hp q hq)

/-- Line 2 for a `fromNetVia` utility whose passing channel check means every channel's
transition is in the body. -/
theorem via14_line2 (hC : ∀ S b, cc S b = none → ∀ c ∈ S.chans, c.trans ∈ transNames b) :
    mod014_line2 (fromNetVia cp cc) := fun X ps cs c hc hn =>
  fromNetVia_fails fun _ hcc => hn (by rw [← transNames_toBuilt]; exact hC _ _ hcc c hc)

/-- Line 3 for a `fromNetVia` utility whose passing port check means distinct port names. -/
theorem via14_line3 (hP : ∀ S b, cp S b = none → (S.ports.map (·.name)).Nodup) :
    mod014_line3 (fromNetVia cp cc) := fun _ _ _ hn =>
  fromNetVia_fails fun hp _ => hn (hP _ _ hp)

/-- Line 4 for a `fromNetVia` utility whose passing channel check means distinct channel
names. -/
theorem via14_line4 (hC : ∀ S b, cc S b = none → (S.chans.map (·.name)).Nodup) :
    mod014_line4 (fromNetVia cp cc) := fun _ _ _ hn =>
  fromNetVia_fails fun _ hc => hn (hC _ _ hc)

/-- Line 6 holds for every `fromNetVia` utility. -/
theorem via14_line6 : mod014_line6 (fromNetVia cp cc) := fun _ _ _ _ h => fromNetVia_ok h

/-- Line 7 for a `fromNetVia` utility whose failing checks name an offender. -/
theorem via14_line7
    (hP : ∀ S b m, cp S b = some m → ∃ q ∈ S.ports, PortOffends S b q ∧ MsgNames m q.name)
    (hC : ∀ S b m, cc S b = some m → ∃ c ∈ S.chans, ChanOffends S b c ∧ MsgNames m c.name) :
    mod014_line7 (fromNetVia cp cc) := by
  intro X ps cs m h
  rcases fromNetVia_error h with hp | ⟨-, hc⟩
  · exact Or.inl (hP _ _ m hp)
  · obtain ⟨c, hcm, hoff, hn⟩ := hC _ _ m hc
    refine Or.inr ⟨c, hcm, ?_, hn⟩
    unfold ChanOffends at hoff
    rw [transNames_toBuilt] at hoff
    exact hoff

end Via

section Ref

variable [DecidableEq N] [ToString N]

/-- **The reference retrofit utility.** MOD-006's reference subnet build (ports in order, a
duplicate name first, then the place; then the channels the same way) over the net builder that
returns the supplied net as it is, as Rust, Java and TypeScript do (`subnet_def.rs:232-293`,
`SubnetDef.java:507-552`, `subnet-def.ts` `fromNet`). The messages are MOD-006's stand-ins. -/
def refFromNet : FromNetFn N A := fromNetVia refPortCheck refChanCheck

/-- `fromNet` is MOD-006's subnet build of the net and its interface, with a net builder that
returns the net as it is. -/
theorem refFromNet_eq (X : ClosedNet N A) (ps : List (Port N)) (cs : List Chan) :
    refFromNet X ps cs = refSubnetBuild (alreadyBuilt X.toBuilt) (X.toIn ps cs) := rfl

end Ref

/- The reference retrofit utility is the witness model of MOD-014. -/
#spec_witness refFromNet

/-- ✓ The reference retrofit utility satisfies MOD-014: it rejects a port on a place the net does
not hold, a channel on a transition name it does not hold, and two ports or two channels of one
name, each with a message naming that port or channel; everything else it accepts, and it returns
the net unchanged with the interface as given. -/
@[evidence holds MOD_014]
theorem MOD_014_reference {N A : Type} [DecidableEq N] [ToString N] :
    MOD_014 (refFromNet (N := N) (A := A)) := by
  refine ⟨via14_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via14_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via14_line3 fun S b h => ((refPortCheck_none S b).1 h).2,
    via14_line4 fun S b h => ((refChanCheck_none S b).1 h).2, ?_, via14_line6,
    via14_line7 refPortCheck_some refChanCheck_some⟩
  intro X ps cs hp hc hpn hcn
  refine ⟨_, fromNetVia_succeeds ((refPortCheck_none _ _).2 ⟨hp, hpn⟩)
    ((refChanCheck_none _ _).2 ⟨fun c hcm => ?_, hcn⟩)⟩
  rw [transNames_toBuilt]
  exact hc c hcm

/-! ### Example -/

/-- The example transition `t`: an input arc on `a` and the output place `b`. -/
def mod014_t : CDef String Unit :=
  { core := ⟨"t", [⟨"a", .one⟩], [], [], []⟩, out := some (.place "b"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The example net `pipe`: the places `a` and `b` and the transition `t`. -/
def mod014_net : ClosedNet String Unit :=
  { name := "pipe", places := ["a", "b"], defs := [mod014_t] }

/-- `pipe` with `b` declared a terminal place. -/
def mod014_netTerm : ClosedNet String Unit := { mod014_net with terminals := ["b"] }

/-- The port `in` on `a`. -/
def mod014_in : Port String := ⟨"in", .input, "a"⟩

/-- The channel `go` on `t`. -/
def mod014_go : Chan := ⟨"go", "t"⟩

/-- ✓ Every line of MOD-014 is exercised by the reference. Wrapping the net `pipe` (places `a`
and `b`, transition `t` from `a` to `b`) with the port `in` on `a` and the channel `go` on `t`
gives the subnet definition `pipe` whose body is the net and whose interface exposes `in` over
`a` (lines 5 and 6, the test derivation). The same net with `b` declared terminal is accepted
too: `fromNet` does not refuse terminal places, instantiation does. A port `in` on `nowhere`, a
channel `go` on `missing`, two ports named `in` and two channels named `go` are rejected, and
every message names `in` or `go` (lines 1 to 4 and 7). -/
@[evidence nonvacuous MOD_014]
theorem MOD_014_nonvacuous :
    refFromNet mod014_net [mod014_in] [mod014_go] =
        .ok { name := "pipe", places := ["a", "b"], defs := [mod014_t], terminals := [],
              ports := [⟨"in", .input, "a"⟩], chans := [⟨"go", "t"⟩] } ∧
      refFromNet mod014_netTerm [mod014_in] [mod014_go] =
        .ok (mod014_netTerm.wrap [mod014_in] [mod014_go]) ∧
      refFromNet mod014_net [⟨"in", .input, "nowhere"⟩] [] =
        .error (portPlaceMsg "pipe" (⟨"in", .input, "nowhere"⟩ : Port String)) ∧
      refFromNet mod014_net [] [⟨"go", "missing"⟩] =
        .error (chanTransMsg "pipe" ⟨"go", "missing"⟩) ∧
      refFromNet mod014_net [mod014_in, ⟨"in", .output, "b"⟩] [] =
        .error (dupPortMsg "pipe" (⟨"in", .output, "b"⟩ : Port String)) ∧
      refFromNet mod014_net [] [mod014_go, mod014_go] =
        .error (dupChanMsg "pipe" mod014_go) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Wrong retrofit utilities -/

/-- A utility that validates nothing and wraps every net with every interface. -/
def fromNetNoValidate : FromNetFn N A := fun X ps cs => .ok (X.wrap ps cs)

/-- A utility that rejects everything. -/
def fromNetRejectAll : FromNetFn N A := fun _ _ _ => .error "rejected"

/-- ✗ A utility that validates nothing violates MOD-014 (line 1): it wraps `pipe` with the port
`in` on `nowhere`, a place the net does not hold. -/
@[evidence forbids MOD_014]
theorem MOD_014_forbids_noValidate : ¬ MOD_014 (fromNetNoValidate (N := String) (A := Unit)) := by
  intro h
  obtain ⟨msg, hm⟩ := h.1 mod014_net [⟨"in", .input, "nowhere"⟩] [] _ List.mem_cons_self
    (by decide)
  cases hm

/-- ✗ A utility that rejects everything violates MOD-014 (line 5): it rejects `pipe` with the port
`in` on `a` and the channel `go` on `t`, which are both fine. -/
@[evidence forbids MOD_014]
theorem MOD_014_forbids_rejectAll : ¬ MOD_014 (fromNetRejectAll (N := String) (A := Unit)) := by
  intro h
  obtain ⟨D, hD⟩ := h.2.2.2.2.1 mod014_net [mod014_in] [mod014_go] (by decide) (by decide)
    (by decide) (by decide)
  cases hD

/-! ### Mutants, one per load-bearing line -/

/-- Mutant reading: MOD-014 without line 1 (no port-place check). -/
def MOD_014_mutant_noPortPlace (F : FromNetFn N A) : Prop :=
  mod014_line2 F ∧ mod014_line3 F ∧ mod014_line4 F ∧ mod014_line5 F ∧ mod014_line6 F ∧
    mod014_line7 F

/-- Mutant reading: MOD-014 without line 2 (no channel-transition check). -/
def MOD_014_mutant_noChanTrans (F : FromNetFn N A) : Prop :=
  mod014_line1 F ∧ mod014_line3 F ∧ mod014_line4 F ∧ mod014_line5 F ∧ mod014_line6 F ∧
    mod014_line7 F

/-- Mutant reading: MOD-014 without line 3 (no duplicate-port check). -/
def MOD_014_mutant_noDupPort (F : FromNetFn N A) : Prop :=
  mod014_line1 F ∧ mod014_line2 F ∧ mod014_line4 F ∧ mod014_line5 F ∧ mod014_line6 F ∧
    mod014_line7 F

/-- Mutant reading: MOD-014 without line 4 (no duplicate-channel check). -/
def MOD_014_mutant_noDupChan (F : FromNetFn N A) : Prop :=
  mod014_line1 F ∧ mod014_line2 F ∧ mod014_line3 F ∧ mod014_line5 F ∧ mod014_line6 F ∧
    mod014_line7 F

/-- Mutant reading: MOD-014 without line 6 (a success may return any definition). -/
def MOD_014_mutant_anyBody (F : FromNetFn N A) : Prop :=
  mod014_line1 F ∧ mod014_line2 F ∧ mod014_line3 F ∧ mod014_line4 F ∧ mod014_line5 F ∧
    mod014_line7 F

/-- Mutant reading: MOD-014 without line 7 (a failure's message need not name anything). -/
def MOD_014_mutant_anyMessage (F : FromNetFn N A) : Prop :=
  mod014_line1 F ∧ mod014_line2 F ∧ mod014_line3 F ∧ mod014_line4 F ∧ mod014_line5 F ∧
    mod014_line6 F

/-- A utility that validates like the reference and then returns a renamed copy of the net: every
place and transition renamed under `copy` (a rebuild under new names instead of the net itself). -/
def fromNetCopiesRenamed : FromNetFn String Unit := fun X ps cs =>
  (refFromNet X ps cs).map fun D =>
    { D with places := D.places.map (preS "copy"), defs := D.defs.map (CDef.map (preS "copy") (preS "copy")) }

/-- The mutant without line 1 is killed by the utility without the place test: it meets every
other line, but wraps `pipe` with the port `in` on `nowhere`. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_noPortPlace_killed :
    MOD_014_mutant_noPortPlace (fromNetVia (N := String) (A := Unit) noPlacePortCheck refChanCheck) ∧
      ¬ MOD_014 (fromNetVia (N := String) (A := Unit) noPlacePortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noPlacePortCheck S b = none ↔
      (S.ports.map (·.name)).Nodup := fun S b => by
    unfold noPlacePortCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via14_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via14_line3 fun S b h => (hP S b).1 h,
    via14_line4 fun S b h => ((refChanCheck_none S b).1 h).2,
    fun X ps cs _ hc hpn hcn => ⟨_, fromNetVia_succeeds ((hP _ _).2 hpn)
      ((refChanCheck_none _ _).2 ⟨fun c hcm => by rw [transNames_toBuilt]; exact hc c hcm, hcn⟩)⟩,
    via14_line6, via14_line7 (fun S b m h => ?_) refChanCheck_some⟩, fun h => ?_⟩
  · obtain ⟨q, hq, hoff, hm⟩ := checkList_some h
    refine ⟨q, hq, ?_, ?_⟩
    · rcases hoff with h1 | h2 | h3
      · exact absurd trivial h1
      · cases h2
      · exact Or.inr h3
    · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
  · obtain ⟨msg, hm⟩ := h.1 mod014_net [⟨"in", .input, "nowhere"⟩] [] _ List.mem_cons_self
      (by decide)
    have : fromNetVia noPlacePortCheck refChanCheck mod014_net [⟨"in", .input, "nowhere"⟩] [] =
      .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 2 is killed by the utility without the transition test: it meets
every other line, but wraps `pipe` with the channel `go` on `missing`. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_noChanTrans_killed :
    MOD_014_mutant_noChanTrans (fromNetVia (N := String) (A := Unit) refPortCheck noTransChanCheck) ∧
      ¬ MOD_014 (fromNetVia (N := String) (A := Unit) refPortCheck noTransChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noTransChanCheck S b = none ↔
      (S.chans.map (·.name)).Nodup := fun S b => by
    unfold noTransChanCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via14_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via14_line3 fun S b h => ((refPortCheck_none S b).1 h).2,
    via14_line4 fun S b h => (hC S b).1 h,
    fun X ps cs hp _ hpn hcn => ⟨_, fromNetVia_succeeds ((refPortCheck_none _ _).2 ⟨hp, hpn⟩)
      ((hC _ _).2 hcn)⟩,
    via14_line6, via14_line7 refPortCheck_some (fun S b m h => ?_)⟩, fun h => ?_⟩
  · obtain ⟨c, hc, hoff, hm⟩ := checkList_some h
    refine ⟨c, hc, ?_, ?_⟩
    · rcases hoff with h1 | h2 | h3
      · exact absurd trivial h1
      · cases h2
      · exact Or.inr h3
    · rcases hm with rfl | rfl <;> exact msgNames_mid _ _ _
  · obtain ⟨msg, hm⟩ := h.2.1 mod014_net [] [⟨"go", "missing"⟩] _ List.mem_cons_self
      (by decide)
    have : fromNetVia refPortCheck noTransChanCheck mod014_net [] [⟨"go", "missing"⟩] =
      .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 3 is killed by the utility without the duplicate-port test: it meets
every other line, but wraps `pipe` with two ports named `in`, both on places of the net. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_noDupPort_killed :
    MOD_014_mutant_noDupPort (fromNetVia (N := String) (A := Unit) noDupPortCheck refChanCheck) ∧
      ¬ MOD_014 (fromNetVia (N := String) (A := Unit) noDupPortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noDupPortCheck S b = none ↔
      ∀ q ∈ S.ports, q.place ∈ b.places := fun S b => by
    unfold noDupPortCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via14_line1 fun S b h => (hP S b).1 h,
    via14_line2 fun S b h => ((refChanCheck_none S b).1 h).1,
    via14_line4 fun S b h => ((refChanCheck_none S b).1 h).2,
    fun X ps cs hp hc _ hcn => ⟨_, fromNetVia_succeeds ((hP _ _).2 hp)
      ((refChanCheck_none _ _).2 ⟨fun c hcm => by rw [transNames_toBuilt]; exact hc c hcm, hcn⟩)⟩,
    via14_line6, via14_line7 (fun S b m h => ?_) refChanCheck_some⟩, fun h => ?_⟩
  · obtain ⟨q, hq, hoff, rfl⟩ := checkOnly_some h
    exact ⟨q, hq, Or.inl hoff, msgNames_mid _ _ _⟩
  · obtain ⟨msg, hm⟩ := h.2.2.1 mod014_net [mod014_in, ⟨"in", .output, "b"⟩] [] (by decide)
    have : fromNetVia noDupPortCheck refChanCheck mod014_net [mod014_in, ⟨"in", .output, "b"⟩] [] =
      .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 4 is killed by the utility without the duplicate-channel test: it
meets every other line, but wraps `pipe` with two channels named `go`, both on `t`. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_noDupChan_killed :
    MOD_014_mutant_noDupChan (fromNetVia (N := String) (A := Unit) refPortCheck noDupChanCheck) ∧
      ¬ MOD_014 (fromNetVia (N := String) (A := Unit) refPortCheck noDupChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noDupChanCheck S b = none ↔
      ∀ c ∈ S.chans, c.trans ∈ transNames b := fun S b => by
    unfold noDupChanCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via14_line1 fun S b h => ((refPortCheck_none S b).1 h).1,
    via14_line2 fun S b h => (hC S b).1 h,
    via14_line3 fun S b h => ((refPortCheck_none S b).1 h).2,
    fun X ps cs hp hc hpn _ => ⟨_, fromNetVia_succeeds ((refPortCheck_none _ _).2 ⟨hp, hpn⟩)
      ((hC _ _).2 fun c hcm => by rw [transNames_toBuilt]; exact hc c hcm)⟩,
    via14_line6, via14_line7 refPortCheck_some (fun S b m h => ?_)⟩, fun h => ?_⟩
  · obtain ⟨c, hc, hoff, rfl⟩ := checkOnly_some h
    exact ⟨c, hc, Or.inl hoff, msgNames_mid _ _ _⟩
  · obtain ⟨msg, hm⟩ := h.2.2.2.1 mod014_net [] [mod014_go, mod014_go] (by decide)
    have : fromNetVia refPortCheck noDupChanCheck mod014_net [] [mod014_go, mod014_go] =
      .ok _ := rfl
    rw [this] at hm; cases hm

/-- The mutant without line 6 is killed by the utility that validates like the reference and then
returns a copy of the net renamed under `copy`: it meets every other line, but wrapping `pipe`
gives a body with the places `copy/a` and `copy/b`, not `a` and `b`. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_anyBody_killed :
    MOD_014_mutant_anyBody fromNetCopiesRenamed ∧ ¬ MOD_014 fromNetCopiesRenamed := by
  have R := MOD_014_reference (N := String) (A := Unit)
  have herr : ∀ X ps cs m, fromNetCopiesRenamed X ps cs = .error m ↔ refFromNet X ps cs = .error m :=
    fun X ps cs m => by
      unfold fromNetCopiesRenamed
      cases refFromNet X ps cs <;> simp [Except.map]
  have hfail : ∀ X ps cs, (∃ m, refFromNet X ps cs = .error m) →
      ∃ m, fromNetCopiesRenamed X ps cs = .error m :=
    fun X ps cs ⟨m, hm⟩ => ⟨m, (herr X ps cs m).2 hm⟩
  refine ⟨⟨fun X ps cs q hq hn => hfail X ps cs (R.1 X ps cs q hq hn),
    fun X ps cs c hc hn => hfail X ps cs (R.2.1 X ps cs c hc hn),
    fun X ps cs hn => hfail X ps cs (R.2.2.1 X ps cs hn),
    fun X ps cs hn => hfail X ps cs (R.2.2.2.1 X ps cs hn),
    fun X ps cs hp hc hpn hcn => ?_,
    fun X ps cs m h => R.2.2.2.2.2.2 X ps cs m ((herr X ps cs m).1 h)⟩, fun h => ?_⟩
  · obtain ⟨D, hD⟩ := R.2.2.2.2.1 X ps cs hp hc hpn hcn
    exact ⟨_, by unfold fromNetCopiesRenamed; rw [hD]; rfl⟩
  · have hc : fromNetCopiesRenamed mod014_net [mod014_in] [mod014_go] =
        .ok { mod014_net.wrap [mod014_in] [mod014_go] with
              places := ["copy/a", "copy/b"],
              defs := [mod014_t].map (CDef.map (preS "copy") (preS "copy")) } := rfl
    have := congrArg SubnetDef.places (h.2.2.2.2.2.1 _ _ _ _ hc)
    revert this; decide

/-- The example with one port `x` on `nowhere` and no channel. -/
def mod014_badX : List (Port String) := [⟨"x", .input, "nowhere"⟩]

/-- The mutant without line 7 is killed by the utility whose messages name the subnet only: it
meets every other line, but rejects `pipe` with its port `x` on `nowhere` with "Subnet 'pipe' is
invalid", which does not name the port `x`. -/
@[evidence mutant MOD_014]
theorem MOD_014_mutant_anyMessage_killed :
    MOD_014_mutant_anyMessage
        (fromNetVia (N := String) (A := Unit) subnetMsgPortCheck subnetMsgChanCheck) ∧
      ¬ MOD_014 (fromNetVia (N := String) (A := Unit) subnetMsgPortCheck subnetMsgChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, subnetMsgPortCheck S b = none ↔
      (∀ q ∈ S.ports, q.place ∈ b.places) ∧ (S.ports.map (·.name)).Nodup := fun S b => by
    unfold subnetMsgPortCheck; rw [checkList_none_iff]; simp
  have hC : ∀ (S : SubnetIn String Unit) b, subnetMsgChanCheck S b = none ↔
      (∀ c ∈ S.chans, c.trans ∈ transNames b) ∧ (S.chans.map (·.name)).Nodup := fun S b => by
    unfold subnetMsgChanCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via14_line1 fun S b h => ((hP S b).1 h).1, via14_line2 fun S b h => ((hC S b).1 h).1,
    via14_line3 fun S b h => ((hP S b).1 h).2, via14_line4 fun S b h => ((hC S b).1 h).2,
    fun X ps cs hp hc hpn hcn => ⟨_, fromNetVia_succeeds ((hP _ _).2 ⟨hp, hpn⟩)
      ((hC _ _).2 ⟨fun c hcm => by rw [transNames_toBuilt]; exact hc c hcm, hcn⟩)⟩,
    via14_line6⟩, fun h => ?_⟩
  have hm : fromNetVia subnetMsgPortCheck subnetMsgChanCheck mod014_net mod014_badX [] =
      .error (subnetOnlyMsg "pipe") := rfl
  rcases h.2.2.2.2.2.2 _ _ _ _ hm with ⟨q, hq, -, hn⟩ | ⟨c, hc, -⟩
  · simp only [mod014_badX, List.mem_singleton] at hq
    subst hq
    exact not_msgNames (ch := 'x') (by decide) (by decide) hn
  · simp at hc

end Libpetri.Spec
