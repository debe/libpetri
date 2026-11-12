import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.Req.CORE_040
import Libpetri.Spec.Req.MOD_006
import Libpetri.Spec.Req.MOD_010

set_option linter.missingDocs true

/-!
# MOD-001: Subnet definition (`spec/11-modular-composition.md`)

MOD-001 is a pure-function requirement (kind F) over the same two abstract functions as MOD-006:
the net builder `NB` of a subnet's body and the subnet builder `SB : SubnetMake N A`. MOD-006 says
when building a subnet definition fails; MOD-001 says what a successful build returns.

When the subnet builder builds, the definition holds exactly the declared ports (name, direction
and place) and exactly the declared channels, both compared as sets; its body holds the places
and terminal places of the net the net builder builds, and the declared transition definitions
in the order added, none renamed; and the definition keeps its declared name. A subnet whose
interface declares no port and no channel builds whenever its body builds.

The witness is MOD-006's reference subnet builder `refSubnetBuild NB`; the block holds of it for
every net builder `NB`. A builder that keeps the ports in another order, as Rust's hash map does,
meets it too (`MOD_001_allows_portOrder`). Wrong builders are killed, one per line. Jointly with
CORE-040 and MOD-006, every definition the subnet builder returns has its ports on body places and
its channels on body transitions, so instantiating it under a valid prefix succeeds when it
declares no terminal place (`mod001_instantiable`, `mod001_mod010`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## MOD-001: SubnetDef Definition (open net + interface) -/

requirement MOD_001
  id "MOD-001"
  title "SubnetDef Definition (open net + interface)"
  kind F
  scope "every subnet builder"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared ports, each with the name, direction and place it was declared with."
        "*When* building the subnet definition succeeds, its interface *shall* hold exactly the declared channels, each with the name and transition it was declared with."
        "*When* building the subnet definition succeeds, its body *shall* hold the places and terminal places of the net that the net builder builds from the declaration, and the declared transitions in the order they were added, none of them renamed."
        "*When* building the subnet definition succeeds, the subnet definition *shall* keep the name it was declared with."
        "*When* the net builder builds the body and the interface declares no port and no channel, building the subnet definition *shall* succeed."
  reading "For every net builder NB of subnet bodies and every subnet builder SB:"
          "if SB builds S as the definition D, a port is a port of D exactly when it is a port of S (same name, direction and place);"
          "if SB builds S as D, a channel is a channel of D exactly when it is a channel of S (same name and transition name);"
          "if SB builds S as D and NB builds the body of S as b, a place is a place of D exactly when it is a place of b, a place is a terminal place of D exactly when it is a terminal place of b, and, when the transition names of S are pairwise distinct, the transition definitions of D are those of S, in the same order;"
          "if SB builds S as D, the name of D is the name of S;"
          "if NB builds the body of S and S declares no port and no channel, SB succeeds on S."
  assumes "A subnet builder (SubnetMake) and the body net builder NB are read as in MOD-006: SB is the build call of one implementation's subnet-definition builder, NB the net builder it builds the body with, typed as a CORE-040 net builder over defsTB so that CORE-040, EXEC-042, MOD-006 and this block speak of the same function. All three runtimes return the declared name, the built body itself and an interface made of the declared ports and channels (rust/libpetri-core/src/subnet_def.rs:378-430, java/src/main/java/org/libpetri/core/SubnetDef.java:624-662, typescript/src/core/subnet-def.ts:539-580); Python rides on Rust. The holds theorem holds for every NB."
          "Lines 1 and 2 compare ports and channels as sets (membership both ways), not as lists: Rust keeps the interface in hash maps (rust/libpetri-core/src/interface.rs:104-107), so its iteration order is not the declaration order (MOD_001_allows_portOrder). A port is its name, direction and place, so a builder that forgets a direction violates line 1. A channel is its name and the name of its transition (ruling D23, settled by D10); Java and TypeScript keep the transition object, which under the unique-names assumption is the same thing. Duplicate names never reach a success (MOD-006 lines 3 and 4), so the set reading loses nothing."
          "Line 3 states the body against the net b that NB builds; that a success comes with a body NB builds at all is MOD-006 line 5, not repeated here. The places include every place an arc of a body transition names (CORE-040), so a port on such a place exposes a place of the definition. Places and terminal places are compared as sets (CORE-040 fixes their collection, not their order). The transition definitions are stated against the declaration, as a list in the order added, under the premise that their names are pairwise distinct, the unique-names assumption of rulings D10 and D23 (TIME-010; RD-10 in spec/runtime-defects.md records that no builder checks names): without it Java and TypeScript keep a transition object added twice once (a set), Rust twice (a vector). A definition carries its correspondence (MOD-031) unchanged, because the line equates the whole definitions. Jointly with CORE-040 the definitions are the built body's transitions (mod001_instantiable)."
          "Line 4 keeps the definition's name, which the runtimes use in their messages (MOD-006) and which direct composition records as the subnet a node belongs to (MOD-026)."
          "Line 5 is AC3's 'possibly empty' set of ports and channels: an empty interface is no reason to reject. Jointly with MOD-006 line 6 it is implied there, but this block states it of its own."
          "AC1 (a subnet definition can be constructed with a body net and an interface) is line 5 together with MOD-006 line 6 (the acceptance line) and the nonvacuity example. AC2 (the body follows all CORE construction rules and is itself immutable per CORE-041): the construction rules are the net builder's (CORE-040, EXEC-042) and MOD-006 line 5 rejects a body they refuse; immutability is a quality property of host values (Lean values are immutable; builder stability is CORE-041's line), tested and not proven. AC3 (the interface enumerates a possibly empty set of ports and a possibly empty set of channels) is lines 1, 2 and 5. AC4 (the definition exposes body() and iface()) is lines 1 to 3: what they hold; the accessor names are API surface, tested and not proven. AC5 (immutable after construction) is a quality property, as for AC2."
          "The MAY sentence on a typed Params value is not modelled: the parameter type is compile-time typing (MOD-010 AC4), and Python offers unparameterised definitions only (rust/libpetri-py/src/model.rs:626, :907), which the MAY allows. The test derivation (two places, one transition, one port; body, interface, port set and channel set accessible and unmodifiable) is the nonvacuity example for the accessible part and AC2/AC5 for the unmodifiable part."
  signoff "pending"
  statement : ∀ {N A : Type}, NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
    fun {N A} NB SB =>
      (∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q, q ∈ D.ports ↔ q ∈ S.ports) ∧
      (∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ c, c ∈ D.chans ↔ c ∈ S.chans) ∧
      (∀ (S : SubnetIn N A) D b, SB S = .ok D → NB S.body = .ok b →
        (∀ p, p ∈ D.places ↔ p ∈ b.places) ∧ (∀ p, p ∈ D.terminals ↔ p ∈ b.terminals) ∧
        ((S.defs.map (·.core.name)).Nodup → D.defs = S.defs)) ∧
      (∀ (S : SubnetIn N A) D, SB S = .ok D → D.name = S.name) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b → S.ports = [] → S.chans = [] →
        ∃ D, SB S = .ok D)

/- The pinned readable form of MOD-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_001 : {N A : Type} → NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
fun {N A} NB SB =>
  (∀ (S : SubnetIn N A) (D : SubnetDef N A), SB S = Except.ok D → ∀ (q : Port N), q ∈ D.ports ↔ q ∈ S.ports) ∧
    (∀ (S : SubnetIn N A) (D : SubnetDef N A), SB S = Except.ok D → ∀ (c : Chan), c ∈ D.chans ↔ c ∈ S.chans) ∧
      (∀ (S : SubnetIn N A) (D : SubnetDef N A) (b : BuiltNet N A),
          SB S = Except.ok D →
            NB S.body = Except.ok b →
              (∀ (p : N), p ∈ D.places ↔ p ∈ b.places) ∧
                (∀ (p : N), p ∈ D.terminals ↔ p ∈ b.terminals) ∧
                  ((List.map (fun x => x.core.name) S.defs).Nodup → D.defs = S.defs)) ∧
        (∀ (S : SubnetIn N A) (D : SubnetDef N A), SB S = Except.ok D → D.name = S.name) ∧
          ∀ (S : SubnetIn N A) (b : BuiltNet N A),
            NB S.body = Except.ok b → S.ports = [] → S.chans = [] → ∃ D, SB S = Except.ok D
-/
#guard_msgs in #print MOD_001

/-! ### The five lines, named (for the mutants) -/

section Lines

/-- Line 1 of MOD-001: a built definition holds exactly the declared ports. -/
def mod001_line1 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q, q ∈ D.ports ↔ q ∈ S.ports

/-- Line 2 of MOD-001: a built definition holds exactly the declared channels. -/
def mod001_line2 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ c, c ∈ D.chans ↔ c ∈ S.chans

/-- Line 3 of MOD-001: a built definition's body is the built net, unrenamed. -/
def mod001_line3 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D b, SB S = .ok D → NB S.body = .ok b →
    (∀ p, p ∈ D.places ↔ p ∈ b.places) ∧ (∀ p, p ∈ D.terminals ↔ p ∈ b.terminals) ∧
    ((S.defs.map (·.core.name)).Nodup → D.defs = S.defs)

/-- Line 4 of MOD-001: a built definition keeps its declared name. -/
def mod001_line4 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D, SB S = .ok D → D.name = S.name

/-- Line 5 of MOD-001: an empty interface over a body that builds builds. -/
def mod001_line5 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b → S.ports = [] → S.chans = [] → ∃ D, SB S = .ok D

/-- MOD-001 is its five lines. -/
theorem mod001_iff (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) :
    MOD_001 NB SB ↔ mod001_line1 SB ∧ mod001_line2 SB ∧ mod001_line3 NB SB ∧ mod001_line4 SB ∧
      mod001_line5 NB SB :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- A `subnetVia` builder succeeds only when the body builds as some `b`, and then returns
`builtDef S b`. -/
theorem subnetVia_eq_ok {NB : NetBuilder (defsTB N A)}
    {cp cc : SubnetIn N A → BuiltNet N A → Option String} {S : SubnetIn N A} {D : SubnetDef N A}
    (h : subnetVia NB cp cc S = .ok D) : ∃ b, NB S.body = .ok b ∧ D = builtDef S b := by
  cases hb : NB S.body with
  | error e => simp [subnetVia, hb] at h
  | ok b =>
    cases hp : cp S b with
    | some m => simp [subnetVia, hb, hp] at h
    | none =>
      cases hc : cc S b with
      | some m => simp [subnetVia, hb, hp, hc] at h
      | none =>
        simp only [subnetVia, hb, hp, hc, Except.ok.injEq] at h
        exact ⟨b, rfl, h.symm⟩

section Ref

variable [DecidableEq N] [ToString N]

/-- The reference subnet builder succeeds only when the body builds as some `b`, and then returns
`builtDef S b`: the declared name, ports, channels and definitions, the built body's places and
terminal places. -/
theorem refSubnetBuild_eq_ok {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    {D : SubnetDef N A} (h : refSubnetBuild NB S = .ok D) :
    ∃ b, NB S.body = .ok b ∧ D = builtDef S b :=
  subnetVia_eq_ok h

/-- The reference subnet builder builds an empty interface whenever the body builds. -/
theorem refSubnetBuild_empty {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A} {b : BuiltNet N A}
    (hb : NB S.body = .ok b) (hp : S.ports = []) (hc : S.chans = []) :
    refSubnetBuild NB S = .ok (builtDef S b) :=
  subnetVia_ok hb (by simp [refPortCheck, hp, checkList]) (by simp [refChanCheck, hc, checkList])

/-- The five lines of the reference subnet builder. -/
theorem refSubnetBuild_lines (NB : NetBuilder (defsTB N A)) :
    mod001_line1 (refSubnetBuild NB) ∧ mod001_line2 (refSubnetBuild NB) ∧
      mod001_line3 NB (refSubnetBuild NB) ∧ mod001_line4 (refSubnetBuild NB) ∧
      mod001_line5 NB (refSubnetBuild NB) := by
  refine ⟨fun S D h q => ?_, fun S D h c => ?_, fun S D b h hb => ?_, fun S D h => ?_,
    fun S b hb hp hc => ⟨_, refSubnetBuild_empty hb hp hc⟩⟩
  · obtain ⟨b, -, rfl⟩ := refSubnetBuild_eq_ok h; exact Iff.rfl
  · obtain ⟨b, -, rfl⟩ := refSubnetBuild_eq_ok h; exact Iff.rfl
  · obtain ⟨b', hb', rfl⟩ := refSubnetBuild_eq_ok h
    rw [hb] at hb'; cases hb'
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl⟩
  · obtain ⟨b, -, rfl⟩ := refSubnetBuild_eq_ok h; rfl

end Ref

/-- ✓ The reference subnet builder satisfies MOD-001 for every net builder: what it returns is the
declared name, the declared ports and channels, and the body the net builder built, with the
declared transitions in the order added; and a subnet with no port and no channel builds whenever
its body does. -/
@[evidence holds MOD_001]
theorem MOD_001_reference {N A : Type} [DecidableEq N] [ToString N]
    (NB : NetBuilder (defsTB N A)) : MOD_001 NB (refSubnetBuild NB) :=
  refSubnetBuild_lines NB

/-! ### Example -/

/-- The example subnet `buf` of MOD-006 with an empty interface: no port, no channel. -/
def mod001_exEmpty : SubnetIn String Unit :=
  { mod006_exS with ports := [], chans := [] }

/-- ✓ Every line of MOD-001 is exercised by the reference over the reference net builder. The
subnet `buf` (place `slots`, transition `take` from `slots` into `done`, port `in` on `slots`,
port `out` on `done`, channel `go` on `take`) builds as a definition named `buf` whose ports are
`in` (input, on `slots`) and `out` (output, on `done`), whose channel is `go` on `take`, whose body
holds `slots` and `done`, and whose transitions are `take`, unrenamed. The same body with no port
and no channel builds too, with an empty interface. -/
@[evidence nonvacuous MOD_001]
theorem MOD_001_nonvacuous :
    (∃ D, refSubnetBuild refNetBuild mod006_exS = .ok D ∧ D.name = "buf" ∧
      D.ports.map (fun q => (q.name, q.dir, q.place)) =
        [("in", .input, "slots"), ("out", .output, "done")] ∧
      D.chans = [⟨"go", "take"⟩] ∧ "slots" ∈ D.places ∧ "done" ∈ D.places ∧
      D.defs.map (·.core.name) = ["take"]) ∧
    (∃ D, refSubnetBuild refNetBuild mod001_exEmpty = .ok D ∧ D.ports.length = 0 ∧ D.chans = [] ∧
      D.defs.map (·.core.name) = ["take"]) :=
  ⟨⟨_, rfl, rfl, rfl, rfl, by decide, by decide, rfl⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-! ### Builders that post-process the reference -/

section Post

variable [DecidableEq N] [ToString N]

/-- A subnet builder that runs the reference and then changes what it returns with `g`. -/
def postSB (NB : NetBuilder (defsTB N A)) (g : SubnetDef N A → SubnetDef N A) :
    SubnetMake N A := fun S =>
  match refSubnetBuild NB S with
  | .ok D => .ok (g D)
  | .error e => .error e

/-- A post-processing builder succeeds exactly where the reference does, with `g` applied. -/
theorem postSB_eq_ok {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A}
    {S : SubnetIn N A} {D' : SubnetDef N A} (h : postSB NB g S = .ok D') :
    ∃ b, NB S.body = .ok b ∧ D' = g (builtDef S b) := by
  unfold postSB at h
  cases hr : refSubnetBuild NB S with
  | error e => rw [hr] at h; cases h
  | ok D =>
    rw [hr] at h; cases h
    obtain ⟨b, hb, rfl⟩ := refSubnetBuild_eq_ok hr
    exact ⟨b, hb, rfl⟩

/-- Line 1 for a post-processing builder that keeps the ports. -/
theorem post_line1 {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A}
    (hg : ∀ D, (g D).ports = D.ports) : mod001_line1 (postSB NB g) := fun S D h q => by
  obtain ⟨b, -, rfl⟩ := postSB_eq_ok h; rw [hg]; exact Iff.rfl

/-- Line 2 for a post-processing builder that keeps the channels. -/
theorem post_line2 {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A}
    (hg : ∀ D, (g D).chans = D.chans) : mod001_line2 (postSB NB g) := fun S D h c => by
  obtain ⟨b, -, rfl⟩ := postSB_eq_ok h; rw [hg]; exact Iff.rfl

/-- Line 3 for a post-processing builder that keeps the body. -/
theorem post_line3 {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A}
    (hg : ∀ D, (g D).places = D.places ∧ (g D).terminals = D.terminals ∧ (g D).defs = D.defs) :
    mod001_line3 NB (postSB NB g) := fun S D b h hb => by
  obtain ⟨b', hb', rfl⟩ := postSB_eq_ok h
  rw [hb] at hb'; cases hb'
  obtain ⟨h1, h2, h3⟩ := hg (builtDef S b)
  rw [h1, h2, h3]
  exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl⟩

/-- Line 4 for a post-processing builder that keeps the name. -/
theorem post_line4 {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A}
    (hg : ∀ D, (g D).name = D.name) : mod001_line4 (postSB NB g) := fun S D h => by
  obtain ⟨b, -, rfl⟩ := postSB_eq_ok h; rw [hg]; rfl

/-- Line 5 holds for every post-processing builder. -/
theorem post_line5 {NB : NetBuilder (defsTB N A)} {g : SubnetDef N A → SubnetDef N A} :
    mod001_line5 NB (postSB NB g) := fun S b hb hp hc =>
  ⟨g (builtDef S b), by simp only [postSB, refSubnetBuild_empty hb hp hc]⟩

end Post

/-! ### A builder that keeps the interface in another order -/

/-- Keep the ports in reverse declaration order (as a hash map may iterate them). -/
def revPorts (D : SubnetDef N A) : SubnetDef N A := { D with ports := D.ports.reverse }

/-- ✓ MOD-001 does not fix the order of the ports. A builder that returns them in reverse order,
as Rust's hash map may, meets it: for `buf` it lists the ports `out`, `in` where the reference
lists `in`, `out`, and both hold the same two ports. -/
@[evidence allows MOD_001]
theorem MOD_001_allows_portOrder :
    MOD_001 refNetBuild (postSB (N := String) (A := Unit) refNetBuild revPorts) ∧
      (∃ D, postSB refNetBuild revPorts mod006_exS = .ok D ∧
        D.ports.map (·.name) = ["out", "in"]) ∧
      (∃ D, refSubnetBuild refNetBuild mod006_exS = .ok D ∧
        D.ports.map (·.name) = ["in", "out"]) := by
  refine ⟨⟨fun S D h q => ?_, post_line2 fun _ => rfl,
    post_line3 fun _ => ⟨rfl, rfl, rfl⟩, post_line4 fun _ => rfl, post_line5⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  obtain ⟨b, -, rfl⟩ := postSB_eq_ok h
  simp [revPorts, builtDef]

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-001 without line 1 (the ports need not be the declared ones). -/
def MOD_001_mutant_anyPorts (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod001_line2 SB ∧ mod001_line3 NB SB ∧ mod001_line4 SB ∧ mod001_line5 NB SB

/-- Mutant reading: MOD-001 without line 2 (the channels need not be the declared ones). -/
def MOD_001_mutant_anyChans (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod001_line1 SB ∧ mod001_line3 NB SB ∧ mod001_line4 SB ∧ mod001_line5 NB SB

/-- Mutant reading: MOD-001 without line 3 (the body need not be the built, unrenamed one). -/
def MOD_001_mutant_anyBody (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod001_line1 SB ∧ mod001_line2 SB ∧ mod001_line4 SB ∧ mod001_line5 NB SB

/-- Mutant reading: MOD-001 without line 4 (the name need not be kept). -/
def MOD_001_mutant_anyName (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod001_line1 SB ∧ mod001_line2 SB ∧ mod001_line3 NB SB ∧ mod001_line5 NB SB

/-- Mutant reading: MOD-001 without line 5 (an empty interface may be refused). -/
def MOD_001_mutant_noEmpty (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod001_line1 SB ∧ mod001_line2 SB ∧ mod001_line3 NB SB ∧ mod001_line4 SB

/-- Store every port as in-out: the direction is forgotten. -/
def forgetDir (D : SubnetDef N A) : SubnetDef N A :=
  { D with ports := D.ports.map fun q => { q with dir := .inout } }

/-- Drop the channels. -/
def dropChans (D : SubnetDef N A) : SubnetDef N A := { D with chans := [] }

/-- Return the body already renamed under the prefix `sub`: places, terminal places and
transitions. -/
def prefixedBody (D : SubnetDef String A) : SubnetDef String A :=
  { D with places := D.places.map (preS "sub"), terminals := D.terminals.map (preS "sub"),
           defs := D.defs.map (CDef.map (preS "sub") (preS "sub")) }

/-- Forget the definition's name. -/
def dropName (D : SubnetDef N A) : SubnetDef N A := { D with name := "" }

/-- A subnet builder that refuses a subnet with no port and no channel and is the reference
otherwise. -/
def rejectEmptySB [DecidableEq N] [ToString N] (NB : NetBuilder (defsTB N A)) : SubnetMake N A :=
  fun S => if S.ports.isEmpty && S.chans.isEmpty then .error "empty interface"
    else refSubnetBuild NB S

/-- The mutant without line 1 is killed by the builder that forgets port directions: it meets every
other line, but builds `buf` with its input port `in` stored as in-out, so the declared port
`in` (input, on `slots`) is not a port of the definition. -/
@[evidence mutant MOD_001]
theorem MOD_001_mutant_anyPorts_killed :
    MOD_001_mutant_anyPorts refNetBuild (postSB (N := String) (A := Unit) refNetBuild forgetDir) ∧
      ¬ MOD_001 refNetBuild (postSB (N := String) (A := Unit) refNetBuild forgetDir) := by
  refine ⟨⟨post_line2 fun _ => rfl, post_line3 fun _ => ⟨rfl, rfl, rfl⟩, post_line4 fun _ => rfl,
    post_line5⟩, fun h => ?_⟩
  have := (h.1 mod006_exS _ rfl ⟨"in", .input, "slots"⟩).2 (by simp [mod006_exS])
  simp [forgetDir, builtDef, mod006_exS] at this

/-- The mutant without line 2 is killed by the builder that drops the channels: it meets every
other line, but builds `buf` without its channel `go`. -/
@[evidence mutant MOD_001]
theorem MOD_001_mutant_anyChans_killed :
    MOD_001_mutant_anyChans refNetBuild (postSB (N := String) (A := Unit) refNetBuild dropChans) ∧
      ¬ MOD_001 refNetBuild (postSB (N := String) (A := Unit) refNetBuild dropChans) := by
  refine ⟨⟨post_line1 fun _ => rfl, post_line3 fun _ => ⟨rfl, rfl, rfl⟩, post_line4 fun _ => rfl,
    post_line5⟩, fun h => ?_⟩
  have := (h.2.1 mod006_exS _ rfl ⟨"go", "take"⟩).2 (by simp [mod006_exS])
  simp [dropChans] at this

/-- The mutant without line 3 is killed by the builder that returns the body already renamed
under `sub`: it meets every other line, but the definition it builds for `buf` holds `sub/slots`
and not the body's place `slots`. -/
@[evidence mutant MOD_001]
theorem MOD_001_mutant_anyBody_killed :
    MOD_001_mutant_anyBody refNetBuild (postSB (A := Unit) refNetBuild prefixedBody) ∧
      ¬ MOD_001 refNetBuild (postSB (A := Unit) refNetBuild prefixedBody) := by
  refine ⟨⟨post_line1 fun _ => rfl, post_line2 fun _ => rfl, post_line4 fun _ => rfl,
    post_line5⟩, fun h => ?_⟩
  have hb : refNetBuild mod006_exS.body = .ok mod006_exS.body.collect :=
    refNetBuild_of_terminals_nil rfl
  have := ((h.2.2.1 mod006_exS _ _ rfl hb).1 "slots").2 (by decide)
  revert this; decide

/-- The mutant without line 4 is killed by the builder that forgets the name: it meets every other
line, but the definition it builds for `buf` is named "" instead of `buf`. -/
@[evidence mutant MOD_001]
theorem MOD_001_mutant_anyName_killed :
    MOD_001_mutant_anyName refNetBuild (postSB (N := String) (A := Unit) refNetBuild dropName) ∧
      ¬ MOD_001 refNetBuild (postSB (N := String) (A := Unit) refNetBuild dropName) := by
  refine ⟨⟨post_line1 fun _ => rfl, post_line2 fun _ => rfl,
    post_line3 fun _ => ⟨rfl, rfl, rfl⟩, post_line5⟩, fun h => ?_⟩
  have := h.2.2.2.1 mod006_exS _ rfl
  revert this; decide

/-- The mutant without line 5 is killed by the builder that refuses an empty interface: it meets
every other line, but refuses `buf` with no port and no channel although its body builds. -/
@[evidence mutant MOD_001]
theorem MOD_001_mutant_noEmpty_killed :
    MOD_001_mutant_noEmpty refNetBuild (rejectEmptySB (N := String) (A := Unit) refNetBuild) ∧
      ¬ MOD_001 refNetBuild (rejectEmptySB (N := String) (A := Unit) refNetBuild) := by
  have R := refSubnetBuild_lines (N := String) (A := Unit) refNetBuild
  have hok : ∀ {S : SubnetIn String Unit} {D}, rejectEmptySB refNetBuild S = .ok D →
      refSubnetBuild refNetBuild S = .ok D := fun {S D} h => by
    unfold rejectEmptySB at h
    split at h
    · cases h
    · exact h
  refine ⟨⟨fun S D h => R.1 S D (hok h), fun S D h => R.2.1 S D (hok h),
    fun S D b h => R.2.2.1 S D b (hok h), fun S D h => R.2.2.2.1 S D (hok h)⟩, fun h => ?_⟩
  obtain ⟨D, hD⟩ := h.2.2.2.2 mod001_exEmpty _ (refNetBuild_of_terminals_nil rfl) rfl rfl
  cases hD

/-! ### A wrong transition order -/

/-- The example body transition `put`: an input arc on `done` and the output place `slots`. -/
def mod001_put : CDef String Unit :=
  { core := ⟨"put", [⟨"done", .one⟩], [], [], []⟩, out := some (.place "slots"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- `buf` with a second transition `put`, added after `take`. -/
def mod001_exTwo : SubnetIn String Unit :=
  { mod006_exS with defs := [mod006_take, mod001_put] }

/-- Keep the transitions in reverse order. -/
def revDefs (D : SubnetDef N A) : SubnetDef N A := { D with defs := D.defs.reverse }

/-- ✗ A builder that keeps the body's transitions in reverse order violates MOD-001 (line 3): for
`buf` with `take` added before `put`, its definition lists `put` first. -/
@[evidence forbids MOD_001]
theorem MOD_001_forbids_revDefs :
    ¬ MOD_001 refNetBuild (postSB (N := String) (A := Unit) refNetBuild revDefs) := by
  intro h
  have hb : refNetBuild mod001_exTwo.body = .ok mod001_exTwo.body.collect :=
    refNetBuild_of_terminals_nil rfl
  have := congrArg (List.map (·.core.name))
    ((h.2.2.1 mod001_exTwo _ _ rfl hb).2.2 (by decide))
  revert this; decide

/-! ### Joint with CORE-040 and MOD-006: a built definition can be instantiated -/

/-- **A built definition's interface sits on its body.** For every net builder that meets CORE-040
and every subnet builder that meets MOD-006 and MOD-001 over it: when the subnet builder builds `S`
as `D` and the transition names of `S` are distinct, the body builds as some `b` whose transitions
are `D`'s definitions, every port of `D` exposes a place of `D`, and every channel of `D` names a
transition of `D`. So for `buf` the port `out` on `done`, a place only the output arc of `take`
names, sits on a place of the definition, and the channel `go` names its transition `take`. -/
theorem mod001_instantiable [DecidableEq N] {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (hc : CORE_040 (defsTB N A) NB) (h6 : MOD_006 NB SB) (h1 : MOD_001 NB SB)
    {S : SubnetIn N A} {D : SubnetDef N A} (hD : SB S = .ok D)
    (hdn : (S.defs.map (·.core.name)).Nodup) :
    ∃ b, NB S.body = .ok b ∧ D.defs.map (·.toTransDef) = b.trans ∧
      (∀ q ∈ D.ports, q.place ∈ D.places) ∧ (∀ c ∈ D.chans, c.trans ∈ D.defs.map (·.core.name)) := by
  cases hb : NB S.body with
  | error e =>
    obtain ⟨msg, hm⟩ := h6.2.2.2.2.1 S e hb
    rw [hD] at hm; cases hm
  | ok b =>
    obtain ⟨hpl, -, hdefs⟩ := h1.2.2.1 S D b hD hb
    have hD' := hdefs hdn
    have htr : b.trans = S.defs.map (·.toTransDef) := hc.1 S.body b hb hdn
    refine ⟨b, rfl, by rw [hD', htr], fun q hq => ?_, fun c hcm => ?_⟩
    · have hqS := (h1.1 S D hD q).1 hq
      refine (hpl _).2 ?_
      refine Classical.byContradiction fun hn => ?_
      obtain ⟨msg, hm⟩ := h6.1 S b hb q hqS hn
      rw [hD] at hm; cases hm
    · have hcS := (h1.2.1 S D hD c).1 hcm
      rw [hD']
      refine Classical.byContradiction fun hn => ?_
      obtain ⟨msg, hm⟩ := h6.2.1 S b hb c hcS (by rw [htr, List.map_map]; exact hn)
      rw [hD] at hm; cases hm

/-- **Every built definition without terminal places can be instantiated.** For every net builder
that meets CORE-040, every subnet builder that meets MOD-006 and MOD-001 over it, and every
instantiation function that meets MOD-010: a definition the subnet builder returns for a
declaration with distinct transition names and no terminal place in its built body is
instantiated under any valid prefix. So `buf`, built by the reference, is instantiated under
`buf1`. -/
theorem mod001_mod010 [DecidableEq N] {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    {Nm : Naming N} {Inst : InstFn N A}
    (hc : CORE_040 (defsTB N A) NB) (h6 : MOD_006 NB SB) (h1 : MOD_001 NB SB)
    (h10 : MOD_010 Nm Inst) {S : SubnetIn N A} {D : SubnetDef N A} (hD : SB S = .ok D)
    (hdn : (S.defs.map (·.core.name)).Nodup) (ht : D.terminals = []) {p : String}
    (hp : ValidPrefix p) : ∃ I, Inst D p = .ok I := by
  obtain ⟨-, -, -, hq, hch⟩ := mod001_instantiable hc h6 h1 hD hdn
  exact h10.2.1 D p hp ht hq hch

end Libpetri.Spec
