import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Spec.Req.MOD_006

set_option linter.missingDocs true

/-!
# MOD-003: Port declaration (`spec/11-modular-composition.md`)

MOD-003 is a behaviour requirement (kind B) over the same two abstract functions as MOD-006: the
net builder `NB` that builds a subnet's body and the subnet builder `SB : SubnetMake N A`, which
turns what the host declared (`SubnetIn`) into a subnet definition or a rejection with a message.
A port (`Port`, `Spec/GlossaryCompose.lean`) is a name, a direction (`Dir`: input, output or
in-out) and the body place it exposes.

The block says three things about ports. Two ports of one name make the build fail. A port on a
place that the built body does not hold makes the build fail. And sharing a place is no reason
to fail: when a subnet definition builds, it still builds with one more port of a new name over
the place of one of its ports, whatever the directions (ruling D35 (a)). No runtime rejects two
ports over one place, whether or not their directions agree.

Lines 1 and 2 are MOD-006's lines 3 and 1, and line 3 follows from MOD-006 as a whole: every
subnet builder that meets MOD-006 meets MOD-003 (`mod003_of_mod006`). So the witness is again the
reference subnet builder `refSubnetBuild NB` of `Spec/Req/MOD_006.lean`, and the block holds of
it for every net builder. Wrong builders are killed, one per line; line 3 kills a builder that
rejects two ports of one direction over one place.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## MOD-003: Port Declaration (name + direction + place) -/

requirement MOD_003
  id "MOD-003"
  title "Port Declaration (name + direction + place)"
  kind B
  scope "every subnet builder"
  source verbatim "spec/11-modular-composition.md"
  quote "*If* two ports of one interface have the same name, *then* building the subnet definition *shall* fail."
        "*If* the net builder builds the body and a port exposes a place that is not a place of the built body, *then* building the subnet definition *shall* fail."
        "*When* building a subnet definition succeeds, building it with one more port, whose name no port of the interface has and which exposes the place of one of its ports, *shall* also succeed, whatever the directions of the two ports."
  reading "For every net builder NB of subnet bodies and every subnet builder SB:"
          "if two ports of S have the same name, SB fails on S;"
          "if NB builds the body of S as the net b and some port of S exposes a place that is not a place of b, SB fails on S;"
          "if SB builds S, q is a port of S, n is the name of no port of S and d is any direction, SB builds S with the port (n, d, place of q) appended to its ports."
  assumes "A subnet builder (SubnetMake) and the body net builder NB are those of MOD-006 (Spec/Req/MOD_006.lean): the build call of one implementation's subnet-definition builder, read as a function from what the host declared to a subnet definition or a rejection with a message, and the net builder that builds the body first (SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs, SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java, SubnetDefBuilder.build in typescript/src/core/subnet-def.ts). Line 1 is MOD-006's line 3 and line 2 is MOD-006's line 1, quoted here because the markdown states them under the port declaration too; which offender a failure names is MOD-006's line 7."
          "Ruling D35 (a): two distinct ports may expose one body place, whatever their directions, as in every runtime (the port loops of the subnet builders' build in rust/libpetri-core/src/subnet_def.rs, java/src/main/java/org/libpetri/core/SubnetDef.java and typescript/src/core/subnet-def.ts check only the port name and the place). Line 3 states the permission as acceptance: adding a port of a new name over the place of an existing port never turns a successful build into a failure. It is relative and appends the new port at the end of the ports; the quote names no position. On its own the block therefore lets a builder reject every subnet that has a port (line 3 is then never triggered); the absolute 'they build' of AC5 and of the MAY sentence 'Two distinct ports MAY expose the same body place', and the insertion of the new port at any other position, are MOD-006 line 6, from which line 3 follows (mod003_of_mod006). The prose sentence 'When two ports expose one body place, a caller binds both to one caller place' is MOD-020's coherent-call precondition (mod020_coherent in Spec/Req/MOD_020.lean): MOD-020 states its binding lines on coherent calls only. Which binding a composition keeps when the two ports are bound to two different caller places is not defined (MOD-020); Rust and Java keep one binding in the iteration order of the caller's map (compose_internal in rust/libpetri-core/src/petri_net.rs, composeInternal in java/src/main/java/org/libpetri/core/PetriNet.java). D35 (b), rejecting a shared place at subnet build, is a later runtime change that would replace line 3."
          "Line 2 compares a port's place with the places of the built body by equality on the place type N, as MOD-006 line 1 does (CORE-002: by name in TypeScript, Rust and Python, by name and token type in Java, body_places.contains in rust/libpetri-core/src/subnet_def.rs, bodyPlaces.contains in java/src/main/java/org/libpetri/core/SubnetDef.java, bodyPlaces.has in typescript/src/core/subnet-def.ts). So a port over a place of name p and token type Integer, on a body that holds p of token type String, is rejected in Java only. The prose MUST sentence 'The exposed place MUST be a place of the subnet's body' is line 2 (and AC4) when the body builds; when it does not, MOD-006 line 5 makes the build fail. That a port on any place of the built body is accepted, including a place only an arc of a body transition names, is MOD-006 line 6: a builder that checks a port's place against the declared places instead of the built body meets MOD-003 and violates MOD-006 (mod003_declPlaces)."
          "Line 1 reads 'unique within the interface' over the ports alone: port names and channel names are two namespaces (MOD-006). Java refuses a blank port name when the port value is constructed (the compact constructors of Interface.Port.Input, Output and InOut, java/src/main/java/org/libpetri/core/Interface.java), before any subnet builder sees it, so line 3's new name n ranges over the names Java can construct; TypeScript and Rust accept a blank name. On the interface-builder route of MOD-014 (fromNet) a duplicate port name is rejected even earlier, at the port() call (rust/libpetri-core/src/interface.rs, java/src/main/java/org/libpetri/core/Interface.java, typescript/src/core/interface.ts), which meets AC2's 'at build' since it is not later."
          "AC1 (a port can be declared with name, direction and a body place) is the Port record of Spec/GlossaryCompose.lean (name, dir, place; Dir has exactly the three directions input, output and in-out); that a built subnet definition keeps every declared port with its name, direction and place is MOD-001's line. AC2 (the port name is unique, duplicates rejected at build) is line 1, stated of the subnet builder itself. AC3 (the exposed place's token type is preserved in the port's typed handle) is MOD_011_typed's, scoped by ruling D36 (a) to the implementations that keep a run-time token type for each port, Java and Rust; its compile-time reading is withdrawn (MOD-011, ruling D36 (a)). TypeScript's port<T>(name) takes T as an annotation it does not check (Instance.port in typescript/src/core/instance.ts) and Python's lookup takes no type, so for them AC3 is out of scope by the same ruling and no block states it. AC4 (a port whose place is not in the body is rejected at build) is line 2. AC5 (two ports of different names over one body place build, whatever their directions) is line 3 relative to a build, and MOD-006 line 6 for the build itself, with MOD_003_nonvacuous as the worked case."
  signoff "2026-11-13 a8ba026eaf2a647c ai"
  statement : ∀ {N A : Type}, NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
    fun {N A} NB SB =>
      (∀ S : SubnetIn N A, ¬ (S.ports.map (·.name)).Nodup → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q ∈ S.ports, ∀ (n : String) (d : Dir),
        n ∉ S.ports.map (·.name) →
        ∃ D', SB { S with ports := S.ports ++ [⟨n, d, q.place⟩] } = .ok D')

/- The pinned readable form of MOD-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_003 : {N A : Type} → NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
fun {N A} NB SB =>
  (∀ (S : SubnetIn N A), ¬(List.map (fun x => x.name) S.ports).Nodup → ∃ msg, SB S = Except.error msg) ∧
    (∀ (S : SubnetIn N A) (b : BuiltNet N A),
        NB S.body = Except.ok b → ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = Except.error msg) ∧
      ∀ (S : SubnetIn N A) (D : SubnetDef N A),
        SB S = Except.ok D →
          ∀ q ∈ S.ports,
            ∀ (n : String) (d : Dir),
              n ∉ List.map (fun x => x.name) S.ports →
                ∃ D',
                  SB
                      { name := S.name, places := S.places, defs := S.defs, terminals := S.terminals,
                        ports := S.ports ++ [{ name := n, dir := d, place := q.place }], chans := S.chans } =
                    Except.ok D'
-/
#guard_msgs in #print MOD_003

/-! ### The three lines, named (for the mutants) -/

section Lines

/-- The subnet input `S` with one more port, named `n`, of direction `d`, over the place `p`,
appended after its ports. -/
def SubnetIn.addPort (S : SubnetIn N A) (n : String) (d : Dir) (p : N) : SubnetIn N A :=
  { S with ports := S.ports ++ [⟨n, d, p⟩] }

/-- Adding a port leaves the body alone. -/
theorem SubnetIn.addPort_body (S : SubnetIn N A) (n : String) (d : Dir) (p : N) :
    (S.addPort n d p).body = S.body := rfl

/-- Line 1 of MOD-003: two ports of one name fail. -/
def mod003_line1 (SB : SubnetMake N A) : Prop :=
  ∀ S : SubnetIn N A, ¬ (S.ports.map (·.name)).Nodup → ∃ msg, SB S = .error msg

/-- Line 2 of MOD-003: a port on a place the built body does not hold fails. -/
def mod003_line2 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    ∀ q ∈ S.ports, q.place ∉ b.places → ∃ msg, SB S = .error msg

/-- Line 3 of MOD-003: a subnet that builds still builds with one more port of a new name over
the place of one of its ports, in any direction. -/
def mod003_line3 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q ∈ S.ports, ∀ (n : String) (d : Dir),
    n ∉ S.ports.map (·.name) → ∃ D', SB (S.addPort n d q.place) = .ok D'

/-- MOD-003 is its three lines. -/
theorem mod003_iff (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) :
    MOD_003 NB SB ↔ mod003_line1 SB ∧ mod003_line2 NB SB ∧ mod003_line3 SB :=
  Iff.rfl

end Lines

/-- Appending a port of a new name keeps the port names distinct. -/
theorem nodup_addPort {S : SubnetIn N A} {n : String} {d : Dir} {p : N}
    (hpn : (S.ports.map (·.name)).Nodup) (hn : n ∉ S.ports.map (·.name)) :
    ((S.addPort n d p).ports.map (·.name)).Nodup := by
  simp only [SubnetIn.addPort, List.map_append, List.map_cons, List.map_nil]
  exact List.nodup_append.2 ⟨hpn, List.nodup_singleton _,
    fun x hx y hy => by simp only [List.mem_singleton] at hy; subst hy; exact fun he => hn (he ▸ hx)⟩

/-- Appending a port over the place of a port on a body place keeps every port on a body
place. -/
theorem places_addPort {S : SubnetIn N A} {b : BuiltNet N A} {q : Port N} {n : String} {d : Dir}
    (hp : ∀ r ∈ S.ports, r.place ∈ b.places) (hq : q ∈ S.ports) :
    ∀ r ∈ (S.addPort n d q.place).ports, r.place ∈ b.places := by
  intro r hr
  simp only [SubnetIn.addPort, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact hp r hr
  · exact hp q hq

/-! ### Every builder that meets MOD-006 meets MOD-003 -/

/-- **MOD-006 implies MOD-003.** Lines 1 and 2 are MOD-006's lines 3 and 1. For line 3: a subnet
that builds has a body that builds (MOD-006 line 5), ports on body places with distinct names
(lines 1 and 3) and channels on body transitions with distinct names (lines 2 and 4). A port of a
new name over the place of one of its ports keeps all of that, so MOD-006 line 6 builds the
larger subnet. For example, `buf` with the port `in` on `slots` builds, so `buf` with a second
port `again` on `slots` builds too. -/
theorem mod003_of_mod006 {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (h : MOD_006 NB SB) : MOD_003 NB SB := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  refine ⟨h3, h1, ?_⟩
  intro S D hS q hq n d hn
  have nf : ∀ {P : Prop}, (P → ∃ msg, SB S = .error msg) → ¬ P := fun hP hp => by
    obtain ⟨m, hm⟩ := hP hp; rw [hS] at hm; cases hm
  cases hb : NB S.body with
  | error e => exact absurd hb (nf (h5 S e))
  | ok b =>
    have hp : ∀ r ∈ S.ports, r.place ∈ b.places := fun r hr =>
      Classical.byContradiction (nf (h1 S b hb r hr))
    have hc : ∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name) := fun c hc =>
      Classical.byContradiction (nf (h2 S b hb c hc))
    have hpn : (S.ports.map (·.name)).Nodup := Classical.byContradiction (nf (h3 S))
    have hcn : (S.chans.map (·.name)).Nodup := Classical.byContradiction (nf (h4 S))
    exact h6 (S.addPort n d q.place) b hb (places_addPort hp hq) hc (nodup_addPort hpn hn) hcn

/-! ### Line lemmas for every builder of the `subnetVia` shape -/

section Via

variable {NB : NetBuilder (defsTB N A)} {cp cc : SubnetIn N A → BuiltNet N A → Option String}

/-- A `subnetVia` builder that builds `S` built its body and passed both checks. -/
theorem subnetVia_ok_inv {S : SubnetIn N A} {D : SubnetDef N A}
    (h : subnetVia NB cp cc S = .ok D) :
    ∃ b, NB S.body = .ok b ∧ cp S b = none ∧ cc S b = none := by
  cases hb : NB S.body with
  | error e => simp [subnetVia, hb] at h
  | ok b =>
    cases hp : cp S b with
    | some m => simp [subnetVia, hb, hp] at h
    | none =>
      cases hc : cc S b with
      | some m => simp [subnetVia, hb, hp, hc] at h
      | none => exact ⟨b, rfl, hp, hc⟩

/-- Line 3 for a `subnetVia` builder whose port check, once passed, still passes with one more
port of a new name over the place of one of the ports, and whose channel check does not read the
ports. -/
theorem via_share
    (hP : ∀ (S : SubnetIn N A) b q n d, cp S b = none → q ∈ S.ports →
      n ∉ S.ports.map (·.name) → cp (S.addPort n d q.place) b = none)
    (hC : ∀ (S : SubnetIn N A) b n d p, cc (S.addPort n d p) b = cc S b) :
    mod003_line3 (subnetVia NB cp cc) := by
  intro S D hS q hq n d hn
  obtain ⟨b, hb, hp, hc⟩ := subnetVia_ok_inv hS
  exact ⟨_, subnetVia_ok (S := S.addPort n d q.place) hb (hP S b q n d hp hq hn)
    (by rw [hC]; exact hc)⟩

end Via

/-- The reference channel check does not read the ports. -/
theorem refChanCheck_addPort (S : SubnetIn N A) (b : BuiltNet N A) (n : String)
    (d : Dir) (p : N) : refChanCheck (S.addPort n d p) b = refChanCheck S b := rfl

/-! ### The reference -/

/-- ✓ The reference subnet builder satisfies MOD-003 for every net builder: it rejects two ports
of one name and a port on a place the built body does not hold, and a subnet it builds still
builds with one more port of a new name over a place a port already exposes. -/
@[evidence holds MOD_003]
theorem MOD_003_reference {N A : Type} [DecidableEq N] [ToString N]
    (NB : NetBuilder (defsTB N A)) : MOD_003 NB (refSubnetBuild NB) :=
  mod003_of_mod006 (MOD_006_reference NB)

/-! ### A port on an arc-only place: MOD-006's matter -/

section DeclPlaces

/-- A port check that compares a port's place with the places the host declared, not with the
places of the built body (a slip that reads the declaration before the body is built). -/
def mod003_declPortCheck (S : SubnetIn String Unit) (_ : BuiltNet String Unit) : Option String :=
  checkList (·.name) (fun q : Port String => q.place ∈ S.places)
    (dupPortMsg S.name) (portPlaceMsg S.name) [] S.ports

/-- `buf` with the single output port `out` on `done`, a place the body holds only because the
output arc of `take` names it. -/
def mod003_exOut : SubnetIn String Unit := { mod006_exS with ports := [⟨"out", .output, "done"⟩] }

/-- **A port on an arc-only place is MOD-006's matter.** The builder that checks ports against
the declared places rejects `buf` with its port `out` on `done`, which the reference builds; it
still rejects two ports of one name and a port on a place the built body does not hold, so the
lines of MOD-003, which state failures and a relative acceptance, do not catch it. MOD-006 line 6
does. -/
theorem mod003_declPlaces :
    MOD_003 refNetBuild (subnetVia refNetBuild mod003_declPortCheck refChanCheck) ∧
    (∃ D, refSubnetBuild refNetBuild mod003_exOut = .ok D) ∧
    (∃ m, subnetVia refNetBuild mod003_declPortCheck refChanCheck mod003_exOut = .error m) ∧
    ¬ MOD_006 refNetBuild (subnetVia refNetBuild mod003_declPortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, mod003_declPortCheck S b = none ↔
      (∀ q ∈ S.ports, q.place ∈ S.places) ∧ (S.ports.map (·.name)).Nodup := fun S b => by
    unfold mod003_declPortCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line3 fun S b h => ((hP S b).1 h).2, fun S b hb q hq hn => ?_, ?_⟩,
    ⟨_, rfl⟩, ⟨_, rfl⟩, fun h => ?_⟩
  · have hb' := (refNetBuild_eq_ok_iff.1 hb).2
    cases hcp : mod003_declPortCheck S b with
    | some m => exact ⟨m, by simp [subnetVia, hb, hcp]⟩
    | none =>
      exfalso; apply hn; subst hb'
      exact mem_collect_places.2 (.inl (((hP S _).1 hcp).1 q hq))
  · exact via_share (fun S b q n d h hq hn => (hP _ b).2
      ⟨fun r hr => by
        simp only [SubnetIn.addPort, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact ((hP S b).1 h).1 r hr
        · exact ((hP S b).1 h).1 q hq,
       nodup_addPort ((hP S b).1 h).2 hn⟩) refChanCheck_addPort
  obtain ⟨D, hD⟩ := h.2.2.2.2.2.1 mod003_exOut _ (refNetBuild_of_terminals_nil rfl)
    (by decide) (by decide) (by decide) (by decide)
  have : subnetVia refNetBuild mod003_declPortCheck refChanCheck mod003_exOut =
      .error (portPlaceMsg "buf" (⟨"out", .output, "done"⟩ : Port String)) := rfl
  rw [this] at hD; cases hD

end DeclPlaces

/-! ### Example -/

/-- The example subnet `buf` (MOD-006's body: the place `slots`, the transition `take` from
`slots` to `done`, the channel `go` on `take`) with the one port `in`, an input on `slots`. -/
def mod003_exS : SubnetIn String Unit :=
  { mod006_exS with ports := [⟨"in", .input, "slots"⟩] }

/-- `buf` with a second input port `again` on `slots`. -/
def mod003_exSame : SubnetIn String Unit := mod003_exS.addPort "again" .input "slots"

/-- `buf` with a second port `peek`, an output, on `slots`. -/
def mod003_exOther : SubnetIn String Unit := mod003_exS.addPort "peek" .output "slots"

/-- `buf` with a second input port also named `in`, on `done`. -/
def mod003_exDup : SubnetIn String Unit := mod003_exS.addPort "in" .input "done"

/-- `buf` with its port `in` on the place `nowhere`, which the body does not hold. -/
def mod003_exBad : SubnetIn String Unit := { mod003_exS with ports := [⟨"in", .input, "nowhere"⟩] }

/-- ✓ Every line of MOD-003 is exercised by the reference over the reference net builder. The
subnet `buf` with the input port `in` on `slots` builds. A second input port `again` on `slots`
builds too, as does a second port `peek` on `slots` that is an output (line 3: two ports may
share a place, whatever their directions). A second port also named `in` fails with "Subnet
'buf': duplicate port name 'in'" (line 1). The port `in` on `nowhere` fails with "Subnet 'buf':
port 'in' references place 'nowhere' which is not in the body" (line 2). -/
@[evidence nonvacuous MOD_003]
theorem MOD_003_nonvacuous :
    (∃ D, refSubnetBuild refNetBuild mod003_exS = .ok D) ∧
    (∃ D, refSubnetBuild refNetBuild mod003_exSame = .ok D ∧ D.ports.length = 2) ∧
    (∃ D, refSubnetBuild refNetBuild mod003_exOther = .ok D ∧ D.ports.length = 2) ∧
    refSubnetBuild refNetBuild mod003_exDup =
      .error (dupPortMsg "buf" (⟨"in", .input, "done"⟩ : Port String)) ∧
    refSubnetBuild refNetBuild mod003_exBad =
      .error (portPlaceMsg "buf" (⟨"in", .input, "nowhere"⟩ : Port String)) := by
  refine ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl⟩

/-! ### Wrong subnet builders -/

/-- ✗ A builder that accepts everything and leaves the checks to instantiation violates MOD-003
(line 2): it builds `buf` with its port `in` on the place `nowhere`, which the body does not
hold. -/
@[evidence forbids MOD_003]
theorem MOD_003_forbids_lazy : ¬ MOD_003 refNetBuild (lazySB (N := String) (A := Unit)) := by
  intro h
  obtain ⟨msg, hm⟩ := h.2.1 mod003_exBad _ (refNetBuild_of_terminals_nil rfl)
    ⟨"in", .input, "nowhere"⟩ (by simp [mod003_exBad]) (by decide)
  cases hm

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-003 without line 1 (no duplicate-name check). -/
def MOD_003_mutant_noDupName (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod003_line2 NB SB ∧ mod003_line3 SB

/-- Mutant reading: MOD-003 without line 2 (no place check). -/
def MOD_003_mutant_noPlace (_NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod003_line1 SB ∧ mod003_line3 SB

/-- Mutant reading: MOD-003 without line 3 (a shared place may be rejected). -/
def MOD_003_mutant_noShare (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod003_line1 SB ∧ mod003_line2 NB SB

section MutantModels

variable [DecidableEq N] [ToString N]

/-- Two ports of the list have one direction and one place. -/
def sameDirClash (ps : List (Port N)) : Bool :=
  ps.any fun q => decide (2 ≤ (ps.filter fun r => r.dir == q.dir && decide (r.place = q.place)).length)

/-- The message of the same-direction check. -/
def sameDirMsg (sn : String) : String :=
  "Subnet '" ++ sn ++ "': two ports of one direction expose one place"

/-- The reference port check, then a same-direction check: two ports of one direction over one
place fail. -/
def sameDirPortCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  match refPortCheck S b with
  | some m => some m
  | none => if sameDirClash S.ports then some (sameDirMsg S.name) else none

/-- The same-direction port check passes only where the reference port check passes. -/
theorem sameDirPortCheck_none {S : SubnetIn N A} {b : BuiltNet N A}
    (h : sameDirPortCheck S b = none) : refPortCheck S b = none := by
  unfold sameDirPortCheck at h
  cases hr : refPortCheck S b with
  | none => rfl
  | some m => rw [hr] at h; cases h

end MutantModels

/-- The mutant without line 1 is killed by the builder without the duplicate-name test (MOD-006's
`noDupPortCheck`): it rejects a port on a place the body does not hold and accepts a shared
place, but builds `buf` with two ports named `in`. -/
@[evidence mutant MOD_003]
theorem MOD_003_mutant_noDupName_killed :
    MOD_003_mutant_noDupName refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noDupPortCheck refChanCheck) ∧
      ¬ MOD_003 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noDupPortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noDupPortCheck S b = none ↔
      ∀ q ∈ S.ports, q.place ∈ b.places := fun S b => by
    unfold noDupPortCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via_line1 fun S b h => (hP S b).1 h,
    via_share (fun S b q n d h hq _ => (hP _ b).2 (places_addPort ((hP S b).1 h) hq))
      refChanCheck_addPort⟩, fun h => ?_⟩
  obtain ⟨msg, hm⟩ := h.1 mod003_exDup (by decide)
  have : subnetVia refNetBuild noDupPortCheck refChanCheck mod003_exDup = .ok _ := rfl
  rw [this] at hm; cases hm

/-- The mutant without line 2 is killed by the builder without the place test (MOD-006's
`noPlacePortCheck`): it rejects two ports of one name and accepts a shared place, but builds
`buf` with its port `in` on `nowhere`. -/
@[evidence mutant MOD_003]
theorem MOD_003_mutant_noPlace_killed :
    MOD_003_mutant_noPlace refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noPlacePortCheck refChanCheck) ∧
      ¬ MOD_003 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild noPlacePortCheck refChanCheck) := by
  have hP : ∀ (S : SubnetIn String Unit) b, noPlacePortCheck S b = none ↔
      (S.ports.map (·.name)).Nodup := fun S b => by
    unfold noPlacePortCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line3 fun S b h => (hP S b).1 h,
    via_share (fun S b q n d h _ hn => (hP _ b).2 (nodup_addPort ((hP S b).1 h) hn))
      refChanCheck_addPort⟩, fun h => ?_⟩
  obtain ⟨msg, hm⟩ := h.2.1 mod003_exBad _ (refNetBuild_of_terminals_nil rfl)
    ⟨"in", .input, "nowhere"⟩ (by simp [mod003_exBad]) (by decide)
  have : subnetVia refNetBuild noPlacePortCheck refChanCheck mod003_exBad = .ok _ := rfl
  rw [this] at hm; cases hm

/-- The mutant without line 3 is killed by a builder that also rejects two ports of one direction
over one place: it rejects two ports of one name and a port on a place the body does not hold, but it
also rejects `buf` with a second input port `again` on `slots`, next to the input port `in` on
`slots`, though `buf` with `in` alone builds. No runtime makes that check. -/
@[evidence mutant MOD_003]
theorem MOD_003_mutant_noShare_killed :
    MOD_003_mutant_noShare refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild sameDirPortCheck refChanCheck) ∧
      ¬ MOD_003 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild sameDirPortCheck refChanCheck) := by
  refine ⟨⟨via_line3 fun S b h => ((refPortCheck_none S b).1 (sameDirPortCheck_none h)).2,
    via_line1 fun S b h => ((refPortCheck_none S b).1 (sameDirPortCheck_none h)).1⟩, fun h => ?_⟩
  obtain ⟨D', hD'⟩ := h.2.2 mod003_exS _ rfl ⟨"in", .input, "slots"⟩ (by simp [mod003_exS])
    "again" .input (by decide)
  change subnetVia refNetBuild sameDirPortCheck refChanCheck
    (mod003_exS.addPort "again" .input "slots") = .ok D' at hD'
  have : subnetVia refNetBuild sameDirPortCheck refChanCheck
      (mod003_exS.addPort "again" .input "slots") = .error (sameDirMsg "buf") := rfl
  rw [this] at hD'; cases hD'

end Libpetri.Spec
