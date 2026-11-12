import Libpetri.Spec.Req.MOD_006

set_option linter.missingDocs true

/-!
# MOD-005: Channel declaration (`spec/11-modular-composition.md`)

MOD-005 is a behaviour requirement (kind B) over the same two abstract functions as MOD-006: the
net builder `NB` that builds a subnet's body and the subnet builder `SB : SubnetMake N A`. It
speaks of channels only: two channels of one name fail, a channel on a transition name the built
body does not hold fails, and adding well-formed channels to a subnet that builds without them
keeps it building. A well-formed channel here exposes a transition of the built body, carries a
name no other channel carries, and carries no port's name: whether a port and a channel may share
a name is left to the implementation by item 1 of MOD-005 (MOD-006 then fixes two namespaces for
subnet definitions).

The witness is MOD-006's reference subnet builder `refSubnetBuild NB`. Every subnet builder that
meets MOD-006 meets MOD-005 (`mod005_of_mod006`), so the block holds of the reference for every
net builder. Wrong builders are killed, one per line. A builder with one shared namespace for
ports and channels meets MOD-005 and violates MOD-006 (`MOD_005_allows_sharedNamespace`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-- The subnet input `S` with its channels removed: the same name, body and ports, no channel. -/
def SubnetIn.withoutChans (S : SubnetIn N A) : SubnetIn N A := { S with chans := [] }

/-! ## MOD-005: Channel Declaration -/

requirement MOD_005
  id "MOD-005"
  title "Channel Declaration (interface transitions for synchronous fusion)"
  kind B
  scope "every subnet builder"
  source verbatim "spec/11-modular-composition.md"
  quote "*If* two channels of the interface have the same name, *then* building the subnet definition *shall* fail."
        "*If* a channel of the interface exposes a transition whose name is not the name of a transition of the built body, *then* building the subnet definition *shall* fail."
        "*When* the net builder builds the body, the subnet definition builds without its channels, every channel exposes a transition of the built body, no two channels have the same name, and no channel has the name of a port, building the subnet definition with its channels *shall* succeed."
  reading "For every net builder NB of subnet bodies and every subnet builder SB:"
          "if two channels of S have the same name, SB fails on S;"
          "if NB builds the body of S as the net b and some channel of S names a transition that is not the name of a transition of b, SB fails on S;"
          "if NB builds the body of S as b, SB succeeds on S without its channels, every channel of S names a transition of b, the channel names of S are pairwise distinct and no channel of S has the name of a port of S, then SB succeeds on S."
  assumes "The subnet builder SB (SubnetMake) and the body net builder NB are MOD-006's: SB is the build call of one implementation's subnet-definition builder, read as a function from what the host declared (SubnetIn: name, declared places, transition definitions, declared terminal places, ports, channels) to a subnet definition or a rejection with a message (a panic or an exception, read as .error msg); NB is a parameter typed as a CORE-040 net builder over defsTB, and the holds theorem holds for every NB. Every runtime builds the body first and checks the channels against the built net after the ports (rust/libpetri-core/src/subnet_def.rs:406-423, java/src/main/java/org/libpetri/core/SubnetDef.java:645-658, typescript/src/core/subnet-def.ts:563-575)."
          "Line 1 is AC2 and the channel half of item 1 ('A name unique within the interface'); it is MOD-006 line 4. The three runtimes also reject a second channel of one name when an interface is assembled by hand for fromNet (MOD-014), at the channel() call itself (rust/libpetri-core/src/interface.rs:191-194, java/src/main/java/org/libpetri/core/Interface.java:205-210, typescript/src/core/interface.ts:134-140), which is earlier than the subnet build and meets AC4's 'at build' as well."
          "Line 2 is AC4 and item 2 read under rulings D10 and D23 and the R-MA3 (a) reading of the mod-a map, as in MOD-006 line 2: the model's channel carries the name of the transition it exposes, and a channel whose transition's name is the name of no body transition fails in every runtime. Rust and Python store and compare names (rust/libpetri-core/src/interface.rs:75-80, rust/libpetri-core/src/subnet_def.rs:415); Java and TypeScript compare transition objects (java/src/main/java/org/libpetri/core/SubnetDef.java:652, typescript/src/core/subnet-def.ts:570), so a channel over a second transition object that has the name of a body transition is rejected there and accepted in Rust. That case is implementation-defined in the markdown and outside the block: under the unique-names assumption of D10 and D23 two transitions of one name are one transition (RD-10 in spec/runtime-defects.md records that no builder checks names)."
          "Line 3 is the acceptance line for channels (skeptic correction S2 of the composition design), and the behaviour half of AC1 ('A channel can be declared with a name and a body transition'): channels that meet lines 1 and 2 add no reason to reject. It is relative to the same subnet without its channels, so that the ports and the body stay MOD-006's matter; a builder that rejects every subnet therefore meets this block, and MOD-006 line 6 rules it out. Every builder that meets MOD-006 meets line 3 (mod005_of_mod006)."
          "Item 1 leaves to the implementation whether port names and channel names share one namespace, and asks that a collision be rejected when they do. Line 3 therefore asks nothing when a channel has the name of a port, and a builder with one shared namespace meets the block (MOD_005_allows_sharedNamespace). No runtime shares the namespace: each keeps two maps or lists (rust/libpetri-core/src/interface.rs:105-106 and :151-152, java/src/main/java/org/libpetri/core/Interface.java:178-179, typescript/src/core/interface.ts:103-104), and MOD-006's markdown fixes two namespaces for subnet definitions, so that MOD-006 line 6 rejects the shared-namespace builder. The conditional MUST of item 1 has no case in libpetri and is not a line."
          "AC1's existence half (an implementation offers a way to declare a channel with a name and a body transition) is an offer clause, not a safety line: every runtime offers it (rust/libpetri-core/src/subnet_def.rs:366, java/src/main/java/org/libpetri/core/SubnetDef.java:617, typescript/src/core/subnet-def.ts:532), and MOD_005_nonvacuous builds a subnet with a declared channel. That the built definition keeps the declared channels is MOD-001's line. AC3 (the exposed transition's identity is preserved through the channel handle) is MOD-011's line: the handle of channel n of an instance under prefix p names the renamed transition p/x. The paragraph 'A channel MAY be bound at composition time' is MOD-020's and MOD-021's (binding and the merged transition). Java refuses a blank channel name when the channel value is constructed (java/src/main/java/org/libpetri/core/Interface.java:167), before any subnet builder sees it; TypeScript and Rust accept a blank name."
          "Error messages are MOD-006 line 7's matter; this block asks only that the build fail or succeed. The test derivation's first half (the handle resolves to the renamed transition) is MOD-011's; its second half (two channels of one name are rejected) is line 1."
  signoff "pending"
  statement : ∀ {N A : Type}, NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
    fun {N A} NB SB =>
      (∀ S : SubnetIn N A, ¬ (S.chans.map (·.name)).Nodup → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        ∀ c ∈ S.chans, c.trans ∉ b.trans.map (·.core.name) → ∃ msg, SB S = .error msg) ∧
      (∀ (S : SubnetIn N A) b, NB S.body = .ok b →
        (∃ D, SB S.withoutChans = .ok D) →
        (∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name)) →
        (S.chans.map (·.name)).Nodup →
        (∀ c ∈ S.chans, c.name ∉ S.ports.map (·.name)) → ∃ D, SB S = .ok D)

/- The pinned readable form of MOD-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_005 : {N A : Type} → NetBuilder (defsTB N A) → SubnetMake N A → Prop :=
fun {N A} NB SB =>
  (∀ (S : SubnetIn N A), ¬(List.map (fun x => x.name) S.chans).Nodup → ∃ msg, SB S = Except.error msg) ∧
    (∀ (S : SubnetIn N A) (b : BuiltNet N A),
        NB S.body = Except.ok b →
          ∀ c ∈ S.chans, c.trans ∉ List.map (fun x => x.core.name) b.trans → ∃ msg, SB S = Except.error msg) ∧
      ∀ (S : SubnetIn N A) (b : BuiltNet N A),
        NB S.body = Except.ok b →
          (∃ D, SB S.withoutChans = Except.ok D) →
            (∀ c ∈ S.chans, c.trans ∈ List.map (fun x => x.core.name) b.trans) →
              (List.map (fun x => x.name) S.chans).Nodup →
                (∀ c ∈ S.chans, c.name ∉ List.map (fun x => x.name) S.ports) → ∃ D, SB S = Except.ok D
-/
#guard_msgs in #print MOD_005

/-! ### The three lines, named (for the mutants) -/

section Lines

/-- Line 1 of MOD-005: two channels of one name fail. -/
def mod005_line1 (SB : SubnetMake N A) : Prop :=
  ∀ S : SubnetIn N A, ¬ (S.chans.map (·.name)).Nodup → ∃ msg, SB S = .error msg

/-- Line 2 of MOD-005: a channel on a transition name the built body does not hold fails. -/
def mod005_line2 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    ∀ c ∈ S.chans, c.trans ∉ b.trans.map (·.core.name) → ∃ msg, SB S = .error msg

/-- Line 3 of MOD-005: well-formed channels added to a subnet that builds keep it building. -/
def mod005_line3 (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) b, NB S.body = .ok b →
    (∃ D, SB S.withoutChans = .ok D) →
    (∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name)) →
    (S.chans.map (·.name)).Nodup →
    (∀ c ∈ S.chans, c.name ∉ S.ports.map (·.name)) → ∃ D, SB S = .ok D

/-- MOD-005 is its three lines. -/
theorem mod005_iff (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) :
    MOD_005 NB SB ↔ mod005_line1 SB ∧ mod005_line2 NB SB ∧ mod005_line3 NB SB :=
  Iff.rfl

end Lines

/-! ### MOD-006 implies MOD-005 -/

/-- **Every subnet builder that meets MOD-006 meets MOD-005.** Lines 1 and 2 are MOD-006's lines 4
and 2. For line 3: the subnet without its channels builds, so its ports sit on body places and
carry distinct names (otherwise MOD-006's lines 1 and 3 would make it fail, and removing the
channels changes neither the body nor the ports); with the channels well formed, MOD-006's line 6
makes the subnet with its channels build. -/
theorem mod005_of_mod006 {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (h : MOD_006 NB SB) : MOD_005 NB SB := by
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := h
  refine ⟨h4, h2, fun S b hb ⟨D, hD⟩ hc hcn _ => h6 S b hb ?_ hc ?_ hcn⟩
  · intro q hq
    by_contra hn
    obtain ⟨msg, hm⟩ := h1 S.withoutChans b hb q hq hn
    rw [hm] at hD; cases hD
  · by_contra hn
    obtain ⟨msg, hm⟩ := h3 S.withoutChans hn
    rw [hm] at hD; cases hD

/-! ### The reference -/

/-- ✓ MOD-006's reference subnet builder satisfies MOD-005 for every net builder: it rejects two
channels of one name and a channel whose transition's name the built body does not hold, and a
subnet that builds without its channels still builds with channels that expose body transitions
under distinct names. -/
@[evidence holds MOD_005]
theorem MOD_005_reference {N A : Type} [DecidableEq N] [ToString N]
    (NB : NetBuilder (defsTB N A)) : MOD_005 NB (refSubnetBuild NB) :=
  mod005_of_mod006 (MOD_006_reference NB)

/-! ### Examples -/

/-- `buf` with its channel named `in`, the name of its input port, on the transition `take`. -/
def mod005_exShared : SubnetIn String Unit :=
  { mod006_exS with chans := [⟨"in", "take"⟩] }

/-- ✓ Every line of MOD-005 is exercised by the reference over the reference net builder. The
subnet `buf` builds without its channel, and it still builds with the channel `go` on its
transition `take` (line 3, and AC1: a channel declared with a name and a body transition). Two
channels named `go` fail with "Subnet 'buf': duplicate channel name 'go'" (line 1). A channel `go`
on `missing`, a name no body transition carries, fails with "Subnet 'buf': channel 'go' references
transition 'missing' which is not in the body" (line 2). A channel named `in` like the input port
builds too, since the reference keeps port names and channel names apart. -/
@[evidence nonvacuous MOD_005]
theorem MOD_005_nonvacuous :
    (∃ D, refSubnetBuild refNetBuild mod006_exS.withoutChans = .ok D ∧ D.chans = []) ∧
    (∃ D, refSubnetBuild refNetBuild mod006_exS = .ok D ∧ D.chans = [⟨"go", "take"⟩]) ∧
    refSubnetBuild refNetBuild mod006_exDupChan = .error (dupChanMsg "buf" ⟨"go", "take"⟩) ∧
    refSubnetBuild refNetBuild mod006_exBadChan = .error (chanTransMsg "buf" ⟨"go", "missing"⟩) ∧
    (∃ D, refSubnetBuild refNetBuild mod005_exShared = .ok D) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ⟨_, rfl⟩⟩

/-! ### Line lemmas for every builder of the `subnetVia` shape -/

section Via

variable {NB : NetBuilder (defsTB N A)} {cp cc : SubnetIn N A → BuiltNet N A → Option String}

/-- A `subnetVia` builder that succeeds built the body and passed both checks. -/
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

/-- Line 3 for a `subnetVia` builder whose port check does not look at the channels and whose
channel check passes on well-formed channels. -/
theorem via_mod005_line3 (hP : ∀ S b, cp S.withoutChans b = none → cp S b = none)
    (hC : ∀ (S : SubnetIn N A) b, (∀ c ∈ S.chans, c.trans ∈ transNames b) →
      (S.chans.map (·.name)).Nodup → (∀ c ∈ S.chans, c.name ∉ S.ports.map (·.name)) →
      cc S b = none) :
    mod005_line3 NB (subnetVia NB cp cc) := by
  intro S b hb ⟨D, hD⟩ hc hcn hns
  obtain ⟨b', hb', hp, -⟩ := subnetVia_ok_inv hD
  have hbb : b' = b := by
    have : NB S.body = .ok b' := hb'
    rw [hb] at this; cases this; rfl
  subst hbb
  exact ⟨_, subnetVia_ok hb (hP S b' hp) (hC S b' hc hcn hns)⟩

end Via

/-! ### Wrong subnet builders -/

section Wrong

variable [DecidableEq N] [ToString N]

/-- Keep the last channel of each name and drop the earlier ones silently. -/
def lastChanPerName (cs : List Chan) : List Chan :=
  cs.foldr (fun c acc => if acc.any (·.name == c.name) then acc else c :: acc) []

/-- A subnet builder that lets the last of two same-named channels win and builds the rest with
the reference. -/
def lastWinsChansSB (NB : NetBuilder (defsTB N A)) : SubnetMake N A := fun S =>
  refSubnetBuild NB { S with chans := lastChanPerName S.chans }

/-- The channel check that also asks the channel's own name to be a body transition's name, as a
builder would that looks the transition up by the channel's name. -/
def chanNameAlsoTransCheck (S : SubnetIn N A) (b : BuiltNet N A) : Option String :=
  checkList (·.name) (fun c : Chan => c.trans ∈ transNames b ∧ c.name ∈ transNames b)
    (dupChanMsg S.name) (chanTransMsg S.name) [] S.chans

/-- Some channel of `S` has the name of a port of `S`. -/
def SubnetIn.nameShared (S : SubnetIn N A) : Bool :=
  S.chans.any fun c => S.ports.any (·.name == c.name)

/-- A subnet builder with one namespace for ports and channels: a channel that has the name of a
port fails, everything else goes to the reference. -/
def sharedNamespaceSB (NB : NetBuilder (defsTB N A)) : SubnetMake N A := fun S =>
  if S.nameShared then .error ("Subnet '" ++ S.name ++ "': a port and a channel share a name")
  else refSubnetBuild NB S

end Wrong

/-- ✗ A builder that silently keeps the last of two same-named channels violates MOD-005 (line 1):
it builds `buf` with two channels named `go`, keeping one. -/
@[evidence forbids MOD_005]
theorem MOD_005_forbids_lastWins :
    ¬ MOD_005 refNetBuild (lastWinsChansSB (N := String) (A := Unit) refNetBuild) := by
  intro h
  obtain ⟨msg, hm⟩ := h.1 mod006_exDupChan (by decide)
  have : lastWinsChansSB refNetBuild mod006_exDupChan = .ok _ := rfl
  rw [this] at hm; cases hm

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-005 without line 1 (two channels of one name need not fail). -/
def MOD_005_mutant_noDupChan (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod005_line2 NB SB ∧ mod005_line3 NB SB

/-- Mutant reading: MOD-005 without line 2 (a channel on a missing transition need not fail). -/
def MOD_005_mutant_noChanTrans (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod005_line1 SB ∧ mod005_line3 NB SB

/-- Mutant reading: MOD-005 without line 3 (a well-formed channel may be rejected). -/
def MOD_005_mutant_noAcceptance (NB : NetBuilder (defsTB N A)) (SB : SubnetMake N A) : Prop :=
  mod005_line1 SB ∧ mod005_line2 NB SB

/-- The reference port check does not look at the channels. -/
theorem refPortCheck_withoutChans [DecidableEq N] [ToString N] (S : SubnetIn N A)
    (b : BuiltNet N A) : refPortCheck S.withoutChans b = refPortCheck S b := rfl

/-- The mutant without line 1 is killed by the builder without the duplicate-channel test: it
checks every channel's transition against the body, and builds `buf` with two channels named
`go`, both on `take`. -/
@[evidence mutant MOD_005]
theorem MOD_005_mutant_noDupChan_killed :
    MOD_005_mutant_noDupChan refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noDupChanCheck) ∧
      ¬ MOD_005 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noDupChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noDupChanCheck S b = none ↔
      ∀ c ∈ S.chans, c.trans ∈ transNames b := fun S b => by
    unfold noDupChanCheck; rw [checkOnly_none_iff]
  refine ⟨⟨via_line2 fun S b h => (hC S b).1 h,
    via_mod005_line3 (fun S b h => by rw [← refPortCheck_withoutChans]; exact h)
      (fun S b hc _ _ => (hC S b).2 hc)⟩, fun h => ?_⟩
  obtain ⟨msg, hm⟩ := h.1 mod006_exDupChan (by decide)
  have : subnetVia refNetBuild refPortCheck noDupChanCheck mod006_exDupChan = .ok _ := rfl
  rw [this] at hm; cases hm

/-- The mutant without line 2 is killed by the builder that leaves the transition test to
instantiation or composition: it rejects two channels of one name, but builds `buf` with its
channel `go` on `missing`. -/
@[evidence mutant MOD_005]
theorem MOD_005_mutant_noChanTrans_killed :
    MOD_005_mutant_noChanTrans refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noTransChanCheck) ∧
      ¬ MOD_005 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck noTransChanCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, noTransChanCheck S b = none ↔
      (S.chans.map (·.name)).Nodup := fun S b => by
    unfold noTransChanCheck; rw [checkList_none_iff]; simp
  refine ⟨⟨via_line4 fun S b h => (hC S b).1 h,
    via_mod005_line3 (fun S b h => by rw [← refPortCheck_withoutChans]; exact h)
      (fun S b _ hcn _ => (hC S b).2 hcn)⟩, fun h => ?_⟩
  obtain ⟨msg, hm⟩ := h.2.1 mod006_exBadChan _ (refNetBuild_of_terminals_nil rfl)
    ⟨"go", "missing"⟩ (by decide) (by decide)
  have : subnetVia refNetBuild refPortCheck noTransChanCheck mod006_exBadChan = .ok _ := rfl
  rw [this] at hm; cases hm

/-- The mutant without line 3 is killed by the builder that also asks a channel's own name to be
the name of a body transition: it rejects every subnet that MOD-005 lines 1 and 2 reject, and
also `buf` with its channel `go` on `take`, because no body transition is named `go`. -/
@[evidence mutant MOD_005]
theorem MOD_005_mutant_noAcceptance_killed :
    MOD_005_mutant_noAcceptance refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck chanNameAlsoTransCheck) ∧
      ¬ MOD_005 refNetBuild
        (subnetVia (N := String) (A := Unit) refNetBuild refPortCheck chanNameAlsoTransCheck) := by
  have hC : ∀ (S : SubnetIn String Unit) b, chanNameAlsoTransCheck S b = none →
      (∀ c ∈ S.chans, c.trans ∈ transNames b) ∧ (S.chans.map (·.name)).Nodup := fun S b h => by
    unfold chanNameAlsoTransCheck at h; rw [checkList_none_iff] at h
    exact ⟨fun c hc => (h.1 c hc).1, h.2.2⟩
  refine ⟨⟨via_line4 fun S b h => (hC S b h).2, via_line2 fun S b h => (hC S b h).1⟩,
    fun h => ?_⟩
  obtain ⟨D, hD⟩ := h.2.2 mod006_exS _ (refNetBuild_of_terminals_nil rfl) ⟨_, rfl⟩
    (by decide) (by decide) (by decide)
  have : subnetVia refNetBuild refPortCheck chanNameAlsoTransCheck mod006_exS =
      .error (chanTransMsg "buf" ⟨"go", "take"⟩) := rfl
  rw [this] at hD; cases hD

/-! ### One shared namespace: allowed here, ruled out by MOD-006 -/

section Shared

variable [DecidableEq N] [ToString N]

/-- Where no channel has a port's name, the shared-namespace builder is the reference. -/
theorem sharedNamespaceSB_eq {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    (h : S.nameShared = false) : sharedNamespaceSB NB S = refSubnetBuild NB S := by
  simp [sharedNamespaceSB, h]

/-- Where the reference fails, the shared-namespace builder fails too. -/
theorem sharedNamespaceSB_fails {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    (h : ∃ m, refSubnetBuild NB S = .error m) : ∃ m, sharedNamespaceSB NB S = .error m := by
  cases hs : S.nameShared with
  | true =>
    exact ⟨"Subnet '" ++ S.name ++ "': a port and a channel share a name",
      by simp [sharedNamespaceSB, hs]⟩
  | false => rw [sharedNamespaceSB_eq hs]; exact h

/-- The shared-namespace builder meets MOD-005 for every net builder. -/
theorem sharedNamespaceSB_meets (NB : NetBuilder (defsTB N A)) :
    MOD_005 NB (sharedNamespaceSB NB) := by
  have R := MOD_005_reference (N := N) (A := A) NB
  refine ⟨fun S hn => sharedNamespaceSB_fails (R.1 S hn),
    fun S b hb c hc hn => sharedNamespaceSB_fails (R.2.1 S b hb c hc hn),
    fun S b hb ⟨D, hD⟩ hc hcn hns => ?_⟩
  have h0 : S.withoutChans.nameShared = false := rfl
  have hs : S.nameShared = false := by
    simp only [SubnetIn.nameShared, List.any_eq_false, List.any_eq_true, beq_iff_eq, not_exists,
      not_and]
    intro c hc q hq he
    exact hns c hc (List.mem_map.2 ⟨q, hq, he⟩)
  rw [sharedNamespaceSB_eq h0] at hD
  rw [sharedNamespaceSB_eq hs]
  exact R.2.2 S b hb ⟨D, hD⟩ hc hcn hns

end Shared

/-- ✓ MOD-005 leaves open whether ports and channels share one namespace, as item 1 says. A builder
with one shared namespace meets MOD-005: given `buf` with its channel named `in`, like its input
port, it fails with "Subnet 'buf': a port and a channel share a name", where the reference builds.
MOD-006 fixes two namespaces for subnet definitions, so the same builder violates MOD-006. -/
@[evidence allows MOD_005]
theorem MOD_005_allows_sharedNamespace :
    MOD_005 refNetBuild (sharedNamespaceSB (N := String) (A := Unit) refNetBuild) ∧
      sharedNamespaceSB refNetBuild mod005_exShared =
        .error "Subnet 'buf': a port and a channel share a name" ∧
      (∃ D, refSubnetBuild refNetBuild mod005_exShared = .ok D) ∧
      ¬ MOD_006 refNetBuild (sharedNamespaceSB (N := String) (A := Unit) refNetBuild) := by
  refine ⟨sharedNamespaceSB_meets _, rfl, ⟨_, rfl⟩, fun h => ?_⟩
  obtain ⟨D, hD⟩ := h.2.2.2.2.2.1 mod005_exShared _ (refNetBuild_of_terminals_nil rfl)
    (by decide) (by decide) (by decide) (by decide)
  have : sharedNamespaceSB refNetBuild mod005_exShared =
      .error "Subnet 'buf': a port and a channel share a name" := rfl
  rw [this] at hD; cases hD

end Libpetri.Spec
