import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeBuild
import Libpetri.Spec.Text.MOD_026

set_option linter.missingDocs true

/-!
# MOD-026: Subnet-membership metadata for direct composition (`spec/11-modular-composition.md`)

MOD-026 has two blocks.

* `MOD_026_resolve` (kind F) is the resolution rule over a list of recorded contributions (node
  name, subnet name): a node recorded under one subnet only maps to it; a node recorded under two
  or more subnets, and a node with no record, have no entry. The model is a resolution function
  `res`, the witness `memberOf` (`Reference/ComposeBuild.lean`).
* `MOD_026` (kind B) is the builder side over a build-script function `S : ScriptFn N A` (a
  script of builder calls from a new builder, then `build()`; `Reference/ComposeBuild.lean`), a
  naming model `Nm` and an action-binding function `Rb` on composed nets. Line 1: on a built
  net, the entry of a name that fusion did not remove is the resolution of the records the
  script's `compose(SubnetDef)` calls make, one per body place and per body transition under the
  definition's name with each `/` written `_`, and no other call records anything. Line 2: a
  name fusion removed has no entry. Line 3: the map changes nothing else, so renaming the subnet
  definitions a script composes directly, each call on its own, builds the same places,
  transitions, terminal places and correspondences. Line 4: binding actions keeps the map.

The witnesses are `memberOf`, the reference build script `buildScript` and `composedRebind`
(core's `refBind`, the map carried along). The resolution block fixes its function
(`mod026_resolve_unique`), and the builder's line 1 is that function applied to the script's
records (`mod026_line1_iff_resolve`). For every model of the block the map does not depend on
the order of the records (`mod026_resolve_congr`, `mod026_perm`), a script without a direct
composition gives an empty map (`mod026_noDirect`), and no entry contains `/`
(`mod026_slashFree`). The reference build script and binding meet the block for every naming
model, token-type map, transition check and channel merge (`mod026_buildScript`). Wrong models
are killed one per line, and line 1's clauses (host-declared
body places, body transitions, nothing for host declarations) one each.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Block-local vocabulary -/

section Vocab

variable {N A : Type}

/-- The name a direct composition records for a subnet definition: its name with each `/` written
`_` ([MOD-026], all three runtimes). -/
def slashFree (s : String) : String :=
  String.ofList (s.toList.map fun c => if c = '/' then '_' else c)

/-- The records of one direct composition of `S`: one per body place (its name) and one per body
transition (its name), each under the definition's recorded name. -/
def directRecords (Nm : Naming N) (S : SubnetDef N A) : List (String × String) :=
  S.places.map (fun x => (Nm.name x, slashFree S.name)) ++
    S.defs.map fun d => (d.core.name, slashFree S.name)

/-- The records one builder call makes: a direct composition its `directRecords`, every other
call none ([MOD-026] rules 1 and 4). -/
def Op.records (Nm : Naming N) : Op N A → List (String × String)
  | .composeDirect S => directRecords Nm S
  | _ => []

/-- The records of a script, in the order of its calls. -/
def scriptRecords (Nm : Naming N) (ops : List (Op N A)) : List (String × String) :=
  ops.flatMap (Op.records Nm)

/-- The fusion set one builder call declares, if any. -/
def Op.fusionSets : Op N A → List (FusionSet N)
  | .fuse s => [s]
  | _ => []

/-- The fusion sets a script declares, in order. -/
def scriptFusions (ops : List (Op N A)) : List (FusionSet N) := ops.flatMap Op.fusionSets

/-- **The resolution rule** ([MOD-026] rules 2 and 3): the records `c` resolve node name `n` to
subnet `s` when `n` is recorded under `s` and under no other subnet. -/
def MemberOf (c : List (String × String)) (n s : String) : Prop :=
  (n, s) ∈ c ∧ ∀ s', (n, s') ∈ c → s' = s

/-- **A name fusion removed** ([MOD-061]): the name of a member of a fusion set the script
declares that is not the set's first member, the canonical one (ruling D54). -/
def FusedAway (Nm : Naming N) (ops : List (Op N A)) (n : String) : Prop :=
  ∃ s ∈ scriptFusions ops, ∃ p ∈ s.members, p ≠ s.canonical p ∧ Nm.name p = n

instance [DecidableEq N] (Nm : Naming N) (ops : List (Op N A)) (n : String) :
    Decidable (FusedAway Nm ops n) :=
  inferInstanceAs (Decidable (∃ s ∈ scriptFusions ops, ∃ p ∈ s.members,
    p ≠ s.canonical p ∧ Nm.name p = n))

/-- The same call with a directly composed subnet definition renamed by `f`; every other call
unchanged. -/
def Op.renameDirect (f : String → String) : Op N A → Op N A
  | .composeDirect S => .composeDirect { S with name := f S.name }
  | op => op

/-- **Scripts that differ only in the names of the directly composed definitions**: call by call,
`ops'` is `ops` with each directly composed definition renamed, each call on its own (so two
definitions of one name may get two names, and two of different names one name); every other
call unchanged. -/
def RenamesDirect (ops ops' : List (Op N A)) : Prop :=
  List.Forall₂ (fun op op' => ∃ f : String → String, op' = op.renameDirect f) ops ops'

/-- Renaming every directly composed definition through one function is a case of
`RenamesDirect`. -/
theorem renamesDirect_map (f : String → String) (ops : List (Op N A)) :
    RenamesDirect ops (ops.map (Op.renameDirect f)) := by
  induction ops with
  | nil => exact .nil
  | cons op rest ih => exact .cons ⟨f, rfl⟩ ih

/-- **An action-binding function on composed nets** ([CORE-042]): a composed net and a resolver
(transition name to an action, `none` to keep the action) give the bound net. -/
abbrev RebindFn (N A : Type) := ComposedNet N A → (String → Option (Act A)) → ComposedNet N A

end Vocab

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec

/-- **The reference binding of a composed net** ([CORE-042], [MOD-026]): core's `refBind` on the
built net; the correspondences and the membership map carried along (Rust `map_transitions`,
Java and TypeScript `bindActions`). -/
def composedRebind {N A : Type} : RebindFn N A := fun c r =>
  { c with toBuiltNet := refBind c.toBuiltNet r }

/- The reference binding of a composed net is the witness model of MOD-026's binding line. -/
#spec_witness composedRebind

/- The membership entry of the composition model is the witness model of the resolution block. -/
#spec_witness memberOf

end Libpetri.Reference

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## MOD-026 (resolution): the recorded contributions resolved -/

requirement MOD_026_resolve
  id "MOD-026"
  title "Subnet-Membership Metadata for Direct Composition (resolution of the recorded contributions)"
  kind F
  scope "the resolution of the subnet contributions recorded by direct composition into the membership mapping (Java, TypeScript, Rust, Python)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_026.s3, MOD_026.s4, MOD_026.s5
  reading "For every resolution function res, which maps a list c of records (node name, subnet name) and a node name n to an optional subnet name:"
          "if (n, s) is a record of c and every record of c for n names s, res c n is s;"
          "if (n, s₁) and (n, s₂) are records of c and s₁ differs from s₂, res c n is absent;"
          "if c has no record for n, res c n is absent."
  assumes "The model is the resolution step of build(): Rust resolve_subnet_membership (rust/libpetri-core/src/petri_net.rs), Java Builder.resolveSubnetMembership (java/src/main/java/org/libpetri/core/PetriNet.java) and TypeScript resolveSubnetMembership (typescript/src/core/petri-net.ts), Python through Rust. Each keeps a set of subnet names per node name and keeps a node exactly when its set has one element; the model takes the records as a list, so a subnet recorded twice for one node (possible only for a place, since MOD-025 rejects a second transition of one name) counts once, as it does in the sets. The witness is memberOf (Reference/ComposeBuild.lean), the function the reference build script uses."
          "Node names are strings and subnets are told apart by their recorded names (MOD-026 rule 1, reworded under ruling D20): two subnet definitions whose recorded names coincide are one subnet here, in the model and in the runtimes. Which records a build makes, and that the built net's mapping is this resolution minus the names fusion removed, is the builder block MOD_026. The three lines fix the resolution (mod026_resolve_unique: every model is memberOf), and the builder's line 1 is exactly the statement that, off the fused-away names, the map of a built net is this resolution applied to the build's records (mod026_line1_iff_resolve, for every model of this block)."
          "The three lines determine res c n from the set of records of c alone, so for every model the resolution does not depend on the order of the records or on repeated records (mod026_resolve_congr): the order-independence of AC4 at the level of the resolution."
  signoff "2026-11-13 41e115c0fed24eb8 ai"
  statement : (List (String × String) → String → Option String) → Prop :=
    fun res =>
      (∀ c n s, (n, s) ∈ c → (∀ s', (n, s') ∈ c → s' = s) → res c n = some s) ∧
      (∀ c n s₁ s₂, (n, s₁) ∈ c → (n, s₂) ∈ c → s₁ ≠ s₂ → res c n = none) ∧
      (∀ c n, (∀ s, (n, s) ∉ c) → res c n = none)

/- The pinned readable form of MOD-026 (resolution): a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.MOD_026_resolve : (List (String × String) → String → Option String) → Prop :=
fun res =>
  (∀ (c : List (String × String)) (n s : String),
      (n, s) ∈ c → (∀ (s' : String), (n, s') ∈ c → s' = s) → res c n = some s) ∧
    (∀ (c : List (String × String)) (n s₁ s₂ : String), (n, s₁) ∈ c → (n, s₂) ∈ c → s₁ ≠ s₂ → res c n = none) ∧
      ∀ (c : List (String × String)) (n : String), (∀ (s : String), (n, s) ∉ c) → res c n = none
-/
#guard_msgs in #print MOD_026_resolve

/-! ### The three lines of the resolution, named (for the mutants) -/

section ResolveLines

/-- Line 1 of the resolution: a node recorded under one subnet only maps to it. -/
def mod026r_line1 (res : List (String × String) → String → Option String) : Prop :=
  ∀ c n s, (n, s) ∈ c → (∀ s', (n, s') ∈ c → s' = s) → res c n = some s

/-- Line 2 of the resolution: a node recorded under two subnets has no entry. -/
def mod026r_line2 (res : List (String × String) → String → Option String) : Prop :=
  ∀ c n s₁ s₂, (n, s₁) ∈ c → (n, s₂) ∈ c → s₁ ≠ s₂ → res c n = none

/-- Line 3 of the resolution: a node without a record has no entry. -/
def mod026r_line3 (res : List (String × String) → String → Option String) : Prop :=
  ∀ c n, (∀ s, (n, s) ∉ c) → res c n = none

end ResolveLines

/-! ## MOD-026 (builder): what a build records, drops and keeps -/

requirement MOD_026
  id "MOD-026"
  title "Subnet-Membership Metadata for Direct Composition"
  kind B
  scope "every build of a net through an enclosing builder (Java, TypeScript, Rust, Python) and every action binding of a built net"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_026.s1, MOD_026.s2, MOD_026.s6, MOD_026.s7, MOD_026.s8, MOD_026.s9
  reading "For every naming model Nm, every build-script function S and every action-binding function Rb on composed nets, where the records of a script are, in the order of its calls, for each direct composition of a subnet definition D one record (name of p, slashFree D.name) per body place p and one record (name of t, slashFree D.name) per body transition t, and nothing for any other call, and a name n is fused away in a script when some fusion set the script declares has a member other than its first member whose name is n:"
          "if S ops returns the composed net c and n is not fused away in ops, then c.member n is s exactly when the records of ops resolve n to s (MemberOf: (n, s) is a record and every record for n names s);"
          "if S ops returns c and n is fused away in ops, then c.member n is absent;"
          "if S ops returns c and ops' is ops with the subnet definition of each direct composition renamed, each call on its own, and every other call unchanged (RenamesDirect), then S ops' returns some c' with the same places, transitions, terminal places and correspondences as c;"
          "for every composed net c and every resolver r, Rb c r has the membership map of c."
  assumes "The model is a triple. Nm is the naming model of places (strNaming, names as keys, for TypeScript, Rust and Python; typedNaming, name and token type, for Java), whose name function gives the name a record carries. S is a build-script function (ScriptFn, Reference/ComposeBuild.lean): a script of builder calls (declare a place, add a transition, declare a terminal place, declare a fusion set, compose an instance with explicit bindings or by auto-binding, compose a subnet definition directly) folded over a new builder, then build(), giving the composed net or a rejection. A composed net is core's built net (places, transitions, terminal places), the MOD-031 correspondences and the membership map, a function from node name to an optional subnet name (none: no entry): Rust PetriNet::subnet_membership, Java subnetMembership(), TypeScript subnetMembership, Python Net.subnet_membership. Rb is an action-binding function on composed nets. The witnesses are buildScript (for every naming model, token type map, transition check and channel merge) and composedRebind, core's refBind with the map carried along."
          "Line 1 is rule 1, the recording sentences and the sentence that the mapping is the resolution: the records are read off the script (scriptRecords), the resolution is MOD_026_resolve's rule written as MemberOf. All three runtimes record exactly a direct composition's body places and body transitions under the definition's name with each / replaced by _ (compose_direct in rust/libpetri-core/src/petri_net.rs, Builder.compose(SubnetDef) in java/src/main/java/org/libpetri/core/PetriNet.java, composeDirect in typescript/src/core/petri-net.ts), and only after every check of the call passed. A body place the builder already held is recorded too, so a place the host declares and one subnet contributes maps to that subnet: host declarations record nothing (wrong models hostSkip, placesOnly and hostRecords). Instance composition by compose and compose_auto records nothing (rule 4, MOD-020 and MOD-024 as reworded under ruling D20; wrong model instanceRecords). That a compose(SubnetDef) call which fails records nothing (rule 1's last sentence) is not a line: in the model a failed call fails the whole script, so a host that catches the rejection and goes on with the builder (Java and TypeScript throw, Rust compose_direct panics) is outside the model. All three runtimes run every check of the call before the first record (compose_direct in rust/libpetri-core/src/petri_net.rs, Builder.compose(SubnetDef) in java/src/main/java/org/libpetri/core/PetriNet.java, composeDirect in typescript/src/core/petri-net.ts); that part is checked by reading the cited code."
          "Places and transitions share one mapping keyed by name, in the model and in all three runtimes. A place and a transition of one name would share an entry; the shared unique-names assumption (rulings D10 and D23; no builder checks names) rules that net out, and the lines need no premise for it because they speak of names, as the runtimes do. That a transition is never recorded by two subnets is MOD-025's transition-name rejection, not a line here."
          "Line 2 is the fusion sentence. A name is fused away when it is the name of a member place of a declared fusion set other than the set's first member (FusionSet.canonical, ruling D54), compared as a place, not as a position in the list of members. The runtimes drop entries by the names of the non-canonical members (the membership filter of build_with_fusion, rust/libpetri-core/src/petri_net.rs; filterFusedMembership in java/src/main/java/org/libpetri/core/PetriNet.java and typescript/src/core/petri-net.ts), so a transition with the name of a removed place loses its entry too; line 2 is stated by name for that reason. Overlapping fusion sets fail the build (MOD-061), so on a built net each member lies in one set. A set may list its first member again (members [a, b, a]): every runtime skips a later member equal to the canonical member when it collects the removed names (build_with_fusion in rust/libpetri-core/src/petri_net.rs, Builder.buildWithFusion in java/src/main/java/org/libpetri/core/PetriNet.java, buildWithFusion in typescript/src/core/petri-net.ts), so the canonical member keeps its entry, as lines 1 and 2 (mod026_dupCanonical_kept), AC5 and the sentence that the surviving canonical place keeps its own entry say."
          "Line 3 is the sentence that the mapping is observability-only. Every runtime reads a subnet definition's name only to record it (and to name it in rejection messages, which the line does not compare), so renaming the definitions changes the mapping freely (two definitions renamed to one name merge their entries, one name split into two splits them) while the built net and the MOD-031 correspondences stay the same, compared as lists. The renaming is per call: one renaming function for every call can merge two definition names but never split one, so that reading would accept a build that rejects a place shared by two definitions of different names, which AC1 and AC2 need to build (mod026_mutant_uniformRename_killed). Execution, marking and the properties of MOD-023 read the built net (places, transitions, terminal places) and the correspondences, never the mapping, in the model, whose executors take only the built net; for the runtimes this part of the sentence (it does not affect execution or marking) rests on that modelling argument, not on a line. That the verifier reads none of it is MOD-050's line. That the mapping is immutable is a property of the value (Java unmodifiableMap, TypeScript ReadonlyMap, Rust no mutator), tested, not proven; in the model the map is a field of an immutable value."
          "Line 4 is the action-binding sentence: Rust bind_actions_with_resolver through map_transitions (rust/libpetri-core/src/petri_net.rs), Java bindActions (java/src/main/java/org/libpetri/core/PetriNet.java) and TypeScript bindActionsWithResolver (typescript/src/core/petri-net.ts) pass the map through. What binding does to the transitions is CORE-042's block; composedRebind does it with core's refBind."
          "Priority SHOULD with shall sentences, in the form ruling D22 gives the SHOULD requirements of VER: recording the mapping is optional, and an implementation that records it follows the lines. All three runtimes record the mapping, so the lines bind every implementation. The opening sentence (cluster-aware export relies on the mapping), the clause that a shared place renders outside any cluster, the purpose clause that the mapping names only nodes that still exist, and rule 4's sentence on subnetOf are motivation and the export side, stated by MOD-040 and EXP-016, not lines of this block."
          "AC1 (a private node of A maps to A) is line 1 with MOD_026_nonvacuous (composing s/one and two directly, a and t1 map to s_one, b and t2 to two). AC2 (a place named in both subnets whose recorded names differ is absent) is line 1 with the resolution's line 2 (pipe has no entry in MOD_026_nonvacuous); two definitions with one recorded name are one subnet, so their shared place maps to that name (mod026_sameName_shared), and line 3 makes the AC2 build succeed whenever the build with one name does. AC3 (a flat or instance-composed net has an empty mapping) is mod026_noDirect, for every model, with a flat net and an instance-composed net in MOD_026_nonvacuous. AC4 (opposite orders give equal mappings) is mod026_perm, for every model: two scripts that are reorderings of each other and both build have equal mappings; MOD_026_nonvacuous decides both orders. AC5 (fusing away a non-canonical place removes its entry, the canonical place keeps its own) is lines 2 and 1, with the fusion of a into b in MOD_026_nonvacuous. AC6 (a name with / is recorded with / replaced) is line 1 through slashFree and mod026_slashFree (no entry of any model contains /), with s/one recorded as s_one in MOD_026_nonvacuous."
  signoff "2026-11-13 274a57bb5e8be4f3 ai"
  statement : ∀ {N A : Type}, Naming N → ScriptFn N A → RebindFn N A → Prop :=
    fun {N A} Nm S Rb =>
      (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n s : String), S ops = .ok c →
        ¬ FusedAway Nm ops n → (c.member n = some s ↔ MemberOf (scriptRecords Nm ops) n s)) ∧
      (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n : String), S ops = .ok c →
        FusedAway Nm ops n → c.member n = none) ∧
      (∀ (ops ops' : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
        RenamesDirect ops ops' →
        ∃ c', S ops' = .ok c' ∧ c'.toBuiltNet = c.toBuiltNet ∧ c'.corrs = c.corrs) ∧
      (∀ (c : ComposedNet N A) (r : String → Option (Act A)), (Rb c r).member = c.member)

/- The pinned readable form of MOD-026: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_026 : {N A : Type} → Naming N → ScriptFn N A → RebindFn N A → Prop :=
fun {N A} Nm S Rb =>
  (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n s : String),
      S ops = Except.ok c → ¬FusedAway Nm ops n → (c.member n = some s ↔ MemberOf (scriptRecords Nm ops) n s)) ∧
    (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n : String),
        S ops = Except.ok c → FusedAway Nm ops n → c.member n = none) ∧
      (∀ (ops ops' : List (Op N A)) (c : ComposedNet N A),
          S ops = Except.ok c →
            RenamesDirect ops ops' → ∃ c', S ops' = Except.ok c' ∧ c'.toBuiltNet = c.toBuiltNet ∧ c'.corrs = c.corrs) ∧
        ∀ (c : ComposedNet N A) (r : String → Option (Act A)), (Rb c r).member = c.member
-/
#guard_msgs in #print MOD_026

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-026: off the fused-away names, the map is the resolution of the records. -/
def mod026_line1 (Nm : Naming N) (S : ScriptFn N A) : Prop :=
  ∀ (ops : List (Op N A)) (c : ComposedNet N A) (n s : String), S ops = .ok c →
    ¬ FusedAway Nm ops n → (c.member n = some s ↔ MemberOf (scriptRecords Nm ops) n s)

/-- Line 2 of MOD-026: a fused-away name has no entry. -/
def mod026_line2 (Nm : Naming N) (S : ScriptFn N A) : Prop :=
  ∀ (ops : List (Op N A)) (c : ComposedNet N A) (n : String), S ops = .ok c →
    FusedAway Nm ops n → c.member n = none

/-- Line 3 of MOD-026: renaming the directly composed definitions, each call on its own, builds
the same net with the same correspondences. -/
def mod026_line3 (S : ScriptFn N A) : Prop :=
  ∀ (ops ops' : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
    RenamesDirect ops ops' →
    ∃ c', S ops' = .ok c' ∧ c'.toBuiltNet = c.toBuiltNet ∧ c'.corrs = c.corrs

/-- Line 4 of MOD-026: binding actions keeps the map. -/
def mod026_line4 (Rb : RebindFn N A) : Prop :=
  ∀ (c : ComposedNet N A) (r : String → Option (Act A)), (Rb c r).member = c.member

/-- MOD-026 is its four lines. -/
theorem mod026_iff (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) :
    MOD_026 Nm S Rb ↔
      mod026_line1 Nm S ∧ mod026_line2 Nm S ∧ mod026_line3 S ∧ mod026_line4 Rb := Iff.rfl

end Lines

end Libpetri.Spec

/-! ## The reference meets both blocks -/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

section Resolve

/-- ✓ **The reference resolution meets MOD-026 (resolution)**: `memberOf` maps a node recorded
under one subnet only to that subnet, and gives no entry to a node recorded under two subnets or
not recorded at all. For example, with the records `(pipe, A)`, `(pipe, B)` and `(a, A)`, the
node `a` resolves to `A`, and `pipe` and `z` resolve to nothing. -/
@[evidence holds MOD_026_resolve]
theorem MOD_026_resolve_reference : MOD_026_resolve memberOf := by
  refine ⟨fun c n s hm hall => memberOf_eq_some_iff.2 ⟨hm, hall⟩, ?_, ?_⟩
  · intro c n s₁ s₂ h₁ h₂ hne
    cases h : memberOf c n with
    | none => rfl
    | some s₀ =>
      obtain ⟨-, hall⟩ := memberOf_eq_some_iff.1 h
      exact absurd ((hall s₁ h₁).trans (hall s₂ h₂).symm) hne
  · intro c n hno
    cases h : memberOf c n with
    | none => rfl
    | some s₀ => exact absurd (memberOf_eq_some_iff.1 h).1 (hno s₀)

end Resolve

section Builder

variable {N A : Type} [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- The recorded name of the reference direct composition is `slashFree`. -/
theorem contribName_eq_slashFree (s : String) : contribName s = slashFree s := rfl

omit [DecidableEq N] [ToString T] in
/-- The reference fusion-set declaration check records the set it was given. -/
theorem refDeclFusion_ok {s s' : FusionSet N} (h : refDeclFusion tyOf s = .ok s') : s' = s := by
  unfold refDeclFusion at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- **One call's records and fusion sets**: a successful call appends its own records (a direct
composition's, none for any other call) and its own fusion set (a fusion declaration's, none for
any other call) to the builder's. -/
theorem step_records {b b' : Bld N A} {op : Op N A} (h : scriptStep Nm tyOf Build Mg b op = .ok b') :
    b'.contrib = b.contrib ++ op.records Nm ∧ b'.fusions = b.fusions ++ op.fusionSets := by
  cases op with
  | place p => cases h; simp [Op.records, Op.fusionSets]
  | trans d =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · cases h; simp [Op.records, Op.fusionSets]
  | terminal p => cases h; simp [Op.records, Op.fusionSets]
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 h
    rw [refDeclFusion_ok hs']
    simp [Op.records, Op.fusionSets]
  | compose I ports chans =>
    obtain ⟨-, -, -, -, hc, hf, -⟩ := refCompose_shape h
    simp [Op.records, Op.fusionSets, hc, hf]
  | composeAuto I cs =>
    simp only [scriptStep] at h
    unfold refAuto at h
    split at h
    · split at h
      · obtain ⟨-, ms, -, rfl⟩ := applyBind_ok_iff.1 h
        simp [Op.records, Op.fusionSets, bindAssemble]
      · obtain ⟨-, -, -, -, hc, hf, -⟩ := refCompose_shape h
        simp [Op.records, Op.fusionSets, hc, hf]
    · cases h
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
      simp [Op.records, Op.fusionSets, directAssemble, directRecords, contribName_eq_slashFree]

/-- **A script's records and fusion sets**: after a successful script from `b₀`, the builder
holds `b₀`'s records followed by the script's, and `b₀`'s fusion sets followed by the script's. -/
theorem script_records {ops : List (Op N A)} {b₀ b : Bld N A}
    (h : ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok b) :
    b.contrib = b₀.contrib ++ scriptRecords Nm ops ∧
      b.fusions = b₀.fusions ++ scriptFusions ops := by
  induction ops generalizing b₀ with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [scriptRecords, scriptFusions]
  | cons op rest ih =>
    rw [foldlM_except_cons] at h
    cases hs : scriptStep Nm tyOf Build Mg b₀ op with
    | error e => rw [hs] at h; cases h
    | ok t =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := ih h
      obtain ⟨g1, g2⟩ := step_records hs
      refine ⟨?_, ?_⟩
      · rw [h1, g1]; simp [scriptRecords, List.flatMap_cons, List.append_assoc]
      · rw [h2, g2]; simp [scriptFusions, List.flatMap_cons, List.append_assoc]

omit [ToString N] in
/-- A name `build()` drops is the name of a member that is not its set's first member. -/
theorem removed_fusedAway {b : Bld N A} {n : String} (h : n ∈ removedNames Nm b) :
    ∃ s ∈ b.fusions, ∃ p ∈ s.members, p ≠ s.canonical p ∧ Nm.name p = n := by
  simp only [removedNames, List.mem_map, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq] at h
  obtain ⟨p, ⟨⟨-, -, -⟩, hne⟩, rfl⟩ := h
  unfold refSubst at hne
  cases ho : fusionOwner b.fusions p with
  | none => rw [ho] at hne; exact absurd rfl hne
  | some s =>
    rw [ho] at hne
    obtain ⟨hs, hp⟩ := fusionOwner_some ho
    exact ⟨s, hs, p, hp, fun e => hne e.symm, rfl⟩

omit [ToString N] in
/-- A name `build()` drops is fused away in the script. -/
theorem fusedAway_of_removed {ops : List (Op N A)} {b : Bld N A}
    (hfu : b.fusions = scriptFusions ops) {n : String} (h : n ∈ removedNames Nm b) :
    FusedAway Nm ops n := by
  obtain ⟨s, hs, p, hp, hne, rfl⟩ := removed_fusedAway h
  exact ⟨s, hfu ▸ hs, p, hp, hne, rfl⟩

/-- Line 1 of the reference: off the fused-away names, the map is the resolution of the
script's records. -/
theorem ref_mod026_line1 : mod026_line1 Nm (buildScript (A := A) Nm tyOf Build Mg) := by
  intro ops c n s h hn
  obtain ⟨b, hb, hf⟩ := buildScript_ok_iff.1 h
  obtain ⟨X, -, -, -, hm, -⟩ := finish_trans hf
  obtain ⟨hc, hfu⟩ := script_records hb
  simp only [Bld.empty, List.nil_append] at hc hfu
  rw [hm, memberMap_kept (fun hr => hn (fusedAway_of_removed hfu hr)), memberOf_eq_some_iff, hc]
  rfl

/-- Line 2 of the reference: a fused-away name has no entry. -/
theorem ref_mod026_line2 : mod026_line2 Nm (buildScript (A := A) Nm tyOf Build Mg) := by
  intro ops c n h hn
  obtain ⟨b, hb, hf⟩ := buildScript_ok_iff.1 h
  obtain ⟨-, hfu⟩ := script_records hb
  simp only [Bld.empty, List.nil_append] at hfu
  obtain ⟨s, hs, p, hp, hne, rfl⟩ := hn
  rw [← hfu] at hs
  obtain ⟨X, hX, -, -, -⟩ := (finish_ok_iff (Nm := Nm) (Build := Build)).1 hf
  rw [fuseStage_cons (List.ne_nil_of_mem hs)] at hX
  have hd := (refFuse_ok_iff.1 hX).1
  obtain ⟨-, -, -, -, hm, -⟩ := finish_trans hf
  rw [hm]
  refine memberMap_removed hs hp ?_
  rw [(refSubst_spec hd).1 s hs p hp]
  exact fun e => hne e.symm

/-- The binding step of a compose call does not read the builder's records. -/
theorem applyBind_withContrib (b : Bld N A) (k : List (String × String)) (I : Instance N A)
    (bm : List (BindEntry N)) (chans : List (String × CDef N A)) :
    applyBind Build Mg { b with contrib := k } I bm chans =
      (applyBind Build Mg b I bm chans).map (fun b' => { b' with contrib := k }) := by
  cases h1 : I.defs.mapM (bindStep Build I.pfx bm) with
  | error m => simp only [applyBind, h1]; rfl
  | ok ds =>
    simp only [applyBind, h1]
    cases ds.mapM (mergeStep Mg I chans) <;> rfl

/-- The reference composition does not read the builder's records. -/
theorem refCompose_withContrib (b : Bld N A) (k : List (String × String)) (I : Instance N A)
    (ports : List (String × N)) (chans : List (String × CDef N A)) :
    refCompose tyOf Build Mg { b with contrib := k } I ports chans =
      (refCompose tyOf Build Mg b I ports chans).map (fun b' => { b' with contrib := k }) := by
  unfold refCompose
  cases portCheck tyOf I ports with
  | some m => rfl
  | none =>
    cases chanCheck I chans with
    | some m => rfl
    | none =>
      simp only
      rw [applyBind_withContrib]
      cases applyBind Build Mg b I (bindEntries I ports) chans <;> rfl

/-- The reference auto-composition does not read the builder's records. -/
theorem refAuto_withContrib (b : Bld N A) (k : List (String × String)) (I : Instance N A)
    (cs : List String) :
    refAuto Nm tyOf Build Mg { b with contrib := k } I cs =
      (refAuto Nm tyOf Build Mg b I cs).map (fun b' => { b' with contrib := k }) := by
  unfold refAuto
  split
  · split
    · exact applyBind_withContrib b k I (inferEntries Nm b I) []
    · exact refCompose_withContrib b k I _ []
  · rfl

/-- **A call ignores the records and the definition names**: a call that succeeds on `b` also
succeeds on `b` with other records and with its direct composition's definition renamed, and
gives the same builder up to the records. -/
theorem step_renameDirect (f : String → String) {b c : Bld N A} {op : Op N A}
    (h : scriptStep Nm tyOf Build Mg b op = .ok c) (k : List (String × String)) :
    ∃ k', scriptStep Nm tyOf Build Mg { b with contrib := k } (op.renameDirect f) =
      .ok { c with contrib := k' } := by
  cases op with
  | place p => cases h; exact ⟨k, rfl⟩
  | trans d =>
    simp only [scriptStep] at h
    cases hd : Build d.toTrans with
    | some m => rw [hd] at h; cases h
    | none =>
      rw [hd] at h; cases h
      exact ⟨k, by simp only [Op.renameDirect, scriptStep, hd]⟩
  | terminal p => cases h; exact ⟨k, rfl⟩
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 h
    exact ⟨k, by simp only [Op.renameDirect, scriptStep, hs', Except.map]⟩
  | compose I ports chans =>
    refine ⟨k, ?_⟩
    simp only [Op.renameDirect, scriptStep] at h ⊢
    rw [refCompose_withContrib, h]; rfl
  | composeAuto I cs =>
    refine ⟨k, ?_⟩
    simp only [Op.renameDirect, scriptStep] at h ⊢
    rw [refAuto_withContrib, h]; rfl
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · rename_i hn
      obtain ⟨h1, h2, h3, h4, rfl⟩ := refDirect_ok_iff.1 h
      refine ⟨k ++ directRecords Nm { S with name := f S.name }, ?_⟩
      simp only [Op.renameDirect, scriptStep]
      rw [show (({ S with name := f S.name } : SubnetDef N A).defs.findSome?
        fun d => Build d.toTrans) = none from hn]
      simp only
      rw [refDirect_accepts (Nm := Nm) (tyOf := tyOf) (b := { b with contrib := k })
        (S := { S with name := f S.name }) h1 h2 h3 h4]
      rfl

/-- The same for a whole script, each call renamed on its own. -/
theorem script_renamesDirect {ops ops' : List (Op N A)} (hr : RenamesDirect ops ops')
    {b c : Bld N A} (h : ops.foldlM (scriptStep Nm tyOf Build Mg) b = .ok c)
    (k : List (String × String)) :
    ∃ k', ops'.foldlM (scriptStep Nm tyOf Build Mg) { b with contrib := k } =
      .ok { c with contrib := k' } := by
  induction hr generalizing b k with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨k, rfl⟩
  | @cons op op' rest rest' hop _ ih =>
    obtain ⟨f, rfl⟩ := hop
    rw [foldlM_except_cons] at h
    cases hs : scriptStep Nm tyOf Build Mg b op with
    | error e => rw [hs] at h; cases h
    | ok t =>
      rw [hs] at h
      obtain ⟨k₁, hk₁⟩ := step_renameDirect f hs k
      obtain ⟨k₂, hk₂⟩ := ih h k₁
      refine ⟨k₂, ?_⟩
      rw [foldlM_except_cons, hk₁]
      exact hk₂

/-- `build()` reads the records only for the map. -/
theorem finish_withContrib {b : Bld N A} {c : ComposedNet N A} (h : finish Nm Build b = .ok c)
    (k : List (String × String)) :
    ∃ c', finish Nm Build { b with contrib := k } = .ok c' ∧ c'.toBuiltNet = c.toBuiltNet ∧
      c'.corrs = c.corrs := by
  obtain ⟨X, hX, hc, hr, rfl⟩ := (finish_ok_iff (Nm := Nm) (Build := Build)).1 h
  exact ⟨_, (finish_ok_iff (Nm := Nm) (Build := Build)).2 ⟨X, hX, hc, hr, rfl⟩, rfl, rfl⟩

/-- **Renaming the directly composed definitions builds the same net** (line 3 of the
reference): the same places, transitions, terminal places and correspondences. -/
theorem ref_mod026_line3 : mod026_line3 (buildScript (A := A) Nm tyOf Build Mg) := by
  intro ops ops' c h hr
  obtain ⟨b, hb, hf⟩ := buildScript_ok_iff.1 h
  obtain ⟨k', hk'⟩ := script_renamesDirect hr hb []
  obtain ⟨c', hc', h1, h2⟩ := finish_withContrib hf k'
  exact ⟨c', buildScript_ok_iff.2 ⟨_, hk', hc'⟩, h1, h2⟩

end Builder

/-- Line 4 of the reference: binding keeps the map. -/
theorem ref_mod026_line4 {N A : Type} : mod026_line4 (composedRebind (N := N) (A := A)) :=
  fun _ _ => rfl

/-- **The reference build script and binding meet MOD-026 for every parameter**: every naming
model, token type map, transition check and channel merge. -/
theorem mod026_buildScript {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) : MOD_026 Nm (buildScript Nm tyOf Build Mg) composedRebind :=
  ⟨ref_mod026_line1, ref_mod026_line2, ref_mod026_line3, ref_mod026_line4⟩

/-- ✓ **The reference build script and binding meet MOD-026**, for every naming model. Composing `s/one` (places `pipe`, `a`, transition
`t1`) and `two` (places `pipe`, `b`, transition `t2`) directly records `a` and `t1` under `s_one`
and `b` and `t2` under `two`, so they map there and the shared `pipe` has no entry; a fusion that
removes `a` drops its entry; renaming `s/one` builds the same net; binding actions keeps the
map. -/
@[evidence holds MOD_026]
theorem MOD_026_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N) :
    MOD_026 Nm (buildScript (A := A) Nm (fun _ : N => ()) refBuild (fun c _ => .ok c))
      composedRebind :=
  mod026_buildScript Nm _ _ _

end Libpetri.Reference

/-! ## Consequences for every model -/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

section Consequences

variable {N A : Type}

/-- **The resolution reads only the set of records** (AC4 at the level of the resolution): for
every model of MOD-026 (resolution), two record lists with the same records, in any order and
with any repetitions, resolve every name alike. -/
theorem mod026_resolve_congr {res : List (String × String) → String → Option String}
    (h : MOD_026_resolve res) {c c' : List (String × String)} (hc : ∀ e, e ∈ c ↔ e ∈ c')
    (n : String) : res c n = res c' n := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hex : ∃ s, (n, s) ∈ c
  · obtain ⟨s, hs⟩ := hex
    by_cases hall : ∀ s', (n, s') ∈ c → s' = s
    · rw [h1 c n s hs hall, h1 c' n s ((hc _).1 hs) fun s' h' => hall s' ((hc _).2 h')]
    · obtain ⟨s', hns⟩ := Classical.not_forall.1 hall
      obtain ⟨hs', hne⟩ := Classical.not_imp.1 hns
      rw [h2 c n s' s (hs') hs hne, h2 c' n s' s ((hc _).1 hs') ((hc _).1 hs) hne]
  · have hno : ∀ s, (n, s) ∉ c := fun s hs => hex ⟨s, hs⟩
    rw [h3 c n hno, h3 c' n fun s hs => hno s ((hc _).2 hs)]

/-- Two models of MOD-026 (resolution) agree on every record list and every name. -/
theorem mod026_resolve_agree {res res' : List (String × String) → String → Option String}
    (h : MOD_026_resolve res) (h' : MOD_026_resolve res') (c : List (String × String))
    (n : String) : res c n = res' c n := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨g1, g2, g3⟩ := h'
  by_cases hex : ∃ s, (n, s) ∈ c
  · obtain ⟨s, hs⟩ := hex
    by_cases hall : ∀ s', (n, s') ∈ c → s' = s
    · rw [h1 c n s hs hall, g1 c n s hs hall]
    · obtain ⟨s', hns⟩ := Classical.not_forall.1 hall
      obtain ⟨hs', hne⟩ := Classical.not_imp.1 hns
      rw [h2 c n s' s hs' hs hne, g2 c n s' s hs' hs hne]
  · have hno : ∀ s, (n, s) ∉ c := fun s hs => hex ⟨s, hs⟩
    rw [h3 c n hno, g3 c n hno]

/-- **The three lines fix the resolution**: every model of MOD-026 (resolution) is `memberOf`. -/
theorem mod026_resolve_unique {res : List (String × String) → String → Option String}
    (h : MOD_026_resolve res) : res = memberOf :=
  funext fun c => funext fun n => mod026_resolve_agree h MOD_026_resolve_reference c n

/-- **The builder's map is the resolution block's resolution.** For every model `res` of
MOD-026 (resolution), line 1 of MOD-026 says exactly that, off the fused-away names, the map of a
built net is `res` applied to the records of the script. So the resolution's three sentences are
what the builder's sentence on the membership mapping refers to. -/
theorem mod026_line1_iff_resolve {res : List (String × String) → String → Option String}
    (hres : MOD_026_resolve res) (Nm : Naming N) (S : ScriptFn N A) :
    mod026_line1 Nm S ↔ ∀ (ops : List (Op N A)) (c : ComposedNet N A) (n : String),
      S ops = .ok c → ¬ FusedAway Nm ops n → c.member n = res (scriptRecords Nm ops) n := by
  rw [mod026_resolve_unique hres]
  constructor
  · intro h ops c n hc hn
    apply Option.ext
    intro s
    rw [h ops c n s hc hn, memberOf_eq_some_iff]
    rfl
  · intro h ops c n s hc hn
    rw [h ops c n hc hn, memberOf_eq_some_iff]
    rfl

/-- **The map reads only the set of records and the fused-away names**: for every model of
MOD-026, two scripts that build, record the same records (in any order) and fuse away the same
name give that name the same entry. -/
theorem mod026_member_congr {Nm : Naming N} {S : ScriptFn N A} {Rb : RebindFn N A}
    (h : MOD_026 Nm S Rb) {ops ops' : List (Op N A)} {c c' : ComposedNet N A}
    (hc : S ops = .ok c) (hc' : S ops' = .ok c') (n : String)
    (hr : ∀ e, e ∈ scriptRecords Nm ops ↔ e ∈ scriptRecords Nm ops')
    (hf : FusedAway Nm ops n ↔ FusedAway Nm ops' n) : c.member n = c'.member n := by
  obtain ⟨h1, h2, -, -⟩ := h
  by_cases hn : FusedAway Nm ops n
  · rw [h2 ops c n hc hn, h2 ops' c' n hc' (hf.1 hn)]
  · have hn' : ¬ FusedAway Nm ops' n := fun x => hn (hf.2 x)
    apply Option.ext
    intro s
    rw [h1 ops c n s hc hn, h1 ops' c' n s hc' hn']
    unfold MemberOf
    simp only [hr]

/-- **AC4: order does not matter.** For every model of MOD-026, two scripts that are
reorderings of each other (for example two direct compositions in opposite orders) and both
build have the same membership map. -/
theorem mod026_perm {Nm : Naming N} {S : ScriptFn N A} {Rb : RebindFn N A}
    (h : MOD_026 Nm S Rb) {ops ops' : List (Op N A)} (hp : ops.Perm ops') {c c' : ComposedNet N A}
    (hc : S ops = .ok c) (hc' : S ops' = .ok c') : c.member = c'.member := by
  funext n
  have hr : (scriptRecords Nm ops).Perm (scriptRecords Nm ops') := hp.flatMap_right _
  have hf : (scriptFusions ops).Perm (scriptFusions ops') := hp.flatMap_right _
  refine mod026_member_congr h hc hc' n (fun e => hr.mem_iff) ?_
  unfold FusedAway
  simp only [hf.mem_iff]

/-- **AC3: no direct composition, no entry.** For every model of MOD-026, a script with no
direct composition (a flat net, or a net built by instance composition) builds a net whose
membership map is empty. -/
theorem mod026_noDirect {Nm : Naming N} {S : ScriptFn N A} {Rb : RebindFn N A}
    (h : MOD_026 Nm S Rb) {ops : List (Op N A)} (hops : ∀ op ∈ ops, ∀ D, op ≠ .composeDirect D)
    {c : ComposedNet N A} (hc : S ops = .ok c) (n : String) : c.member n = none := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hr : scriptRecords Nm ops = [] := by
    simp only [scriptRecords, List.flatMap_eq_nil_iff]
    intro op hop
    cases op with
    | composeDirect D => exact absurd rfl (hops _ hop D)
    | _ => rfl
  by_cases hn : FusedAway Nm ops n
  · exact h2 ops c n hc hn
  · cases hm : c.member n with
    | none => rfl
    | some s =>
      have := ((h1 ops c n s hc hn).1 hm).1
      rw [hr] at this
      cases this

/-- `slashFree` leaves no `/`. -/
theorem slashFree_noSlash (s : String) : '/' ∉ (slashFree s).toList := by
  simp only [slashFree, String.toList_ofList, List.mem_map, not_exists, not_and]
  intro c _
  split <;> simp_all

/-- **AC6: no entry contains `/`.** For every model of MOD-026, every entry of the membership map
of a built net is a recorded name, `/`-free. -/
theorem mod026_slashFree {Nm : Naming N} {S : ScriptFn N A} {Rb : RebindFn N A}
    (h : MOD_026 Nm S Rb) {ops : List (Op N A)} {c : ComposedNet N A} (hc : S ops = .ok c)
    {n s : String} (hm : c.member n = some s) : '/' ∉ s.toList := by
  obtain ⟨h1, h2, -, -⟩ := h
  by_cases hn : FusedAway Nm ops n
  · rw [h2 ops c n hc hn] at hm; cases hm
  · have hrec := ((h1 ops c n s hc hn).1 hm).1
    simp only [scriptRecords, List.mem_flatMap] at hrec
    obtain ⟨op, -, hop⟩ := hrec
    cases op with
    | composeDirect D =>
      simp only [Op.records, directRecords, List.mem_append, List.mem_map, Prod.mk.injEq] at hop
      rcases hop with ⟨x, -, -, rfl⟩ | ⟨d, -, -, rfl⟩ <;> exact slashFree_noSlash _
    | _ => simp [Op.records] at hop

end Consequences

end Libpetri.Spec

/-! ## Worked examples -/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec

section Examples

/-- The reference channel merge of the examples. -/
def mod026Mg : MergeFn String Unit :=
  refMerge refBuild (seqAct fun a _ => a) (fun _ _ => .ok none)

/-- The entries of `pipe`, `a`, `t1`, `b`, `t2` and `z` in a composed net. -/
def mod026View (c : ComposedNet String Unit) : List (Option String) :=
  ["pipe", "a", "t1", "b", "t2", "z"].map c.member

/-- The flat net of the examples: `t` from `p` to `q`. -/
def mod026Flat : List (Op String Unit) :=
  [.place "p", .trans (buildExDef "t" [⟨"p", .one⟩] (some (.place "q")))]

set_option maxRecDepth 20000 in
/-- ✓ **Every line of MOD-026 is exercised by the reference.** Composing `s/one` (places `pipe`
and `a`, transition `t1` from `a` to `pipe`) and `two` (places `pipe` and `b`, transition `t2`
from `pipe` to `b`) directly: `a` and `t1` map to `s_one` (the `/` written `_`), `b` and `t2` to
`two`, the shared `pipe` and the unknown `z` have no entry (AC1, AC2, AC6, line 1). The other
order gives the same map (AC4). A flat net and a net built by instance composition have no entry
(AC3). Declaring the fusion set `[b, a]` removes `a`: its entry is gone while the first member `b`
keeps `two` (AC5, line 2). Renaming `s/one` to `x` builds the same transitions (line 3). Binding
keeps the map (line 4). -/
@[evidence nonvacuous MOD_026]
theorem MOD_026_nonvacuous :
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.composeDirect buildExOne, .composeDirect buildExTwo]).toOption.map mod026View =
      some [none, some "s_one", some "s_one", some "two", some "two", none] ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.composeDirect buildExTwo, .composeDirect buildExOne]).toOption.map mod026View =
      some [none, some "s_one", some "s_one", some "two", some "two", none] ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg mod026Flat).toOption.map
        (fun c => ["p", "t", "q"].map c.member) = some [none, none, none] ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.compose buildExInst [("in", "A_IN")] []]).toOption.map
        (fun c => ["answer/work", "answer/OUT", "A_IN"].map c.member) = some [none, none, none] ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.composeDirect buildExOne, .composeDirect buildExTwo, .fuse ⟨"f", ["b", "a"]⟩]).toOption.map
        mod026View = some [none, none, some "s_one", some "two", some "two", none] ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        ([.composeDirect buildExOne, .composeDirect buildExTwo].map
          (Op.renameDirect fun s => if s = "s/one" then "x" else s))).toOption.map
        (fun c => (c.trans.map (·.core.name), mod026View c)) =
      some (["t1", "t2"], [none, some "x", some "x", some "two", some "two", none]) ∧
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.composeDirect buildExOne]).toOption.map
        (fun c => mod026View (composedRebind c fun _ => some .passthrough)) =
      some [some "s_one", some "s_one", some "s_one", none, none, none] := by
  decide

set_option maxRecDepth 20000 in
/-- **A set that lists its first member again keeps that member's entry** (lines 1 and 2, AC5).
With the fusion set `[a, b, a]` the place `b` is fused into `a`: `b` loses its entry and `a` keeps
`s_one`, since `a` is the set's first member. A wrong builder that treats every later position as
non-canonical (the behaviour RD-25 recorded) drops the entry of `a` too. -/
theorem mod026_dupCanonical_kept :
    (buildScript strNaming (fun _ => ()) refBuild mod026Mg
        [.composeDirect buildExOne, .composeDirect buildExTwo, .fuse ⟨"f", ["a", "b", "a"]⟩]).toOption.map
        mod026View = some [none, some "s_one", some "s_one", none, some "two", none] := by
  decide

/-- ✓ **The resolution has cases of every kind.** With the records `(pipe, A)`, `(pipe, B)`,
`(a, A)` and `(a, A)`: `a` is recorded under `A` only (twice) and resolves to `A`; `pipe` is
recorded under two subnets and has no entry; `z` is not recorded and has no entry. -/
@[evidence nonvacuous MOD_026_resolve]
theorem MOD_026_resolve_nonvacuous :
    let c := [("pipe", "A"), ("pipe", "B"), ("a", "A"), ("a", "A")]
    (memberOf c "a", memberOf c "pipe", memberOf c "z") = (some "A", none, none) := by
  decide

end Examples

end Libpetri.Reference

/-! ## Wrong readings and wrong models -/

namespace Libpetri.Spec

section Mutants

variable {N A : Type}

/-- The records of a script with each definition's name as written, `/` kept (the wrong reading
of AC6). -/
def rawRecords (Nm : Naming N) (ops : List (Op N A)) : List (String × String) :=
  ops.flatMap fun op => match op with
    | .composeDirect S => S.places.map (fun x => (Nm.name x, S.name)) ++
        S.defs.map fun d => (d.core.name, S.name)
    | _ => []

/-- Mutant reading: MOD-026 without line 1, so the map need not hold the records' resolution. -/
def MOD_026_mutant_noRecords (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) : Prop :=
  mod026_line2 Nm S ∧ mod026_line3 S ∧ mod026_line4 Rb

/-- Mutant reading of line 1 with the definition's name recorded as written, `/` kept. Lines 2
to 4 as in MOD-026. -/
def MOD_026_mutant_rawName (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) : Prop :=
  (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n s : String), S ops = .ok c →
    ¬ FusedAway Nm ops n → (c.member n = some s ↔ MemberOf (rawRecords Nm ops) n s)) ∧
  mod026_line2 Nm S ∧ mod026_line3 S ∧ mod026_line4 Rb

/-- Mutant reading: MOD-026 without line 2, so fusion may leave the entry of a removed place. -/
def MOD_026_mutant_noDrop (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) : Prop :=
  (∀ (ops : List (Op N A)) (c : ComposedNet N A) (n s : String), S ops = .ok c →
    (c.member n = some s ↔ MemberOf (scriptRecords Nm ops) n s)) ∧
  mod026_line3 S ∧ mod026_line4 Rb

/-- Mutant reading: MOD-026 without line 3, so the definitions' names may change the net. -/
def MOD_026_mutant_noRename (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) : Prop :=
  mod026_line1 Nm S ∧ mod026_line2 Nm S ∧ mod026_line4 Rb

/-- Mutant reading of line 3 with one renaming function for every call and the correspondences
not compared. One function can give two definitions one name but never two names to definitions
that had one, so a build may fail once two definitions of one name are told apart. Lines 1, 2
and 4 as in MOD-026. -/
def MOD_026_mutant_uniformRename (Nm : Naming N) (S : ScriptFn N A) (Rb : RebindFn N A) : Prop :=
  mod026_line1 Nm S ∧ mod026_line2 Nm S ∧
  (∀ (f : String → String) (ops : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
    ∃ c', S (ops.map (Op.renameDirect f)) = .ok c' ∧ c'.toBuiltNet = c.toBuiltNet) ∧
  mod026_line4 Rb

/-- Mutant reading: MOD-026 without line 4, so binding may lose the map. -/
def MOD_026_mutant_noRebind (Nm : Naming N) (S : ScriptFn N A) (_Rb : RebindFn N A) : Prop :=
  mod026_line1 Nm S ∧ mod026_line2 Nm S ∧ mod026_line3 S

/-- Mutant reading of the resolution without its line 2: a node recorded under two subnets may
get an entry. -/
def MOD_026_resolve_mutant_noShared (res : List (String × String) → String → Option String) :
    Prop :=
  mod026r_line1 res ∧ mod026r_line3 res

/-- Mutant reading of the resolution without its line 1: a node recorded under one subnet need
not map to it. -/
def MOD_026_resolve_mutant_noSole (res : List (String × String) → String → Option String) :
    Prop :=
  mod026r_line2 res ∧ mod026r_line3 res

/-- Mutant reading of the resolution without its line 3: a node without a record may get an
entry. -/
def MOD_026_resolve_mutant_noRecord (res : List (String × String) → String → Option String) :
    Prop :=
  mod026r_line1 res ∧ mod026r_line2 res

end Mutants

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec

section WrongModels

variable {N A : Type}

/-- A build script with the map of every built net replaced by `g` applied to the script. -/
def withMember (S : ScriptFn N A) (g : List (Op N A) → String → Option String) : ScriptFn N A :=
  fun ops => (S ops).map fun c => { c with member := g ops }

theorem withMember_ok {S : ScriptFn N A} {g : List (Op N A) → String → Option String}
    {ops : List (Op N A)} {c : ComposedNet N A} (h : withMember S g ops = .ok c) :
    ∃ c₀, S ops = .ok c₀ ∧ c = { c₀ with member := g ops } := by
  obtain ⟨c₀, h₀, rfl⟩ := except_map_ok_iff.1 h
  exact ⟨c₀, h₀, rfl⟩

/-- Replacing the map keeps line 3. -/
theorem withMember_line3 {S : ScriptFn N A} {g : List (Op N A) → String → Option String}
    (h : mod026_line3 S) : mod026_line3 (withMember S g) := by
  intro ops ops' c hc hr
  obtain ⟨c₀, h₀, rfl⟩ := withMember_ok hc
  obtain ⟨c₁, h₁, e₁, e₂⟩ := h ops ops' c₀ h₀ hr
  exact ⟨{ c₁ with member := g ops' }, by simp only [withMember, h₁, Except.map], e₁, e₂⟩

/-- The membership entry is the resolution rule. -/
theorem memberOf_iff_MemberOf {c : List (String × String)} {n s : String} :
    memberOf c n = some s ↔ MemberOf c n s := memberOf_eq_some_iff

/-- A computation whose view is `some y` succeeded with a result of that view. -/
theorem mod026_ok_of_map {α β : Type} {e : Except String α} {f : α → β} {y : β}
    (h : e.toOption.map f = some y) : ∃ x, e = .ok x ∧ f x = y := by
  cases e with
  | error m => simp [Except.toOption] at h
  | ok x => exact ⟨x, rfl, by simpa [Except.toOption] using h⟩

/-- A computation that failed has no result. -/
theorem mod026_not_ok {α : Type} {e : Except String α} (h : e.toOption.isNone = true) (x : α) :
    e ≠ .ok x := by
  rintro rfl; simp [Except.toOption] at h

end WrongModels

section Concrete

/-- The reference build script of the examples. -/
abbrev mod026Ref : ScriptFn String Unit := buildScript strNaming (fun _ => ()) refBuild mod026Mg

/-- Wrong: a build script that records no membership at all. -/
def emptyMemberScript : ScriptFn String Unit := withMember mod026Ref fun _ _ => none

/-- Wrong: a build script that records the definition's name with `/` kept. -/
def rawNameScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops n =>
    if FusedAway strNaming ops n then none else memberOf (rawRecords strNaming ops) n

/-- Wrong: a build script that keeps the entries of the places fusion removed. -/
def keepFusedScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops => memberOf (scriptRecords strNaming ops)

/-- Whether a call composes a definition named `x` directly. -/
def composesX : Op String Unit → Bool
  | .composeDirect S => S.name == "x"
  | _ => false

/-- Wrong: a build script that rejects a definition named `x`, so a name changes the net. -/
def nameSensitiveScript : ScriptFn String Unit := fun ops =>
  if ops.any composesX then .error "x" else mod026Ref ops

/-- Wrong: a binding that loses the map. -/
def dropRebind : RebindFn String Unit := fun c r =>
  { composedRebind c r with member := fun _ => none }

/-- Wrong: a build script whose map gives every recorded node its first recorded subnet, so a
shared place gets an owner and the order of the calls decides which. -/
def firstOwnerScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops n =>
    ((scriptRecords strNaming ops).find? (·.1 == n)).map (·.2)

/-- The records an instance composition would make under its prefix. -/
def instRecords (ops : List (Op String Unit)) : List (String × String) :=
  ops.flatMap fun op => match op with
    | .compose I _ _ => I.places.map (fun x => (x, I.pfx)) ++ I.defs.map fun d => (d.core.name, I.pfx)
    | .composeAuto I _ => I.places.map (fun x => (x, I.pfx)) ++ I.defs.map fun d => (d.core.name, I.pfx)
    | _ => []

/-- Wrong: a build script that also records instance composition under the instance's prefix. -/
def instanceRecordsScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops => memberOf (scriptRecords strNaming ops ++ instRecords ops)

/-- Whether a script declares the place `n` itself (a host declaration). -/
def hostDeclares (ops : List (Op String Unit)) (n : String) : Bool :=
  ops.any fun op => match op with
    | .place p => p == n
    | _ => false

/-- Wrong: a build script that skips the record of a body place the host declared itself. -/
def hostSkipScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops n =>
    if FusedAway strNaming ops n then none
    else memberOf ((scriptRecords strNaming ops).filter fun e => !hostDeclares ops e.1) n

/-- The records of a script's direct compositions with their body places only. -/
def placeRecords (ops : List (Op String Unit)) : List (String × String) :=
  ops.flatMap fun op => match op with
    | .composeDirect S => S.places.map fun x => (x, slashFree S.name)
    | _ => []

/-- Wrong: a build script that records body places and no body transitions. -/
def placesOnlyScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops n =>
    if FusedAway strNaming ops n then none else memberOf (placeRecords ops) n

/-- The records a host declaration would make under the name `host`. -/
def hostRecords (ops : List (Op String Unit)) : List (String × String) :=
  ops.flatMap fun op => match op with
    | .place p => [(p, "host")]
    | .trans d => [(d.core.name, "host")]
    | _ => []

/-- Wrong: a build script that also records the host's own places and transitions under `host`. -/
def hostRecordsScript : ScriptFn String Unit :=
  withMember mod026Ref fun ops => memberOf (scriptRecords strNaming ops ++ hostRecords ops)

/-- Two direct compositions whose definitions have different names and share a place name. -/
def shareClash : Op String Unit → Op String Unit → Bool
  | .composeDirect S₁, .composeDirect S₂ =>
      S₁.name != S₂.name && S₁.places.any (fun p => S₂.places.contains p)
  | _, _ => false

/-- Wrong: a build script that rejects a place shared by two definitions of different names
(MOD-025's transition-name check wrongly applied to places), otherwise the reference. -/
def strictShareScript : ScriptFn String Unit := fun ops =>
  if ops.any (fun o₁ => ops.any (shareClash o₁)) then .error "place shared by two subnets"
  else mod026Ref ops

/-- `s/one` and a copy of `two` renamed to `s/one`: both definitions have one name. -/
def mod026TwoSame : List (Op String Unit) :=
  [.composeDirect buildExOne, .composeDirect { buildExTwo with name := "s/one" }]

/-- Wrong: a resolution that gives a node its first recorded subnet. -/
def firstOwner (c : List (String × String)) (n : String) : Option String :=
  (c.find? (·.1 == n)).map (·.2)

/-- Wrong: a resolution that gives a node without a record the entry `?`. -/
def defaultOwner (c : List (String × String)) (n : String) : Option String :=
  if c.any (·.1 == n) then memberOf c n else some "?"

/-- The two composed subnets of the examples. -/
def mod026Two : List (Op String Unit) := [.composeDirect buildExOne, .composeDirect buildExTwo]

/-- The two subnets with the fusion set `[b, a]`, which removes `a`. -/
def mod026Fused : List (Op String Unit) := mod026Two ++ [.fuse ⟨"f", ["b", "a"]⟩]

/-- A composed net with one entry for every name. -/
def mod026Marked : ComposedNet String Unit :=
  { places := [], trans := [], terminals := [], corrs := [], member := fun _ => some "s" }

theorem mod026Ref_line1 : mod026_line1 strNaming mod026Ref := ref_mod026_line1
theorem mod026Ref_line2 : mod026_line2 strNaming mod026Ref := ref_mod026_line2
theorem mod026Ref_line3 : mod026_line3 mod026Ref := ref_mod026_line3

set_option maxRecDepth 20000 in
/-- ✗ **A build that records nothing breaks line 1.** Composing `s/one` and `two` directly with
a build that keeps no membership leaves `a` without an entry, while `a` is recorded under
`s_one` only; it keeps lines 2 to 4. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_noRecords_killed :
    MOD_026_mutant_noRecords strNaming emptyMemberScript composedRebind ∧
      ¬ MOD_026 strNaming emptyMemberScript composedRebind := by
  refine ⟨⟨?_, withMember_line3 mod026Ref_line3, ref_mod026_line4⟩, ?_⟩
  · intro ops c n hc _
    obtain ⟨c₀, -, rfl⟩ := withMember_ok hc
    rfl
  · intro h
    obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "a")
      (show (emptyMemberScript mod026Two).toOption.map (fun c => c.member "a") = some none by
        decide)
    have := (h.1 mod026Two c "a" "s_one" hc (by decide)).2
      (memberOf_iff_MemberOf.1 (by decide))
    rw [hv] at this; cases this

set_option maxRecDepth 20000 in
/-- ✗ **Keeping the `/` breaks line 1 (AC6).** A build that records `s/one` as written maps `a`
to `s/one`, while the records name `s_one`; it keeps lines 2 to 4 and its own reading of line 1. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_rawName_killed :
    MOD_026_mutant_rawName strNaming rawNameScript composedRebind ∧
      ¬ MOD_026 strNaming rawNameScript composedRebind := by
  refine ⟨⟨?_, ?_, withMember_line3 mod026Ref_line3, ref_mod026_line4⟩, ?_⟩
  · intro ops c n s hc hn
    obtain ⟨c₀, -, rfl⟩ := withMember_ok hc
    simp only [hn, if_false]
    exact memberOf_iff_MemberOf
  · intro ops c n hc hn
    obtain ⟨c₀, -, rfl⟩ := withMember_ok hc
    simp only [hn, if_true]
  · intro h
    obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "a")
      (show (rawNameScript mod026Two).toOption.map (fun c => c.member "a") = some (some "s/one") by
        decide)
    have := memberOf_iff_MemberOf.2 ((h.1 mod026Two c "a" "s/one" hc (by decide)).1 hv)
    exact absurd this (by decide)

set_option maxRecDepth 20000 in
/-- ✗ **Keeping a fused-away entry breaks line 2 (AC5).** With the fusion set `[b, a]` the place
`a` is gone, but a build that keeps its entry still maps `a` to `s_one`; it keeps the resolution
of the records and lines 3 and 4. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_noDrop_killed :
    MOD_026_mutant_noDrop strNaming keepFusedScript composedRebind ∧
      ¬ MOD_026 strNaming keepFusedScript composedRebind := by
  refine ⟨⟨?_, withMember_line3 mod026Ref_line3, ref_mod026_line4⟩, ?_⟩
  · intro ops c n s hc
    obtain ⟨c₀, -, rfl⟩ := withMember_ok hc
    exact memberOf_iff_MemberOf
  · intro h
    obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "a")
      (show (keepFusedScript mod026Fused).toOption.map (fun c => c.member "a") =
        some (some "s_one") by decide)
    have := h.2.1 mod026Fused c "a" hc (by decide)
    rw [hv] at this; cases this

set_option maxRecDepth 20000 in
/-- ✗ **A name that changes the net breaks line 3.** A build that rejects a definition named `x`
builds `s/one` but not the same script with `s/one` renamed to `x`; it keeps lines 1, 2 and 4. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_noRename_killed :
    MOD_026_mutant_noRename strNaming nameSensitiveScript composedRebind ∧
      ¬ MOD_026 strNaming nameSensitiveScript composedRebind := by
  refine ⟨⟨?_, ?_, ref_mod026_line4⟩, ?_⟩
  · intro ops c n s hc hn
    unfold nameSensitiveScript at hc
    split at hc
    · cases hc
    · exact mod026Ref_line1 ops c n s hc hn
  · intro ops c n hc hn
    unfold nameSensitiveScript at hc
    split at hc
    · cases hc
    · exact mod026Ref_line2 ops c n hc hn
  · intro h
    obtain ⟨c, hc, -⟩ := mod026_ok_of_map (f := fun _ => ())
      (show (nameSensitiveScript [.composeDirect buildExOne]).toOption.map (fun _ => ()) =
        some () by decide)
    obtain ⟨c', hc', -⟩ := h.2.2.1 _ _ c hc (renamesDirect_map (fun _ => "x") _)
    exact mod026_not_ok (by decide) c' hc'

/-- ✗ **A binding that loses the map breaks line 4.** On a net whose map gives every name the
entry `s`, the binding that drops the map returns a net without entries; the reference build
keeps lines 1 to 3. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_noRebind_killed :
    MOD_026_mutant_noRebind strNaming mod026Ref dropRebind ∧
      ¬ MOD_026 strNaming mod026Ref dropRebind := by
  refine ⟨⟨mod026Ref_line1, mod026Ref_line2, mod026Ref_line3⟩, ?_⟩
  intro h
  have := congrFun (h.2.2.2 mod026Marked fun _ => none) "a"
  cases this

set_option maxRecDepth 20000 in
/-- ✗ **A first-come owner breaks line 1 (AC2, AC4).** Composing `s/one` then `two`, a build
that gives each node its first recorded subnet maps the shared place `pipe` to `s_one`, although
`pipe` is recorded under two subnets (the other order would give `two`). -/
@[evidence forbids MOD_026]
theorem MOD_026_forbids_firstOwner : ¬ MOD_026 strNaming firstOwnerScript composedRebind := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "pipe")
    (show (firstOwnerScript mod026Two).toOption.map (fun c => c.member "pipe") =
      some (some "s_one") by decide)
  have := memberOf_iff_MemberOf.2 ((h.1 mod026Two c "pipe" "s_one" hc (by decide)).1 hv)
  exact absurd this (by decide)

set_option maxRecDepth 20000 in
/-- ✗ **Recording instance composition breaks line 1 (rule 4, AC3).** Composing the instance
`answer` with a build that records its nodes under the prefix maps `answer/work` to `answer`,
although no `compose(SubnetDef)` call recorded it. -/
@[evidence forbids MOD_026]
theorem MOD_026_forbids_instanceRecords :
    ¬ MOD_026 strNaming instanceRecordsScript composedRebind := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "answer/work")
    (show (instanceRecordsScript [.compose buildExInst [("in", "A_IN")] []]).toOption.map
      (fun c => c.member "answer/work") = some (some "answer") by decide)
  have := memberOf_iff_MemberOf.2
    ((h.1 [.compose buildExInst [("in", "A_IN")] []] c "answer/work" "answer" hc (by decide)).1 hv)
  exact absurd this (by decide)

set_option maxRecDepth 20000 in
/-- ✗ **Skipping a place the host declared first breaks line 1 (rule 1).** The host declares the
place `a`, then composes `s/one`, whose body has `a` too. The body place is recorded under
`s_one` all the same, so `a` must map to `s_one`; a build that skips it because the builder
already held `a` leaves `a` without an entry. -/
@[evidence forbids MOD_026]
theorem MOD_026_forbids_hostSkip : ¬ MOD_026 strNaming hostSkipScript composedRebind := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "a")
    (show (hostSkipScript [.place "a", .composeDirect buildExOne]).toOption.map
      (fun c => c.member "a") = some none by decide)
  have := (h.1 [.place "a", .composeDirect buildExOne] c "a" "s_one" hc (by decide)).2
    (memberOf_iff_MemberOf.1 (by decide))
  rw [hv] at this; cases this

set_option maxRecDepth 20000 in
/-- ✗ **Recording places only breaks line 1 (rule 1, AC1).** Composing `s/one` and `two`
directly, the transition `t1` is recorded under `s_one` only and must map there; a build that
records body places and no body transitions leaves `t1` without an entry. -/
@[evidence forbids MOD_026]
theorem MOD_026_forbids_placesOnly : ¬ MOD_026 strNaming placesOnlyScript composedRebind := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "t1")
    (show (placesOnlyScript mod026Two).toOption.map (fun c => c.member "t1") = some none by
      decide)
  have := (h.1 mod026Two c "t1" "s_one" hc (by decide)).2
    (memberOf_iff_MemberOf.1 (by decide))
  rw [hv] at this; cases this

set_option maxRecDepth 20000 in
/-- ✗ **Recording the host's own nodes breaks line 1 (rule 4, AC3).** In the flat net with place
`p` and transition `t`, nothing is composed, so nothing is recorded and `p` must have no entry; a
build that records host declarations under the name `host` maps `p` to `host`. -/
@[evidence forbids MOD_026]
theorem MOD_026_forbids_hostRecords : ¬ MOD_026 strNaming hostRecordsScript composedRebind := by
  intro h
  obtain ⟨c, hc, hv⟩ := mod026_ok_of_map (f := fun c : ComposedNet String Unit => c.member "p")
    (show (hostRecordsScript mod026Flat).toOption.map (fun c => c.member "p") =
      some (some "host") by decide)
  have := memberOf_iff_MemberOf.2 ((h.1 mod026Flat c "p" "host" hc (by decide)).1 hv)
  exact absurd this (by decide)

/-- No call of a script renamed through one function shares a place between definitions of
different names unless the script did: one function can give two names one name, never split
one name into two. -/
theorem shareClash_renameDirect (f : String → String) (o₁ o₂ : Op String Unit)
    (h : shareClash (o₁.renameDirect f) (o₂.renameDirect f) = true) : shareClash o₁ o₂ = true := by
  cases o₁ <;> cases o₂ <;> simp_all [shareClash, Op.renameDirect]
  rename_i S₁ S₂
  obtain ⟨hne, -⟩ := h
  intro e; exact hne (by rw [e])

set_option maxRecDepth 20000 in
/-- **Two definitions with one recorded name are one subnet** (AC2's qualification). Composing
`s/one` and a copy of `two` also named `s/one`, the place `pipe` is recorded twice under
`s_one` and maps there; with the second definition named `two` it has no entry. -/
theorem mod026_sameName_shared :
    (mod026Ref mod026TwoSame).toOption.map (·.member "pipe") = some (some "s_one") ∧
    (mod026Ref mod026Two).toOption.map (·.member "pipe") = some none := by
  decide

theorem strictShare_ok {ops : List (Op String Unit)} {c : ComposedNet String Unit}
    (h : strictShareScript ops = .ok c) : mod026Ref ops = .ok c := by
  unfold strictShareScript at h
  split at h
  · cases h
  · exact h

set_option maxRecDepth 20000 in
/-- ✗ **Rejecting a place two subnets share breaks line 3 (AC1, AC2).** Composing `s/one` and a
copy of `two` also named `s/one` builds: both record `pipe` under one name. Naming the copy
`two` again changes only a definition name, so that build must succeed too, as AC1 and AC2
need; a build that rejects a place shared by definitions of different names fails it. A
renaming through one function for every call never tells two definitions of one name apart, so
the weaker reading accepts this build. -/
@[evidence mutant MOD_026]
theorem MOD_026_mutant_uniformRename_killed :
    MOD_026_mutant_uniformRename strNaming strictShareScript composedRebind ∧
      ¬ MOD_026 strNaming strictShareScript composedRebind := by
  refine ⟨⟨fun ops c n s hc hn => mod026Ref_line1 ops c n s (strictShare_ok hc) hn,
    fun ops c n hc hn => mod026Ref_line2 ops c n (strictShare_ok hc) hn, ?_, ref_mod026_line4⟩, ?_⟩
  · intro f ops c hc
    have hno : ¬ (ops.any (fun o₁ => ops.any (shareClash o₁))) = true := by
      intro hb; unfold strictShareScript at hc; rw [if_pos hb] at hc; cases hc
    obtain ⟨c', h1, h2, -⟩ :=
      mod026Ref_line3 ops _ c (strictShare_ok hc) (renamesDirect_map f ops)
    refine ⟨c', ?_, h2⟩
    unfold strictShareScript
    rw [if_neg]
    · exact h1
    · intro hb
      apply hno
      simp only [List.any_map, List.any_eq_true, Function.comp] at hb ⊢
      obtain ⟨o₁, h₁, o₂, h₂, hc₂⟩ := hb
      exact ⟨o₁, h₁, o₂, h₂, shareClash_renameDirect f o₁ o₂ hc₂⟩
  · intro h
    obtain ⟨c, hc, -⟩ := mod026_ok_of_map (f := fun _ => ())
      (show (strictShareScript mod026TwoSame).toOption.map (fun _ => ()) = some () by decide)
    have hr : RenamesDirect mod026TwoSame mod026Two :=
      .cons ⟨id, rfl⟩ (.cons ⟨fun _ => "two", rfl⟩ .nil)
    obtain ⟨c', hc', -⟩ := h.2.2.1 _ _ c hc hr
    exact mod026_not_ok (by decide) c' hc'

/-- ✗ **A first-come resolution breaks the resolution's line 2.** With the records `(p, A)` and
`(p, B)`, the first-come resolution gives `p` the entry `A`, while `p` is recorded under two
subnets; it keeps lines 1 and 3. -/
@[evidence mutant MOD_026_resolve]
theorem MOD_026_resolve_mutant_noShared_killed :
    MOD_026_resolve_mutant_noShared firstOwner ∧ ¬ MOD_026_resolve firstOwner := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c n s hm hall
    unfold firstOwner
    cases hf : c.find? (·.1 == n) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf _ hm)
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have h1 := List.find?_some hf
      obtain ⟨a, b⟩ := e
      simp only [beq_iff_eq] at h1
      subst h1
      exact congrArg some (hall b he)
  · intro c n hno
    unfold firstOwner
    cases hf : c.find? (·.1 == n) with
    | none => rfl
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have h1 := List.find?_some hf
      obtain ⟨a, b⟩ := e
      simp only [beq_iff_eq] at h1
      subst h1
      exact absurd he (hno b)
  · intro h
    have := h.2.1 [("p", "A"), ("p", "B")] "p" "A" "B" (by simp) (by simp) (by decide)
    exact absurd this (by decide)

/-- ✗ **A resolution that never answers breaks the resolution's line 1.** With the record
`(a, A)`, `a` is recorded under `A` only, but the resolution that always answers nothing gives no
entry; it keeps lines 2 and 3. -/
@[evidence mutant MOD_026_resolve]
theorem MOD_026_resolve_mutant_noSole_killed :
    MOD_026_resolve_mutant_noSole (fun _ _ => none) ∧ ¬ MOD_026_resolve (fun _ _ => none) := by
  refine ⟨⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  intro h
  have := h.1 [("a", "A")] "a" "A" (by simp) (by simp)
  cases this

/-- ✗ **A default entry breaks the resolution's line 3.** With no record at all, the resolution
that answers `?` for an unrecorded node gives `z` an entry; it keeps lines 1 and 2. -/
@[evidence mutant MOD_026_resolve]
theorem MOD_026_resolve_mutant_noRecord_killed :
    MOD_026_resolve_mutant_noRecord defaultOwner ∧ ¬ MOD_026_resolve defaultOwner := by
  have hany : ∀ (c : List (String × String)) n s, (n, s) ∈ c → c.any (·.1 == n) = true :=
    fun c n s hm => List.any_eq_true.2 ⟨(n, s), hm, by simp⟩
  obtain ⟨r1, r2, -⟩ := MOD_026_resolve_reference
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c n s hm hall
    simp only [defaultOwner, hany c n s hm, if_true]
    exact r1 c n s hm hall
  · intro c n s₁ s₂ h₁ h₂ hne
    simp only [defaultOwner, hany c n s₁ h₁, if_true]
    exact r2 c n s₁ s₂ h₁ h₂ hne
  · intro h
    have := h.2.2 [] "z" (by simp)
    cases this

end Concrete

end Libpetri.Reference
