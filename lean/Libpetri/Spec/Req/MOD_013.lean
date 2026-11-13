import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Reference.ComposeBuild
import Libpetri.Spec.Req.MOD_010
import Libpetri.Spec.Req.MOD_014
import Libpetri.Spec.Text.MOD_013

set_option linter.missingDocs true

/-!
# MOD-013: Nested instantiation (`spec/11-modular-composition.md`)

MOD-013 is a pure-function requirement (kind F) over the same two parameters as [MOD-010]: an
abstract instantiation function `Inst : InstFn N A` and a naming model `Nm : Naming N` (how a
prefix renames a place). It says what instantiating a subnet definition `S` under an outer prefix
`o` does to the places and transitions that the body of `S` took over from an instance of another
definition `T` under an inner prefix `i`: the place `i/x` becomes `o/i/x`, the transition `i/t`
becomes `o/i/t`. A third line says that such a nested definition is accepted like any other: the
`/` that its body names already contain is no reason to fail.

The witness is the reference instantiation `refInst Nm` (`Reference/ComposeDef.lean`); every model
of [MOD-010] is a model of MOD-013 (`mod013_of_mod010`). Consequences for every model: the nested
name `o/i/x` is the name `x` renamed under the concatenated prefix `o/i` (`mod013_flat`, AC2),
which no single instantiation produces since `o/i` is not a valid prefix
(`mod013_concat_rejected`), and nested instances under different inner prefixes never share a
place (`mod013_nested_inj`, the naming half of AC3). The lines say what an instance holds, not
that it holds nothing more: that is the "exactly" of [MOD-010] line 3, which gives the nested
name set in both directions (`mod013_nestedSet`) and the nested form only (`mod013_ofTheForm`).
An instantiation that keeps the body places next to the renamed ones meets MOD-013 and violates
MOD-010 (`mod013_keepBody_accepted`, `mod013_keepBody_not_mod010`). The nonvacuous example runs the whole
pipeline of the runtimes' tests on the reference: instantiate `T` under `inner`, compose it into
a net with its port bound, build, wrap the net with `fromNet` ([MOD-014]), instantiate under
`outer`. Wrong instantiations are killed: one that drops the inner prefix of a place, one that
drops it from a transition, and one that refuses a body whose names contain `/`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## MOD-013: Nested Instantiation (prefix concatenation associative) -/

requirement MOD_013
  id "MOD-013"
  title "Nested Instantiation (prefix concatenation associative)"
  kind F
  scope "every instantiation of a subnet definition whose body holds places or transitions of a composed instance"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_013.s1, MOD_013.s2, MOD_013.s3
  reading "For every naming model Nm (how a prefix renames a place) and every instantiation function Inst:"
          "if Inst instantiates T under i to J and S under o to I, then for every place x of T whose renamed place Nm.pre i x is a place of J and a place of the body of S, the place Nm.pre o (Nm.pre i x) is a place of I (its name is o/i/x, by the naming law pre_name);"
          "if Inst instantiates T under i to J and S under o to I, then for every transition of T named t such that i/t names a transition of J and a transition of the body of S, o/i/t names a transition of I;"
          "if o is valid and the body of S declares no terminal place (and every port exposes a body place and every channel a body transition), Inst succeeds on S under o, whatever the names of the body of S contain. The lines do not trace the body of S back to J: S only has to hold a place equal to Nm.pre i x or a transition named i/t."
  assumes "The body of S is any subnet definition whose body holds the renamed place or transition: the runtimes build it with fromNet ([MOD-014], raised to MUST by ruling D57 (a)) over a net that composed the instance of T under i ([MOD-020]), as the nested tests of every language do (nested_instantiation_resolves_doubly_prefixed in rust/libpetri-core/tests/mod031_place_resolution.rs, autoCompose_nestedInstance_prefixesConcatenate in java/src/test/java/org/libpetri/core/AutoComposeTest.java, test_nested_instantiation_resolves_doubly_prefixed in python/tests/test_subnet_local_names.py). mod013_viaFromNet gives line 1 through every fromNet that meets MOD-014 line 6, and MOD_013_nonvacuous runs that pipeline on the reference models."
          "Which places of T reach the body of S is composition's, and the lines take it as a premise: a port place of T that S binds to a place of its own is replaced by that place ([MOD-020] item 2) and does not become o/i/x; an internal place of T that no arc names is not added by the composition ([MOD-020] clause 3); a transition of T merged with a caller transition through a channel takes the caller's name ([MOD-021]). The sentence that a subnet composing other subnets can be instantiated like any other is line 3, and the sentence on the separator at every level is lines 1 and 2. That the names i/x and i/t of the body of S are the ones the instance of T under i gave, and not places or transitions S declares itself under those names, is composition's too (MOD-020): the lines take the body of S as given and the instance J only bounds which x and t they range over."
          "Places are the abstract N, the key type of the place model (CORE-002), renamed by the naming model Nm as in MOD-010: by name in TypeScript, Rust and Python (strNaming), by name with the token type kept in Java (typedNaming). The place Nm.pre o (Nm.pre i x) is named o/i/x at every naming model by its law pre_name (mod013_name). Transition names are strings renamed by preS."
          "The associativity sentence ('Prefix concatenation is associative on names: ...') carries no MUST and is no line: it is mod013_flat, a fact about names that holds for every instantiation function, the nested name o/(i/x) being the name (o/i)/x, x renamed under the concatenated prefix o/i (preS_assoc), at every naming model. Ruling D25 (a) makes o/i an invalid prefix, so no single instantiation produces it: every model of MOD-010 rejects the prefix o/i (mod013_concat_rejected), and the markdown no longer compares with an instantiation under outer/inner."
          "MOD-013 adds no constraint beyond MOD-010: every model of MOD-010 meets all three lines (mod013_of_mod010). Lines 1 and 2 are MOD-010 line 3 read for the places and transitions a body took over from an instance, and line 3 is MOD-010 line 2 word for word; the clause 'also when names of the body contain /' explains that the formula has no premise on names. The block states the nested reading of MOD-010 that AC1 asks for and gives each nested line a mutant that is a plausible slip. Line 3 is a line of MOD-013 because AC1 says that the nested instantiation produces names, which needs it to succeed; its mutant is an instantiation that refuses a body whose names contain the separator, which the prefix check of D25 makes a plausible mistake. All three runtimes check only the prefix and the terminal places before renaming (SubnetDef::instantiate in rust/libpetri-core/src/subnet_def.rs, validatePrefix in java/src/main/java/org/libpetri/core/SubnetDef.java and in typescript/src/core/subnet-def.ts)."
          "The third quoted sentence leaves out line 3's premises that every port exposes a body place and every channel a body transition, for the reason MOD-010 gives for its line 2: they hold of every subnet definition the subnet builder accepts (MOD-006) and of every definition fromNet accepts (MOD-014), so a nested definition built either way meets them."
          "The correspondence of a nested transition (its declared places resolving to o/i/x) is MOD-031's, which cites this ID; the lines state names only."
          "AC1 (S composing T under inner, instantiated under outer, produces names of the form outer/inner/<original>) is lines 1 and 2 with line 3 for the success, and MOD_013_nonvacuous on the reference: outer/inner/x and outer/inner/t, with the bound port of T replaced by the place outer/src. That the nested items appear in that form only (no outer/x or inner/x next to outer/inner/x) is MOD-010 line 3's 'exactly': in every model of MOD-010 every place of the instance is a body place renamed under o and every transition name a body transition name renamed under o (mod013_ofTheForm)."
          "AC2 (the names of the form outer/inner/x are exactly the names inner/x the body of S holds, renamed under outer, which is x under the concatenated prefix outer/inner) has two directions. Line 1 gives the inclusion (mod013_nestedName, with mod013_flat for the concatenated reading). The converse, that the instance holds no other place named outer/inner/x, is MOD-010 line 3, not a line of this block: in every model of MOD-010, o/i/x is a place of the instance exactly when i/x is a place of the body (mod013_nestedSet). MOD-013 alone does not give it: the instantiation that keeps the body places next to the renamed ones meets all three lines and violates MOD-010 (mod013_keepBody_accepted, mod013_keepBody_not_mod010). So AC2 is MOD-013 line 1 with MOD-010 line 3 and has no mutant of its own here (skeptic correction S4 of the composition design); the rejection of a single instantiation under outer/inner is mod013_concat_rejected, from MOD-010 line 1."
          "AC3 (per-instance state isolation holds at every nesting level) is not a line of this block; it is delegated. It is MOD-012 applied to the nested definition: MOD-012 ranges over every subnet definition, nested or not, and its runtime-state half is MOD-012's: its isolation line over the firing relation (MOD_012) and its clock line over the timed relation (MOD_012_clock), both stated over every build script, so over a net that composes a nested definition too. Its naming half holds for every model of MOD-010, not of MOD-013 alone: two nested places o/i1/x and o/i2/y are one place only when i1 = i2 and x = y (mod013_nested_inj, a fact of the naming laws), and two outer instances of one definition share no name (mod010_disjoint). The instantiation that keeps the body places meets MOD-013 and gives two outer instances o1 and o2 of the nested S the shared place inner/x (mod013_keepBody_shares)."
          "The test derivation (T with an internal place x, S composing T under inner, S instantiated under outer, outer/inner/x among the renamed places) is MOD_013_nonvacuous."
  signoff "2026-11-13 a6b8a90eac14b12e ai"
  statement : ∀ {N A : Type}, Naming N → InstFn N A → Prop :=
    fun {N A} Nm Inst =>
      (∀ (T S : SubnetDef N A) i o J I, Inst T i = .ok J → Inst S o = .ok I →
        ∀ x ∈ T.places, Nm.pre i x ∈ J.places → Nm.pre i x ∈ S.places →
          Nm.pre o (Nm.pre i x) ∈ I.places) ∧
      (∀ (T S : SubnetDef N A) i o J I, Inst T i = .ok J → Inst S o = .ok I →
        ∀ d ∈ T.defs, preS i d.core.name ∈ J.defs.map (·.core.name) →
          preS i d.core.name ∈ S.defs.map (·.core.name) →
          preS o (preS i d.core.name) ∈ I.defs.map (·.core.name)) ∧
      (∀ (S : SubnetDef N A) o, ValidPrefix o → S.terminals = [] →
        (∀ q ∈ S.ports, q.place ∈ S.places) →
        (∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name)) → ∃ I, Inst S o = .ok I)

/- The pinned readable form of MOD-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_013 : {N A : Type} → Naming N → InstFn N A → Prop :=
fun {N A} Nm Inst =>
  (∀ (T S : SubnetDef N A) (i o : String) (J I : Instance N A),
      Inst T i = Except.ok J →
        Inst S o = Except.ok I →
          ∀ x ∈ T.places, Nm.pre i x ∈ J.places → Nm.pre i x ∈ S.places → Nm.pre o (Nm.pre i x) ∈ I.places) ∧
    (∀ (T S : SubnetDef N A) (i o : String) (J I : Instance N A),
        Inst T i = Except.ok J →
          Inst S o = Except.ok I →
            ∀ d ∈ T.defs,
              preS i d.core.name ∈ List.map (fun x => x.core.name) J.defs →
                preS i d.core.name ∈ List.map (fun x => x.core.name) S.defs →
                  preS o (preS i d.core.name) ∈ List.map (fun x => x.core.name) I.defs) ∧
      ∀ (S : SubnetDef N A) (o : String),
        ValidPrefix o →
          S.terminals = [] →
            (∀ q ∈ S.ports, q.place ∈ S.places) →
              (∀ c ∈ S.chans, c.trans ∈ List.map (fun x => x.core.name) S.defs) → ∃ I, Inst S o = Except.ok I
-/
#guard_msgs in #print MOD_013

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-013: a place `i/x` the outer body took over from an instance becomes `o/i/x`. -/
def mod013_line1 (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  ∀ (T S : SubnetDef N A) i o J I, Inst T i = .ok J → Inst S o = .ok I →
    ∀ x ∈ T.places, Nm.pre i x ∈ J.places → Nm.pre i x ∈ S.places →
      Nm.pre o (Nm.pre i x) ∈ I.places

/-- Line 2 of MOD-013: a transition `i/t` the outer body took over from an instance becomes
`o/i/t`. -/
def mod013_line2 (Inst : InstFn N A) : Prop :=
  ∀ (T S : SubnetDef N A) i o J I, Inst T i = .ok J → Inst S o = .ok I →
    ∀ d ∈ T.defs, preS i d.core.name ∈ J.defs.map (·.core.name) →
      preS i d.core.name ∈ S.defs.map (·.core.name) →
      preS o (preS i d.core.name) ∈ I.defs.map (·.core.name)

/-- Line 3 of MOD-013: a nested definition is accepted like any other. -/
def mod013_line3 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) o, ValidPrefix o → S.terminals = [] →
    (∀ q ∈ S.ports, q.place ∈ S.places) →
    (∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name)) → ∃ I, Inst S o = .ok I

/-- MOD-013 is its three lines. -/
theorem mod013_iff (Nm : Naming N) (Inst : InstFn N A) :
    MOD_013 Nm Inst ↔ mod013_line1 Nm Inst ∧ mod013_line2 Inst ∧ mod013_line3 Inst :=
  Iff.rfl

/-- The transition names after one rewrite pass are the renamed names. -/
theorem mod013_names_map (σ : N → N) (g : String → String) (l : List (CDef N A)) :
    (l.map (CDef.map σ g)).map (·.core.name) = (l.map (·.core.name)).map g := by
  rw [List.map_map, List.map_map]
  rfl

end Lines

/-! ### Every model of MOD-010 is a model of MOD-013 -/

section FromMod010

variable {N A : Type}

/-- The transition names of an instance, in every model of MOD-010 line 3, are the body's names
renamed under the prefix. -/
theorem mod013_instNames {Nm : Naming N} {Inst : InstFn N A} (h3 : mod010_line3 Nm Inst)
    {S : SubnetDef N A} {p : String} {I : Instance N A} (hI : Inst S p = .ok I) :
    I.defs.map (·.core.name) = (S.defs.map (·.core.name)).map (preS p) := by
  have he : I.defs.map (·.core.name) =
      (I.defs.map CDef.toTransDef).map (·.core.name) := by rw [List.map_map]; rfl
  rw [he, (h3 S p I hI).2, List.map_map, List.map_map]
  rfl

/-- **MOD-010 gives MOD-013.** Every model of MOD-010 meets MOD-013: line 3 of MOD-010 renames
every body place and every body transition of the outer definition under `o`, the ones it took
over from an instance included, and line 2 of MOD-010 is line 3 of MOD-013. -/
theorem mod013_of_mod010 {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst) :
    MOD_013 Nm Inst := by
  refine ⟨fun T S i o J I _ hI x _ _ hS => ?_, fun T S i o J I _ hI d _ _ hS => ?_, h.2.1⟩
  · exact ((h.2.2.1 S o I hI).1 _).2 (List.mem_map_of_mem hS)
  · rw [mod013_instNames h.2.2.1 hI]
    exact List.mem_map_of_mem hS

end FromMod010

/-! ### The reference -/

/-- ✓ The reference instantiation satisfies MOD-013 for every naming model. An outer body that
holds an instance under `inner` has the place `inner/x` and the transition `inner/t`;
instantiating that body under `outer` gives `outer/inner/x` and `outer/inner/t`, which are the
same names as `x` and `t` under the prefix `outer/inner`. The `/` inside the body's names does not
stop the instantiation. -/
@[evidence holds MOD_013]
theorem MOD_013_reference {N A : Type} (Nm : Naming N) : MOD_013 Nm (refInst (A := A) Nm) :=
  mod013_of_mod010 (MOD_010_reference Nm)

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A : Type}

/-- **The nested name** (AC1): the place `Nm.pre o (Nm.pre i x)` is named `o/i/x` under every
naming model; for a place `x` of `T`, nesting `T` under `inner` and then under `outer` gives the
name `outer/inner/x`. -/
theorem mod013_name (Nm : Naming N) (o i : String) (x : N) :
    Nm.name (Nm.pre o (Nm.pre i x)) = preS o (preS i (Nm.name x)) := by
  rw [Nm.pre_name, Nm.pre_name]

/-- **The flat name set** (AC2, the associativity sentence): renaming the places `xs` of `T`
under `i` and then under `o` gives, name by name, the names a rename under the concatenated
prefix `o/i` gives: `outer/(inner/x)` is `(outer/inner)/x`. -/
theorem mod013_flat (Nm : Naming N) (o i : String) (xs : List N) :
    xs.map (fun x => Nm.name (Nm.pre o (Nm.pre i x))) =
      xs.map (fun x => preS (preS o i) (Nm.name x)) := by
  congr 1
  funext x
  rw [mod013_name, preS_assoc]

/-- In every model of MOD-013, a place `x` of `T` that the outer body took over as `i/x` gives a
place of the outer instance whose name is `o/i/x`, which is `x` under the concatenated prefix
`o/i`. -/
theorem mod013_nestedName {Nm : Naming N} {Inst : InstFn N A} (h : MOD_013 Nm Inst)
    {T S : SubnetDef N A} {i o : String} {J I : Instance N A} (hJ : Inst T i = .ok J)
    (hI : Inst S o = .ok I) {x : N} (hx : x ∈ T.places) (hJx : Nm.pre i x ∈ J.places)
    (hSx : Nm.pre i x ∈ S.places) :
    ∃ z ∈ I.places, Nm.name z = preS o (preS i (Nm.name x)) ∧
      Nm.name z = preS (preS o i) (Nm.name x) :=
  ⟨_, h.1 T S i o J I hJ hI x hx hJx hSx, mod013_name Nm o i x,
    (mod013_name Nm o i x).trans (preS_assoc _ _ _)⟩

/-- The concatenated prefix `o/i` is never a valid prefix: it contains `/`. -/
theorem mod013_preS_not_valid (o i : String) : ¬ ValidPrefix (preS o i) := fun h =>
  h.2 (by simp [preS, String.toList_append])

/-- **No single instantiation under `o/i`** (AC2): every model of MOD-010 rejects the
concatenated prefix, so the nested names are reached only by nesting. Instantiating `T` under
`outer/inner` fails. -/
theorem mod013_concat_rejected {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst)
    (T : SubnetDef N A) (o i : String) : ∃ msg, Inst T (preS o i) = .error msg :=
  h.1 T _ (mod013_preS_not_valid o i)

/-- **Isolation of names at every level** (AC3, naming half): under valid prefixes, two nested
places `o/i₁/x` and `o/i₂/y` are one place only when `i₁ = i₂` and `x = y`; two instances
`inner1` and `inner2` of `T` composed into one outer definition stay apart after `outer`. -/
theorem mod013_nested_inj (Nm : Naming N) {o i₁ i₂ : String} {x y : N} (ho : ValidPrefix o)
    (h₁ : ValidPrefix i₁) (h₂ : ValidPrefix i₂)
    (h : Nm.pre o (Nm.pre i₁ x) = Nm.pre o (Nm.pre i₂ y)) : i₁ = i₂ ∧ x = y :=
  Nm.pre_inj _ _ _ _ h₁ h₂ (Nm.pre_inj _ _ _ _ ho ho h).2

/-- **Through `fromNet`** ([MOD-014], ruling D57): when the outer definition is `fromNet` over a
net `X` that holds the place `i/x` (as composing the instance of `T` under `i` leaves it), every
model of MOD-013 gives the place `o/i/x` to the outer instance, for every `fromNet` that wraps the
net unchanged (MOD-014 line 6). -/
theorem mod013_viaFromNet {Nm : Naming N} {Inst : InstFn N A} {F : FromNetFn N A}
    (h1 : mod013_line1 Nm Inst) (hF : mod014_line6 F) {T S : SubnetDef N A} {X : ClosedNet N A}
    {ps : List (Port N)} {cs : List Chan} {i o : String} {J I : Instance N A}
    (hJ : Inst T i = .ok J) (hS : F X ps cs = .ok S) (hI : Inst S o = .ok I) {x : N}
    (hx : x ∈ T.places) (hJx : Nm.pre i x ∈ J.places) (hXx : Nm.pre i x ∈ X.places) :
    Nm.pre o (Nm.pre i x) ∈ I.places := by
  have hw := hF _ _ _ _ hS
  subst hw
  exact h1 T _ i o J I hJ hI x hx hJx hXx

end Consequences

/-! ### What MOD-010 adds: exactness of the nested names -/

section Exactness

variable {N A : Type}

/-- **Only the nested form** (AC1, "of the form"), for every model of [MOD-010]: every place of
the instance under `o` is a place of the body renamed under `o`, and every transition name is a
body transition name renamed under `o`. So the place `inner/x` of the body appears as
`outer/inner/x` and nowhere as `outer/x` or `inner/x`. -/
theorem mod013_ofTheForm {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst)
    {S : SubnetDef N A} {o : String} {I : Instance N A} (hI : Inst S o = .ok I) :
    (∀ y ∈ I.places, ∃ z ∈ S.places, Nm.pre o z = y) ∧
    (∀ n ∈ I.defs.map (·.core.name), ∃ m ∈ S.defs.map (·.core.name), preS o m = n) := by
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · exact List.mem_map.mp (((h.2.2.1 S o I hI).1 y).1 hy)
  · rw [mod013_instNames h.2.2.1 hI] at hn
    exact List.mem_map.mp hn

/-- **The nested name set** (AC2, both directions), for every model of [MOD-010]: the place
`o/i/x` belongs to the instance of `S` under `o` exactly when the body of `S` holds `i/x`. With
the body holding `inner/x` and not `inner/y`, the instance under `outer` holds `outer/inner/x` and
not `outer/inner/y`. -/
theorem mod013_nestedSet {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst)
    {S : SubnetDef N A} {o : String} {I : Instance N A} (hI : Inst S o = .ok I) (i : String)
    (x : N) : Nm.pre o (Nm.pre i x) ∈ I.places ↔ Nm.pre i x ∈ S.places := by
  have ho := mod010_ok_valid h.1 hI
  rw [(h.2.2.1 S o I hI).1, List.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rwa [← Nm.pre_injective ho hzx]
  · exact fun hS => ⟨_, hS, rfl⟩

end Exactness

/-! ### Example: the pipeline of the runtimes' nested tests -/

/-- An example definition: name, input arcs and output specification; `Immediate`, priority 0,
passthrough action. -/
def mod013_def (nm : String) (ins : List (NInSpec String)) (out : Option (Out String)) :
    CDef String Unit :=
  { core := ⟨nm, ins, [], [], []⟩, out := out, timing := .immediate, priority := 0,
    action := .passthrough }

/-- The inner subnet `T`: the transition `t` takes a token from the port place `in` and puts one
into the internal place `x`. -/
def mod013_T : SubnetDef String Unit :=
  { name := "T", places := ["in", "x"], defs := [mod013_def "t" [⟨"in", .one⟩] (some (.place "x"))],
    ports := [⟨"in", .input, "in"⟩], chans := [] }

/-- A composed net read as a closed net for `fromNet`, named `S`: its places, its definitions with
their correspondences, its terminal places. -/
def mod013_closed (c : ComposedNet String Unit) : ClosedNet String Unit :=
  { name := "S", places := c.places,
    defs := (c.trans.zip c.corrs).map fun e => { toTransDef := e.1, corr := e.2 },
    terminals := c.terminals }

/-- The outer definition `S`: a net that declares `src` and composes `T` under `inner` with the
port `in` bound to `src`, built, then wrapped by `fromNet` with the port `feed` on `src`. -/
def mod013_S : Except String (SubnetDef String Unit) :=
  refInst strNaming mod013_T "inner" >>= fun J =>
  buildExScript [.place "src", .compose J [("in", "src")] []] >>= fun c =>
  refFromNet (mod013_closed c) [⟨"feed", .input, "src"⟩] []

/-- The places, transition names and input places of an instance. -/
def mod013_view (I : Instance String Unit) : List String × List String × List (List String) :=
  (I.places, I.defs.map (·.core.name), I.defs.map (·.core.inputs.map (·.place)))

set_option maxRecDepth 20000 in
/-- ✓ Every line of MOD-013 is exercised by the reference, on the test derivation. `T` has the
port place `in`, the internal place `x` and the transition `t` from `in` to `x`. Instantiated
under `inner` it holds `inner/x` and `inner/t`. Composed into a net with `in` bound to `src`, then
wrapped by `fromNet`, it gives the definition `S` whose body holds `src`, `inner/x` and `inner/t`
(the port place `inner/in` is gone, replaced by `src`). Instantiating `S` under `outer` succeeds
(line 3, though its body names contain `/`) and gives the places `outer/src` and `outer/inner/x`
(line 1) and the transition `outer/inner/t` from `outer/src` (line 2). -/
@[evidence nonvacuous MOD_013]
theorem MOD_013_nonvacuous :
    (refInst strNaming mod013_T "inner").toOption.map mod013_view =
      some (["inner/in", "inner/x"], ["inner/t"], [["inner/in"]]) ∧
    mod013_S.toOption.map (fun S => (S.places, S.defs.map (·.core.name), S.terminals)) =
      some (["src", "inner/x"], ["inner/t"], []) ∧
    (mod013_S >>= fun S => refInst strNaming S "outer").toOption.map mod013_view =
      some (["outer/src", "outer/inner/x"], ["outer/inner/t"], [["outer/src"]]) := by
  decide

/-! ### Wrong instantiations -/

/-- The last `/`-segment of a name: `inner/x` gives `x`. -/
def mod013_lastSeg (y : String) : String :=
  String.ofList ((y.toList.reverse.takeWhile (· ≠ '/')).reverse)

/-- A rename that drops every inner prefix: `y` under `o` becomes `o/` and the last segment of
`y`, so `inner/x` under `outer` becomes `outer/x`. -/
def mod013_dropInner (o y : String) : String := preS o (mod013_lastSeg y)

/-- A rename that puts the inner prefix first: `inner/x` under `outer` becomes
`inner/outer/x`; a name without `/` becomes `o/y`. -/
def mod013_innerFirst (o y : String) : String :=
  match y.toList.span (· ≠ '/') with
  | (a, _ :: rest) => String.ofList (a ++ '/' :: o.toList ++ '/' :: rest)
  | (_, []) => preS o y

/-- An instantiation (places by name) that renames places with `mod013_dropInner`, transitions
correctly. -/
def mod013_dropInnerPlaceInst : InstFn String Unit :=
  instVia refChk mod013_dropInner (fun p => CDef.map (preS p) (preS p))

/-- An instantiation (places by name) that renames places correctly and transition names with
`mod013_dropInner`. -/
def mod013_dropInnerTransInst : InstFn String Unit :=
  instVia refChk preS (fun p => CDef.map (preS p) (mod013_dropInner p))

/-- An instantiation (places by name) that renames correctly but refuses a body whose place
names contain `/`. -/
def mod013_refuseNestedInst : InstFn String Unit :=
  instVia (fun S p => refChk S p && S.places.all (fun y => decide ('/' ∉ y.toList)))
    preS (fun p => CDef.map (preS p) (preS p))

/-- An instantiation (places by name) that renames everything with `mod013_innerFirst`. -/
def mod013_innerFirstInst : InstFn String Unit :=
  instVia refChk mod013_innerFirst (fun p => CDef.map (mod013_innerFirst p) (mod013_innerFirst p))

/-- The hand-written outer definition `S` of the wrong-model examples: the places `src` and
`inner/x`, the transition `inner/t` from `src` to `inner/x`, and the port `feed` on `src`; what
`fromNet` gives in `MOD_013_nonvacuous`, without the correspondence. -/
def mod013_handS : SubnetDef String Unit :=
  { name := "S", places := ["src", "inner/x"],
    defs := [mod013_def "inner/t" [⟨"src", .one⟩] (some (.place "inner/x"))],
    ports := [⟨"feed", .input, "src"⟩], chans := [] }

section WrongLemmas

/-- A wrong instantiation that renames places with `preS` meets line 1. -/
theorem mod013_line1_of_preS {chk : SubnetDef String Unit → String → Bool}
    {dm : String → CDef String Unit → CDef String Unit} :
    mod013_line1 strNaming (instVia chk preS dm) := by
  intro T S i o J I _ hI x _ _ hS
  obtain ⟨-, hpl, -⟩ := instVia_ok hI
  rw [hpl]
  exact List.mem_map_of_mem hS

/-- A wrong instantiation that renames transitions by one rewrite pass with the name map `preS`
meets line 2. -/
theorem mod013_line2_of_preS {chk : SubnetDef String Unit → String → Bool}
    {pl : String → String → String}
    {σ : String → String → String} :
    mod013_line2 (instVia chk pl (fun p => CDef.map (σ p) (preS p))) := by
  intro T S i o J I _ hI d _ _ hS
  obtain ⟨-, -, hd⟩ := instVia_ok hI
  rw [hd, mod013_names_map]
  exact List.mem_map_of_mem hS

/-- A wrong instantiation with the reference's check meets line 3. -/
theorem mod013_line3_of_refChk {pl : String → String → String}
    {dm : String → CDef String Unit → CDef String Unit} :
    mod013_line3 (instVia refChk pl dm) := fun S o ho ht _ _ =>
  ⟨_, instVia_of_chk (by simp [refChk, ho, ht])⟩

end WrongLemmas

/-- ✗ An instantiation that puts the inner prefix first violates MOD-013 (line 1): the place
`inner/x` of the outer body becomes `inner/outer/x`, not `outer/inner/x`. -/
@[evidence forbids MOD_013]
theorem MOD_013_forbids_innerFirst : ¬ MOD_013 strNaming mod013_innerFirstInst := by
  intro h
  have hJ := instVia_of_chk (chk := refChk) (pl := mod013_innerFirst)
    (dm := fun p => CDef.map (mod013_innerFirst p) (mod013_innerFirst p)) (S := mod013_T)
    (p := "inner") (by decide)
  have hI := instVia_of_chk (chk := refChk) (pl := mod013_innerFirst)
    (dm := fun p => CDef.map (mod013_innerFirst p) (mod013_innerFirst p)) (S := mod013_handS)
    (p := "outer")
    (by decide)
  have := h.1 _ _ _ _ _ _ hJ hI "x" (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-- ✗ An instantiation that rejects everything violates MOD-013 (line 3): it rejects the nested
definition `S` under the valid prefix `outer`. -/
@[evidence forbids MOD_013]
theorem MOD_013_forbids_rejectAll : ¬ MOD_013 strNaming (rejectAllInst (A := Unit)) := by
  intro h
  obtain ⟨I, hI⟩ := h.2.2 mod013_handS "outer" (by decide) rfl (by decide) (by decide)
  exact nomatch hI

/-! ### Mutant: line 1 dropped (places) -/

/-- Mutant reading: MOD-013 without line 1, so the places an outer body took over may lose their
inner prefix. -/
def MOD_013_mutant_noPlaces {N A : Type} (_Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod013_line2 Inst ∧ mod013_line3 Inst

/-- The instantiation that drops the inner prefix of a place kills the mutant: it renames
transitions correctly and accepts every valid call (lines 2 and 3), but the place `inner/x` of the
outer body becomes `outer/x`, and `outer/inner/x` is missing (line 1). -/
@[evidence mutant MOD_013]
theorem MOD_013_mutant_noPlaces_killed :
    MOD_013_mutant_noPlaces strNaming mod013_dropInnerPlaceInst ∧
      ¬ MOD_013 strNaming mod013_dropInnerPlaceInst := by
  refine ⟨⟨mod013_line2_of_preS, mod013_line3_of_refChk⟩, fun h => ?_⟩
  have hJ := instVia_of_chk (chk := refChk) (pl := mod013_dropInner)
    (dm := fun p => CDef.map (preS p) (preS p)) (S := mod013_T) (p := "inner") (by decide)
  have hI := instVia_of_chk (chk := refChk) (pl := mod013_dropInner)
    (dm := fun p => CDef.map (preS p) (preS p)) (S := mod013_handS) (p := "outer") (by decide)
  have := h.1 _ _ _ _ _ _ hJ hI "x" (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Mutant: line 2 dropped (transitions) -/

/-- Mutant reading: MOD-013 without line 2, so the transitions an outer body took over may lose
their inner prefix. -/
def MOD_013_mutant_noTransitions {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod013_line1 Nm Inst ∧ mod013_line3 Inst

/-- The instantiation that drops the inner prefix of a transition name kills the mutant: it
renames places correctly and accepts every valid call (lines 1 and 3), but the transition `inner/t`
of the outer body becomes `outer/t`, and `outer/inner/t` is missing (line 2). -/
@[evidence mutant MOD_013]
theorem MOD_013_mutant_noTransitions_killed :
    MOD_013_mutant_noTransitions strNaming mod013_dropInnerTransInst ∧
      ¬ MOD_013 strNaming mod013_dropInnerTransInst := by
  refine ⟨⟨mod013_line1_of_preS, mod013_line3_of_refChk⟩, fun h => ?_⟩
  have hJ := instVia_of_chk (chk := refChk) (pl := preS)
    (dm := fun p => CDef.map (preS p) (mod013_dropInner p)) (S := mod013_T) (p := "inner")
    (by decide)
  have hI := instVia_of_chk (chk := refChk) (pl := preS)
    (dm := fun p => CDef.map (preS p) (mod013_dropInner p)) (S := mod013_handS)
    (p := "outer") (by decide)
  have := h.2.1 _ _ _ _ _ _ hJ hI (mod013_def "t" [⟨"in", .one⟩] (some (.place "x")))
    (by simp [mod013_T]) (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Mutant: line 3 dropped (acceptance of nested bodies) -/

/-- Mutant reading: MOD-013 without line 3, the names of a nested instance only. -/
def MOD_013_mutant_noAcceptance {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod013_line1 Nm Inst ∧ mod013_line2 Inst

/-- The instantiation that refuses a body whose place names contain `/` kills the mutant: it
renames correctly (lines 1 and 2), but refuses the nested definition `S`, whose body holds
`inner/x`, under the valid prefix `outer` (line 3). -/
@[evidence mutant MOD_013]
theorem MOD_013_mutant_noAcceptance_killed :
    MOD_013_mutant_noAcceptance strNaming mod013_refuseNestedInst ∧
      ¬ MOD_013 strNaming mod013_refuseNestedInst := by
  refine ⟨⟨mod013_line1_of_preS, mod013_line2_of_preS⟩, fun h => ?_⟩
  obtain ⟨I, hI⟩ := h.2.2 mod013_handS "outer" (by decide) rfl (by decide) (by decide)
  unfold mod013_refuseNestedInst instVia at hI
  rw [if_neg (by decide)] at hI
  cases hI

/-! ### Exactness is MOD-010's: a model of MOD-013 that keeps the body places -/

/-- An instance that holds the renamed places and the body places unrenamed as well; the
definitions are renamed correctly. -/
def mod013_keepBodyInstance (S : SubnetDef String Unit) (p : String) : Instance String Unit where
  pfx := p
  places := S.places.map (preS p) ++ S.places
  defs := S.defs.map (CDef.map (preS p) (preS p))
  port _ := none
  chan _ := none
  iface := S.ports

/-- An instantiation (places by name) that keeps the body places next to the renamed ones, the
slip of adding the body's own places in the loop that keeps unreferenced places of a rename
(`rename_net` in rust/libpetri-core/src/rewriter.rs). -/
def mod013_keepBodyInst : InstFn String Unit := fun S p =>
  if refChk S p then .ok (mod013_keepBodyInstance S p) else .error "rejected"

/-- A success of the instantiation that keeps the body places is its instance. -/
theorem mod013_keepBody_ok {S : SubnetDef String Unit} {p : String} {I : Instance String Unit}
    (h : mod013_keepBodyInst S p = .ok I) : I = mod013_keepBodyInstance S p := by
  unfold mod013_keepBodyInst at h
  split at h
  · cases h; rfl
  · cases h

/-- **MOD-013 alone does not give exactness.** The instantiation that keeps the body places meets
all three lines of MOD-013: it holds `o/i/x` and `o/i/t` for every held `i/x` and `i/t`, and it
accepts every valid call. The lines say what an instance holds, not that it holds nothing more;
that is MOD-010's "exactly" (`mod013_keepBody_not_mod010`). -/
theorem mod013_keepBody_accepted : MOD_013 strNaming mod013_keepBodyInst := by
  refine ⟨fun T S i o J I _ hI x _ _ hS => ?_, fun T S i o J I _ hI d _ _ hS => ?_,
    fun S o ho ht _ _ => ⟨mod013_keepBodyInstance S o, ?_⟩⟩
  · rw [mod013_keepBody_ok hI]
    exact List.mem_append_left _ (List.mem_map_of_mem hS)
  · rw [mod013_keepBody_ok hI]
    show _ ∈ (S.defs.map (CDef.map (preS o) (preS o))).map (·.core.name)
    rw [mod013_names_map]
    exact List.mem_map_of_mem hS
  · unfold mod013_keepBodyInst; rw [if_pos (by simp [refChk, ho, ht])]

/-- The instantiation that keeps the body places breaks isolation at the nested level (AC3): two
instances of the nested `S` under `o1` and `o2` both hold the place `inner/x`, so they share it. -/
theorem mod013_keepBody_shares :
    (mod013_keepBodyInst mod013_handS "o1").toOption.map (·.places) =
        some ["o1/src", "o1/inner/x", "src", "inner/x"] ∧
      (mod013_keepBodyInst mod013_handS "o2").toOption.map (·.places) =
        some ["o2/src", "o2/inner/x", "src", "inner/x"] := by
  decide

/-- MOD-010 rejects the instantiation that keeps the body places: under `o1` the instance holds the
unrenamed place `src`, which is not the rename of any body place. -/
theorem mod013_keepBody_not_mod010 : ¬ MOD_010 strNaming mod013_keepBodyInst := by
  intro h
  have hI : mod013_keepBodyInst mod013_handS "o1" =
      .ok (mod013_keepBodyInstance mod013_handS "o1") := by
    unfold mod013_keepBodyInst; rw [if_pos (by decide)]
  have := ((h.2.2.1 _ _ _ hI).1 "src").1 (by decide)
  exact absurd this (by decide)

end Libpetri.Spec
