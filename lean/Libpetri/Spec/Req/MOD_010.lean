import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Spec.Text.MOD_010

set_option linter.missingDocs true

/-!
# MOD-010: Instance creation (`spec/11-modular-composition.md`)

MOD-010 is a pure-function requirement (kind F) over an abstract instantiation function
`Inst : InstFn N A` (a subnet definition and a prefix give a module instance or a rejection) and
a naming model `Nm : Naming N` (how a prefix renames a place: by name in TypeScript, Rust and
Python, by name and token type in Java). It says when instantiation fails (an invalid prefix; a
valid prefix on a body that declares a terminal place, with a message naming such a place), when
it succeeds (a valid prefix on a body without terminal places), and what a successful
instantiation returns: the body renamed under the prefix, with arcs following the rename and
timing, priority and action kept.

The reference is `refInst Nm` (`Reference/ComposeDef.lean`, through `refInst_ok`,
`refInst_invalid`, `refInst_valid` and `refInst_terminals_named`).

The witness is the reference instantiation `refInst Nm` (`Reference/ComposeDef.lean`); the block
holds for every naming model. Three consequences hold for every model of the block: every
instance place is named `p/x` for a body place named `x` (`mod010_placeName`, AC1), two instances
of one definition under different prefixes share no name (`mod010_disjoint`, AC2), and a renamed
transition fires under the reference firing relation exactly as the body transition it renames,
at the marking pulled back through the rename (`mod010_firesAsBody`, the RefFire link
`fires_mapT`). Wrong instantiations are killed: one without the prefix check, one with the
separator `.`, one that leaves the reset arcs unrenamed, one whose terminal-place rejection
names no place, and one per line that meets a plausible wrong reading of that line.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## MOD-010: Instance Creation via instantiate(prefix, params) -/

requirement MOD_010
  id "MOD-010"
  title "Instance Creation via instantiate(prefix, params)"
  kind F
  scope "every instantiation of a subnet definition"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_010.s1, MOD_010.s2, MOD_010.s4, MOD_010.s3
  reading "For every naming model Nm (how a prefix renames a place) and every instantiation function Inst:"
          "if the prefix p is not valid (empty, or containing '/'), Inst fails on every subnet definition;"
          "if p is valid and the definition's body declares no terminal place (and every port exposes a body place and every channel a body transition), Inst succeeds;"
          "if Inst returns an instance I under p, the places of I are, as a set, the body's places each renamed by Nm.pre p, and the definitions of I, as transition definitions, are the body's definitions in order, each mapped by TransDef.map (Nm.pre p) (preS p): every input, inhibitor, read, reset and output-specification place renamed by Nm.pre p, the name x renamed to p/x, timing, priority and action unchanged;"
          "if p is valid and the definition's body declares a terminal place, Inst fails with a message that names (contains, MsgNames) the name of one of the body's terminal places."
  assumes "Ruling D25 (a): a prefix is valid when it is non-empty and contains no '/' (ValidPrefix), as Rust, Java and TypeScript check before renaming (SubnetDef::instantiate in rust/libpetri-core/src/subnet_def.rs, SubnetDef.validatePrefix in java/src/main/java/org/libpetri/core/SubnetDef.java, validatePrefix in typescript/src/core/subnet-def.ts; Python calls the Rust check). The separator sentence ('Implementations MUST use exactly \"/\"') is preS: the renamed name of x under p is p ++ \"/\" ++ x, for transition names directly and for place names through the naming model's law pre_name. The order of the prefix check and the terminal-place check is not stated, which is why line 4 has the premise that the prefix is valid; the message of line 1 is not stated. Lines 3 and 4 are the markdown's fourth and third shall sentences: the block states what a success returns before the terminal-place rejection, the order the other blocks cite (MOD-010 line 3 for the shape, line 4 for EXEC-042 AC6)."
          "Places are the abstract N, the key type of the place model (PlaceKeyed.K, CORE-002), and the naming model Nm says how a prefix renames a key. Its law pre_name (the renamed place's name is p/name, item 2) pins the rename at every naming model, so a model that renames x to x/p is not a naming model; its law pre_inj (valid prefixes rename injectively and to disjoint sets) is what the prefix check buys. strNaming (TypeScript, Rust, Python: a place is its name, renamed to p/name) and typedNaming (Java: the name renamed, the token type kept) are the runtime naming models; the holds theorem holds for every naming model. Transition names are strings and are renamed by preS under every naming model."
          "Line 4 is EXEC-042 AC6 for instantiate (a subnet body that declares terminal places is rejected with an error that names the place), the composition MUST that EXEC-042's block leaves to the composition model; its direct-composition half is MOD-025 line 7. To name is to contain as a substring (MsgNames, as in MOD-006). Every runtime rejects the body before renaming and names its first terminal place (SubnetDef::instantiate in rust/libpetri-core/src/subnet_def.rs through reject_subnet_terminals, SubnetRewriter.renameNet through SubnetRewriter.rejectTerminals in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, renameNet through rejectSubnetTerminals in typescript/src/core/internal/subnet-rewriter.ts; Python calls the Rust check); the line asks for one of them. An instantiation without the terminal check meets lines 1 to 3 (MOD_010_mutant_noTerminalCheck_killed), and one that rejects without naming the place breaks line 4 (MOD_010_forbids_unnamedTerminal). Line 2's premises that every port exposes a body place and every channel a body transition hold of every subnet definition the subnet builder accepts (MOD-006). All three runtimes fail instantiate on a port whose place or a channel whose transition is missing from the renamed body (SubnetDef::instantiate in rust/libpetri-core/src/subnet_def.rs, SubnetDef.instantiate in java/src/main/java/org/libpetri/core/SubnetDef.java and in typescript/src/core/subnet-def.ts), which is unreachable from a built definition; the premises keep line 2 true of those runtimes on the definitions the Lean type allows beyond the built ones."
          "Line 3 compares the places as a set: Rust collects the renamed places through a hash map (rename_net in rust/libpetri-core/src/rewriter.rs), and the order of places is not normative (ruling D32). It compares the transitions as a list: every runtime rewrites them in the body's order (rename_net in rust/libpetri-core/src/rewriter.rs). It states the definitions' TransDef part only: the declared-to-actual correspondence a rewrite pass records (CDef.corr) is MOD-031's, and the instance's handles, prefix and interface (port, chan, pfx, iface) are MOD-011's and MOD-024's."
          "Item 4 (arcs reference the renamed places, the arc topology identical modulo the rename) is line 3: TransDef.map renames every arc place of all five arc kinds and every output-specification place, and keeps the arc lists' order, repetitions and cardinalities. Its consequence for firing is mod010_firesAsBody: under the reference firing relation a renamed transition fires exactly as the body transition at the marking pulled back through the rename, and leaves every place outside the rename's image unchanged (fires_mapT, Spec/GlossaryCompose.lean)."
          "Item 5 (timing, priority and action preserved) is line 3's 'unchanged': the action is read as its identity tag (Act), so 'shared by reference' is MOD-030's line. Item 3 (the renamed body is a structurally valid PetriNet per CORE-040) is not stated here: that every renamed definition passes the build check, which holds since an injective rename keeps every build-time check, is the line 'every definition of a built net passes Build' of MOD-023 (composition wave W8). Every runtime also renames the body net itself to prefix/bodyName (rename_net in rust/libpetri-core/src/rewriter.rs, SubnetRewriter.renameNet in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, renameNet in typescript/src/core/internal/subnet-rewriter.ts), which the spec does not state."
          "Item 1 and AC4 (a params value of the wrong type is rejected) are API shape: the parameters value is not modelled, its type is checked by the host language at compile time where it has generics and at construction otherwise, tested and not proven. AC3 (the renamed body is immutable) is a quality property of the host values (Lean values are immutable; CORE-041 states builder stability), tested and not proven."
          "AC1 (instantiate(\"buf1\", params) over a body containing place slots produces buf1/slots) is MOD_010_nonvacuous on the reference, by decide; so is line 4 on a body with the terminal place done."
          "AC2 (two instantiations of one definition under different prefixes have disjoint place and transition name sets) follows from lines 1 and 3 and the naming model's laws (mod010_disjoint, for every model of the block, on place names and transition names; AC1 at every naming model is mod010_placeName), so it has no mutant of its own (skeptic correction S4 of the composition design). The nested form outer/inner/originalName is MOD-013's (preS_assoc)."
  signoff "2026-11-13 ee51dcfb3dcac4fe ai"
  statement : ∀ {N A : Type}, Naming N → InstFn N A → Prop :=
    fun {N A} Nm Inst =>
      (∀ (S : SubnetDef N A) p, ¬ ValidPrefix p → ∃ msg, Inst S p = .error msg) ∧
      (∀ (S : SubnetDef N A) p, ValidPrefix p → S.terminals = [] →
        (∀ q ∈ S.ports, q.place ∈ S.places) →
        (∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name)) → ∃ I, Inst S p = .ok I) ∧
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I →
        (∀ x, x ∈ I.places ↔ x ∈ S.places.map (Nm.pre p)) ∧
        I.defs.map CDef.toTransDef = S.defs.map (fun d => d.toTransDef.map (Nm.pre p) (preS p))) ∧
      (∀ (S : SubnetDef N A) p, ValidPrefix p → S.terminals ≠ [] →
        ∃ msg, Inst S p = .error msg ∧ ∃ x ∈ S.terminals, MsgNames msg (Nm.name x))

/- The pinned readable form of MOD-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_010 : {N A : Type} → Naming N → InstFn N A → Prop :=
fun {N A} Nm Inst =>
  (∀ (S : SubnetDef N A) (p : String), ¬ValidPrefix p → ∃ msg, Inst S p = Except.error msg) ∧
    (∀ (S : SubnetDef N A) (p : String),
        ValidPrefix p →
          S.terminals = [] →
            (∀ q ∈ S.ports, q.place ∈ S.places) →
              (∀ c ∈ S.chans, c.trans ∈ List.map (fun x => x.core.name) S.defs) → ∃ I, Inst S p = Except.ok I) ∧
      (∀ (S : SubnetDef N A) (p : String) (I : Instance N A),
          Inst S p = Except.ok I →
            (∀ (x : N), x ∈ I.places ↔ x ∈ List.map (Nm.pre p) S.places) ∧
              List.map CDef.toTransDef I.defs =
                List.map (fun d => TransDef.map (Nm.pre p) (preS p) d.toTransDef) S.defs) ∧
        ∀ (S : SubnetDef N A) (p : String),
          ValidPrefix p →
            S.terminals ≠ [] → ∃ msg, Inst S p = Except.error msg ∧ ∃ x ∈ S.terminals, MsgNames msg (Nm.name x)
-/
#guard_msgs in #print MOD_010

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-010: an invalid prefix fails. -/
def mod010_line1 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p, ¬ ValidPrefix p → ∃ msg, Inst S p = .error msg

/-- Line 2 of MOD-010: a valid prefix on a body without terminal places succeeds. -/
def mod010_line2 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p, ValidPrefix p → S.terminals = [] →
    (∀ q ∈ S.ports, q.place ∈ S.places) →
    (∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name)) → ∃ I, Inst S p = .ok I

/-- Line 3 of MOD-010: what a success returns. -/
def mod010_line3 (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I →
    (∀ x, x ∈ I.places ↔ x ∈ S.places.map (Nm.pre p)) ∧
    I.defs.map CDef.toTransDef = S.defs.map (fun d => d.toTransDef.map (Nm.pre p) (preS p))

/-- Line 4 of MOD-010 (EXEC-042 AC6): under a valid prefix, a body that declares a terminal place
fails, with a message naming one of its terminal places. -/
def mod010_line4 (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p, ValidPrefix p → S.terminals ≠ [] →
    ∃ msg, Inst S p = .error msg ∧ ∃ x ∈ S.terminals, MsgNames msg (Nm.name x)

/-- MOD-010 is its four lines, in order. -/
theorem mod010_iff (Nm : Naming N) (Inst : InstFn N A) :
    MOD_010 Nm Inst ↔
      mod010_line1 Inst ∧ mod010_line2 Inst ∧ mod010_line3 Nm Inst ∧ mod010_line4 Nm Inst :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference instantiation satisfies MOD-010 for every naming model. Instantiating the
subnet `buf` under `buf1` renames the place `slots` to `buf1/slots` and the transition `take` to
`buf1/take`, whose input arc moves to `buf1/slots`, with its timing, priority and action kept.
The prefixes `a/b` and the empty prefix are rejected, and so is a body that declares the terminal
place `done`, with a message that names `done`. -/
@[evidence holds MOD_010]
theorem MOD_010_reference {N A : Type} (Nm : Naming N) : MOD_010 Nm (refInst (A := A) Nm) := by
  refine ⟨fun S p hp => ⟨_, refInst_invalid Nm S hp⟩,
    fun S p hp ht _ _ => ⟨_, refInst_valid Nm S hp ht⟩,
    fun S p I hI => ?_,
    fun S p hp ht => ⟨_, refInst_terminals_named Nm S hp ht, instTermMsg_names Nm S ht⟩⟩
  obtain ⟨-, -, -, hpl, hd, -⟩ := refInst_ok hI
  refine ⟨fun x => by rw [hpl], ?_⟩
  rw [hd, List.map_map]
  rfl

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A : Type}

/-- Under line 1, a success is at a valid prefix. -/
theorem mod010_ok_valid {Inst : InstFn N A} (h1 : mod010_line1 Inst) {S : SubnetDef N A}
    {p : String} {I : Instance N A} (h : Inst S p = .ok I) : ValidPrefix p := by
  by_contra hp
  obtain ⟨msg, hm⟩ := h1 S p hp
  rw [h] at hm
  cases hm

/-- Two instances of one instantiation function under different prefixes share no place name
(under the naming model `Nm`) and no transition name. -/
def InstDisjoint (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p q I J, p ≠ q → Inst S p = .ok I → Inst S q = .ok J →
    (∀ x ∈ I.places, ∀ y ∈ J.places, Nm.name x ≠ Nm.name y) ∧
      ∀ n ∈ I.defs.map (·.core.name), n ∉ J.defs.map (·.core.name)

/-- A transition name of an instance is the renamed name of a body transition. -/
theorem mod010_name {Nm : Naming N} {Inst : InstFn N A} (h3 : mod010_line3 Nm Inst)
    {S : SubnetDef N A} {p : String} {I : Instance N A} (hI : Inst S p = .ok I) {n : String}
    (hn : n ∈ I.defs.map (·.core.name)) : ∃ x, n = preS p x := by
  have he : I.defs.map (·.core.name) =
      (I.defs.map CDef.toTransDef).map (·.core.name) := by rw [List.map_map]; rfl
  rw [he, (h3 S p I hI).2, List.map_map] at hn
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hn
  exact ⟨d.core.name, rfl⟩

/-- **Item 2 and AC1 for places.** In every model of MOD-010, every place of an instance under
`p` is named `p/x` for the name `x` of a body place, and every body place named `x` gives an
instance place named `p/x`: instantiating a body with the place `slots` under `buf1` gives a
place named `buf1/slots`, whatever the naming model. -/
theorem mod010_placeName {Nm : Naming N} {Inst : InstFn N A} (h3 : mod010_line3 Nm Inst)
    {S : SubnetDef N A} {p : String} {I : Instance N A} (hI : Inst S p = .ok I) :
    (∀ x ∈ I.places, ∃ y ∈ S.places, Nm.name x = preS p (Nm.name y)) ∧
      ∀ y ∈ S.places, ∃ x ∈ I.places, Nm.name x = preS p (Nm.name y) := by
  refine ⟨fun x hx => ?_, fun y hy => ⟨Nm.pre p y, ?_, Nm.pre_name p y⟩⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (((h3 S p I hI).1 x).1 hx)
    exact ⟨y, hy, Nm.pre_name p y⟩
  · exact ((h3 S p I hI).1 _).2 (List.mem_map_of_mem hy)

/-- **AC2.** Every model of MOD-010 gives two instances of one definition under different
prefixes disjoint place-name sets and disjoint transition-name sets: lines 1 and 3 and the
naming model's laws imply it, so no model can violate it alone. Instances `b1` and `b2` of a
body with the place `slots` hold `b1/slots` and `b2/slots`, never one name twice. -/
theorem mod010_disjoint {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst) :
    InstDisjoint Nm Inst := by
  intro S p q I J hne hI hJ
  have vp := mod010_ok_valid h.1 hI
  have vq := mod010_ok_valid h.1 hJ
  refine ⟨fun x hx y hy hxy => ?_, fun n hn hm => ?_⟩
  · obtain ⟨a, -, ha⟩ := (mod010_placeName h.2.2.1 hI).1 x hx
    obtain ⟨b, -, hb⟩ := (mod010_placeName h.2.2.1 hJ).1 y hy
    rw [ha, hb] at hxy
    exact hne (preS_inj _ _ _ _ vp vq hxy).1
  · obtain ⟨a, rfl⟩ := mod010_name h.2.2.1 hI hn
    obtain ⟨b, hb⟩ := mod010_name h.2.2.1 hJ hm
    exact hne (preS_inj _ _ _ _ vp vq hb).1

/-- **The RefFire link.** Every model of MOD-010 renames firings faithfully: every transition of
an instance is the rename of a body transition, fires under the reference firing relation
exactly as that body transition at the marking pulled back through the rename, and leaves every
place outside the rename's image as it was (`fires_mapT`, the rename being injective under a
valid prefix). -/
theorem mod010_firesAsBody [DecidableEq N] {Nm : Naming N} {Inst : InstFn N A}
    (h : MOD_010 Nm Inst) : InstFiresAsBody Nm Inst RefFire := by
  intro S p I hI d hd
  have vp := mod010_ok_valid h.1 hI
  have hm : d.toTransDef ∈ S.defs.map (fun d => d.toTransDef.map (Nm.pre p) (preS p)) := by
    rw [← (h.2.2.1 S p I hI).2]; exact List.mem_map_of_mem hd
  obtain ⟨d₀, hd₀, he⟩ := List.mem_map.1 hm
  refine ⟨d₀, hd₀, fun m dep m' => ?_⟩
  have ht : d.toTransDef.toTrans = mapT (Nm.pre p) (preS p) d₀.toTransDef.toTrans := by
    rw [← he]; rfl
  show RefFire d.toTransDef.toTrans m dep m' ↔ _
  rw [ht]
  exact fires_mapT (Nm.pre_injective vp) (preS p) _ m dep m'

/-- The reference instantiation renames firings faithfully under the reference firing
relation. -/
theorem refInst_firesAsBody [DecidableEq N] (Nm : Naming N) :
    InstFiresAsBody Nm (refInst (A := A) Nm) RefFire :=
  mod010_firesAsBody (MOD_010_reference Nm)

/-- The reference instantiation keeps instances under different prefixes disjoint. -/
theorem refInst_disjoint (Nm : Naming N) : InstDisjoint Nm (refInst (A := A) Nm) :=
  mod010_disjoint (MOD_010_reference Nm)

end Consequences

/-! ### Example -/

/-- The example body transition `take`: an input arc on `slots`, a reset arc on `r`, the output
place `out`, priority 3 and an action. -/
def mod010_exDef : CDef String Unit :=
  { core := ⟨"take", [⟨"slots", .one⟩], [], [], ["r"]⟩, out := some (.place "out"),
    timing := .immediate, priority := 3, action := .other () }

/-- The example subnet definition `buf`: places `slots`, `out` and `r`, the transition `take`,
and the port `input` on `slots`. -/
def mod010_exS : SubnetDef String Unit :=
  { name := "buf", places := ["slots", "out", "r"], defs := [mod010_exDef],
    ports := [⟨"input", .input, "slots"⟩], chans := [] }

/-- The example subnet definition `fin`, whose body declares the terminal place `done`. -/
def mod010_exT : SubnetDef String Unit :=
  { name := "fin", places := ["done"], defs := [], terminals := ["done"], ports := [], chans := [] }

/-- ✓ Every line of MOD-010 is exercised by the reference: instantiating `buf` under `buf1` gives
the place `buf1/slots` (AC1) and the transition `buf1/take`, whose input arc is on `buf1/slots`,
whose reset arc is on `buf1/r` and whose priority is still 3 (lines 2 and 3); the prefixes `a/b`
and the empty prefix are rejected (line 1); and instantiating `fin`, whose body declares the
terminal place `done`, under `buf1` fails with a message that names `done` (line 4). -/
@[evidence nonvacuous MOD_010]
theorem MOD_010_nonvacuous :
    (∃ I, refInst strNaming mod010_exS "buf1" = .ok I ∧
      I.places = ["buf1/slots", "buf1/out", "buf1/r"] ∧
      I.defs.map (·.core.name) = ["buf1/take"] ∧
      I.defs.map (·.core.inputs.map (·.place)) = [["buf1/slots"]] ∧
      I.defs.map (·.core.resets) = [["buf1/r"]] ∧
      I.defs.map (·.priority) = [3]) ∧
    (∃ msg, refInst strNaming mod010_exS "a/b" = .error msg) ∧
    (∃ msg, refInst strNaming mod010_exS "" = .error msg) ∧
    (∃ msg, refInst strNaming mod010_exT "buf1" = .error msg ∧
      msg = "subnet 'fin' declares terminal place 'done'; a subnet body may not (EXEC-042)") := by
  refine ⟨⟨_, refInst_valid strNaming mod010_exS (by decide) rfl, ?_⟩,
    ⟨_, refInst_invalid strNaming mod010_exS (by decide)⟩,
    ⟨_, refInst_invalid strNaming mod010_exS (by decide)⟩,
    ⟨_, refInst_terminals_named strNaming mod010_exT (by decide) (by simp [mod010_exT]), by decide⟩⟩
  decide

/-! ### Wrong instantiations -/

section Wrong

variable {N A : Type}

/-- The instance of a wrong instantiation: places renamed with `pl`, definitions with `dm`, no
handles. -/
def viaInstance (pl : String → N → N) (dm : String → CDef N A → CDef N A) (S : SubnetDef N A)
    (p : String) : Instance N A where
  pfx := p
  places := S.places.map (pl p)
  defs := S.defs.map (dm p)
  port _ := none
  chan _ := none
  iface := S.ports

/-- An instantiation that succeeds when `chk` holds, renaming places with `pl` and definitions
with `dm`, and fails otherwise; the shape of every wrong instantiation below. -/
def instVia (chk : SubnetDef N A → String → Bool) (pl : String → N → N)
    (dm : String → CDef N A → CDef N A) : InstFn N A := fun S p =>
  if chk S p then .ok (viaInstance pl dm S p) else .error "rejected"

/-- A success of `instVia` holds the mapped places and definitions, and `chk` held. -/
theorem instVia_ok {chk : SubnetDef N A → String → Bool} {pl : String → N → N}
    {dm : String → CDef N A → CDef N A} {S : SubnetDef N A} {p : String} {I : Instance N A}
    (h : instVia chk pl dm S p = .ok I) :
    chk S p = true ∧ I.places = S.places.map (pl p) ∧ I.defs = S.defs.map (dm p) := by
  unfold instVia at h
  split at h
  · cases h; exact ⟨by assumption, rfl, rfl⟩
  · cases h

/-- When `chk` holds, `instVia` succeeds with the mapped places and definitions. -/
theorem instVia_of_chk {chk : SubnetDef N A → String → Bool} {pl : String → N → N}
    {dm : String → CDef N A → CDef N A} {S : SubnetDef N A} {p : String} (h : chk S p = true) :
    instVia chk pl dm S p = .ok (viaInstance pl dm S p) := by
  unfold instVia
  rw [if_pos h]

/-- The reference's check: a valid prefix and no terminal place. -/
def refChk (S : SubnetDef N A) (p : String) : Bool := decide (ValidPrefix p) && S.terminals.isEmpty

/-- An instantiation without the prefix check: it renames under any string. -/
def looseInst (Nm : Naming N) : InstFn N A :=
  instVia (fun S _ => S.terminals.isEmpty) Nm.pre (fun p => CDef.map (Nm.pre p) (preS p))

/-- An instantiation that skips the prefix check when the body is empty, and is the reference
otherwise. -/
def emptyLooseInst (Nm : Naming N) : InstFn N A :=
  instVia (fun S p => (decide (ValidPrefix p) || (S.places.isEmpty && S.defs.isEmpty)) &&
    S.terminals.isEmpty) Nm.pre (fun p => CDef.map (Nm.pre p) (preS p))

/-- An instantiation without the terminal-place check: it renames every body under a valid
prefix. -/
def termLooseInst (Nm : Naming N) : InstFn N A :=
  instVia (fun _ p => decide (ValidPrefix p)) Nm.pre (fun p => CDef.map (Nm.pre p) (preS p))

/-- An instantiation that is the reference except for its messages: it rejects with the text
`rejected`, which names no place. -/
def plainMsgInst (Nm : Naming N) : InstFn N A :=
  instVia refChk Nm.pre (fun p => CDef.map (Nm.pre p) (preS p))

/-- An instantiation that rejects everything. -/
def rejectAllInst : InstFn N A := fun _ _ => .error "rejected"

/-- An instantiation that renames place and transition names, and leaves the arcs and the output
specification of every transition on the unrenamed places. -/
def namesOnlyInst (Nm : Naming N) : InstFn N A :=
  instVia refChk Nm.pre (fun p d => { d with core := { d.core with name := preS p d.core.name } })

/-- An instantiation that renames everything but the reset arcs. -/
def missesResetsInst (Nm : Naming N) : InstFn N A :=
  instVia refChk Nm.pre (fun p d =>
    let e := d.map (Nm.pre p) (preS p)
    { e with core := { e.core with resets := d.core.resets } })

end Wrong

/-- The rename with the separator `.` in place of `/`. -/
def dotS (p x : String) : String := p ++ "." ++ x

/-- An instantiation (places by name) that renames with the separator `.`. -/
def dotInst : InstFn String Unit :=
  instVia refChk dotS (fun p => CDef.map (dotS p) (dotS p))

/-- ✗ An instantiation without the prefix check violates MOD-010 (line 1): it renames the example
under `a/b`. -/
@[evidence forbids MOD_010]
theorem MOD_010_forbids_loose : ¬ MOD_010 strNaming (looseInst (A := Unit) strNaming) := by
  intro h
  obtain ⟨msg, hm⟩ := h.1 mod010_exS "a/b" (by decide)
  simp [looseInst, instVia, mod010_exS] at hm

/-- ✗ An instantiation with the separator `.` violates MOD-010 (line 3): the example's place
`slots` becomes `buf1.slots`, not `buf1/slots`. -/
@[evidence forbids MOD_010]
theorem MOD_010_forbids_dot : ¬ MOD_010 strNaming dotInst := by
  intro h
  have hI := instVia_of_chk (chk := refChk) (pl := dotS) (dm := fun p => CDef.map (dotS p) (dotS p))
    (S := mod010_exS) (p := "buf1") (by decide)
  have := ((h.2.2.1 _ _ _ hI).1 "buf1/slots").2 (by decide)
  exact absurd this (by decide)

/-- ✗ An instantiation that leaves the reset arcs unrenamed violates MOD-010 (line 3): the
example's reset arc stays on `r`. -/
@[evidence forbids MOD_010]
theorem MOD_010_forbids_missesResets :
    ¬ MOD_010 strNaming (missesResetsInst (A := Unit) strNaming) := by
  intro h
  have hI := instVia_of_chk (chk := refChk) (pl := strNaming.pre) (dm := fun p (d : CDef String Unit) =>
    let e := d.map (strNaming.pre p) (preS p)
    { e with core := { e.core with resets := d.core.resets } }) (S := mod010_exS) (p := "buf1")
    (by decide)
  have := congrArg (List.map (·.core.resets)) (h.2.2.1 _ _ _ hI).2
  exact absurd this (by decide)

/-- ✗ An instantiation that rejects a body with a terminal place without naming the place violates
MOD-010 (line 4): instantiating `fin` under `a` fails with the text `rejected`, which does not
name the terminal place `done`. -/
@[evidence forbids MOD_010]
theorem MOD_010_forbids_unnamedTerminal :
    ¬ MOD_010 strNaming (plainMsgInst (A := Unit) strNaming) := by
  intro h
  obtain ⟨msg, hm, x, hx, hn⟩ := h.2.2.2 mod010_exT "a" (by decide) (by simp [mod010_exT])
  have he : plainMsgInst (A := Unit) strNaming mod010_exT "a" = .error "rejected" := by
    unfold plainMsgInst instVia
    rw [if_neg (by decide)]
  rw [he] at hm
  cases hm
  have hx' : x = "done" := by simpa [mod010_exT] using hx
  subst hx'
  exact not_msgNames (ch := 'o') (by decide) (by decide) hn

/-! ### Mutant: line 4 dropped (no terminal-place check) -/

section MutantTerminal

variable {N A : Type}

/-- Mutant reading: MOD-010 without line 4, so instantiation need not refuse a body that declares
a terminal place. -/
def MOD_010_mutant_noTerminalCheck (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod010_line1 Inst ∧ mod010_line2 Inst ∧ mod010_line3 Nm Inst

end MutantTerminal

/-- The instantiation without the terminal-place check kills the mutant: it rejects every invalid
prefix and renames as the reference does, but it instantiates `fin`, whose body declares the
terminal place `done`, under `a` (line 4). -/
@[evidence mutant MOD_010]
theorem MOD_010_mutant_noTerminalCheck_killed :
    MOD_010_mutant_noTerminalCheck strNaming (termLooseInst (A := Unit) strNaming) ∧
      ¬ MOD_010 strNaming (termLooseInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p hp => ⟨_, if_neg (by simp [hp])⟩,
    fun S p hp _ _ _ => ⟨_, if_pos (by simp [hp])⟩, fun S p I hI => ?_⟩, fun h => ?_⟩
  · obtain ⟨-, hpl, hd⟩ := instVia_ok hI
    refine ⟨fun x => by rw [hpl], ?_⟩
    rw [hd, List.map_map]
    rfl
  · obtain ⟨msg, hm, -⟩ := h.2.2.2 mod010_exT "a" (by decide) (by simp [mod010_exT])
    have hok : termLooseInst (A := Unit) strNaming mod010_exT "a" = .ok _ :=
      instVia_of_chk (chk := fun _ p => decide (ValidPrefix p)) (by decide)
    rw [hok] at hm
    cases hm

/-! ### Mutant: line 1 dropped (no prefix check) -/

section MutantPrefix

variable {N A : Type}

/-- Mutant reading: MOD-010 without line 1, so an instantiation need not check the prefix. Line 4
is left out too: the killer's rejection text names no place, and line 4 has its own kill
(`MOD_010_forbids_unnamedTerminal`). -/
def MOD_010_mutant_dropPrefixCheck (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod010_line2 Inst ∧ mod010_line3 Nm Inst

/-- The instantiation that skips the prefix check on an empty body kills the mutant: it meets
lines 2 and 3 (an empty body renamed under any string is empty), but accepts the empty
definition under the invalid prefix `a/b` (line 1). -/
@[evidence mutant MOD_010]
theorem MOD_010_mutant_dropPrefixCheck_killed (Nm : Naming N) :
    MOD_010_mutant_dropPrefixCheck Nm (emptyLooseInst (A := A) Nm) ∧
      ¬ MOD_010 Nm (emptyLooseInst (A := A) Nm) := by
  refine ⟨⟨fun S p hp ht _ _ => ⟨_, if_pos (by simp [hp, ht])⟩, fun S p I hI => ?_⟩, fun h => ?_⟩
  · obtain ⟨-, hpl, hd⟩ := instVia_ok hI
    refine ⟨fun x => by rw [hpl], ?_⟩
    rw [hd, List.map_map]
    rfl
  · obtain ⟨msg, hm⟩ := h.1 ⟨"e", [], [], [], [], []⟩ "a/b" (by decide)
    simp [emptyLooseInst, instVia] at hm

end MutantPrefix

/-! ### Mutant: line 2 dropped (no acceptance) -/

section MutantAccept

variable {N A : Type}

/-- Mutant reading: MOD-010 without line 2, the prefix rejection and the shape of a success only
(skeptic correction S2 of the composition design: a partial function needs an acceptance line).
Line 4 is left out too: the killer's rejection text names no place. -/
def MOD_010_mutant_noAcceptance (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod010_line1 Inst ∧ mod010_line3 Nm Inst

/-- The instantiation that rejects everything kills the mutant: it meets lines 1 and 3, but
rejects the empty definition under the valid prefix `a` (line 2). -/
@[evidence mutant MOD_010]
theorem MOD_010_mutant_noAcceptance_killed (Nm : Naming N) :
    MOD_010_mutant_noAcceptance Nm (rejectAllInst (N := N) (A := A)) ∧
      ¬ MOD_010 Nm (rejectAllInst (N := N) (A := A)) := by
  refine ⟨⟨fun _ _ _ => ⟨_, rfl⟩, fun _ _ _ h => nomatch h⟩, fun h => ?_⟩
  obtain ⟨I, hI⟩ := h.2.1 ⟨"e", [], [], [], [], []⟩ "a" (by decide) rfl (fun _ h => nomatch h)
    (fun _ h => nomatch h)
  exact nomatch hI

end MutantAccept

/-! ### Mutant: line 3 read as a rename of names only -/

section MutantNames

variable {N A : Type}

/-- Mutant reading of line 3 (item 2 without item 4): a success renames every place and every
transition name under the prefix, and says nothing about the arcs. Lines 1 and 2 are as in
MOD-010; line 4 is left out, since the killer's rejection text names no place. -/
def MOD_010_mutant_namesOnly (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod010_line1 Inst ∧ mod010_line2 Inst ∧
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I →
    (∀ x, x ∈ I.places ↔ x ∈ S.places.map (Nm.pre p)) ∧
    I.defs.map (·.core.name) = S.defs.map (fun d => preS p d.core.name)

end MutantNames

/-- The instantiation that renames names only kills the mutant: it renames every place and
transition name, but the example's transition keeps its input arc on `slots` instead of
`buf1/slots` (line 3, item 4). -/
@[evidence mutant MOD_010]
theorem MOD_010_mutant_namesOnly_killed :
    MOD_010_mutant_namesOnly strNaming (namesOnlyInst (A := Unit) strNaming) ∧
      ¬ MOD_010 strNaming (namesOnlyInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p hp => ⟨_, if_neg (by simp [refChk, hp])⟩,
    fun S p hp ht _ _ => ⟨_, if_pos (by simp [refChk, hp, ht])⟩, fun S p I hI => ?_⟩, fun h => ?_⟩
  · obtain ⟨-, hpl, hd⟩ := instVia_ok hI
    refine ⟨fun x => by rw [hpl], ?_⟩
    rw [hd, List.map_map]
    rfl
  · have hI := instVia_of_chk (chk := refChk) (pl := strNaming.pre)
      (dm := fun p (d : CDef String Unit) =>
        { d with core := { d.core with name := preS p d.core.name } })
      (S := mod010_exS) (p := "buf1") (by decide)
    have := congrArg (List.map (·.core.inputs.map (·.place))) (h.2.2.1 _ _ _ hI).2
    exact absurd this (by decide)

end Libpetri.Spec
