import Libpetri.Spec.GlossaryBuild

set_option linter.missingDocs true

/-!
# Glossary: modular composition

The terms the MOD blocks ([MOD-001]–[MOD-061], `spec/11-modular-composition.md`) are stated
over. Composition is build-time only: everything here is a pure function on definitions, and a
composed net runs as an ordinary net through the existing firing relations.

* **Names.** A valid instance prefix (`ValidPrefix`: non-empty, no `/`, ruling D25 (a)) and the
  prefixed name `preS p x = p ++ "/" ++ x`. Under valid prefixes the prefixed name determines
  prefix and original name (`preS_inj`), which is what makes two instances of one definition
  disjoint; nesting reassociates (`preS_assoc`, [MOD-013]).
* **The naming model** `Naming N`: how a prefix renames a place, as a lawful model parameter, so
  that every composition block holds at every place type `N`. Its laws: a renamed place is named
  `p/name` (`pre_name`), and valid prefixes rename injectively (`pre_inj`). `strNaming` is place identity by
  name (TypeScript, Rust, Python: the key type of `refPlacesByName`), `typedNaming Ty` by name
  and token type (Java: the key type of `refPlacesByNameType`); the prefix renames the name and
  keeps the type.
* **Transition definitions under a place map.** `mapT f g` maps every place of a transition (all
  five arc kinds, every output-spec place) through `f` and its name through `g`; `TransDef.map`
  does the same on RefNetBuild's `TransDef` and keeps timing, priority and action. `CDef`
  extends `TransDef` (there is one `TransDef`, `Reference/Build.lean`) with the declared-to-actual
  place correspondence of [MOD-031]; `CDef.map` is one rewrite pass.
* **The RefFire link.** A transition renamed through an injective place map fires exactly as
  the original at the pulled-back marking and leaves every place outside the map's image as it
  was (`fires_mapT`); enablement needs no injectivity (`enabled_mapT`).
* **Interface and instances.** Ports, channels, subnet definitions, module instances and the
  instantiation function type `InstFn` ([MOD-010]); the input-arc merge table `mergeCard`
  ([MOD-021] rule (b), shared with fusion, [MOD-061]) and fusion sets ([MOD-060]).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## Names -/

/-- Glossary: *Prefix* (spec/glossary.md).

The validity half (ruling D25 (a): what Rust, Java and TypeScript check before renaming, `SubnetDef::instantiate` in `rust/libpetri-core/src/subnet_def.rs`,
`validatePrefix` in `java/src/main/java/org/libpetri/core/SubnetDef.java`,
`validatePrefix` in `typescript/src/core/subnet-def.ts`). -/
def ValidPrefix (p : String) : Prop := p ≠ "" ∧ '/' ∉ p.toList

instance (p : String) : Decidable (ValidPrefix p) := inferInstanceAs (Decidable (_ ∧ _))

/-- **Glossary: Prefix** (the rename half): under prefix `p` the name `x` is renamed `p/x`
([MOD-010] item 2: `prefix + "/" + originalName`). -/
def preS (p x : String) : String := p ++ "/" ++ x

/-- Prefixing on character lists. -/
def preL (p x : List Char) : List Char := p ++ '/' :: x

/-- On character lists, a separator-free prefix and the rest are determined by the prefixed
list. -/
theorem preL_inj : ∀ (p q x y : List Char), '/' ∉ p → '/' ∉ q → preL p x = preL q y →
    p = q ∧ x = y
  | [], [], x, y, _, _, h => by simpa [preL] using h
  | [], c :: q, x, y, _, hq, h => by
      simp [preL] at h
      exact absurd h.1.symm (by intro hc; exact hq (by simp [hc]))
  | c :: p, [], x, y, hp, _, h => by
      simp [preL] at h
      exact absurd h.1 (by intro hc; exact hp (by simp [hc]))
  | c :: p, e :: q, x, y, hp, hq, h => by
      simp [preL] at h
      obtain ⟨hce, hrest⟩ := h
      have := preL_inj p q x y (by intro hm; exact hp (by simp [hm]))
        (by intro hm; exact hq (by simp [hm])) (by simpa [preL] using hrest)
      exact ⟨by rw [hce, this.1], this.2⟩

/-- Under valid prefixes the prefixed name determines the prefix and the original name: two
instances under different prefixes never give one name. -/
theorem preS_inj (p q x y : String) (hp : ValidPrefix p) (hq : ValidPrefix q)
    (h : preS p x = preS q y) : p = q ∧ x = y := by
  have hl : preL p.toList x.toList = preL q.toList y.toList := by
    have := congrArg String.toList h
    simpa [preS, preL, String.toList_append] using this
  obtain ⟨h1, h2⟩ := preL_inj _ _ _ _ hp.2 hq.2 hl
  exact ⟨String.ext h1, String.ext h2⟩

/-- Nesting reassociates: `o/(i/x)` is the name `(o/i)/x` ([MOD-013]); no single
instantiation produces it, since `o/i` is not a valid prefix. -/
theorem preS_assoc (o i x : String) : preS o (preS i x) = preS (preS o i) x := by
  simp only [preS, String.append_assoc]

/-- **Clash R-MA1** without the prefix rule: prefix `a` over the body name `b/x` and prefix `a/b`
over the body name `x` give one name, and `a/b` is not a valid prefix. -/
theorem preS_clash_without_rule : preS "a" "b/x" = preS "a/b" "x" ∧ ¬ ValidPrefix "a/b" := by
  decide

/-! ## The naming model -/

/-- **The naming model**: how an instance prefix renames a place, with two laws: the rename of a
place's name is `p/name` ([MOD-010] item 2), and valid prefixes rename injectively and to
disjoint sets. A model parameter of every composition block, so that a block holds at every place
type: the place type `N` is the key type of the place model (`PlaceKeyed.K`, [CORE-002]), and the
rename acts on keys. -/
structure Naming (N : Type) where
  /-- The name of a place. -/
  name : N → String
  /-- The rename of a place under a prefix. -/
  pre : String → N → N
  /-- The renamed place's name is the prefixed name: `x` becomes `p/x`. -/
  pre_name : ∀ p x, name (pre p x) = preS p (name x)
  /-- Valid prefixes rename injectively and to disjoint sets of places. -/
  pre_inj : ∀ p q x y, ValidPrefix p → ValidPrefix q → pre p x = pre q y → p = q ∧ x = y

/-- Under one valid prefix the rename is injective. -/
theorem Naming.pre_injective {N : Type} (Nm : Naming N) {p : String} (hp : ValidPrefix p) :
    Function.Injective (Nm.pre p) :=
  fun _ _ h => (Nm.pre_inj _ _ _ _ hp hp h).2

/-- **Places by name** (TypeScript, Rust, Python): the place is its name, renamed to `p/name`.
`String` is the key type of `refPlacesByName` at `Nm := String`. -/
def strNaming : Naming String := ⟨id, preS, fun _ _ => rfl, preS_inj⟩

/-- **Places by name and token type** (Java, [MOD-024]'s divergence note): the prefix renames the
name and keeps the token type. `String × Ty` is the key type of `refPlacesByNameType`. -/
def typedNaming (Ty : Type) : Naming (String × Ty) where
  name x := x.1
  pre p x := (preS p x.1, x.2)
  pre_name _ _ := rfl
  pre_inj p q x y hp hq h := by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    obtain ⟨hpq, hxy⟩ := preS_inj _ _ _ _ hp hq h1
    exact ⟨hpq, Prod.ext hxy h2⟩

/-- `strNaming`'s place type is the key type of name identity. -/
theorem strNaming_key {Ty : Type} :
    (refPlacesByName (Nm := String) (Ty := Ty)).K = String := rfl

/-- `typedNaming`'s place type is the key type of name-and-type identity. -/
theorem typedNaming_key {Ty : Type} :
    (refPlacesByNameType (Nm := String) (Ty := Ty)).K = (String × Ty) := rfl

/-! ## Transitions under a place map -/

variable {N M A : Type}

/-- An input arc through a place map: the place mapped, the cardinality kept. -/
def mapIn (f : N → M) (s : NInSpec N) : NInSpec M := ⟨f s.place, s.card⟩

/-- An output specification through a place map: every place of every node mapped, the tree
kept. -/
def mapOut (f : N → M) : Out N → Out M
  | .place p => .place (f p)
  | .and l r => .and (mapOut f l) (mapOut f r)
  | .xor l r => .xor (mapOut f l) (mapOut f r)
  | .timeout c => .timeout (mapOut f c)
  | .forward a b => .forward (f a) (f b)

/-- A transition's name and arcs through a place map `f` and a name map `g`: every input,
inhibitor, read and reset place mapped, in order and with repetitions. -/
def mapCore (f : N → M) (g : String → String) (c : NTransition N) : NTransition M :=
  { name := g c.name, inputs := c.inputs.map (mapIn f), inhibitors := c.inhibitors.map f,
    reads := c.reads.map f, resets := c.resets.map f }

/-- A transition (firing view) through a place map and a name map: all five arc kinds and every
output-spec place mapped; the `reapable` bit kept. Instantiation ([MOD-010]: `f = Nm.pre p`,
`g = preS p`), port substitution ([MOD-020], `g = id`) and fusion ([MOD-061], before the input
merge) are instances. -/
def mapT (f : N → M) (g : String → String) (t : Trans N) : Trans M :=
  ⟨mapCore f g t.core, t.out.map (mapOut f), t.reapable⟩

/-- A transition definition through a place map and a name map: arcs and output specification
mapped as `mapT` does; timing, priority and action kept ([MOD-010] item 5). -/
def _root_.Libpetri.Reference.TransDef.map (f : N → M) (g : String → String) (d : TransDef N A) :
    TransDef M A :=
  ⟨mapCore f g d.core, d.out.map (mapOut f), d.timing, d.priority, d.action⟩

/-- The firing view of a mapped definition is the mapped firing view. -/
theorem TransDef.map_toTrans (f : N → M) (g : String → String) (d : TransDef N A) :
    (d.map f g).toTrans = mapT f g d.toTrans := rfl

/-- Mapping keeps the timing, the priority and the action. -/
theorem TransDef.map_kept (f : N → M) (g : String → String) (d : TransDef N A) :
    (d.map f g).timing = d.timing ∧ (d.map f g).priority = d.priority ∧
      (d.map f g).action = d.action := ⟨rfl, rfl, rfl⟩

/-- The name of a mapped definition is the mapped name. -/
theorem TransDef.map_name (f : N → M) (g : String → String) (d : TransDef N A) :
    (d.map f g).core.name = g d.core.name := rfl

/-! ## Composition definitions -/

/-- A transition definition as composition carries it: RefNetBuild's `TransDef` (one record for
building, composition and ν-nets) and the declared-to-actual place correspondence of [MOD-031]
(`none`: a hand-written definition, which resolves every place to itself). -/
structure CDef (N A : Type) extends TransDef N A where
  /-- The correspondence from declared places to the places the arcs now name ([MOD-031]). -/
  corr : Option (List (N × N)) := none

/-- Look a declared place up in a correspondence: the first entry for it. -/
def corrLookup [DecidableEq N] (al : List (N × N)) (p : N) : Option N :=
  (al.find? fun e => decide (e.1 = p)).map (·.2)

/-- Resolve a declared place of a definition ([MOD-031], as Java and TypeScript do it): through
the correspondence first, the place itself when there is no entry or no correspondence. -/
def CDef.resolve [DecidableEq N] (d : CDef N A) (p : N) : N :=
  match d.corr with
  | none => p
  | some al => (corrLookup al p).getD p

/-- The correspondence after one rewrite pass through `σ`: a carried correspondence is chained
(keys kept, values through `σ`); a hand-written definition gets one entry per place it names.
(The MAY of [MOD-031], dropping an all-identity correspondence, is not taken.) -/
def corrPass (σ : N → N) (d : CDef N A) : List (N × N) :=
  match d.corr with
  | some al => al.map fun e => (e.1, σ e.2)
  | none => d.namedPlaces.map fun p => (p, σ p)

/-- **One rewrite pass** of a composition definition through the place map `σ` and the name map
`g`: the definition mapped (`TransDef.map`), the correspondence chained (`corrPass`). -/
def CDef.map (σ : N → N) (g : String → String) (d : CDef N A) : CDef N A :=
  { d.toTransDef.map σ g with corr := some (corrPass σ d) }

/-- A rewrite pass maps the definition as `TransDef.map` does. -/
theorem CDef.map_toTransDef (σ : N → N) (g : String → String) (d : CDef N A) :
    (d.map σ g).toTransDef = d.toTransDef.map σ g := rfl

/-! ## The interface, subnet definitions and module instances -/

/-- A port direction ([MOD-003]). -/
inductive Dir where
  /-- Tokens flow into the subnet. -/
  | input
  /-- Tokens flow out of the subnet. -/
  | output
  /-- Both. -/
  | inout
  deriving DecidableEq, Repr

/-- A port ([MOD-003]): a name, a direction and the body place it exposes. -/
structure Port (N : Type) where
  /-- The port's name. -/
  name  : String
  /-- The port's direction. -/
  dir   : Dir
  /-- The body place the port exposes. -/
  place : N

/-- A synchronous channel ([MOD-005]): a name and the body transition it exposes, by name (ruling
D10: transitions are identified by name). -/
structure Chan where
  /-- The channel's name. -/
  name  : String
  /-- The name of the body transition the channel exposes. -/
  trans : String
  deriving DecidableEq, Repr

/-- What a host hands the subnet builder ([MOD-001], [MOD-006]): a name, a body (places,
transition definitions in order, declared terminal places) and an interface (ports, channels). -/
structure SubnetIn (N A : Type) where
  /-- The definition's name. -/
  name      : String
  /-- The body's places. -/
  places    : List N
  /-- The body's transition definitions, in order. -/
  defs      : List (CDef N A)
  /-- The body's declared terminal places ([EXEC-042]). -/
  terminals : List N := []
  /-- The interface's ports. -/
  ports     : List (Port N)
  /-- The interface's channels. -/
  chans     : List Chan

/-- Glossary: *Subnet definition* (spec/glossary.md).

A subnet definition as the subnet builder returns it: the same fields as its input. -/
structure SubnetDef (N A : Type) where
  /-- The definition's name. -/
  name      : String
  /-- The body's places. -/
  places    : List N
  /-- The body's transition definitions, in order. -/
  defs      : List (CDef N A)
  /-- The body's declared terminal places ([EXEC-042]). -/
  terminals : List N := []
  /-- The interface's ports. -/
  ports     : List (Port N)
  /-- The interface's channels. -/
  chans     : List Chan

/-- Glossary: *Module instance* (spec/glossary.md).

A module instance: the prefix, the renamed body (places, definitions in order), the handles
(`port`, `chan`: the renamed place of a port name, the renamed transition name of a channel
name, `none` for a name the interface does not declare) and the definition's ports, unrenamed. -/
structure Instance (N A : Type) where
  /-- The prefix. -/
  pfx    : String
  /-- The renamed body's places. -/
  places : List N
  /-- The renamed body's definitions, in order. -/
  defs   : List (CDef N A)
  /-- The renamed place of a port name ([MOD-011]). -/
  port   : String → Option N
  /-- The renamed transition name of a channel name ([MOD-011]). -/
  chan   : String → Option String
  /-- The definition's ports, unrenamed ([MOD-024]). -/
  iface  : List (Port N)

/-- An instantiation function ([MOD-010]): a subnet definition and a prefix give a module instance
or a rejection with a message. The parameters value is not modelled (its type is checked by the
host language, [MOD-010] AC4). -/
abbrev InstFn (N A : Type) := SubnetDef N A → String → Except String (Instance N A)

/-! ## The input-arc merge table and fusion sets -/

/-- **The input-arc merge table** ([MOD-021] rule (b)): two input arcs on one place merge into
one; `none` is rule (c), a rejection. Shared with fusion ([MOD-061]). -/
def mergeCard : Card → Card → Option Card
  | .one, .one => some (.exactly 2)
  | .one, .exactly n => some (.exactly (n + 1))
  | .exactly n, .one => some (.exactly (n + 1))
  | .exactly n, .exactly m => some (.exactly (n + m))
  | .all, .all => some .all
  | .atLeast n, .atLeast m => some (.atLeast (max n m))
  | _, _ => none

/-- The merge table is symmetric. -/
theorem mergeCard_comm (a b : Card) : mergeCard a b = mergeCard b a := by
  cases a <;> cases b <;> simp [mergeCard, Nat.add_comm, Nat.max_comm]

/-- A fusion set ([MOD-060]): a name (diagnostics only) and the member places, in declaration
order. -/
structure FusionSet (N : Type) where
  /-- The set's name. -/
  name    : String
  /-- The member places, in declaration order. -/
  members : List N

/-- The canonical member of a fusion set: the first declared (ruling R-MC6 (a)); `dflt` for an
empty set, which the builder rejects. -/
def FusionSet.canonical (s : FusionSet N) (dflt : N) : N := s.members.headD dflt

/-! ## The RefFire link: renamed transitions fire as the original -/

section Link

/-- The branches of a mapped output specification are the mapped branches. -/
theorem cross_map (f : N → M) (xs ys : List (List N)) :
    cross (xs.map (List.map f)) (ys.map (List.map f)) = (cross xs ys).map (List.map f) := by
  simp [cross, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- The branches of a mapped output specification are the mapped branches. -/
theorem branches_mapOut (f : N → M) :
    ∀ o : Out N, (mapOut f o).branches = o.branches.map (List.map f)
  | .place p => rfl
  | .forward _ _ => rfl
  | .and l r => by
      simp only [mapOut, Out.branches, branches_mapOut f l, branches_mapOut f r, cross_map]
  | .xor l r => by
      simp only [mapOut, Out.branches, branches_mapOut f l, branches_mapOut f r, List.map_append]
  | .timeout c => by simp only [mapOut, Out.branches, branches_mapOut f c]

/-- The timeout deposits of a mapped output specification are the mapped deposits, when the
consumed counts agree on the mapped places. -/
theorem timeoutDeposits_mapOut (f : N → M) (c' : M → Nat) (c : N → Nat)
    (hc : ∀ x, c' (f x) = c x) :
    ∀ o : Out N, (mapOut f o).timeoutDeposits c' = (o.timeoutDeposits c).map (List.map f)
  | .place p => rfl
  | .forward s d => by
      simp [mapOut, Out.timeoutDeposits, hc, List.map_replicate]
  | .and l r => by
      simp only [mapOut, Out.timeoutDeposits, timeoutDeposits_mapOut f c' c hc l,
        timeoutDeposits_mapOut f c' c hc r, cross_map]
  | .xor l r => by
      simp only [mapOut, Out.timeoutDeposits, timeoutDeposits_mapOut f c' c hc l,
        timeoutDeposits_mapOut f c' c hc r, List.map_append]
  | .timeout o => by simp only [mapOut, Out.timeoutDeposits, timeoutDeposits_mapOut f c' c hc o]

/-- The timeout node of a mapped output specification is the mapped timeout node. -/
theorem findTimeout_mapOut (f : N → M) :
    ∀ o : Out N, (mapOut f o).findTimeout = o.findTimeout.map (mapOut f)
  | .place _ => rfl
  | .forward _ _ => rfl
  | .timeout _ => rfl
  | .and l r => by
      simp only [mapOut, Out.findTimeout, findTimeout_mapOut f l, findTimeout_mapOut f r]
      cases l.findTimeout <;> rfl
  | .xor l r => by
      simp only [mapOut, Out.findTimeout, findTimeout_mapOut f l, findTimeout_mapOut f r]
      cases l.findTimeout <;> rfl

/-- The deposit of a mapped transition is the mapped deposit, when the consumed counts agree on
the mapped places. -/
theorem deposit_mapOut (f : N → M) (c' : M → Nat) (c : N → Nat) (hc : ∀ x, c' (f x) = c x)
    (o : Option (Out N)) (ch : Novel.ForwardDeposit.Choice) :
    deposit c' (o.map (mapOut f)) ch = (deposit c o ch).map (List.map f) := by
  cases o with
  | none =>
    cases ch with
    | action i => cases i <;> rfl
    | timedOut j => rfl
  | some o =>
    cases ch with
    | action i => simp [deposit, branches_mapOut]
    | timedOut j =>
      simp only [deposit, Option.map_some, findTimeout_mapOut]
      cases o.findTimeout with
      | none => rfl
      | some t => simp [timeoutDeposits_mapOut f c' c hc]

/-- **Enablement under a place map**: a mapped transition is enabled at `m` exactly when the
original is enabled at the pulled-back marking `m ∘ f`. No injectivity is needed. -/
theorem enabled_mapT (f : N → M) (g : String → String) (t : Trans N) (m : M → Nat) :
    enabledNA m (mapT f g t).core = enabledNA (fun n => m (f n)) t.core := by
  simp [enabledNA, mapT, mapCore, mapIn, List.all_map, Function.comp_def]
  first | done | rfl

variable [DecidableEq N] [DecidableEq M]

/-- The input arc a mapped transition has on a mapped place is the mapped arc, under an injective
map. -/
theorem nspecAt_mapCore {f : N → M} (hf : Function.Injective f) (g : String → String)
    (c : NTransition N) (x : N) :
    nspecAt (mapCore f g c) (f x) = (nspecAt c x).map (mapIn f) := by
  simp only [nspecAt, mapCore, List.find?_map]
  congr 2
  funext s
  simp only [Function.comp_def, mapIn, decide_eq_decide]
  exact hf.eq_iff

omit [DecidableEq N] in
/-- A mapped transition has no input arc on a place outside the map's image. -/
theorem nspecAt_mapCore_out {f : N → M} (g : String → String) (c : NTransition N) {y : M}
    (hy : ∀ x, f x ≠ y) : nspecAt (mapCore f g c) y = none := by
  simp only [nspecAt, mapCore, List.find?_map, Option.map_eq_none_iff, List.find?_eq_none]
  intro s _
  simpa [mapIn] using hy s.place

/-- A mapped transition consumes from a mapped place what the original consumes at the
pulled-back marking, under an injective map. -/
theorem nconsumed_mapCore {f : N → M} (hf : Function.Injective f) (g : String → String)
    (c : NTransition N) (m : M → Nat) (x : N) :
    nconsumed m (mapCore f g c) (f x) = nconsumed (fun n => m (f n)) c x := by
  simp only [nconsumed, nspecAt_mapCore hf]
  cases nspecAt c x <;> rfl

omit [DecidableEq N] in
/-- A mapped transition consumes nothing from a place outside the map's image. -/
theorem nconsumed_mapCore_out {f : N → M} (g : String → String) (c : NTransition N)
    (m : M → Nat) {y : M} (hy : ∀ x, f x ≠ y) : nconsumed m (mapCore f g c) y = 0 := by
  simp only [nconsumed, nspecAt_mapCore_out g c hy]

omit [DecidableEq N] [DecidableEq M] in
/-- An injective map keeps membership. -/
theorem mem_map_inj {f : N → M} (hf : Function.Injective f) {l : List N} {x : N} :
    f x ∈ l.map f ↔ x ∈ l := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := List.mem_map.1 h
    exact hf he ▸ ha
  · exact List.mem_map_of_mem

/-- An injective map keeps counts. -/
theorem count_map_inj {f : N → M} (hf : Function.Injective f) (l : List N) (x : N) :
    (l.map f).count (f x) = l.count x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq, hf.eq_iff]

omit [DecidableEq N] in
/-- A place outside the map's image is counted zero times in a mapped list. -/
theorem count_map_out {f : N → M} (l : List N) {y : M} (hy : ∀ x, f x ≠ y) :
    (l.map f).count y = 0 := by
  rw [List.count_eq_zero]
  intro h
  obtain ⟨a, -, he⟩ := List.mem_map.1 h
  exact hy a he

/-- The successor counts of a mapped firing, on a mapped place, are the original's at the
pulled-back marking, under an injective map. -/
theorem fireNC_mapCore {f : N → M} (hf : Function.Injective f) (g : String → String)
    (c : NTransition N) (m : M → Nat) (d : List N) (x : N) :
    fireNC m (mapCore f g c) (depProd (d.map f)) (f x) =
      fireNC (fun n => m (f n)) c (depProd d) x := by
  show (if f x ∈ c.resets.map f then (d.map f).count (f x)
      else m (f x) - nconsumed m (mapCore f g c) (f x) + (d.map f).count (f x)) = _
  rw [nconsumed_mapCore hf, count_map_inj hf]
  simp only [fireNC, depProd, mem_map_inj hf]

omit [DecidableEq N] in
/-- A mapped firing leaves a place outside the map's image as it was. -/
theorem fireNC_mapCore_out {f : N → M} (g : String → String) (c : NTransition N)
    (m : M → Nat) (d : List N) {y : M} (hy : ∀ x, f x ≠ y) :
    fireNC m (mapCore f g c) (depProd (d.map f)) y = m y := by
  have hr : y ∉ (mapCore f g c).resets := by
    intro h
    obtain ⟨a, -, he⟩ := List.mem_map.1 h
    exact hy a he
  simp only [fireNC, if_neg hr, nconsumed_mapCore_out g c m hy, depProd, count_map_out d hy]
  omega

/-- **The RefFire link** ([MOD-010]): under an injective place map `f`, a mapped transition
fires from `m` with deposit `d'` to `m'` exactly when `d'` is the mapped deposit of a firing of
the original from the pulled-back marking `m ∘ f` to `m' ∘ f`, and every place outside the map's
image keeps its count. A renamed transition behaves as the original, and touches no place the
rename does not reach. -/
theorem fires_mapT {f : N → M} (hf : Function.Injective f) (g : String → String) (t : Trans N)
    (m : M → Nat) (d' : List M) (m' : M → Nat) :
    Fires (mapT f g t) m d' m' ↔
      ∃ d, d' = d.map f ∧ Fires t (fun x => m (f x)) d (fun x => m' (f x)) ∧
        ∀ y, (∀ x, f x ≠ y) → m' y = m y := by
  have hc : ∀ x, nconsumed m (mapCore f g t.core) (f x) =
      nconsumed (fun n => m (f n)) t.core x := nconsumed_mapCore hf g t.core m
  constructor
  · rintro ⟨hen, ⟨ch, hdep⟩, rfl⟩
    have hdep' : deposit (nconsumed m (mapCore f g t.core)) (t.out.map (mapOut f)) ch = some d' :=
      hdep
    rw [deposit_mapOut f _ _ hc, Option.map_eq_some_iff] at hdep'
    obtain ⟨d, hd, rfl⟩ := hdep'
    refine ⟨d, rfl, ⟨?_, ⟨ch, hd⟩, ?_⟩, fun y hy => ?_⟩
    · rw [← enabled_mapT f g t m]; exact hen
    · funext x; exact fireNC_mapCore hf g t.core m d x
    · exact fireNC_mapCore_out g t.core m d hy
  · rintro ⟨d, rfl, ⟨hen, ⟨ch, hd⟩, hm'⟩, hout⟩
    refine ⟨by rw [enabled_mapT f g t m]; exact hen, ⟨ch, ?_⟩, ?_⟩
    · show deposit (nconsumed m (mapCore f g t.core)) (t.out.map (mapOut f)) ch = _
      rw [deposit_mapOut f _ _ hc, hd]; rfl
    · funext y
      by_cases hy : ∃ x, f x = y
      · obtain ⟨x, rfl⟩ := hy
        show m' (f x) = fireNC m (mapCore f g t.core) (depProd (d.map f)) (f x)
        rw [fireNC_mapCore hf g t.core m d x, ← hm']
      · have hy' : ∀ x, f x ≠ y := fun x h => hy ⟨x, h⟩
        show m' y = fireNC m (mapCore f g t.core) (depProd (d.map f)) y
        rw [fireNC_mapCore_out g t.core m d hy', hout y hy']

end Link

/-! ## Agreement of an instantiation function with a firing relation -/

/-- **Renamed firings match** under the firing relation `F`: for every instance `Inst` returns
under prefix `p`, every definition of the renamed body is the rename of a body definition, and
fires under `F` exactly as that definition fires at the marking pulled back through the rename,
leaving every place outside the rename's image as it was. The agreement conjunct that ties an
instantiation function to the firing relation of the CORE and IO blocks. -/
def InstFiresAsBody (Nm : Naming N) (Inst : InstFn N A) (F : FireRel N) : Prop :=
  ∀ S p I, Inst S p = .ok I → ∀ d ∈ I.defs, ∃ d₀ ∈ S.defs,
    ∀ m dep m', F d.toTrans m dep m' ↔
      ∃ dep₀, dep = dep₀.map (Nm.pre p) ∧
        F d₀.toTrans (fun x => m (Nm.pre p x)) dep₀ (fun x => m' (Nm.pre p x)) ∧
        ∀ y, (∀ x, Nm.pre p x ≠ y) → m' y = m y

/-! ## Diagnostics: a message names a string -/

/-- **A message names a string**: it contains the string as a substring. Every MOD block that
asks a rejection to name something (a port, a channel, a place, a transition, a token type)
reads "names" this way. A message that happens to contain a short name meets it, and an empty
name is contained in every message. -/
def MsgNames (msg s : String) : Prop := s.toList <:+: msg.toList

/-- A message of the form `a ++ s ++ c` names `s`. -/
theorem msgNames_mid (a s c : String) : MsgNames (a ++ s ++ c) s := by
  unfold MsgNames
  simp only [String.toList_append]
  exact List.infix_append _ _ _

/-- A message ending in `s` names `s`. -/
theorem msgNames_end (a s : String) : MsgNames (a ++ s) s := by
  unfold MsgNames
  simp only [String.toList_append]
  exact (List.suffix_append _ _).isInfix

/-- A message names what its beginning names. -/
theorem msgNames_app {m s : String} (t : String) (h : MsgNames m s) : MsgNames (m ++ t) s := by
  unfold MsgNames at *
  simp only [String.toList_append]
  exact h.trans (List.prefix_append _ _).isInfix

/-- A message names what its end names. -/
theorem msgNames_appL {m s : String} (t : String) (h : MsgNames m s) : MsgNames (t ++ m) s := by
  unfold MsgNames at *
  simp only [String.toList_append]
  exact h.trans (List.suffix_append _ _).isInfix

/-- The append form: a message names `s` exactly when it is `u ++ s ++ v` for some `u` and `v`. -/
theorem msgNames_iff_append {m s : String} : MsgNames m s ↔ ∃ u v, m = u ++ s ++ v := by
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨String.ofList u, String.ofList v, String.ext ?_⟩
    simp [String.toList_append, h]
  · rintro ⟨u, v, rfl⟩
    exact msgNames_mid u s v

/-- A message names itself. -/
theorem msgNames_self (s : String) : MsgNames s s := List.infix_refl _

/-- A message that names `s` holds every character of `s`. -/
theorem msgNames_chars {msg s : String} (h : MsgNames msg s) {ch : Char} (hc : ch ∈ s.toList) :
    ch ∈ msg.toList :=
  List.IsInfix.subset h hc

/-- A message without the character `ch` does not name a string that holds it. -/
theorem not_msgNames {msg s : String} {ch : Char} (hc : ch ∈ s.toList) (hn : ch ∉ msg.toList) :
    ¬ MsgNames msg s := fun h => hn (msgNames_chars h hc)

end Libpetri.Spec
