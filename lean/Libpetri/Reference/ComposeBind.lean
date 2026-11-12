import Libpetri.Reference.ComposeDef
import Libpetri.Reference.Fuse

set_option linter.missingDocs true

/-!
# RefCompose: port binding

The binding slice of the composition model ([MOD-020], [MOD-022], [MOD-024], [MOD-025]): what an
enclosing builder holds (`Bld`), and the three ways an instance or a definition enters it.

* `refCompose tyOf Build Mg` is `compose(instance, bindings)` ([MOD-020]). In the runtimes' order
  (Rust `rust/libpetri-core/src/petri_net.rs` `compose_internal` / `apply_composition` /
  `reject_port_collision` and `compose.rs` `bind_port` / `bind_channel`; Java
  `java/src/main/java/org/libpetri/core/PetriNet.java` `composeInternal` / `rejectPortCollisions`
  / `applyComposition`; TypeScript `typescript/src/core/petri-net.ts` `compose`):
  1. a port bound twice in one call, an unknown port, and (where the place model carries a token
     type, `tyOf`, [MOD-022]) a caller place of another type than the port reject the call;
  2. a channel bound twice, an unknown channel, a channel whose transition is missing from the
     instance, and two channels on one transition reject the call;
  3. every bound port resolves to its renamed place (`bindEntries`); the place map `bindSubst`
     sends each such place to its caller place and keeps every other place;
  4. every definition of the instance, in order: two different bound ports sent to one caller
     place with an input arc on each reject with the input collision message, the same inside
     one AND branch with the output collision message; otherwise the definition is rewritten
     through `bindSubst` in all five arc kinds and the output specification, name, timing,
     priority and action kept (`rewriteDef`), and rebuilt through the transition builder's
     check `Build`, whose message a failure carries (`bindStep`);
  5. a rewritten definition that a channel binding names is replaced by the merge `Mg caller d`
     of the caller-side definition and it, at the same position (`mergeStep`; the merge itself is
     [MOD-021]'s `refMerge`, a parameter here);
  6. the builder keeps its definitions and appends the new ones; it gains every place an arc of a
     new definition names (an instance place no arc names is not added); every bound port whose
     caller place differs from its renamed place is recorded as retired, a place already recorded
     keeping its first record ([MOD-027], checked at build).
* `refAuto Nm tyOf Build Mg` is `compose(instance)` ([MOD-024]): a declared channel rejects; with
  ports, it is `refCompose` with every port bound to its own unrenamed body place; without ports,
  every renamed body place whose original place the builder holds is bound to it (`inferEntries`).
* `refDirect Nm tyOf` is `compose(definition)` ([MOD-025]): a declared terminal place, a declared
  channel, a body transition whose name the builder holds, and (typed place models) a body place
  whose name the builder holds with another token type reject; otherwise the body's places and
  definitions are appended unrenamed and every body node is recorded under the definition's name,
  `/` written as `_` ([MOD-026]).

Not modelled: a caller-side transition already in the builder (ruling D42 (m): assumed absent;
Java and TypeScript replace it, Rust keeps both); the declaration slot of a merged transition
(here the slot of the instance-side transition, as in Rust; Java appends merged transitions
first); which offender a message names when there are several; the hash order in which Rust
visits bindings. Two ports over one body place bound to different caller places (ruling D35)
keep the first binding here; the runtimes keep one of them.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## The builder state -/

/-- A retired port ([MOD-027]): the renamed port place that a compose call replaced by a caller
place, the port's name, the instance prefix and the caller place. -/
structure Retired (N : Type) where
  /-- The renamed port place, gone from the composed net. -/
  place  : N
  /-- The port's name. -/
  port   : String
  /-- The instance prefix. -/
  pfx    : String
  /-- The caller place the port was bound to. -/
  caller : N
  deriving DecidableEq, Repr

/-- **What an enclosing builder holds** ([CORE-040], [MOD-020]): the declared and collected places,
the transition definitions in the order added, the declared terminal places, and what composition
leaves for `build()`: the retired ports ([MOD-027]), the subnet contributions of direct
composition (node name, recorded definition name; [MOD-026]) and the declared fusion sets
([MOD-060]). -/
structure Bld (N A : Type) where
  /-- The places, in the order added. -/
  places    : List N
  /-- The transition definitions, in the order added. -/
  defs      : List (CDef N A)
  /-- The declared terminal places ([EXEC-042]). -/
  terminals : List N := []
  /-- The retired ports ([MOD-027]). -/
  retired   : List (Retired N) := []
  /-- The subnet contributions of direct composition: node name, recorded definition name. -/
  contrib   : List (String × String) := []
  /-- The declared fusion sets ([MOD-060]). -/
  fusions   : List (FusionSet N) := []

/-- The empty builder. -/
def Bld.empty : Bld N A := ⟨[], [], [], [], [], []⟩

/-- One port binding resolved on an instance: the renamed port place, the port's name and the
caller place it is bound to. -/
structure BindEntry (N : Type) where
  /-- The renamed port place. -/
  place  : N
  /-- The port's name. -/
  port   : String
  /-- The caller place. -/
  caller : N
  deriving DecidableEq, Repr

/-- The port bindings of a compose call resolved on the instance: one entry per binding whose port
the instance knows, in the order given. -/
def bindEntries (I : Instance N A) (ports : List (String × N)) : List (BindEntry N) :=
  ports.filterMap fun e => (I.port e.1).map fun q => ⟨q, e.1, e.2⟩

/-- **A composition function** ([MOD-020]): a builder, an instance, port bindings (port name,
caller place) and channel bindings (channel name, caller-side definition) give the builder after
the call, or a rejection with a message. -/
abbrev ComposeFn (N A : Type) :=
  Bld N A → Instance N A → List (String × N) → List (String × CDef N A) → Except String (Bld N A)

/-- **An auto-composition function** ([MOD-024]): a builder, an instance and the names of the
channels its definition declares give the builder after the call, or a rejection. -/
abbrev AutoFn (N A : Type) := Bld N A → Instance N A → List String → Except String (Bld N A)

/-- **A direct-composition function** ([MOD-025]): a builder and a subnet definition give the
builder after the call, or a rejection. -/
abbrev DirectFn (N A : Type) := Bld N A → SubnetDef N A → Except String (Bld N A)

/-- Every port of a compose call is bound at most once. -/
def PortsDistinct (ports : List (String × N)) : Prop := (ports.map (·.1)).Nodup

/-- Every port of a compose call is a port of the instance. -/
def PortsKnown (I : Instance N A) (ports : List (String × N)) : Prop :=
  ∀ e ∈ ports, I.port e.1 ≠ none

/-- Every bound caller place has the token type of its port's place ([MOD-022]), where the place
model keeps a token type `tyOf`. -/
def PortTypesAgree {T : Type} (tyOf : N → T) (I : Instance N A) (ports : List (String × N)) :
    Prop :=
  ∀ e ∈ ports, ∀ q, I.port e.1 = some q → tyOf q = tyOf e.2

/-- The channel bindings of a compose call are well formed: no channel bound twice, every channel
known to the instance, every channel's transition among the instance's definitions, and no two
channels on one transition. -/
def ChansOk (I : Instance N A) (chans : List (String × CDef N A)) : Prop :=
  (chans.map (·.1)).Nodup ∧ (∀ c ∈ chans, I.chan c.1 ≠ none) ∧
    (∀ c ∈ chans, ∀ t, I.chan c.1 = some t → t ∈ I.defs.map (·.core.name)) ∧
    (chans.filterMap fun c => I.chan c.1).Nodup

section Subst

variable [DecidableEq N]

/-- The first binding of a renamed place. -/
def bindLookup (bm : List (BindEntry N)) (q : N) : Option (BindEntry N) :=
  bm.find? fun e => decide (e.place = q)

/-- **The binding's place map** ([MOD-020] item 2): a bound port place goes to its caller place,
every other place stays. -/
def bindSubst (bm : List (BindEntry N)) (q : N) : N :=
  ((bindLookup bm q).map (·.caller)).getD q

/-- **One definition rewritten through the binding** ([MOD-020] items 2 and 4): every arc and
output-spec place through `bindSubst`, the name kept, timing, priority and action kept, the
[MOD-031] correspondence chained. -/
def rewriteDef (bm : List (BindEntry N)) (d : CDef N A) : CDef N A := d.map (bindSubst bm) id

/-- Two different places that are both bound, to one caller place: the shape of a port-binding
collision. -/
def BindClash (bm : List (BindEntry N)) (a b : N) : Prop :=
  a ≠ b ∧ ∃ e e', bindLookup bm a = some e ∧ bindLookup bm b = some e' ∧ e.caller = e'.caller

/-- **Input collision** ([MOD-020]): two different bound ports sent to one caller place, with an
input arc of the definition on each. -/
def InCollision (bm : List (BindEntry N)) (d : CDef N A) : Prop :=
  ∃ a ∈ d.core.inputs.map (·.place), ∃ b ∈ d.core.inputs.map (·.place), BindClash bm a b

/-- **Output collision** ([MOD-020]): two different bound ports sent to one caller place, both
named in one AND branch of the definition's output specification. -/
def OutCollision (bm : List (BindEntry N)) (d : CDef N A) : Prop :=
  ∃ o, d.out = some o ∧ ∃ br ∈ o.branches, ∃ a ∈ br, ∃ b ∈ br, BindClash bm a b

end Subst

/-- A direct composition whose body has a transition name the builder already holds. -/
def DirectNameClash (b : Bld N A) (S : SubnetDef N A) : Prop :=
  ∃ d ∈ S.defs, ∃ d' ∈ b.defs, d'.core.name = d.core.name

/-- A direct composition whose body has a place whose name the builder holds with another token
type (`tyOf`; never, where the place model keeps no token type). -/
def DirectTypeClash {T : Type} (Nm : Naming N) (tyOf : N → T) (b : Bld N A) (S : SubnetDef N A) :
    Prop :=
  ∃ x ∈ S.places, ∃ h ∈ b.places, Nm.name h = Nm.name x ∧ tyOf h ≠ tyOf x

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N A : Type}

/-! ## Helpers -/

/-- The first element of a list that occurs again later in it. -/
def bindDup {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: xs => if x ∈ xs then some x else bindDup xs

theorem bindDup_eq_none_iff {α : Type} [DecidableEq α] :
    ∀ l : List α, bindDup l = none ↔ l.Nodup
  | [] => by simp [bindDup]
  | x :: xs => by
    by_cases h : x ∈ xs
    · simp [bindDup, h]
    · simp [bindDup, h, bindDup_eq_none_iff xs]

theorem bindDup_some {α : Type} [DecidableEq α] {l : List α} {x : α} (h : bindDup l = some x) :
    ¬ l.Nodup := by
  intro hn
  rw [← bindDup_eq_none_iff] at hn
  rw [hn] at h
  cases h

/-- The places `new` adds to `ps`: those not yet there, once each, after the old ones. -/
def appendNew [DecidableEq N] (ps new : List N) : List N :=
  ps ++ (new.filter fun p => decide (p ∉ ps)).eraseDups

theorem mem_appendNew [DecidableEq N] {ps new : List N} {p : N} :
    p ∈ appendNew ps new ↔ p ∈ ps ∨ p ∈ new := by
  unfold appendNew
  simp only [List.mem_append, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  by_cases h : p ∈ ps <;> simp [h]

theorem appendNew_nil [DecidableEq N] (ps : List N) : appendNew ps [] = ps := by
  simp [appendNew]

/-! ## The place map -/

section Subst

variable [DecidableEq N]

theorem bindLookup_some {bm : List (BindEntry N)} {q : N} {e : BindEntry N}
    (h : bindLookup bm q = some e) : e ∈ bm ∧ e.place = q := by
  unfold bindLookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem bindLookup_eq_none_iff {bm : List (BindEntry N)} {q : N} :
    bindLookup bm q = none ↔ ∀ e ∈ bm, e.place ≠ q := by
  unfold bindLookup
  simp [List.find?_eq_none]

theorem bindLookup_isSome {bm : List (BindEntry N)} {e : BindEntry N} (he : e ∈ bm) :
    ∃ e', bindLookup bm e.place = some e' := by
  cases h : bindLookup bm e.place with
  | none => exact absurd rfl ((bindLookup_eq_none_iff.1 h) e he)
  | some e' => exact ⟨e', rfl⟩

theorem bindSubst_of_lookup {bm : List (BindEntry N)} {q : N} {e : BindEntry N}
    (h : bindLookup bm q = some e) : bindSubst bm q = e.caller := by
  simp [bindSubst, h]

theorem bindSubst_of_none {bm : List (BindEntry N)} {q : N} (h : ∀ e ∈ bm, e.place ≠ q) :
    bindSubst bm q = q := by
  simp [bindSubst, bindLookup_eq_none_iff.2 h]

/-- A place of the binding's image: a caller place, or a place no binding names. -/
theorem bindSubst_cases (bm : List (BindEntry N)) (q : N) :
    (∃ e ∈ bm, e.place = q ∧ bindSubst bm q = e.caller) ∨
      ((∀ e ∈ bm, e.place ≠ q) ∧ bindSubst bm q = q) := by
  cases h : bindLookup bm q with
  | none =>
    have hn := bindLookup_eq_none_iff.1 h
    exact Or.inr ⟨hn, bindSubst_of_none hn⟩
  | some e =>
    obtain ⟨he, hq⟩ := bindLookup_some h
    exact Or.inl ⟨e, he, hq, bindSubst_of_lookup h⟩

/-- **The port place is gone** ([MOD-020] item 5, eager): when no caller place of the binding is
itself a bound port place, nothing is sent to a bound port place whose caller differs from it. -/
theorem bindSubst_ne_place {bm : List (BindEntry N)} {e : BindEntry N} (he : e ∈ bm)
    (hc : ∀ e₁ ∈ bm, ∀ e₂ ∈ bm, e₁.caller ≠ e₂.place) (r : N) : bindSubst bm r ≠ e.place := by
  rcases bindSubst_cases bm r with ⟨e₁, he₁, -, hs⟩ | ⟨hn, hs⟩
  · rw [hs]; exact hc e₁ he₁ e he
  · rw [hs]; intro h; exact hn e he h.symm

omit [DecidableEq N] in
theorem mem_bindEntries {I : Instance N A} {ports : List (String × N)} {e : BindEntry N} :
    e ∈ bindEntries I ports ↔ (e.port, e.caller) ∈ ports ∧ I.port e.port = some e.place := by
  unfold bindEntries
  simp only [List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨n, X⟩, hx, q, hq, rfl⟩
    exact ⟨hx, hq⟩
  · rintro ⟨hx, hq⟩
    exact ⟨(e.port, e.caller), hx, e.place, hq, rfl⟩

/-- The places a rewritten definition names are the original's through the place map. -/
theorem rewriteDef_namedPlaces (bm : List (BindEntry N)) (d : CDef N A) :
    (rewriteDef bm d).namedPlaces = d.namedPlaces.map (bindSubst bm) := by
  cases d with
  | mk td corr =>
    cases td with
    | mk core out timing priority action =>
      cases out <;>
        simp [rewriteDef, CDef.map, TransDef.map, TransDef.namedPlaces, mapCore, mapIn,
          outPlaces_mapOut, List.map_map, Function.comp_def]

theorem rewriteDef_name (bm : List (BindEntry N)) (d : CDef N A) :
    (rewriteDef bm d).core.name = d.core.name := rfl

theorem rewriteDef_toTransDef (bm : List (BindEntry N)) (d : CDef N A) :
    (rewriteDef bm d).toTransDef = d.toTransDef.map (bindSubst bm) id := rfl

/-- **A rewritten definition names no retired port place**: under the premise of
`bindSubst_ne_place`, no place a rewritten definition names is a bound port place. -/
theorem rewriteDef_clears {bm : List (BindEntry N)} {e : BindEntry N} (he : e ∈ bm)
    (hc : ∀ e₁ ∈ bm, ∀ e₂ ∈ bm, e₁.caller ≠ e₂.place) (d : CDef N A) :
    e.place ∉ (rewriteDef bm d).namedPlaces := by
  rw [rewriteDef_namedPlaces]
  intro h
  obtain ⟨r, -, hr⟩ := List.mem_map.1 h
  exact bindSubst_ne_place he hc r hr

end Subst

/-! ## Collisions -/

section Collide

variable [DecidableEq N]

/-- The clash of two places under a binding, with their entries. -/
def clashPair (bm : List (BindEntry N)) (a b : N) : Option (BindEntry N × BindEntry N) :=
  match bindLookup bm a, bindLookup bm b with
  | some e, some e' => if a ≠ b ∧ e.caller = e'.caller then some (e, e') else none
  | _, _ => none

theorem clashPair_eq_none_iff {bm : List (BindEntry N)} {a b : N} :
    clashPair bm a b = none ↔ ¬ BindClash bm a b := by
  unfold clashPair BindClash
  cases ha : bindLookup bm a <;> cases hb : bindLookup bm b <;> simp

theorem clashPair_some {bm : List (BindEntry N)} {a b : N} {e e' : BindEntry N}
    (h : clashPair bm a b = some (e, e')) :
    BindClash bm a b ∧ bindLookup bm a = some e ∧ bindLookup bm b = some e' := by
  unfold clashPair at h
  cases ha : bindLookup bm a <;> cases hb : bindLookup bm b <;> simp [ha, hb] at h
  rename_i x y
  obtain ⟨⟨hne, hc⟩, rfl, rfl⟩ := h
  exact ⟨⟨hne, x, y, ha, hb, hc⟩, rfl, rfl⟩

/-- Every clashing pair of a list of places, in list order. -/
def collPairs (bm : List (BindEntry N)) (l : List N) : List (BindEntry N × BindEntry N) :=
  l.flatMap fun a => l.filterMap (clashPair bm a)

theorem collPairs_eq_nil_iff {bm : List (BindEntry N)} {l : List N} :
    collPairs bm l = [] ↔ ¬ ∃ a ∈ l, ∃ b ∈ l, BindClash bm a b := by
  simp only [collPairs, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff,
    clashPair_eq_none_iff]
  constructor
  · rintro h ⟨a, ha, b, hb, hc⟩; exact h a ha b hb hc
  · intro h a ha b hb hc; exact h ⟨a, ha, b, hb, hc⟩

theorem mem_collPairs {bm : List (BindEntry N)} {l : List N} {e e' : BindEntry N}
    (h : (e, e') ∈ collPairs bm l) :
    ∃ a ∈ l, ∃ b ∈ l, BindClash bm a b ∧ bindLookup bm a = some e ∧ bindLookup bm b = some e' := by
  simp only [collPairs, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨a, ha, b, hb, hp⟩ := h
  exact ⟨a, ha, b, hb, clashPair_some hp⟩

/-- The input-side clashing pairs of a definition. -/
def inPairs (bm : List (BindEntry N)) (d : CDef N A) : List (BindEntry N × BindEntry N) :=
  collPairs bm (d.core.inputs.map (·.place))

/-- The output-side clashing pairs of a definition: inside one branch of its output
specification. -/
def outPairs (bm : List (BindEntry N)) (d : CDef N A) : List (BindEntry N × BindEntry N) :=
  match d.out with
  | none => []
  | some o => o.branches.flatMap (collPairs bm)

theorem inPairs_eq_nil_iff {bm : List (BindEntry N)} {d : CDef N A} :
    inPairs bm d = [] ↔ ¬ InCollision bm d := collPairs_eq_nil_iff

theorem outPairs_eq_nil_iff {bm : List (BindEntry N)} {d : CDef N A} :
    outPairs bm d = [] ↔ ¬ OutCollision bm d := by
  unfold outPairs OutCollision
  cases ho : d.out with
  | none => simp
  | some o =>
    simp only [List.flatMap_eq_nil_iff, collPairs_eq_nil_iff, Option.some.injEq, exists_eq_left']
    constructor
    · rintro h ⟨br, hbr, hc⟩; exact h br hbr hc
    · intro h br hbr hc; exact h ⟨br, hbr, hc⟩

theorem inPairs_head {bm : List (BindEntry N)} {d : CDef N A} {e e' : BindEntry N}
    (h : (inPairs bm d).head? = some (e, e')) :
    ∃ a ∈ d.core.inputs.map (·.place), ∃ b ∈ d.core.inputs.map (·.place),
      BindClash bm a b ∧ bindLookup bm a = some e ∧ bindLookup bm b = some e' :=
  mem_collPairs (List.mem_of_mem_head? h)

theorem outPairs_head {bm : List (BindEntry N)} {d : CDef N A} {e e' : BindEntry N}
    (h : (outPairs bm d).head? = some (e, e')) :
    ∃ o, d.out = some o ∧ ∃ br ∈ o.branches, ∃ a ∈ br, ∃ b ∈ br,
      BindClash bm a b ∧ bindLookup bm a = some e ∧ bindLookup bm b = some e' := by
  have hm := List.mem_of_mem_head? h
  unfold outPairs at hm
  cases ho : d.out with
  | none => simp [ho] at hm
  | some o =>
    simp only [ho, List.mem_flatMap] at hm
    obtain ⟨br, hbr, hp⟩ := hm
    exact ⟨o, rfl, br, hbr, mem_collPairs hp⟩

end Collide

/-! ## Messages -/

section Msg

variable [ToString N]

/-- The input collision message of [MOD-020] (the text of all three runtimes). -/
def inCollMsg (pfx : String) (e e' : BindEntry N) (t : String) : String :=
  s!"ports '{e.port}' and '{e'.port}' of instance '{pfx}' are both bound to host place '{e.caller}'; transition '{t}' would consume from '{e.caller}' through two input arcs. Bind them to distinct places or use one port."

/-- The output collision message of [MOD-020] (the text of all three runtimes). -/
def outCollMsg (pfx : String) (e e' : BindEntry N) (t : String) : String :=
  s!"ports '{e.port}' and '{e'.port}' of instance '{pfx}' are both bound to host place '{e.caller}'; transition '{t}' would produce into '{e.caller}' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port."

/-- A port bound twice in one call (Rust `compose.rs` `bind_port`; ruling D72 (i)(a): the message
names the port). -/
def dupPortMsg (n : String) : String := s!"Port '{n}' is already bound"

/-- A channel bound twice in one call (Rust `compose.rs` `bind_channel`). -/
def dupChanMsg (n : String) : String := s!"Channel '{n}' is already bound"

/-- An unknown port (stand-in text; the runtimes add the known ports). -/
def unknownPortMsg (pfx n : String) : String :=
  s!"compose: no port named '{n}' on instance prefix '{pfx}'"

/-- An unknown channel (stand-in text; the runtimes add the known channels). -/
def unknownChanMsg (pfx n : String) : String :=
  s!"compose: no channel named '{n}' on instance prefix '{pfx}'"

/-- A channel whose transition is not among the instance's definitions, or a second channel on one
transition (stand-in text; Rust and Java fail when the instance-side transition is not staged). -/
def chanTransMsg (pfx n : String) : String :=
  s!"compose: channel '{n}' of instance prefix '{pfx}' resolved to a transition that is not staged"

/-- A caller place whose token type differs from its port's ([MOD-022]; the text follows Java). -/
def portTypeMsg {T : Type} [ToString T] (pfx n : String) (tq tx : T) (X : N) : String :=
  s!"compose: port '{n}' of instance prefix '{pfx}' has token type {tq} but caller place '{X}' has token type {tx} (MOD-022)"

end Msg

/-! ## The checks before the rewrite -/

section Checks

variable {T : Type} [DecidableEq T] [ToString T] [ToString N]

/-- A binding whose caller place has another token type than its port's place. -/
def portTyBad (tyOf : N → T) (I : Instance N A) (e : String × N) : Bool :=
  match I.port e.1 with
  | some q => decide (tyOf q ≠ tyOf e.2)
  | none => false

/-- The message for a binding of the wrong type. -/
def portTyMsgOf (tyOf : N → T) (I : Instance N A) (e : String × N) : String :=
  match I.port e.1 with
  | some q => portTypeMsg I.pfx e.1 (tyOf q) (tyOf e.2) e.2
  | none => unknownPortMsg I.pfx e.1

/-- The port checks of a compose call, in order: a port bound twice, an unknown port, a caller
place of another token type. -/
def portCheck (tyOf : N → T) (I : Instance N A) (ports : List (String × N)) : Option String :=
  match bindDup (ports.map (·.1)) with
  | some n => some (dupPortMsg n)
  | none =>
    match ports.find? (fun e => (I.port e.1).isNone) with
    | some e => some (unknownPortMsg I.pfx e.1)
    | none =>
      match ports.find? (portTyBad tyOf I) with
      | some e => some (portTyMsgOf tyOf I e)
      | none => none

/-- A channel whose transition is missing from the instance's definitions. -/
def chanMissing (I : Instance N A) (c : String × CDef N A) : Bool :=
  match I.chan c.1 with
  | some t => !(I.defs.any fun d => d.core.name == t)
  | none => false

/-- The channel checks of a compose call, in order: a channel bound twice, an unknown channel, a
channel whose transition is missing, two channels on one transition. -/
def chanCheck (I : Instance N A) (chans : List (String × CDef N A)) : Option String :=
  match bindDup (chans.map (·.1)) with
  | some n => some (dupChanMsg n)
  | none =>
    match chans.find? (fun c => (I.chan c.1).isNone) with
    | some c => some (unknownChanMsg I.pfx c.1)
    | none =>
      match chans.find? (chanMissing I) with
      | some c => some (chanTransMsg I.pfx c.1)
      | none =>
        match bindDup (chans.filterMap fun c => I.chan c.1) with
        | some t => some (chanTransMsg I.pfx t)
        | none => none

theorem portCheck_eq_none_iff {tyOf : N → T} {I : Instance N A} {ports : List (String × N)} :
    portCheck tyOf I ports = none ↔
      PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree tyOf I ports := by
  have e1 : bindDup (ports.map (·.1)) = none ↔ PortsDistinct ports := bindDup_eq_none_iff _
  have e2 : ports.find? (fun e => (I.port e.1).isNone) = none ↔ PortsKnown I ports := by
    rw [List.find?_eq_none]; simp [PortsKnown, Option.isNone_iff_eq_none]
  have e3 : ports.find? (portTyBad tyOf I) = none ↔ PortTypesAgree tyOf I ports := by
    rw [List.find?_eq_none]
    unfold PortTypesAgree
    refine forall_congr' fun e => imp_congr_right fun _ => ?_
    cases hq : I.port e.1 <;> simp [portTyBad, hq]
  unfold portCheck
  cases h1 : bindDup (ports.map (·.1)) with
  | some n =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hd, -, -⟩; rw [e1.2 hd] at h1; cases h1
  | none =>
    cases h2 : ports.find? (fun e => (I.port e.1).isNone) with
    | some x =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨-, hk, -⟩; rw [e2.2 hk] at h2; cases h2
    | none =>
      cases h3 : ports.find? (portTyBad tyOf I) with
      | some x =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, -, ht⟩; rw [e3.2 ht] at h3; cases h3
      | none => simp only [true_iff]; exact ⟨e1.1 h1, e2.1 h2, e3.1 h3⟩

omit [ToString N] in
theorem chanCheck_eq_none_iff {I : Instance N A} {chans : List (String × CDef N A)} :
    chanCheck I chans = none ↔ ChansOk I chans := by
  have e1 : bindDup (chans.map (·.1)) = none ↔ (chans.map (·.1)).Nodup := bindDup_eq_none_iff _
  have e2 : chans.find? (fun c => (I.chan c.1).isNone) = none ↔ ∀ c ∈ chans, I.chan c.1 ≠ none := by
    rw [List.find?_eq_none]; simp [Option.isNone_iff_eq_none]
  have e3 : chans.find? (chanMissing I) = none ↔
      ∀ c ∈ chans, ∀ t, I.chan c.1 = some t → t ∈ I.defs.map (·.core.name) := by
    rw [List.find?_eq_none]
    refine forall_congr' fun c => imp_congr_right fun _ => ?_
    cases ht : I.chan c.1 <;> simp [chanMissing, ht]
  have e4 := bindDup_eq_none_iff (chans.filterMap fun c => I.chan c.1)
  unfold chanCheck ChansOk
  cases h1 : bindDup (chans.map (·.1)) with
  | some n =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hd, -, -, -⟩; rw [e1.2 hd] at h1; cases h1
  | none =>
    cases h2 : chans.find? (fun c => (I.chan c.1).isNone) with
    | some x =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨-, hk, -, -⟩; rw [e2.2 hk] at h2; cases h2
    | none =>
      cases h3 : chans.find? (chanMissing I) with
      | some x =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, -, hm, -⟩; rw [e3.2 hm] at h3; cases h3
      | none =>
        cases h4 : bindDup (chans.filterMap fun c => I.chan c.1) with
        | some t =>
          simp only [reduceCtorEq, false_iff]
          rintro ⟨-, -, -, hs⟩; rw [e4.2 hs] at h4; cases h4
        | none =>
          simp only [true_iff]; exact ⟨e1.1 h1, e2.1 h2, e3.1 h3, e4.1 h4⟩

end Checks

/-! ## One definition through the binding, and the channel merges -/

section Steps

variable [DecidableEq N] [ToString N]

/-- **One instance definition through the binding** ([MOD-020]): an input collision rejects with
the input collision message, an output collision with the output collision message; otherwise the
rewritten definition, which `Build` must accept (a failure carries `Build`'s message). -/
def bindStep (Build : Trans N → Option String) (pfx : String) (bm : List (BindEntry N))
    (d : CDef N A) : Except String (CDef N A) :=
  match (inPairs bm d).head? with
  | some (e, e') => .error (inCollMsg pfx e e' d.core.name)
  | none =>
    match (outPairs bm d).head? with
    | some (e, e') => .error (outCollMsg pfx e e' d.core.name)
    | none =>
      match Build (rewriteDef bm d).toTrans with
      | some m => .error m
      | none => .ok (rewriteDef bm d)

/-- **One rewritten definition through the channel bindings** ([MOD-021]): the definition a channel
names is replaced by the merge `Mg caller d`; any other stays. -/
def mergeStep (Mg : CDef N A → CDef N A → Except String (CDef N A)) (I : Instance N A)
    (chans : List (String × CDef N A)) (d : CDef N A) : Except String (CDef N A) :=
  match chans.find? (fun c => decide (I.chan c.1 = some d.core.name)) with
  | some c => Mg c.2 d
  | none => .ok d

/-- The builder after a compose call's definitions `ms`: the old definitions then the new ones,
the old places then every place a new definition names that the builder lacks. -/
def bindAssemble (b : Bld N A) (ms : List (CDef N A)) : Bld N A :=
  { b with places := appendNew b.places (ms.flatMap (·.namedPlaces)), defs := b.defs ++ ms }

/-- The retired records of a binding ([MOD-027]): one per bound port whose caller place differs
from its renamed place. -/
def retiredOf (pfx : String) (bm : List (BindEntry N)) : List (Retired N) :=
  bm.filterMap fun e => if e.place = e.caller then none else some ⟨e.place, e.port, pfx, e.caller⟩

/-- New retired records after old ones; a place already recorded keeps its first record (Rust
`petri_net.rs` `apply_composition`, Java `retiredPorts.putIfAbsent`). -/
def addRetired (old new : List (Retired N)) : List (Retired N) :=
  new.foldl (fun acc r => if acc.any (fun x => decide (x.place = r.place)) then acc else acc ++ [r])
    old

/-- The builder with a compose call's retired records added. -/
def retire (pfx : String) (bm : List (BindEntry N)) (b : Bld N A) : Bld N A :=
  { b with retired := addRetired b.retired (retiredOf pfx bm) }

/-- The rewrite and merge of a compose call over resolved bindings `bm`: every instance definition
through `bindStep`, in order, then the channel merges, then the definitions and places added. -/
def applyBind (Build : Trans N → Option String) (Mg : CDef N A → CDef N A → Except String (CDef N A))
    (b : Bld N A) (I : Instance N A) (bm : List (BindEntry N)) (chans : List (String × CDef N A)) :
    Except String (Bld N A) :=
  match I.defs.mapM (bindStep Build I.pfx bm) with
  | .error m => .error m
  | .ok ds => (ds.mapM (mergeStep Mg I chans)).map (bindAssemble b)

end Steps

/-! ## The reference composition functions -/

section Compose

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- **The reference composition** ([MOD-020]): the port checks, the channel checks, then every
instance definition rewritten through the binding (collisions and `Build` checked per
definition), the channel merges through `Mg`, the new definitions and their places added, and the
retired ports recorded. `tyOf` is the token type where the place model keeps one ([MOD-022]:
`Prod.snd` on `typedNaming` keys for Java, `fun _ => ()` where nothing is checked). -/
def refCompose (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  match portCheck tyOf I ports with
  | some m => .error m
  | none =>
    match chanCheck I chans with
    | some m => .error m
    | none =>
      (applyBind Build Mg b I (bindEntries I ports) chans).map (retire I.pfx (bindEntries I ports))

/- The reference composition is the witness model of the composition blocks. -/
#spec_witness refCompose

/-- The inferred bindings of auto-composition without ports ([MOD-024]): every builder place `h`
whose renamed copy `Nm.pre p h` is a place of the instance binds that copy to `h`. -/
def inferEntries (Nm : Naming N) (b : Bld N A) (I : Instance N A) : List (BindEntry N) :=
  b.places.filterMap fun h =>
    if Nm.pre I.pfx h ∈ I.places then some ⟨Nm.pre I.pfx h, toString (Nm.pre I.pfx h), h⟩
    else none

/-- Auto-composition of an instance whose definition declares channels (stand-in text). -/
def autoChanMsg (pfx : String) (cs : List String) : String :=
  s!"compose_auto: instance prefix '{pfx}' declares channels {cs}; auto-compose does not bind channels"

/-- **The reference auto-composition** ([MOD-024]): a declared channel rejects; with ports, the
reference composition with every port bound to its own unrenamed body place; without ports, every
renamed body place whose original place the builder holds is bound to it. `cs` is the names of the
channels the instance's definition declares. -/
def refAuto (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : AutoFn N A := fun b I cs =>
  if cs.isEmpty then
    if I.iface.isEmpty then applyBind Build Mg b I (inferEntries Nm b I) []
    else refCompose tyOf Build Mg b I (I.iface.map fun pt => (pt.name, pt.place)) []
  else .error (autoChanMsg I.pfx cs)

/- The reference auto-composition is the witness model of the auto-composition block. -/
#spec_witness refAuto

/-- The name a direct composition records for its definition ([MOD-026]): `/` written as `_`. -/
def contribName (s : String) : String :=
  String.ofList (s.toList.map fun c => if c = '/' then '_' else c)

/-- The builder after a direct composition: the body's places, then every place a body definition
names, added where missing; the body's definitions appended unrenamed; one contribution per body
place and per body definition under the definition's recorded name. -/
def directAssemble (Nm : Naming N) (b : Bld N A) (S : SubnetDef N A) : Bld N A :=
  { b with
    places := appendNew b.places (S.places ++ S.defs.flatMap (·.namedPlaces))
    defs := b.defs ++ S.defs
    contrib := b.contrib ++ (S.places.map (fun x => (Nm.name x, contribName S.name)) ++
      S.defs.map fun d => (d.core.name, contribName S.name)) }

/-- **The reference direct composition** ([MOD-025]): a declared terminal place ([EXEC-042]), a
declared channel, a body transition whose name the builder holds, and a body place whose name the
builder holds with another token type reject (stand-in texts); otherwise `directAssemble`. -/
def refDirect (Nm : Naming N) (tyOf : N → T) : DirectFn N A := fun b S =>
  if !S.terminals.isEmpty then
    .error s!"compose(SubnetDef): subnet '{S.name}' declares terminal places (EXEC-042)"
  else if !S.chans.isEmpty then
    .error s!"compose(SubnetDef): subnet '{S.name}' declares channels; direct composition does not bind channels"
  else
    match S.defs.find? (fun d => b.defs.any fun d' => d'.core.name == d.core.name) with
    | some d =>
      .error s!"compose(SubnetDef): transition '{d.core.name}' from subnet '{S.name}' collides with a transition already in the net"
    | none =>
      match S.places.find? (fun x => b.places.any fun h =>
          Nm.name h == Nm.name x && decide (tyOf h ≠ tyOf x)) with
      | some x =>
        .error s!"compose(SubnetDef): place '{Nm.name x}' has another token type in the net than in subnet '{S.name}' (MOD-025)"
      | none => .ok (directAssemble Nm b S)

/- The reference direct composition is the witness model of the direct-composition block. -/
#spec_witness refDirect

end Compose

/-! ## Lemmas: one definition, the merges, the assembly -/

section StepLemmas

variable [DecidableEq N] [ToString N]

/-- `mapM` in `Except` of a function that succeeds on `x` exactly when `P x`, with `g x`. -/
theorem mapM_except_det {ε α β : Type} (f : α → Except ε β) (P : α → Prop) (g : α → β)
    (hf : ∀ x y, f x = .ok y ↔ P x ∧ y = g x) :
    ∀ (l : List α) (ys : List β), l.mapM f = .ok ys ↔ (∀ x ∈ l, P x) ∧ ys = l.map g := by
  intro l ys
  rw [mapM_except_ok_iff]
  induction l generalizing ys with
  | nil => cases ys <;> simp
  | cons x l ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [List.forall₂_cons, hf, ih]
      simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.cons.injEq]
      tauto

theorem bindStep_ok_iff {Build : Trans N → Option String} {pfx : String}
    {bm : List (BindEntry N)} {d d' : CDef N A} :
    bindStep Build pfx bm d = .ok d' ↔
      ¬ InCollision bm d ∧ ¬ OutCollision bm d ∧ Build (rewriteDef bm d).toTrans = none ∧
        d' = rewriteDef bm d := by
  rw [← inPairs_eq_nil_iff, ← outPairs_eq_nil_iff, ← List.head?_eq_none_iff,
    ← List.head?_eq_none_iff]
  unfold bindStep
  cases hi : (inPairs bm d).head? with
  | some p => obtain ⟨e, e'⟩ := p; simp
  | none =>
    cases ho : (outPairs bm d).head? with
    | some p => obtain ⟨e, e'⟩ := p; simp
    | none =>
      cases hb : Build (rewriteDef bm d).toTrans with
      | some m => simp
      | none => simp [eq_comm]

theorem mapM_bindStep_ok_iff {Build : Trans N → Option String} {pfx : String}
    {bm : List (BindEntry N)} {l ds : List (CDef N A)} :
    l.mapM (bindStep Build pfx bm) = .ok ds ↔
      (∀ d ∈ l, ¬ InCollision bm d ∧ ¬ OutCollision bm d ∧
        Build (rewriteDef bm d).toTrans = none) ∧ ds = l.map (rewriteDef bm) :=
  mapM_except_det _ _ _ (fun _ _ => by rw [bindStep_ok_iff]; tauto) l ds

/-- An input collision rejects with the input collision message naming the first clashing
pair. -/
theorem bindStep_inColl {Build : Trans N → Option String} {pfx : String}
    {bm : List (BindEntry N)} {d : CDef N A} {e e' : BindEntry N}
    (h : (inPairs bm d).head? = some (e, e')) :
    bindStep Build pfx bm d = .error (inCollMsg pfx e e' d.core.name) := by
  simp [bindStep, h]

/-- An output collision, with no input collision, rejects with the output collision message
naming the first clashing pair. -/
theorem bindStep_outColl {Build : Trans N → Option String} {pfx : String}
    {bm : List (BindEntry N)} {d : CDef N A} {e e' : BindEntry N}
    (hi : ¬ InCollision bm d) (h : (outPairs bm d).head? = some (e, e')) :
    bindStep Build pfx bm d = .error (outCollMsg pfx e e' d.core.name) := by
  have hi' : (inPairs bm d).head? = none := by
    rw [List.head?_eq_none_iff]; exact inPairs_eq_nil_iff.2 hi
  simp [bindStep, hi', h]

/-- With no collision, a rewritten definition `Build` rejects fails with `Build`'s message. -/
theorem bindStep_build {Build : Trans N → Option String} {pfx : String}
    {bm : List (BindEntry N)} {d : CDef N A} {m : String}
    (hi : ¬ InCollision bm d) (ho : ¬ OutCollision bm d)
    (hb : Build (rewriteDef bm d).toTrans = some m) :
    bindStep Build pfx bm d = .error m := by
  have hi' : (inPairs bm d).head? = none := by
    rw [List.head?_eq_none_iff]; exact inPairs_eq_nil_iff.2 hi
  have ho' : (outPairs bm d).head? = none := by
    rw [List.head?_eq_none_iff]; exact outPairs_eq_nil_iff.2 ho
  simp [bindStep, hi', ho', hb]

omit [DecidableEq N] [ToString N] in
theorem mergeStep_of_find {Mg : CDef N A → CDef N A → Except String (CDef N A)}
    {I : Instance N A} {chans : List (String × CDef N A)} {d : CDef N A} {c : String × CDef N A}
    (h : chans.find? (fun c => decide (I.chan c.1 = some d.core.name)) = some c) :
    mergeStep Mg I chans d = Mg c.2 d := by
  simp [mergeStep, h]

omit [DecidableEq N] [ToString N] in
/-- A definition no channel names is kept as it is. -/
theorem mergeStep_none {Mg : CDef N A → CDef N A → Except String (CDef N A)}
    {I : Instance N A} {chans : List (String × CDef N A)} {d : CDef N A}
    (h : ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name) : mergeStep Mg I chans d = .ok d := by
  have : chans.find? (fun c => decide (I.chan c.1 = some d.core.name)) = none := by
    rw [List.find?_eq_none]; intro c hc; simpa using h c hc
  simp [mergeStep, this]

omit [DecidableEq N] [ToString N] in
/-- The definition a channel names is merged by `Mg` with the first such channel's caller-side
definition. -/
theorem mergeStep_some {Mg : CDef N A → CDef N A → Except String (CDef N A)}
    {I : Instance N A} {chans : List (String × CDef N A)} {d : CDef N A}
    (h : ∃ c ∈ chans, I.chan c.1 = some d.core.name) :
    ∃ c ∈ chans, I.chan c.1 = some d.core.name ∧ mergeStep Mg I chans d = Mg c.2 d := by
  cases hf : chans.find? (fun c => decide (I.chan c.1 = some d.core.name)) with
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨c, hc, he⟩ := h
    exact absurd (by simpa using he) (hf c hc)
  | some c =>
    exact ⟨c, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf,
      mergeStep_of_find hf⟩

omit [DecidableEq N] [ToString N] in
theorem mergeStep_ok {Mg : CDef N A → CDef N A → Except String (CDef N A)}
    {I : Instance N A} {chans : List (String × CDef N A)} {d : CDef N A}
    (h : ∀ c ∈ chans, I.chan c.1 = some d.core.name → ∃ m, Mg c.2 d = .ok m) :
    ∃ m, mergeStep Mg I chans d = .ok m := by
  by_cases hc : ∃ c ∈ chans, I.chan c.1 = some d.core.name
  · obtain ⟨c, hc, he, hs⟩ := mergeStep_some (Mg := Mg) hc
    rw [hs]; exact h c hc he
  · exact ⟨d, mergeStep_none fun c hm he => hc ⟨c, hm, he⟩⟩

theorem applyBind_ok_iff {Build : Trans N → Option String}
    {Mg : CDef N A → CDef N A → Except String (CDef N A)} {b b' : Bld N A} {I : Instance N A}
    {bm : List (BindEntry N)} {chans : List (String × CDef N A)} :
    applyBind Build Mg b I bm chans = .ok b' ↔
      (∀ d ∈ I.defs, ¬ InCollision bm d ∧ ¬ OutCollision bm d ∧
        Build (rewriteDef bm d).toTrans = none) ∧
      ∃ ms, (I.defs.map (rewriteDef bm)).mapM (mergeStep Mg I chans) = .ok ms ∧
        b' = bindAssemble b ms := by
  unfold applyBind
  cases h : I.defs.mapM (bindStep Build I.pfx bm) with
  | error m =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hall
    have := (mapM_bindStep_ok_iff (pfx := I.pfx) (Build := Build)).2 ⟨hall, rfl⟩
    rw [h] at this; cases this
  | ok ds =>
    obtain ⟨hall, rfl⟩ := (mapM_bindStep_ok_iff (pfx := I.pfx) (Build := Build)).1 h
    simp only [except_map_ok_iff]
    constructor
    · rintro ⟨ms, hms, rfl⟩; exact ⟨hall, ms, hms, rfl⟩
    · rintro ⟨-, ms, hms, rfl⟩; exact ⟨ms, hms, rfl⟩

omit [ToString N] in
theorem bindAssemble_defs (b : Bld N A) (ms : List (CDef N A)) :
    (bindAssemble b ms).defs = b.defs ++ ms := rfl

omit [ToString N] in
theorem mem_bindAssemble_places {b : Bld N A} {ms : List (CDef N A)} {p : N} :
    p ∈ (bindAssemble b ms).places ↔ p ∈ b.places ∨ ∃ d ∈ ms, p ∈ d.namedPlaces := by
  simp [bindAssemble, mem_appendNew, List.mem_flatMap]

omit [ToString N] in
theorem addRetired_nil (old : List (Retired N)) : addRetired old [] = old := rfl

omit [ToString N] in
theorem addRetired_cons (old : List (Retired N)) (r : Retired N) (rs : List (Retired N)) :
    addRetired old (r :: rs) =
      addRetired (if old.any (fun x => decide (x.place = r.place)) then old else old ++ [r]) rs :=
  rfl

omit [ToString N] in
/-- The old records are kept, first, as they were. -/
theorem addRetired_prefix : ∀ (old new : List (Retired N)), ∃ l, addRetired old new = old ++ l
  | old, [] => ⟨[], by simp [addRetired_nil]⟩
  | old, r :: rs => by
    rw [addRetired_cons]
    split
    · exact addRetired_prefix old rs
    · obtain ⟨l, hl⟩ := addRetired_prefix (old ++ [r]) rs
      exact ⟨r :: l, by simp [hl]⟩

omit [ToString N] in
/-- Every record comes from the old or the new ones. -/
theorem mem_addRetired : ∀ {old new : List (Retired N)} {x : Retired N},
    x ∈ addRetired old new → x ∈ old ∨ x ∈ new
  | old, [], x, h => Or.inl h
  | old, r :: rs, x, h => by
    rw [addRetired_cons] at h
    split at h
    · rcases mem_addRetired h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases mem_addRetired h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · simp at h; exact Or.inr (h ▸ List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)

omit [ToString N] in
/-- Every new record's place is recorded. -/
theorem addRetired_covers : ∀ {old new : List (Retired N)} {r : Retired N}, r ∈ new →
    ∃ x ∈ addRetired old new, x.place = r.place
  | _, [], _, h => by cases h
  | old, r' :: rs, r, h => by
    rw [addRetired_cons]
    rcases List.mem_cons.1 h with rfl | h
    · split
      · rename_i hx
        obtain ⟨x, hx, he⟩ := List.any_eq_true.1 hx
        obtain ⟨l, hl⟩ := addRetired_prefix old rs
        exact ⟨x, by rw [hl]; exact List.mem_append_left _ hx, by simpa using he⟩
      · obtain ⟨l, hl⟩ := addRetired_prefix (old ++ [r]) rs
        exact ⟨r, by rw [hl]; simp, rfl⟩
    · exact addRetired_covers h

omit [ToString N] in
theorem mem_retiredOf {pfx : String} {bm : List (BindEntry N)} {r : Retired N} :
    r ∈ retiredOf pfx bm ↔ ∃ e ∈ bm, e.place ≠ e.caller ∧ r = ⟨e.place, e.port, pfx, e.caller⟩ := by
  unfold retiredOf
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    by_cases hc : e.place = e.caller
    · simp [hc] at h
    · simp only [hc, if_false, Option.some.injEq] at h
      exact ⟨e, he, hc, h.symm⟩
  · rintro ⟨e, he, hc, rfl⟩
    exact ⟨e, he, by simp [hc]⟩

end StepLemmas

/-! ## Lemmas: the reference composition -/

section ComposeLemmas

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {tyOf : N → T} {Build : Trans N → Option String}
  {Mg : CDef N A → CDef N A → Except String (CDef N A)}

/-- **What a successful compose call is** ([MOD-020]): the ports are bound once each, known and of
their ports' token types; the channel bindings are well formed; no instance definition has an
input or output collision and every rewritten definition passes `Build`; the channel merges
succeed with `ms`; and the builder after the call is the old one with the definitions `ms` and
their places added and the retired ports recorded. -/
theorem refCompose_ok_iff {b b' : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} :
    refCompose tyOf Build Mg b I ports chans = .ok b' ↔
      PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree tyOf I ports ∧ ChansOk I chans ∧
      (∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧
        ¬ OutCollision (bindEntries I ports) d ∧
        Build (rewriteDef (bindEntries I ports) d).toTrans = none) ∧
      ∃ ms, (I.defs.map (rewriteDef (bindEntries I ports))).mapM (mergeStep Mg I chans) = .ok ms ∧
        b' = retire I.pfx (bindEntries I ports) (bindAssemble b ms) := by
  unfold refCompose
  cases hp : portCheck tyOf I ports with
  | some m =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro h1 h2 h3
    rw [portCheck_eq_none_iff.2 ⟨h1, h2, h3⟩] at hp; cases hp
  | none =>
    obtain ⟨h1, h2, h3⟩ := portCheck_eq_none_iff.1 hp
    simp only [h1, h2, h3, true_and]
    cases hc : chanCheck I chans with
    | some m =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro h4
      rw [chanCheck_eq_none_iff.2 h4] at hc; cases hc
    | none =>
      simp only [chanCheck_eq_none_iff.1 hc, true_and]
      rw [except_map_ok_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨hall, ms, hms, rfl⟩ := applyBind_ok_iff.1 hx
        exact ⟨hall, ms, hms, rfl⟩
      · rintro ⟨hall, ms, hms, rfl⟩
        exact ⟨_, applyBind_ok_iff.2 ⟨hall, ms, hms, rfl⟩, rfl⟩

/-- **Acceptance** ([MOD-020], skeptic S2): when the ports are bound once each, known and of their
ports' types, the channel bindings are well formed, no instance definition collides, every
rewritten definition passes `Build` and every channel merge succeeds, the compose call
succeeds. -/
theorem refCompose_accepts {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h1 : PortsDistinct ports) (h2 : PortsKnown I ports)
    (h3 : PortTypesAgree tyOf I ports) (h4 : ChansOk I chans)
    (h5 : ∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧
      ¬ OutCollision (bindEntries I ports) d ∧
      Build (rewriteDef (bindEntries I ports) d).toTrans = none)
    (h6 : ∀ d ∈ I.defs, ∀ c ∈ chans, I.chan c.1 = some d.core.name →
      ∃ m, Mg c.2 (rewriteDef (bindEntries I ports) d) = .ok m) :
    ∃ b', refCompose tyOf Build Mg b I ports chans = .ok b' := by
  obtain ⟨ms, hms, -⟩ := mapM_except_ok_of_forall (mergeStep Mg I chans) (fun _ => True)
    (I.defs.map (rewriteDef (bindEntries I ports))) (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      obtain ⟨m, hm⟩ := mergeStep_ok (Mg := Mg) (I := I) (chans := chans)
        (d := rewriteDef (bindEntries I ports) d) (fun c hc he => h6 d hd c hc he)
      exact ⟨m, hm, trivial⟩)
  exact ⟨_, refCompose_ok_iff.2 ⟨h1, h2, h3, h4, h5, ms, hms, rfl⟩⟩

theorem refCompose_error_of {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)}
    (h : ¬ (PortsDistinct ports ∧ PortsKnown I ports ∧ PortTypesAgree tyOf I ports ∧
      ChansOk I chans ∧
      (∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧
        ¬ OutCollision (bindEntries I ports) d ∧
        Build (rewriteDef (bindEntries I ports) d).toTrans = none) ∧
      ∃ ms, (I.defs.map (rewriteDef (bindEntries I ports))).mapM (mergeStep Mg I chans) = .ok ms)) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m := by
  apply except_error_of_not_ok
  intro b' hb
  obtain ⟨h1, h2, h3, h4, h5, ms, hms, -⟩ := refCompose_ok_iff.1 hb
  exact h ⟨h1, h2, h3, h4, h5, ms, hms⟩

/-- A port bound twice rejects ([MOD-020], AC5). -/
theorem refCompose_dupPort {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : ¬ PortsDistinct ports) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => h hc.1

/-- A port bound twice rejects with a message naming the first such port. -/
theorem refCompose_dupPort_msg {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {n : String} (h : bindDup (ports.map (·.1)) = some n) :
    refCompose tyOf Build Mg b I ports chans = .error (dupPortMsg n) := by
  simp [refCompose, portCheck, h]

/-- An unknown port rejects. -/
theorem refCompose_unknownPort {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : ¬ PortsKnown I ports) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => h hc.2.1

/-- A caller place of another token type than its port's rejects ([MOD-022]). -/
theorem refCompose_portType {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : ¬ PortTypesAgree tyOf I ports) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => h hc.2.2.1

/-- With every port bound once and known, a caller place of another token type than its port's
rejects with the [MOD-022] message naming the first such binding. -/
theorem refCompose_portType_msg {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {e : String × N} (h1 : PortsDistinct ports)
    (h2 : PortsKnown I ports) (h : ports.find? (portTyBad tyOf I) = some e) :
    refCompose tyOf Build Mg b I ports chans = .error (portTyMsgOf tyOf I e) := by
  have hd : bindDup (ports.map (·.1)) = none := (bindDup_eq_none_iff _).2 h1
  have hk : ports.find? (fun e => (I.port e.1).isNone) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using h2 x hx
  simp [refCompose, portCheck, hd, hk, h]

/-- Ill-formed channel bindings reject. -/
theorem refCompose_chans {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : ¬ ChansOk I chans) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => h hc.2.2.2.1

/-- **An input collision rejects** ([MOD-020], AC7). -/
theorem refCompose_inCollision {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {d : CDef N A} (hd : d ∈ I.defs)
    (h : InCollision (bindEntries I ports) d) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => (hc.2.2.2.2.1 d hd).1 h

/-- **An output collision rejects** ([MOD-020], AC8). -/
theorem refCompose_outCollision {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {d : CDef N A} (hd : d ∈ I.defs)
    (h : OutCollision (bindEntries I ports) d) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => (hc.2.2.2.2.1 d hd).2.1 h

/-- **A rewritten definition the transition builder rejects rejects the call** ([MOD-020]: the
[IO-012] and [EXEC-012] rebuild failures). -/
theorem refCompose_buildFails {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {d : CDef N A} {m : String} (hd : d ∈ I.defs)
    (h : Build (rewriteDef (bindEntries I ports) d).toTrans = some m) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => by
    have := (hc.2.2.2.2.1 d hd).2.2
    rw [h] at this; cases this

/-- **A failing channel merge rejects the call** ([MOD-021]). -/
theorem refCompose_mergeFails {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {d : CDef N A} {m : String} (hd : d ∈ I.defs)
    (h : mergeStep Mg I chans (rewriteDef (bindEntries I ports) d) = .error m) :
    ∃ m, refCompose tyOf Build Mg b I ports chans = .error m :=
  refCompose_error_of fun hc => by
    obtain ⟨ms, hms⟩ := hc.2.2.2.2.2
    rw [mapM_except_ok_iff] at hms
    obtain ⟨y, -, hy⟩ := forall₂_mem_left hms _ (List.mem_map.2 ⟨d, hd, rfl⟩)
    rw [h] at hy; cases hy

/-- **The first failing definition names the error** (sole-offender message lines): with the port
and channel checks passed, every definition before `d` through the binding, and `d` failing with
`m`, the call fails with `m`. -/
theorem refCompose_step_error {b : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {pre post : List (CDef N A)} {d : CDef N A} {m : String}
    (hp : portCheck tyOf I ports = none) (hc : chanCheck I chans = none)
    (hI : I.defs = pre ++ d :: post)
    (hpre : ∀ y ∈ pre, ∃ z, bindStep Build I.pfx (bindEntries I ports) y = .ok z)
    (hd : bindStep Build I.pfx (bindEntries I ports) d = .error m) :
    refCompose tyOf Build Mg b I ports chans = .error m := by
  have := mapM_except_error_first (bindStep Build I.pfx (bindEntries I ports)) d m post hd pre hpre
  simp [refCompose, hp, hc, applyBind, hI, this, Except.map]

/-- **The builder after a successful call** ([MOD-020] items 3-5): the old definitions, then one
definition per instance definition (the rewritten one, or its channel merge); the old places and
every place a new definition names; the terminal places, contributions and fusion sets unchanged. -/
theorem refCompose_shape {b b' : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : refCompose tyOf Build Mg b I ports chans = .ok b') :
    ∃ ms, b'.defs = b.defs ++ ms ∧
      (∀ p, p ∈ b'.places ↔ p ∈ b.places ∨ ∃ d ∈ ms, p ∈ d.namedPlaces) ∧
      b'.terminals = b.terminals ∧ b'.contrib = b.contrib ∧ b'.fusions = b.fusions ∧
      List.Forall₂ (fun d m => mergeStep Mg I chans (rewriteDef (bindEntries I ports) d) = .ok m)
        I.defs ms := by
  obtain ⟨-, -, -, -, -, ms, hms, rfl⟩ := refCompose_ok_iff.1 h
  refine ⟨ms, rfl, fun p => mem_bindAssemble_places, rfl, rfl, rfl, ?_⟩
  rw [mapM_except_ok_iff] at hms
  exact List.forall₂_map_left_iff.1 hms

/-- **The retired records after a successful call** ([MOD-027]): every bound port whose caller
place differs from its renamed place has its place recorded, and every record is an old one or one
of this call's. -/
theorem refCompose_retired {b b' : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (h : refCompose tyOf Build Mg b I ports chans = .ok b') :
    b'.retired = addRetired b.retired (retiredOf I.pfx (bindEntries I ports)) := by
  obtain ⟨-, -, -, -, -, ms, -, rfl⟩ := refCompose_ok_iff.1 h
  rfl

end ComposeLemmas

/-! ## Lemmas: auto-composition and direct composition -/

section AutoLemmas

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String}
  {Mg : CDef N A → CDef N A → Except String (CDef N A)}

omit [DecidableEq N] [ToString N] in
/-- A renamed place is never the place itself: its name is longer. So a port bound to its own
unrenamed place is always retired ([MOD-024] with [MOD-027]). -/
theorem pre_ne_self (Nm : Naming N) (p : String) (x : N) : Nm.pre p x ≠ x := by
  intro h
  have h1 := Nm.pre_name p x
  rw [h] at h1
  have h2 := congrArg (fun s => s.toList.length) h1
  simp [preS, String.toList_append] at h2
  omega

/-- A declared channel rejects auto-composition. -/
theorem refAuto_chans {b : Bld N A} {I : Instance N A} {cs : List String} (h : cs ≠ []) :
    refAuto Nm tyOf Build Mg b I cs = .error (autoChanMsg I.pfx cs) := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs => rfl

/-- **With ports, auto-composition is the explicit composition** with every port bound to its own
unrenamed body place ([MOD-024] line 1). -/
theorem refAuto_ports {b : Bld N A} {I : Instance N A} (h : I.iface ≠ []) :
    refAuto Nm tyOf Build Mg b I [] =
      refCompose tyOf Build Mg b I (I.iface.map fun pt => (pt.name, pt.place)) [] := by
  cases hi : I.iface with
  | nil => exact absurd hi h
  | cons pt ps => simp [refAuto, hi]

/-- Without ports, auto-composition binds the inferred places. -/
theorem refAuto_infer {b : Bld N A} {I : Instance N A} (h : I.iface = []) :
    refAuto Nm tyOf Build Mg b I [] = applyBind Build Mg b I (inferEntries Nm b I) [] := by
  simp [refAuto, h]

/-- **An empty instance leaves the builder unchanged** ([MOD-024]). -/
theorem refAuto_empty {b : Bld N A} {I : Instance N A} (hi : I.iface = []) (hd : I.defs = []) :
    refAuto Nm tyOf Build Mg b I [] = .ok b := by
  rw [refAuto_infer hi]
  cases b
  simp [applyBind, hd, bindAssemble, appendNew_nil, Except.map, pure, Except.pure]

theorem mem_inferEntries {b : Bld N A} {I : Instance N A} {e : BindEntry N} :
    e ∈ inferEntries Nm b I ↔ ∃ h ∈ b.places, Nm.pre I.pfx h ∈ I.places ∧
      e = ⟨Nm.pre I.pfx h, toString (Nm.pre I.pfx h), h⟩ := by
  unfold inferEntries
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    by_cases hq : Nm.pre I.pfx h ∈ I.places
    · simp only [hq, if_true, Option.some.injEq] at he
      exact ⟨h, hh, hq, he.symm⟩
    · simp [hq] at he
  · rintro ⟨h, hh, hq, rfl⟩
    exact ⟨h, hh, by simp [hq]⟩

/-- **Inference binds a renamed place to its original** ([MOD-024] line 3): under a valid prefix,
when the builder holds `h` and the instance holds its renamed copy, the copy goes to `h`. -/
theorem inferSubst_of_mem {b : Bld N A} {I : Instance N A} (hp : ValidPrefix I.pfx) {h : N}
    (hh : h ∈ b.places) (hq : Nm.pre I.pfx h ∈ I.places) :
    bindSubst (inferEntries Nm b I) (Nm.pre I.pfx h) = h := by
  have hm : (⟨Nm.pre I.pfx h, toString (Nm.pre I.pfx h), h⟩ : BindEntry N) ∈ inferEntries Nm b I :=
    mem_inferEntries.2 ⟨h, hh, hq, rfl⟩
  obtain ⟨e, he⟩ := bindLookup_isSome hm
  obtain ⟨hem, hep⟩ := bindLookup_some he
  obtain ⟨h', -, -, rfl⟩ := mem_inferEntries.1 hem
  rw [bindSubst_of_lookup he]
  exact Nm.pre_injective hp hep

/-- Inference keeps a place that is no renamed copy of a builder place. -/
theorem inferSubst_of_not {b : Bld N A} {I : Instance N A} {q : N}
    (hq : ∀ h ∈ b.places, Nm.pre I.pfx h ≠ q) : bindSubst (inferEntries Nm b I) q = q := by
  apply bindSubst_of_none
  intro e he
  obtain ⟨h, hh, -, rfl⟩ := mem_inferEntries.1 he
  exact hq h hh

/-- **Every port of an auto-composed instance is retired** ([MOD-024] with [MOD-027]): a port
whose renamed place the instance resolves is recorded. -/
theorem refAuto_retired {b b' : Bld N A} {I : Instance N A} (hi : I.iface ≠ [])
    (h : refAuto Nm tyOf Build Mg b I [] = .ok b') {pt : Port N} (hpt : pt ∈ I.iface) {q : N}
    (hq : I.port pt.name = some q) (hne : q ≠ pt.place) : ∃ x ∈ b'.retired, x.place = q := by
  rw [refAuto_ports hi] at h
  rw [refCompose_retired h]
  have he : (⟨q, pt.name, pt.place⟩ : BindEntry N) ∈
      bindEntries I (I.iface.map fun pt => (pt.name, pt.place)) :=
    mem_bindEntries.2 ⟨List.mem_map.2 ⟨pt, hpt, rfl⟩, hq⟩
  exact addRetired_covers (mem_retiredOf.2 ⟨_, he, hne, rfl⟩)

end AutoLemmas

section DirectLemmas

variable [DecidableEq N] {T : Type} [DecidableEq T]
  {Nm : Naming N} {tyOf : N → T}

omit [DecidableEq N] in
theorem directNameClash_find_iff {b : Bld N A} {S : SubnetDef N A} :
    S.defs.find? (fun d => b.defs.any fun d' => d'.core.name == d.core.name) = none ↔
      ¬ DirectNameClash b S := by
  rw [List.find?_eq_none]
  simp [DirectNameClash]

omit [DecidableEq N] in
theorem directTypeClash_find_iff {b : Bld N A} {S : SubnetDef N A} :
    S.places.find? (fun x => b.places.any fun h =>
        Nm.name h == Nm.name x && decide (tyOf h ≠ tyOf x)) = none ↔
      ¬ DirectTypeClash Nm tyOf b S := by
  rw [List.find?_eq_none]
  simp [DirectTypeClash]

/-- **What a successful direct composition is** ([MOD-025]): no terminal place, no channel, no
transition name the builder holds, no place name the builder holds with another token type, and
the builder after the call is `directAssemble`. -/
theorem refDirect_ok_iff {b b' : Bld N A} {S : SubnetDef N A} :
    refDirect Nm tyOf b S = .ok b' ↔
      S.terminals = [] ∧ S.chans = [] ∧ ¬ DirectNameClash b S ∧ ¬ DirectTypeClash Nm tyOf b S ∧
        b' = directAssemble Nm b S := by
  unfold refDirect
  by_cases h1 : S.terminals = []
  · by_cases h2 : S.chans = []
    · simp only [h1, h2, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, true_and]
      cases h3 : S.defs.find? (fun d => b.defs.any fun d' => d'.core.name == d.core.name) with
      | some d =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro hn; rw [directNameClash_find_iff.2 hn] at h3; cases h3
      | none =>
        simp only [directNameClash_find_iff.1 h3, not_false_eq_true, true_and]
        cases h4 : S.places.find? (fun x => b.places.any fun h =>
            Nm.name h == Nm.name x && decide (tyOf h ≠ tyOf x)) with
        | some x =>
          simp only [reduceCtorEq, false_iff, not_and]
          intro hn; rw [directTypeClash_find_iff.2 hn] at h4; cases h4
        | none =>
          simp only [directTypeClash_find_iff.1 h4, not_false_eq_true, true_and,
            Except.ok.injEq]
          exact eq_comm
    · have : S.chans.isEmpty = false := by simpa using h2
      simp [h1, h2, this]
  · have : S.terminals.isEmpty = false := by simpa using h1
    simp [h1, this]

/-- **Acceptance** of direct composition (skeptic S2): no terminal place, no channel and no clash
give success. -/
theorem refDirect_accepts {b : Bld N A} {S : SubnetDef N A} (h1 : S.terminals = [])
    (h2 : S.chans = []) (h3 : ¬ DirectNameClash b S) (h4 : ¬ DirectTypeClash Nm tyOf b S) :
    refDirect Nm tyOf b S = .ok (directAssemble Nm b S) :=
  refDirect_ok_iff.2 ⟨h1, h2, h3, h4, rfl⟩

/-- A failing condition rejects direct composition. -/
theorem refDirect_error_of {b : Bld N A} {S : SubnetDef N A}
    (h : ¬ (S.terminals = [] ∧ S.chans = [] ∧ ¬ DirectNameClash b S ∧
      ¬ DirectTypeClash Nm tyOf b S)) :
    ∃ m, refDirect Nm tyOf b S = .error m := by
  apply except_error_of_not_ok
  intro b' hb
  obtain ⟨h1, h2, h3, h4, -⟩ := refDirect_ok_iff.1 hb
  exact h ⟨h1, h2, h3, h4⟩

omit [DecidableEq T] in
theorem directAssemble_defs (b : Bld N A) (S : SubnetDef N A) :
    (directAssemble Nm b S).defs = b.defs ++ S.defs := rfl

omit [DecidableEq T] in
theorem mem_directAssemble_places {b : Bld N A} {S : SubnetDef N A} {p : N} :
    p ∈ (directAssemble Nm b S).places ↔
      p ∈ b.places ∨ p ∈ S.places ∨ ∃ d ∈ S.defs, p ∈ d.namedPlaces := by
  simp [directAssemble, mem_appendNew, List.mem_flatMap]

end DirectLemmas

/-! ## Worked examples -/

section Examples

/-- An example definition over named places: name, input arcs and output specification;
`Immediate`, priority 0, passthrough action. -/
def bindExDef (nm : String) (ins : List (NInSpec String)) (out : Option (Out String)) :
    CDef String Unit :=
  { core := ⟨nm, ins, [], [], []⟩, out := out, timing := .immediate, priority := 0,
    action := .passthrough }

/-- A subnet whose transition `join` takes one token from port `a` and one from port `b` and puts
one into port `out`. -/
def bindExJoin : SubnetDef String Unit :=
  { name := "Join", places := ["a", "b", "out"],
    defs := [bindExDef "join" [⟨"a", .one⟩, ⟨"b", .one⟩] (some (.place "out"))],
    ports := [⟨"a", .input, "a"⟩, ⟨"b", .input, "b"⟩, ⟨"out", .output, "out"⟩], chans := [] }

/-- A subnet whose transition `split` takes one token from port `in` and writes the output
specification `o` over ports `a` and `b`. -/
def bindExSplit (o : Out String) : SubnetDef String Unit :=
  { name := "Split", places := ["in", "a", "b"],
    defs := [bindExDef "split" [⟨"in", .one⟩] (some o)],
    ports := [⟨"in", .input, "in"⟩, ⟨"a", .output, "a"⟩, ⟨"b", .output, "b"⟩], chans := [] }

/-- A subnet with two transitions, `ta` taking from port `a` and `tb` taking from port `b`: no
transition consumes from both ports. -/
def bindExTwo : SubnetDef String Unit :=
  { name := "Two", places := ["a", "b", "x", "y"],
    defs := [bindExDef "ta" [⟨"a", .one⟩] (some (.place "x")),
             bindExDef "tb" [⟨"b", .one⟩] (some (.place "y"))],
    ports := [⟨"a", .input, "a"⟩, ⟨"b", .input, "b"⟩], chans := [] }

/-- A subnet whose transition `go` (from port `a` into `x`) is exposed as channel `go`. -/
def bindExChan : SubnetDef String Unit :=
  { name := "C", places := ["a", "x"],
    defs := [bindExDef "go" [⟨"a", .one⟩] (some (.place "x"))],
    ports := [⟨"a", .input, "a"⟩], chans := [⟨"go", "go"⟩] }

/-- Instantiate `S` under prefix `s` (places by name) and compose it into an empty builder with the
port bindings `ports`, no type check, the reference transition builder and a merge that keeps the
caller side. -/
def bindExCompose (S : SubnetDef String Unit) (ports : List (String × String))
    (chans : List (String × CDef String Unit) := []) : Except String (Bld String Unit) :=
  refInst strNaming S "s" >>= fun I =>
    refCompose (fun _ => ()) refBuild (fun c _ => .ok c) Bld.empty I ports chans

/-- The message of a rejection, `none` on success. -/
def bindExErr {α : Type} : Except String α → Option String
  | .error m => some m
  | .ok _ => none

/-- **Binding rewrites the arcs** ([MOD-020] AC1, AC2): instantiating `Join` under `s` and binding
`a` to `X`, `b` to `Y` and `out` to `P` gives one transition `s/join` that takes from `X` and `Y`
and puts into `P`; the builder's places are exactly `X`, `Y` and `P`. -/
theorem bindEx_rewrite :
    (bindExCompose bindExJoin [("a", "X"), ("b", "Y"), ("out", "P")]).toOption.map
        (fun b => (b.defs.map fun d => (d.core.name, d.namedPlaces), b.places)) =
      some ([("s/join", ["X", "Y", "P"])], ["X", "Y", "P"]) := by
  decide

/-- **Bound ports are retired** ([MOD-027]): the same call records `s/a`, `s/b` and `s/out` as
retired, each with its port and caller place. -/
theorem bindEx_retired :
    (bindExCompose bindExJoin [("a", "X"), ("b", "Y"), ("out", "P")]).toOption.map
        (fun b => b.retired.map fun r => (r.place, r.port, r.caller)) =
      some [("s/a", "a", "X"), ("s/b", "b", "Y"), ("s/out", "out", "P")] := by
  decide

set_option maxRecDepth 20000 in
/-- **Input collision** ([MOD-020] AC7): binding both `a` and `b` of `Join` to `X` would give
`s/join` two input arcs on `X`, so the call fails with the collision message naming `a`, `b`, `s`,
`X` and `s/join`. -/
theorem bindEx_inCollision :
    bindExErr (bindExCompose bindExJoin [("a", "X"), ("b", "X")]) =
      some "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join' would consume from 'X' through two input arcs. Bind them to distinct places or use one port." := by
  decide

/-- **No transition consumes from both: accepted** ([MOD-020] AC7, second half): binding `a` and
`b` of `Two` to `X` is fine, since `s/ta` and `s/tb` each take from one port. -/
theorem bindEx_noCollision :
    (bindExCompose bindExTwo [("a", "X"), ("b", "X")]).toOption.map
        (fun b => b.defs.map fun d => d.namedPlaces) = some [["X", "s/x"], ["X", "s/y"]] := by
  decide

set_option maxRecDepth 20000 in
/-- **Output collision** ([MOD-020] AC8): with `split` writing `And(a, b)`, binding `a` and `b` to
`X` would name `X` twice in one AND branch, so the call fails with the output collision
message. -/
theorem bindEx_outCollision :
    bindExErr (bindExCompose (bindExSplit (.and (.place "a") (.place "b"))) [("a", "X"), ("b", "X")]) =
      some "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/split' would produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port." := by
  decide

set_option maxRecDepth 20000 in
/-- **Two XOR alternatives: the rebuild rejects** ([MOD-020] AC8, [IO-012]): with `split` writing
`Xor(a, b)`, binding `a` and `b` to `X` is no collision, but the rewritten `Xor(X, X)` is
ambiguous, and the call fails with the transition builder's message. -/
theorem bindEx_xorAmbiguous :
    bindExErr (bindExCompose (bindExSplit (.xor (.place "a") (.place "b"))) [("a", "X"), ("b", "X")]) =
      some "output spec of transition 's/split' is ambiguous: output branches 0 and 1 both claim {X}; no write can tell them apart (IO-012)" := by
  decide

/-- **A port bound twice is rejected** ([MOD-020] AC5): binding `a` to `X` and again to `Y`
fails, naming `a`. -/
theorem bindEx_dupPort :
    bindExErr (bindExCompose bindExJoin [("a", "X"), ("a", "Y")]) =
      some "Port 'a' is already bound" := by
  decide

/-- **A channel merge takes the instance transition's slot** ([MOD-021]): binding channel `go` of
`C` to the caller transition `host`, with a merge that keeps the caller side, leaves one
transition, `host`, and no `s/go`. -/
theorem bindEx_channel :
    (bindExCompose bindExChan [("a", "X")] [("go", bindExDef "host" [] none)]).toOption.map
        (fun b => b.defs.map (·.core.name)) = some ["host"] := by
  decide

/-- **Auto-composition binds every port to its own place** ([MOD-024]): auto-composing `Join`
under `s` gives `s/join` taking from `a` and `b` and putting into `out`. -/
theorem bindEx_auto :
    (refInst strNaming bindExJoin "s" >>= fun I =>
        refAuto strNaming (fun _ => ()) refBuild (fun c _ => .ok c) Bld.empty I []).toOption.map
      (fun b => b.defs.map fun d => d.namedPlaces) = some [["a", "b", "out"]] := by
  decide

/-- A subnet over places keyed by name and token type, with one input port on `("a", 1)`. -/
def bindExTyped : SubnetDef (String × Nat) Unit :=
  { name := "T", places := [("a", 1)], defs := [], ports := [⟨"a", .input, ("a", 1)⟩], chans := [] }

/-- **A caller place of another token type is rejected** ([MOD-022]): with places keyed by name
and token type, binding the type-1 port `a` to a type-2 place fails, and to a type-1 place
succeeds. -/
theorem bindEx_types :
    (bindExErr (refInst (typedNaming Nat) bindExTyped "s" >>= fun I =>
        refCompose Prod.snd refBuild (fun c _ => .ok c) Bld.empty I [("a", ("X", 2))] [])).isSome
      = true ∧
    (bindExErr (refInst (typedNaming Nat) bindExTyped "s" >>= fun I =>
        refCompose Prod.snd refBuild (fun c _ => .ok c) Bld.empty I [("a", ("X", 1))] [])).isNone
      = true := by
  decide

/-- **Direct composition appends unrenamed** ([MOD-025], [MOD-026]): composing `Two` directly into
a builder that holds place `a` adds places `b`, `x`, `y` and transitions `ta`, `tb` under their own
names, and records every body node under `Two`. -/
theorem bindEx_direct :
    (refDirect strNaming (fun _ => ()) ({ places := ["a"], defs := [] } : Bld String Unit)
        bindExTwo).toOption.map (fun b => (b.places, b.defs.map (·.core.name), b.contrib)) =
      some (["a", "b", "x", "y"], ["ta", "tb"],
        [("a", "Two"), ("b", "Two"), ("x", "Two"), ("y", "Two"), ("ta", "Two"), ("tb", "Two")]) := by
  decide

/-- **A transition name clash rejects direct composition** ([MOD-025]): a builder that already
holds a transition `ta` rejects composing `Two` directly. -/
theorem bindEx_directClash :
    (refDirect strNaming (fun _ => ())
        ({ places := ["a"], defs := [bindExDef "ta" [] none] } : Bld String Unit)
        bindExTwo).toOption.isNone = true := by
  decide

/-- The recorded name of a definition writes `/` as `_` ([MOD-026]). -/
theorem bindEx_contribName : contribName "a/b" = "a_b" := by decide

end Examples

end Libpetri.Reference
