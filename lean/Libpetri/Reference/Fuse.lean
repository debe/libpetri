import Libpetri.Spec.GlossaryCompose

set_option linter.missingDocs true

/-!
# RefCompose: place fusion

The fusion slice of the composition model ([MOD-060], [MOD-061]). Fusion is a pure function on
what a builder holds after every `compose(...)` call: its places, its transition definitions in
order and its terminal places (`FuseNet`). The reference `refFuse Build` does what Rust
(`rust/libpetri-core/src/petri_net.rs` `build_with_fusion`, `rewriter.rs` `apply_fusion`), Java
(`PetriNet.java` `buildWithFusion`, `SubnetRewriter.applyFusion`) and TypeScript
(`petri-net.ts` `buildWithFusion`, `subnet-rewriter.ts` `applyFusion`) do, in their order:

1. two sets that share a place reject the build, naming the place and both sets
   (`findOverlap`; every runtime, [MOD-061] AC7);
2. every member goes to the first declared member of its set, every other place stays
   (`refSubst`; ruling D54 (a): the first member is canonical and keeps its own name);
3. every definition is rewritten through that substitution in all five arc kinds and the output
   specification, keeping name, timing, priority and action (`CDef.map σ id`); a definition with an
   input arc on a removed member has its input arcs merged by the [MOD-021] table
   (`mergeInputsE`), an off-table pair rejecting with the shared diagnostic (`fuseMsg`); read,
   inhibitor and reset arcs brought onto one place are kept as they are (`fuseDef`);
4. every rewritten definition is rebuilt through the transition builder's check `Build`, a
   failure rejecting with `Build`'s message (`fuseStep`);
5. the places are the declared ones minus the removed members, every place a rewritten definition
   names and every terminal place; a terminal declared on a removed member names the canonical
   place (`fuseAssemble`).

The declaration check `refDeclFusion` ([MOD-060]) rejects an empty set and, where the runtime keeps
a token type (`tyOf`), members of two types; a one-member set is accepted and fuses nothing
(ruling D54 (a)).

What the blocks read: on pairwise disjoint sets the substitution is the unique `SubstSpec`
(`substSpec_unique`, `refSubst_spec`), so it does not depend on the order of the sets
(`refSubst_perm`, `refFuse_perm`); `refFuse_ok_iff` characterises success; the rejection lemmas
(`refFuse_overlap`, `refFuse_offTable`, `refFuse_buildFails`) and the acceptance lemma
(`refFuse_accepts`) give the lines of [MOD-061]; `refFuse_places_fixed` gives "no removed member
is a place of the result".
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## Disjoint fusion sets -/

/-- Two member lists share no place. -/
def MembersDisjoint (a b : List N) : Prop := ∀ p, p ∈ a → p ∉ b

/-- Two fusion sets share no member. -/
def SetsDisjoint (a b : FusionSet N) : Prop := MembersDisjoint a.members b.members

theorem SetsDisjoint.symm {a b : FusionSet N} (h : SetsDisjoint a b) : SetsDisjoint b a :=
  fun p hb ha => h p ha hb

/-- **Pairwise disjoint fusion sets** ([MOD-061]): no place is a member of two declared sets.
Declaring one non-empty set twice is not disjoint. -/
def FusionDisjoint (sets : List (FusionSet N)) : Prop := sets.Pairwise SetsDisjoint

/-- Disjointness reads the member lists only, never the sets' names. -/
theorem fusionDisjoint_iff_members (sets : List (FusionSet N)) :
    FusionDisjoint sets ↔ (sets.map (·.members)).Pairwise MembersDisjoint := by
  rw [List.pairwise_map]; rfl

/-- Reordering the declared sets keeps them disjoint. -/
theorem FusionDisjoint.perm {sets sets' : List (FusionSet N)} (hp : sets.Perm sets')
    (hd : FusionDisjoint sets) : FusionDisjoint sets' :=
  (hp.pairwise_iff (fun h => SetsDisjoint.symm h)).1 hd

/-- In disjoint sets a place is a member of at most one set. -/
theorem FusionDisjoint.unique {sets : List (FusionSet N)} (hd : FusionDisjoint sets)
    {s s' : FusionSet N} (hs : s ∈ sets) (hs' : s' ∈ sets) {p : N} (hp : p ∈ s.members)
    (hp' : p ∈ s'.members) : s = s' := by
  induction sets with
  | nil => cases hs
  | cons a rest ih =>
    rw [FusionDisjoint, List.pairwise_cons] at hd
    rcases List.mem_cons.1 hs with rfl | hsr <;> rcases List.mem_cons.1 hs' with rfl | hsr'
    · rfl
    · exact absurd hp' (hd.1 s' hsr' p hp)
    · exact absurd hp (hd.1 s hsr p hp')
    · exact ih hd.2 hsr hsr'

/-! ## The substitution a fusion asks for -/

/-- **What fusion asks of the place substitution** ([MOD-061] step 2): a member goes to its set's
canonical member (the first declared, D54 (a)), every other place stays. It reads the sets only
through membership, so it cannot depend on the order the sets are declared or applied in. -/
def SubstSpec (sets : List (FusionSet N)) (σ : N → N) : Prop :=
  (∀ s ∈ sets, ∀ p ∈ s.members, σ p = s.canonical p) ∧
  (∀ p, (∀ s ∈ sets, p ∉ s.members) → σ p = p)

/-- The substitution is unique, whatever the sets (two overlapping sets with different canonical
members have none, `substSpec_overlap`). -/
theorem substSpec_unique {sets : List (FusionSet N)} {σ τ : N → N}
    (hσ : SubstSpec sets σ) (hτ : SubstSpec sets τ) : σ = τ := by
  classical
  funext p
  by_cases h : ∃ s ∈ sets, p ∈ s.members
  · obtain ⟨s, hs, hp⟩ := h
    rw [hσ.1 s hs p hp, hτ.1 s hs p hp]
  · have h' : ∀ s ∈ sets, p ∉ s.members := fun s hs hp => h ⟨s, hs, hp⟩
    rw [hσ.2 p h', hτ.2 p h']

/-- Reordering the declared sets asks the same of the substitution. -/
theorem substSpec_perm {sets sets' : List (FusionSet N)} (hp : sets.Perm sets') (σ : N → N) :
    SubstSpec sets σ ↔ SubstSpec sets' σ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun s hs => h1 s (hp.mem_iff.2 hs), fun p h => h2 p (fun s hs => h s (hp.mem_iff.1 hs))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s hs => h1 s (hp.mem_iff.1 hs), fun p h => h2 p (fun s hs => h s (hp.mem_iff.2 hs))⟩

/-- Two sets that share place `1` and have different canonical members (`0` and `2`) have no
substitution: overlap leaves the fused structure undetermined. -/
theorem substSpec_overlap :
    ¬ ∃ σ : Nat → Nat, SubstSpec [⟨"ab", [0, 1]⟩, ⟨"cb", [2, 1]⟩] σ := by
  rintro ⟨σ, h1, _⟩
  have a := h1 ⟨"ab", [0, 1]⟩ (by simp) 1 (by simp)
  have b := h1 ⟨"cb", [2, 1]⟩ (by simp) 1 (by simp)
  simp [FusionSet.canonical] at a b
  omega

/-- The canonical member of a set whose first declared member is `a` is `a`. -/
theorem FusionSet.canonical_cons (n : String) (a : N) (l : List N) (d : N) :
    (⟨n, a :: l⟩ : FusionSet N).canonical d = a := rfl

/-- The canonical member of a non-empty set is one of its members. -/
theorem FusionSet.canonical_mem {s : FusionSet N} (h : s.members ≠ []) (d : N) :
    s.canonical d ∈ s.members := by
  obtain ⟨n, ms⟩ := s
  cases ms with
  | nil => exact absurd rfl h
  | cons a l => exact List.mem_cons_self

/-! ## The input-arc merge table over a list of arcs -/

/-- An off-table pair of input arcs on one place ([MOD-021] rule (c)): the place and the two
cardinalities, the one already merged first. -/
structure Collision (N : Type) where
  /-- The place both arcs name. -/
  place : N
  /-- The cardinality of the arc met first (after the merges before it). -/
  left  : Card
  /-- The cardinality of the arc met second. -/
  right : Card

/-- A cardinality as the [MOD-021] diagnostic renders it: `one()`, `exactly(3)`, `all()`,
`atLeast(2)`. -/
def cardStr : Card → String
  | .one => "one()"
  | .exactly n => s!"exactly({n})"
  | .all => "all()"
  | .atLeast n => s!"atLeast({n})"

/-- Put one input arc into a list holding at most one arc per place: on a place already present
the two merge by the table, at the first-seen position (Rust `merge_input_arcs`, Java
`mergeInputArcs`, TypeScript `normalizeInputArcs`); an off-table pair is a collision. -/
def insertInE [DecidableEq N] :
    List (NInSpec N) → NInSpec N → Except (Collision N) (List (NInSpec N))
  | [], s => .ok [s]
  | a :: rest, s =>
    if a.place = s.place then
      match mergeCard a.card s.card with
      | some c => .ok (⟨a.place, c⟩ :: rest)
      | none => .error ⟨s.place, a.card, s.card⟩
    else (insertInE rest s).map (a :: ·)

/-- **The merge table over a list of input arcs** ([MOD-021] rule (b), [MOD-061] step 2): one arc
per place, colliding arcs merged by `mergeCard` at the first-seen position; the first off-table
pair is the collision. -/
def mergeInputsE [DecidableEq N] (xs : List (NInSpec N)) :
    Except (Collision N) (List (NInSpec N)) :=
  xs.foldlM insertInE []

/-! ## One definition through a fusion -/

/-- A definition has an input arc on a place the substitution moves: the runtimes run the merge
on exactly these definitions (a duplicate on an untouched place stays the transition builder's
[CORE-030] rejection). -/
def fuseTouches (σ : N → N) [DecidableEq N] (d : CDef N A) : Bool :=
  d.core.inputs.any fun s => decide (σ s.place ≠ s.place)

/-- **One definition through a fusion** ([MOD-061] step 2): every place of every arc and of the
output specification through `σ`, name, timing, priority and action kept, the correspondence
chained (`CDef.map σ id`); when an input arc moved, the input arcs merged by the table
(`mergeInputsE`), an off-table pair being the collision. Read, inhibitor and reset arcs brought
onto one place are kept as they are (all three runtimes; unlike a channel merge, [MOD-021]
rule (a)). -/
def fuseDef [DecidableEq N] (σ : N → N) (d : CDef N A) : Except (Collision N) (CDef N A) :=
  if fuseTouches σ d then
    (mergeInputsE ((d.map σ id).core.inputs)).map fun ins =>
      { d.map σ id with core := { (d.map σ id).core with inputs := ins } }
  else .ok (d.map σ id)

/-! ## The fusion function -/

/-- What a builder holds when fusion runs ([MOD-061]: after every `compose(...)` call): its
places, its transition definitions in order and its declared terminal places ([EXEC-042]). -/
structure FuseNet (N A : Type) where
  /-- The places. -/
  places    : List N
  /-- The transition definitions, in order. -/
  defs      : List (CDef N A)
  /-- The declared terminal places. -/
  terminals : List N := []

/-- A fusion function ([MOD-061]): the declared fusion sets and the builder's content give the
fused content, or reject the build with a message. -/
abbrev FuseFn (N A : Type) := List (FusionSet N) → FuseNet N A → Except String (FuseNet N A)

/-- A fusion-set declaration check ([MOD-060]): a declared set is accepted (returned) or rejected
with a message. -/
abbrev DeclFn (N : Type) := FusionSet N → Except String (FusionSet N)

/-- The members of a set agree on the token type `tyOf` reads ([MOD-060] item 3, scope
"implementations that keep a run-time token type", ruling D36 (a)). -/
def TypesAgree {T : Type} (tyOf : N → T) (s : FusionSet N) : Prop :=
  ∀ m ∈ s.members, ∀ m' ∈ s.members, tyOf m = tyOf m'

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N A : Type}

/-! ## The reference substitution -/

section Subst

variable [DecidableEq N]

/-- The set that lists a place: the first declared one. -/
def fusionOwner (sets : List (FusionSet N)) (p : N) : Option (FusionSet N) :=
  sets.find? fun s => decide (p ∈ s.members)

theorem fusionOwner_eq_none_iff {sets : List (FusionSet N)} {p : N} :
    fusionOwner sets p = none ↔ ∀ s ∈ sets, p ∉ s.members := by
  simp [fusionOwner, List.find?_eq_none]

theorem fusionOwner_some {sets : List (FusionSet N)} {p : N} {s : FusionSet N}
    (h : fusionOwner sets p = some s) : s ∈ sets ∧ p ∈ s.members :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- In disjoint sets the owner of a place is the one set that lists it. -/
theorem fusionOwner_eq_some_iff {sets : List (FusionSet N)} (hd : FusionDisjoint sets)
    {p : N} {s : FusionSet N} : fusionOwner sets p = some s ↔ s ∈ sets ∧ p ∈ s.members := by
  constructor
  · exact fusionOwner_some
  · rintro ⟨hs, hp⟩
    cases h : fusionOwner sets p with
    | none => exact absurd hp ((fusionOwner_eq_none_iff.1 h) s hs)
    | some s' =>
      obtain ⟨hs', hp'⟩ := fusionOwner_some h
      rw [hd.unique hs' hs hp' hp]

/-- In disjoint sets the owner of a place does not depend on the order of the sets. -/
theorem fusionOwner_perm {sets sets' : List (FusionSet N)} (hp : sets.Perm sets')
    (hd : FusionDisjoint sets) : fusionOwner sets = fusionOwner sets' := by
  funext p
  have hd' := hd.perm hp
  cases h : fusionOwner sets p with
  | none =>
    exact (fusionOwner_eq_none_iff.2 fun s hs =>
      fusionOwner_eq_none_iff.1 h s (hp.mem_iff.2 hs)).symm
  | some s =>
    obtain ⟨hs, hm⟩ := fusionOwner_some h
    exact ((fusionOwner_eq_some_iff hd').2 ⟨hp.mem_iff.1 hs, hm⟩).symm

/-- **The reference substitution**: a place listed by a set goes to that set's first member,
every other place stays. -/
def refSubst (sets : List (FusionSet N)) (p : N) : N :=
  match fusionOwner sets p with
  | some s => s.canonical p
  | none => p

theorem refSubst_cons (a : FusionSet N) (rest : List (FusionSet N)) (p : N) :
    refSubst (a :: rest) p = if p ∈ a.members then a.canonical p else refSubst rest p := by
  by_cases h : p ∈ a.members <;> simp [refSubst, fusionOwner, h]

/-- The reference substitution reads the member lists only, never the sets' names. -/
theorem refSubst_members {sets sets' : List (FusionSet N)}
    (h : sets.map (·.members) = sets'.map (·.members)) : refSubst sets = refSubst sets' := by
  induction sets generalizing sets' with
  | nil =>
    cases sets' with
    | nil => rfl
    | cons _ _ => cases h
  | cons a rest ih =>
    cases sets' with
    | nil => cases h
    | cons b rest' =>
      simp only [List.map_cons, List.cons.injEq] at h
      funext p
      rw [refSubst_cons, refSubst_cons, ih h.2]
      simp only [FusionSet.canonical, h.1]

/-- On disjoint sets the reference substitution is what fusion asks for. -/
theorem refSubst_spec {sets : List (FusionSet N)} (hd : FusionDisjoint sets) :
    SubstSpec sets (refSubst sets) := by
  refine ⟨fun s hs p hp => ?_, fun p h => ?_⟩
  · simp only [refSubst, (fusionOwner_eq_some_iff hd).2 ⟨hs, hp⟩]
  · simp only [refSubst, fusionOwner_eq_none_iff.2 h]

/-- On disjoint sets, a substitution meets `SubstSpec` exactly when it is the reference one. -/
theorem substSpec_iff {sets : List (FusionSet N)} (hd : FusionDisjoint sets) {σ : N → N} :
    SubstSpec sets σ ↔ σ = refSubst sets :=
  ⟨fun h => substSpec_unique h (refSubst_spec hd), fun h => h ▸ refSubst_spec hd⟩

/-- **Order independence of the substitution** ([MOD-061] AC6): on disjoint sets, any two
declaration orders give the same substitution. -/
theorem refSubst_perm {sets sets' : List (FusionSet N)} (hp : sets.Perm sets')
    (hd : FusionDisjoint sets) : refSubst sets = refSubst sets' := by
  funext p
  simp only [refSubst, fusionOwner_perm hp hd]

/-- On disjoint sets the substitution is idempotent: a canonical member stays where it is. -/
theorem refSubst_idem {sets : List (FusionSet N)} (hd : FusionDisjoint sets) (p : N) :
    refSubst sets (refSubst sets p) = refSubst sets p := by
  cases h : fusionOwner sets p with
  | none => simp only [refSubst, h]
  | some s =>
    obtain ⟨hs, hp⟩ := fusionOwner_some h
    have hne : s.members ≠ [] := List.ne_nil_of_mem hp
    have hc := s.canonical_mem hne p
    have hc' : fusionOwner sets (s.canonical p) = some s :=
      (fusionOwner_eq_some_iff hd).2 ⟨hs, hc⟩
    simp only [refSubst, h, hc']
    obtain ⟨n, ms⟩ := s
    cases ms with
    | nil => exact absurd rfl hne
    | cons a l => rfl

/-- Sets of at most one member move no place (ruling D54 (a): a one-member set fuses nothing). -/
theorem refSubst_short {sets : List (FusionSet N)} (h : ∀ s ∈ sets, s.members.length ≤ 1) :
    refSubst sets = id := by
  funext p
  cases ho : fusionOwner sets p with
  | none => simp only [refSubst, ho, id]
  | some s =>
    obtain ⟨hs, hp⟩ := fusionOwner_some ho
    simp only [refSubst, ho, id]
    obtain ⟨n, ms⟩ := s
    have hl := h _ hs
    cases ms with
    | nil => cases hp
    | cons a l =>
      cases l with
      | nil =>
        show a = p
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        exact hp.symm
      | cons b l => simp at hl

/-! ## Overlap -/

/-- Overlap detection in the runtimes' order: walk the sets in declaration order and each set's
members in order; the first member an earlier set already lists is reported with that earlier set
(the first one listing it) and the current set. -/
def overlapAux : List (FusionSet N) → List (FusionSet N) → Option (N × String × String)
  | _, [] => none
  | seen, s :: rest =>
    match s.members.find? (fun p => seen.any fun r => decide (p ∈ r.members)) with
    | some p => some (p, ((fusionOwner seen p).map (·.name)).getD "", s.name)
    | none => overlapAux (seen ++ [s]) rest

/-- The first overlap of the declared sets: a shared place and the names of the two sets. -/
def findOverlap (sets : List (FusionSet N)) : Option (N × String × String) := overlapAux [] sets

theorem overlapAux_eq_none_iff :
    ∀ (seen l : List (FusionSet N)),
      overlapAux seen l = none ↔ (∀ r ∈ seen, ∀ s ∈ l, SetsDisjoint r s) ∧ FusionDisjoint l
  | seen, [] => by simp [overlapAux, FusionDisjoint]
  | seen, s :: rest => by
    unfold overlapAux
    split
    · rename_i p hf
      have hp := List.mem_of_find?_eq_some hf
      have hq := List.find?_some hf
      simp only [List.any_eq_true, decide_eq_true_eq] at hq
      obtain ⟨r, hr, hpr⟩ := hq
      simp only [reduceCtorEq, false_iff, not_and]
      intro h
      exact absurd hp (h r hr s List.mem_cons_self p hpr)
    · rename_i hf
      rw [overlapAux_eq_none_iff (seen ++ [s]) rest]
      have hn : ∀ p ∈ s.members, ∀ r ∈ seen, p ∉ r.members := by
        intro p hp r hr hpr
        have := List.find?_eq_none.1 hf p hp
        simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at this
        exact this r hr hpr
      simp only [FusionDisjoint, List.pairwise_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun r hr s' hs' => ?_, fun s' hs' => h1 s (Or.inr rfl) s' hs', h2⟩
        rcases hs' with rfl | hs'
        · exact fun p hpr hps => hn p hps r hr hpr
        · exact h1 r (Or.inl hr) s' hs'
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun r hr s' hs' => ?_, h3⟩
        rcases hr with hr | rfl
        · exact h1 r hr s' (Or.inr hs')
        · exact h2 s' hs'

/-- **Overlap detection** finds nothing exactly when the sets are pairwise disjoint. -/
theorem findOverlap_eq_none_iff (sets : List (FusionSet N)) :
    findOverlap sets = none ↔ FusionDisjoint sets := by
  rw [findOverlap, overlapAux_eq_none_iff]
  simp

end Subst

/-! ## The reference fusion -/

section Fuse

variable [DecidableEq N] [ToString N]

/-- The rejection for two sets that share a place ([MOD-061] AC7; the text of all three
runtimes). -/
def overlapMsg (p : N) (a b : String) : String :=
  s!"Fusion overlap: place '{p}' appears in two fusion sets ('{a}' and '{b}'). A place may appear in at most one fusion set (MOD-060)."

/-- The seam of a fusion diagnostic: the set that lists the place, by name (the place's own name
when no set lists it, as all three runtimes fall back). -/
def seamOf (sets : List (FusionSet N)) (p : N) : String :=
  "Fusion set '" ++ ((fusionOwner sets p).map (·.name)).getD (toString p) ++ "'"

/-- The [MOD-021] rule (c) diagnostic for an off-table collision, with the seam `seam` gives for
the place. -/
def fuseMsg (seam : N → String) (c : Collision N) : String :=
  s!"{seam c.place}: input arcs {cardStr c.left} and {cardStr c.right} collide on place '{c.place}' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)."

/-- One definition through the fusion and the transition builder's check `Build`: a collision
rejects with the [MOD-021] diagnostic, a rewritten definition `Build` rejects with `Build`'s
message. -/
def fuseStep (Build : Trans N → Option String) (σ : N → N) (seam : N → String) (d : CDef N A) :
    Except String (CDef N A) :=
  match fuseDef σ d with
  | .error c => .error (fuseMsg seam c)
  | .ok d' =>
    match Build d'.toTrans with
    | some m => .error m
    | none => .ok d'

/-- The fused content from the rewritten definitions `ds`: the declared places the substitution
keeps, the terminal places through the substitution (once each, in declaration order) and every
place a rewritten definition names; the rewritten definitions in order. -/
def fuseAssemble (σ : N → N) (X : FuseNet N A) (ds : List (CDef N A)) : FuseNet N A :=
  ⟨(X.places.filter (fun p => decide (σ p = p)) ++ (X.terminals.map σ).eraseDups ++
      ds.flatMap (·.namedPlaces)).dedup,
    ds, (X.terminals.map σ).eraseDups⟩

/-- **The reference fusion** ([MOD-061]): reject two sets that share a place; otherwise rewrite
every definition through the reference substitution, merging moved input arcs by the table and
re-running `Build`, in definition order, and assemble the fused content. -/
def refFuse (Build : Trans N → Option String) : FuseFn N A := fun sets X =>
  match findOverlap sets with
  | some (p, a, b) => .error (overlapMsg p a b)
  | none => (X.defs.mapM (fuseStep Build (refSubst sets) (seamOf sets))).map (fuseAssemble (refSubst sets) X)

/- The reference fusion is the witness model of the fusion blocks. -/
#spec_witness refFuse

end Fuse

/-! ## The reference declaration check -/

/-- **The reference fusion-set declaration** ([MOD-060]): an empty set is rejected; a member whose
token type (`tyOf`) differs from the first member's is rejected; otherwise the set is accepted as
declared, one member included (ruling D54 (a)). `tyOf` is a model parameter: Java reads the token
type (`FusionSet.java` `build`), Rust the run-time `TypeId` (`fusion.rs` `member`); TypeScript's
builder path and Python check nothing, `tyOf := fun _ => ()`. -/
def refDeclFusion [ToString N] {T : Type} [DecidableEq T] (tyOf : N → T) : DeclFn N := fun s =>
  match s.members with
  | [] => .error s!"FusionSet '{s.name}': must have at least one member (MOD-060)"
  | c :: rest =>
    match rest.find? (fun m => decide (tyOf m ≠ tyOf c)) with
    | some m => .error s!"FusionSet '{s.name}': member '{m}' has a different token type than the first member '{c}' (MOD-060)"
    | none => .ok s

/- The reference declaration check is the witness model of the declaration block. -/
#spec_witness refDeclFusion

/-! ## Lemmas: `Except` and `mapM` -/

section ExceptLemmas

variable {ε α β : Type}

theorem except_map_ok_iff {f : α → β} {e : Except ε α} {y : β} :
    e.map f = .ok y ↔ ∃ x, e = .ok x ∧ f x = y := by
  cases e <;> simp [Except.map]

theorem except_error_of_not_ok {e : Except ε α} (h : ∀ x, e ≠ .ok x) : ∃ m, e = .error m := by
  cases e with
  | error m => exact ⟨m, rfl⟩
  | ok x => exact absurd rfl (h x)

/-- `mapM` in `Except` succeeds with `ys` exactly when every element succeeds with the element of
`ys` at its position. -/
theorem mapM_except_ok_iff (f : α → Except ε β) :
    ∀ (l : List α) (ys : List β), l.mapM f = .ok ys ↔ List.Forall₂ (fun x y => f x = .ok y) l ys
  | [], ys => by
    cases ys <;> simp [List.mapM_nil, pure, Except.pure]
  | x :: l, ys => by
    rw [List.mapM_cons]
    cases hx : f x with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, false_iff]
      intro h
      cases h with
      | cons hr _ => rw [hx] at hr; cases hr
    | ok y =>
      have ih := mapM_except_ok_iff f l
      simp only [bind, Except.bind]
      cases hl : l.mapM f with
      | error e =>
        simp only [reduceCtorEq, false_iff]
        intro h
        cases h with
        | cons _ hr => exact absurd ((ih _).2 hr) (by rw [hl]; simp)
      | ok ys' =>
        simp only [pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          exact List.Forall₂.cons hx ((ih ys').1 hl)
        · intro h
          cases h with
          | cons hr hrest =>
            rw [hx] at hr
            cases hr
            have := (ih _).2 hrest
            rw [hl] at this
            cases this
            rfl

/-- An element of a `Forall₂`-related left list has a related partner. -/
theorem forall₂_mem_left {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, List.Forall₂ R l ys → ∀ x ∈ l, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (a := a) (b := b) hab hrest, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, hr⟩ := forall₂_mem_left hrest x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

/-- An element of a `Forall₂`-related right list has a related partner. -/
theorem forall₂_mem_right {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, List.Forall₂ R l ys → ∀ y ∈ ys, ∃ x ∈ l, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons (a := a) (b := b) hab hrest, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_mem_right hrest y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- Splitting a conjunction that reads only the right element. -/
theorem forall₂_and_right {R : α → β → Prop} {Q : β → Prop} :
    ∀ {l : List α} {ys : List β},
      List.Forall₂ (fun x y => R x y ∧ Q y) l ys ↔ List.Forall₂ R l ys ∧ ∀ y ∈ ys, Q y
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: l, y :: ys => by
    rw [List.forall₂_cons, List.forall₂_cons, forall₂_and_right]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- `mapM` in `Except` succeeds when every element does. -/
theorem mapM_except_ok_of_forall (f : α → Except ε β) (Q : β → Prop) :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = .ok y ∧ Q y) →
      ∃ ys, l.mapM f = .ok ys ∧ ∀ y ∈ ys, Q y
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: l, h => by
    obtain ⟨y, hy, hq⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hqs⟩ :=
      mapM_except_ok_of_forall f Q l (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    refine ⟨y :: ys, ?_, ?_⟩
    · rw [mapM_except_ok_iff] at hys ⊢
      exact List.Forall₂.cons hy hys
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hq, hqs⟩

/-- `mapM` in `Except` of a function that always succeeds is the mapped list. -/
theorem mapM_except_pure (f : α → Except ε β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    have hl := mapM_except_pure f g l (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    rw [mapM_except_ok_iff] at hl ⊢
    exact List.Forall₂.cons (h x List.mem_cons_self) hl

/-- `mapM` in `Except` reports the first failing element: when every element before `x`
succeeds and `x` fails with `e`, the whole call fails with `e`. -/
theorem mapM_except_error_first (f : α → Except ε β) (x : α) (e : ε) (post : List α)
    (hx : f x = .error e) :
    ∀ (pre : List α), (∀ y ∈ pre, ∃ z, f y = .ok z) → (pre ++ x :: post).mapM f = .error e
  | [], _ => by
    simp only [List.nil_append, List.mapM_cons, hx, bind, Except.bind]
  | y :: pre, h => by
    obtain ⟨z, hz⟩ := h y List.mem_cons_self
    have ih := mapM_except_error_first f x e post hx pre
      (fun y' hy' => h y' (List.mem_cons_of_mem _ hy'))
    simp only [List.cons_append, List.mapM_cons, hz, ih, bind, Except.bind]

end ExceptLemmas

/-! ## Lemmas: the merge table over a list, and one definition through a fusion -/

section DefLemmas

variable [DecidableEq N]

/-- Inserting an arc keeps every place among the inserted arc's and the list's. -/
theorem insertInE_places :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N) (acc' : List (NInSpec N)),
      insertInE acc s = .ok acc' → ∀ y ∈ acc', y.place = s.place ∨ y.place ∈ acc.map (·.place)
  | [], s, acc', h => by
    simp only [insertInE, Except.ok.injEq] at h
    subst h
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact Or.inl rfl
  | a :: rest, s, acc', h => by
    unfold insertInE at h
    split at h
    · rename_i he
      split at h
      · rename_i c _
        cases h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl he
        · exact Or.inr (List.mem_map_of_mem (List.mem_cons_of_mem _ hy))
      · cases h
    · obtain ⟨r, hr, rfl⟩ := except_map_ok_iff.1 h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inr (List.mem_map_of_mem List.mem_cons_self)
      · rcases insertInE_places rest s r hr y hy with h1 | h1
        · exact Or.inl h1
        · right
          obtain ⟨b, hb, e⟩ := List.mem_map.1 h1
          exact List.mem_map.2 ⟨b, List.mem_cons_of_mem _ hb, e⟩

theorem foldlM_insertInE_places :
    ∀ (xs acc ys : List (NInSpec N)), xs.foldlM insertInE acc = .ok ys →
      ∀ y ∈ ys, y.place ∈ acc.map (·.place) ++ xs.map (·.place)
  | [], acc, ys, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro y hy
    exact List.mem_append_left _ (List.mem_map_of_mem hy)
  | x :: xs, acc, ys, h => by
    rw [List.foldlM_cons] at h
    cases hx : insertInE acc x with
    | error e => rw [hx] at h; cases h
    | ok acc' =>
      rw [hx] at h
      simp only [bind, Except.bind] at h
      intro y hy
      have h1 := foldlM_insertInE_places xs acc' ys h y hy
      rcases List.mem_append.1 h1 with h1 | h1
      · obtain ⟨b, hb, e⟩ := List.mem_map.1 h1
        rcases insertInE_places acc x acc' hx b hb with h2 | h2
        · rw [← e, h2]; simp
        · rw [← e]; exact List.mem_append_left _ h2
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h1)

/-- **Merging names no new place**: every place of the merged arcs is the place of an input
arc. -/
theorem mergeInputsE_places {xs ys : List (NInSpec N)} (h : mergeInputsE xs = .ok ys) :
    ∀ y ∈ ys, y.place ∈ xs.map (·.place) := by
  intro y hy
  simpa using foldlM_insertInE_places xs [] ys h y hy

omit [DecidableEq N] in
/-- The places of a mapped output specification are the mapped places. -/
theorem outPlaces_mapOut {M : Type} (f : N → M) :
    ∀ o : Out N, outPlaces (mapOut f o) = (outPlaces o).map f
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by simp [mapOut, outPlaces, outPlaces_mapOut f l, outPlaces_mapOut f r]
  | .xor l r => by simp [mapOut, outPlaces, outPlaces_mapOut f l, outPlaces_mapOut f r]
  | .timeout c => by simp [mapOut, outPlaces, outPlaces_mapOut f c]

omit [DecidableEq N] in
/-- The identity map leaves an output specification as it is. -/
theorem mapOut_id : ∀ o : Out N, mapOut id o = o
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by simp [mapOut, mapOut_id l, mapOut_id r]
  | .xor l r => by simp [mapOut, mapOut_id l, mapOut_id r]
  | .timeout c => by simp [mapOut, mapOut_id c]

omit [DecidableEq N] in
/-- The identity rewrite leaves a definition's arcs, output specification, timing, priority and
action as they are (only the correspondence is recorded). -/
theorem CDef.map_id_toTransDef (d : CDef N A) : (d.map id id).toTransDef = d.toTransDef := by
  obtain ⟨⟨⟨nm, ins, inh, rd, rs⟩, out, tm, pr, act⟩, corr⟩ := d
  have hi : ins.map (mapIn id) = ins := by
    conv => rhs; rw [← List.map_id ins]
    rfl
  cases out with
  | none => simp [CDef.map, TransDef.map, mapCore, hi]
  | some o => simp [CDef.map, TransDef.map, mapCore, hi, mapOut_id]

/-- A definition with no moved input arc is rewritten without a merge. -/
theorem fuseDef_untouched (σ : N → N) (d : CDef N A) (h : fuseTouches σ d = false) :
    fuseDef σ d = .ok (d.map σ id) := by
  simp [fuseDef, h]

/-- A definition with a moved input arc has its mapped input arcs merged by the table. -/
theorem fuseDef_touched (σ : N → N) (d : CDef N A) (h : fuseTouches σ d = true) :
    fuseDef σ d = (mergeInputsE (d.core.inputs.map (mapIn σ))).map fun ins =>
      { d.map σ id with core := { (d.map σ id).core with inputs := ins } } := by
  simp only [fuseDef, h, if_true]
  rfl

/-- **What a fusion keeps** of a definition: name, timing, priority and action; the inhibitor,
read and reset arcs and the output specification are mapped through `σ` as they are; the
correspondence is chained. -/
theorem fuseDef_kept {σ : N → N} {d d' : CDef N A} (h : fuseDef σ d = .ok d') :
    d'.core.name = d.core.name ∧ d'.core.inhibitors = d.core.inhibitors.map σ ∧
      d'.core.reads = d.core.reads.map σ ∧ d'.core.resets = d.core.resets.map σ ∧
      d'.out = d.out.map (mapOut σ) ∧ d'.timing = d.timing ∧ d'.priority = d.priority ∧
      d'.action = d.action ∧ d'.corr = some (corrPass σ d) := by
  unfold fuseDef at h
  split at h
  · obtain ⟨ins, -, rfl⟩ := except_map_ok_iff.1 h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The input arcs of a rewritten definition: the mapped arcs when no input arc moved, else the
table's merge of the mapped arcs. -/
theorem fuseDef_inputs {σ : N → N} {d d' : CDef N A} (h : fuseDef σ d = .ok d') :
    (fuseTouches σ d = false ∧ d'.core.inputs = d.core.inputs.map (mapIn σ)) ∨
      (fuseTouches σ d = true ∧ mergeInputsE (d.core.inputs.map (mapIn σ)) = .ok d'.core.inputs) := by
  unfold fuseDef at h
  split at h
  · rename_i ht
    obtain ⟨ins, hins, rfl⟩ := except_map_ok_iff.1 h
    exact Or.inr ⟨ht, hins⟩
  · rename_i ht
    cases h
    exact Or.inl ⟨by simpa using ht, rfl⟩

/-- **A fusion names no new place**: every place a rewritten definition names is the image under
`σ` of a place the original names. -/
theorem fuseDef_namedPlaces {σ : N → N} {d d' : CDef N A} (h : fuseDef σ d = .ok d') :
    ∀ q ∈ d'.namedPlaces, ∃ p ∈ d.namedPlaces, q = σ p := by
  obtain ⟨-, hinh, hrd, hrs, hout, -⟩ := fuseDef_kept h
  have hin : ∀ s ∈ d'.core.inputs, ∃ p ∈ d.core.inputs.map (·.place), s.place = σ p := by
    intro s hs
    rcases fuseDef_inputs h with ⟨-, he⟩ | ⟨-, he⟩
    · rw [he] at hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact ⟨a.place, List.mem_map_of_mem ha, rfl⟩
    · have := mergeInputsE_places he s hs
      simp only [List.map_map, Function.comp_def, mapIn] at this
      obtain ⟨a, ha, e⟩ := List.mem_map.1 this
      exact ⟨a.place, List.mem_map_of_mem ha, e.symm⟩
  intro q hq
  simp only [TransDef.namedPlaces, List.mem_append] at hq ⊢
  rcases hq with (((hq | hq) | hq) | hq) | hq
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hq
    obtain ⟨p, hp, e⟩ := hin s hs
    exact ⟨p, Or.inl (Or.inl (Or.inl (Or.inl hp))), e⟩
  · rw [hinh] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, Or.inl (Or.inl (Or.inl (Or.inr hp))), rfl⟩
  · rw [hrd] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, Or.inl (Or.inl (Or.inr hp)), rfl⟩
  · rw [hrs] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, Or.inl (Or.inr hp), rfl⟩
  · rw [hout] at hq
    cases ho : d.out with
    | none => rw [ho] at hq; simp at hq
    | some o =>
      rw [ho] at hq
      simp only [Option.map_some, Option.getD_some, outPlaces_mapOut] at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact ⟨p, Or.inr (by simp [hp]), rfl⟩

/-- The identity substitution rewrites a definition without a merge. -/
theorem fuseDef_id (d : CDef N A) : fuseDef id d = .ok (d.map id id) :=
  fuseDef_untouched id d (by simp [fuseTouches])

end DefLemmas

/-! ## Lemmas: the reference fusion -/

section FuseLemmas

variable [DecidableEq N] [ToString N] {Build : Trans N → Option String}

theorem fuseStep_ok_iff {σ : N → N} {seam : N → String} {d d' : CDef N A} :
    fuseStep Build σ seam d = .ok d' ↔ fuseDef σ d = .ok d' ∧ Build d'.toTrans = none := by
  unfold fuseStep
  cases h : fuseDef σ d with
  | error c => simp
  | ok e =>
    cases hb : Build e.toTrans with
    | some m =>
      simp only [hb, reduceCtorEq, Except.ok.injEq, false_iff, not_and]
      rintro rfl; rw [hb]; simp
    | none =>
      simp only [hb, Except.ok.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hb⟩
      · rintro ⟨rfl, -⟩; rfl

theorem mapM_fuseStep_ok_iff {σ : N → N} {seam : N → String} {l ds : List (CDef N A)} :
    l.mapM (fuseStep Build σ seam) = .ok ds ↔
      l.mapM (fuseDef σ) = .ok ds ∧ ∀ d ∈ ds, Build d.toTrans = none := by
  rw [mapM_except_ok_iff, mapM_except_ok_iff]
  have : (fun (x y : CDef N A) => fuseStep Build σ seam x = .ok y) =
      (fun (x y : CDef N A) => fuseDef σ x = .ok y ∧ Build y.toTrans = none) := by
    funext x y; exact propext fuseStep_ok_iff
  rw [this, forall₂_and_right]

/-- **When the reference fusion succeeds**: the sets are pairwise disjoint, every definition
rewrites through the reference substitution in order, every rewritten definition passes `Build`,
and the result is the assembled content. -/
theorem refFuse_ok_iff {sets : List (FusionSet N)} {X Y : FuseNet N A} :
    refFuse Build sets X = .ok Y ↔
      FusionDisjoint sets ∧ X.defs.mapM (fuseDef (refSubst sets)) = .ok Y.defs ∧
        (∀ d ∈ Y.defs, Build d.toTrans = none) ∧ Y = fuseAssemble (refSubst sets) X Y.defs := by
  unfold refFuse
  cases ho : findOverlap sets with
  | some t =>
    obtain ⟨p, a, b⟩ := t
    simp only [reduceCtorEq, false_iff, not_and]
    intro hd
    rw [(findOverlap_eq_none_iff sets).2 hd] at ho
    cases ho
  | none =>
    have hd := (findOverlap_eq_none_iff sets).1 ho
    simp only
    rw [except_map_ok_iff]
    constructor
    · rintro ⟨ds, hds, rfl⟩
      obtain ⟨h1, h2⟩ := mapM_fuseStep_ok_iff.1 hds
      exact ⟨hd, h1, h2, rfl⟩
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨Y.defs, mapM_fuseStep_ok_iff.2 ⟨h1, h2⟩, h3.symm⟩

/-- **Acceptance**: on disjoint sets, when every definition rewrites on the table and every
rewritten definition passes `Build`, the reference fusion succeeds. -/
theorem refFuse_accepts {sets : List (FusionSet N)} {X : FuseNet N A} {ds : List (CDef N A)}
    (hd : FusionDisjoint sets) (hm : X.defs.mapM (fuseDef (refSubst sets)) = .ok ds)
    (hb : ∀ d ∈ ds, Build d.toTrans = none) :
    refFuse Build sets X = .ok (fuseAssemble (refSubst sets) X ds) :=
  refFuse_ok_iff.2 ⟨hd, hm, hb, rfl⟩

/-- **Acceptance**, pointwise: on disjoint sets, when every definition rewrites on the table to a
definition `Build` accepts, the reference fusion succeeds. -/
theorem refFuse_accepts' {sets : List (FusionSet N)} {X : FuseNet N A} (hd : FusionDisjoint sets)
    (h : ∀ d ∈ X.defs, ∃ d', fuseDef (refSubst sets) d = .ok d' ∧ Build d'.toTrans = none) :
    ∃ Y, refFuse Build sets X = .ok Y := by
  obtain ⟨ds, hm, hb⟩ := mapM_except_ok_of_forall _ _ X.defs h
  exact ⟨_, refFuse_accepts hd hm hb⟩

/-- **Overlap rejects**: two sets that share a place reject the build. -/
theorem refFuse_overlap {sets : List (FusionSet N)} (X : FuseNet N A)
    (h : ¬ FusionDisjoint sets) : ∃ m, refFuse Build sets X = .error m :=
  except_error_of_not_ok fun _ hY => h (refFuse_ok_iff.1 hY).1

/-- The overlap message names the shared place and both sets. -/
theorem refFuse_overlap_msg {sets : List (FusionSet N)} (X : FuseNet N A) {p : N} {a b : String}
    (h : findOverlap sets = some (p, a, b)) :
    refFuse Build sets X = .error (overlapMsg p a b) := by
  simp only [refFuse, h]

/-- **An off-table collision rejects**: a definition whose moved input arcs do not merge by the
table rejects the build. -/
theorem refFuse_offTable {sets : List (FusionSet N)} {X : FuseNet N A} {d : CDef N A}
    {c : Collision N} (hd : d ∈ X.defs) (hc : fuseDef (refSubst sets) d = .error c) :
    ∃ m, refFuse Build sets X = .error m := by
  refine except_error_of_not_ok fun Y hY => ?_
  obtain ⟨-, hm, -⟩ := refFuse_ok_iff.1 hY
  obtain ⟨y, -, hy⟩ := forall₂_mem_left ((mapM_except_ok_iff _ _ _).1 hm) d hd
  rw [hc] at hy; cases hy

/-- **A rewritten definition `Build` rejects rejects the build** (IO-011, IO-012, EXEC-012 and
CORE-030 name fusion as a construction path). -/
theorem refFuse_buildFails {sets : List (FusionSet N)} {X : FuseNet N A} {d d' : CDef N A}
    {m : String} (hd : d ∈ X.defs) (hf : fuseDef (refSubst sets) d = .ok d')
    (hb : Build d'.toTrans = some m) : ∃ m', refFuse Build sets X = .error m' := by
  refine except_error_of_not_ok fun Y hY => ?_
  obtain ⟨-, hm, hB, -⟩ := refFuse_ok_iff.1 hY
  obtain ⟨y, hy, hfy⟩ := forall₂_mem_left ((mapM_except_ok_iff _ _ _).1 hm) d hd
  rw [hf] at hfy; cases hfy
  rw [hB _ hy] at hb; cases hb

/-- In disjoint sets the seam of a member is its set's name. -/
theorem seamOf_member {sets : List (FusionSet N)} (hd : FusionDisjoint sets) {s : FusionSet N}
    (hs : s ∈ sets) {p : N} (hp : p ∈ s.members) : seamOf sets p = "Fusion set '" ++ s.name ++ "'" := by
  simp only [seamOf, (fusionOwner_eq_some_iff hd).2 ⟨hs, hp⟩, Option.map_some, Option.getD_some]

/-- **The first offender's message**: when every definition before `d` passes, a collision at `d`
rejects the build with the [MOD-021] diagnostic for that collision. -/
theorem refFuse_offTable_msg {sets : List (FusionSet N)} {X : FuseNet N A}
    (hd : FusionDisjoint sets) {pre post : List (CDef N A)} {d : CDef N A} {c : Collision N}
    (hX : X.defs = pre ++ d :: post)
    (hpre : ∀ e ∈ pre, ∃ e', fuseDef (refSubst sets) e = .ok e' ∧ Build e'.toTrans = none)
    (hc : fuseDef (refSubst sets) d = .error c) :
    refFuse Build sets X = .error (fuseMsg (seamOf sets) c) := by
  simp only [refFuse, (findOverlap_eq_none_iff sets).2 hd, hX]
  rw [mapM_except_error_first _ d (fuseMsg (seamOf sets) c) post (by simp [fuseStep, hc]) pre
    (fun e he => by obtain ⟨e', h⟩ := hpre e he; exact ⟨e', fuseStep_ok_iff.2 h⟩)]
  rfl

/-- **The first offender's message**: when every definition before `d` passes, a rewritten `d`
that `Build` rejects with `m` rejects the build with `m`. -/
theorem refFuse_buildFails_msg {sets : List (FusionSet N)} {X : FuseNet N A}
    (hd : FusionDisjoint sets) {pre post : List (CDef N A)} {d d' : CDef N A} {m : String}
    (hX : X.defs = pre ++ d :: post)
    (hpre : ∀ e ∈ pre, ∃ e', fuseDef (refSubst sets) e = .ok e' ∧ Build e'.toTrans = none)
    (hf : fuseDef (refSubst sets) d = .ok d') (hb : Build d'.toTrans = some m) :
    refFuse Build sets X = .error m := by
  simp only [refFuse, (findOverlap_eq_none_iff sets).2 hd, hX]
  rw [mapM_except_error_first _ d m post (by simp [fuseStep, hf, hb]) pre
    (fun e he => by obtain ⟨e', h⟩ := hpre e he; exact ⟨e', fuseStep_ok_iff.2 h⟩)]
  rfl

/-- **Order independence** ([MOD-061] AC6): on disjoint sets, any reordering of the sets gives
the same result, the same net or the same rejection. -/
theorem refFuse_perm {sets sets' : List (FusionSet N)} (hp : sets.Perm sets')
    (hd : FusionDisjoint sets) (X : FuseNet N A) :
    refFuse Build sets X = refFuse Build sets' X := by
  have h1 := refSubst_perm hp hd
  have h2 : seamOf sets = seamOf sets' := by
    funext p; simp only [seamOf, fusionOwner_perm hp hd]
  simp only [refFuse, (findOverlap_eq_none_iff sets).2 hd,
    (findOverlap_eq_none_iff sets').2 (hd.perm hp), h1, h2]

/-- **The set's name is for diagnostics only**: two declarations with the same member lists
succeed alike, with the same result. -/
theorem refFuse_ok_members {sets sets' : List (FusionSet N)}
    (h : sets.map (·.members) = sets'.map (·.members)) (X Y : FuseNet N A) :
    refFuse Build sets X = .ok Y ↔ refFuse Build sets' X = .ok Y := by
  have hd : FusionDisjoint sets ↔ FusionDisjoint sets' := by
    rw [fusionDisjoint_iff_members, fusionDisjoint_iff_members, h]
  rw [refFuse_ok_iff, refFuse_ok_iff, refSubst_members h, hd]

/-- The places of a fused result: a declared place the substitution keeps, a terminal place
through the substitution, or a place a rewritten definition names. -/
theorem refFuse_mem_places {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (h : refFuse Build sets X = .ok Y) (p : N) :
    p ∈ Y.places ↔ (p ∈ X.places ∧ refSubst sets p = p) ∨ p ∈ X.terminals.map (refSubst sets) ∨
      ∃ d ∈ Y.defs, p ∈ d.namedPlaces := by
  obtain ⟨-, -, -, hY⟩ := refFuse_ok_iff.1 h
  rw [hY]
  simp only [fuseAssemble, List.mem_dedup, List.mem_append, List.mem_filter, decide_eq_true_eq,
    List.mem_eraseDups, List.mem_flatMap]
  tauto

/-- The terminal places of a fused result are the declared ones through the substitution, once
each, in declaration order (a terminal on a removed member names the canonical place). -/
theorem refFuse_terminals {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (h : refFuse Build sets X = .ok Y) :
    Y.terminals = (X.terminals.map (refSubst sets)).eraseDups := by
  obtain ⟨-, -, -, hY⟩ := refFuse_ok_iff.1 h
  rw [hY]; rfl

/-- **No removed member is a place of the result**: every place of a fused result is fixed by the
substitution. -/
theorem refFuse_places_fixed {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (h : refFuse Build sets X = .ok Y) : ∀ p ∈ Y.places, refSubst sets p = p := by
  obtain ⟨hd, hm, -, -⟩ := refFuse_ok_iff.1 h
  intro p hp
  rcases (refFuse_mem_places h p).1 hp with ⟨-, hp⟩ | hp | ⟨d', hd', hp⟩
  · exact hp
  · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
    exact refSubst_idem hd q
  · obtain ⟨d, -, hf⟩ := forall₂_mem_right ((mapM_except_ok_iff _ _ _).1 hm) d' hd'
    obtain ⟨q, -, rfl⟩ := fuseDef_namedPlaces hf p hp
    exact refSubst_idem hd q

/-- A member other than its set's canonical member is not a place of the result. -/
theorem refFuse_removed_absent {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (h : refFuse Build sets X = .ok Y) {s : FusionSet N} (hs : s ∈ sets) {p : N}
    (hp : p ∈ s.members) (hne : p ≠ s.canonical p) : p ∉ Y.places := by
  intro hY
  have hd := (refFuse_ok_iff.1 h).1
  have := refFuse_places_fixed h p hY
  rw [(refSubst_spec hd).1 s hs p hp] at this
  exact hne this.symm

/-- A declared place no set moves stays a place of the result. -/
theorem refFuse_keeps {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (h : refFuse Build sets X = .ok Y) {p : N} (hp : p ∈ X.places) (hf : refSubst sets p = p) :
    p ∈ Y.places :=
  (refFuse_mem_places h p).2 (Or.inl ⟨hp, hf⟩)

/-- **Sets of at most one member fuse nothing**: on disjoint sets of at most one member each, a
successful fusion keeps every definition's arcs, output specification, timing, priority and
action. -/
theorem refFuse_short {sets : List (FusionSet N)} {X Y : FuseNet N A}
    (hs : ∀ s ∈ sets, s.members.length ≤ 1) (h : refFuse Build sets X = .ok Y) :
    Y.defs.map (·.toTransDef) = X.defs.map (·.toTransDef) := by
  obtain ⟨-, hm, -, -⟩ := refFuse_ok_iff.1 h
  rw [refSubst_short hs] at hm
  rw [mapM_except_pure _ (CDef.map id id) X.defs (fun d _ => fuseDef_id d)] at hm
  rw [← Except.ok.inj hm]
  simp [List.map_map, Function.comp_def, CDef.map_id_toTransDef]

/-- On disjoint sets of at most one member each, a builder whose definitions all pass `Build`
fuses successfully. -/
theorem refFuse_short_ok {sets : List (FusionSet N)} {X : FuseNet N A} (hd : FusionDisjoint sets)
    (hs : ∀ s ∈ sets, s.members.length ≤ 1) (hb : ∀ d ∈ X.defs, Build d.toTrans = none) :
    ∃ Y, refFuse Build sets X = .ok Y := by
  refine refFuse_accepts' hd fun d hd' => ⟨d.map id id, ?_, ?_⟩
  · rw [refSubst_short hs]; exact fuseDef_id d
  · have : (d.map id id).toTrans = d.toTrans := by
      simp only [TransDef.toTrans, CDef.map_id_toTransDef]
    rw [this]; exact hb d hd'

end FuseLemmas

/-! ## Lemmas: the reference declaration check -/

section DeclLemmas

variable [ToString N] {T : Type} [DecidableEq T]

/-- **When a declaration is accepted**: the set has a member and its members agree on the token
type; the accepted set is the declared one. -/
theorem refDeclFusion_ok_iff (tyOf : N → T) (s s' : FusionSet N) :
    refDeclFusion tyOf s = .ok s' ↔ s.members ≠ [] ∧ TypesAgree tyOf s ∧ s' = s := by
  obtain ⟨n, ms⟩ := s
  cases ms with
  | nil => simp [refDeclFusion]
  | cons c rest =>
    simp only [refDeclFusion]
    cases hf : rest.find? (fun m => decide (tyOf m ≠ tyOf c)) with
    | some m =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ ht
      have hm := List.mem_of_find?_eq_some hf
      have hne := List.find?_some hf
      simp only [decide_eq_true_eq] at hne
      exact absurd (ht m (List.mem_cons_of_mem _ hm) c List.mem_cons_self) hne
    | none =>
      have hall : ∀ m ∈ c :: rest, tyOf m = tyOf c := by
        intro m hm
        rcases List.mem_cons.1 hm with rfl | hm
        · rfl
        · have := List.find?_eq_none.1 hf m hm
          simpa using this
      simp only [Except.ok.injEq, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      constructor
      · rintro rfl
        exact ⟨fun m hm m' hm' => (hall m hm).trans (hall m' hm').symm, rfl⟩
      · rintro ⟨-, rfl⟩; rfl

/-- An empty declaration is rejected. -/
theorem refDeclFusion_empty (tyOf : N → T) (n : String) :
    ∃ m, refDeclFusion tyOf (⟨n, []⟩ : FusionSet N) = .error m := ⟨_, rfl⟩

/-- A one-member declaration is accepted as declared. -/
theorem refDeclFusion_single (tyOf : N → T) (n : String) (a : N) :
    refDeclFusion tyOf (⟨n, [a]⟩ : FusionSet N) = .ok ⟨n, [a]⟩ := rfl

end DeclLemmas

/-! ## Worked examples -/

section Examples

/-- An example definition over named places: name, input arcs, output specification and read
arcs; `Immediate`, priority 0, passthrough action. -/
def fuseExDef (nm : String) (ins : List (NInSpec String)) (out : Option (Out String))
    (reads : List String := []) : CDef String Unit :=
  { core := ⟨nm, ins, [], reads, []⟩, out := out, timing := .immediate, priority := 0,
    action := .passthrough }

/-- The take transition of leaky-bucket instance `b`: one request and one permit from its own
limiter. -/
def fuseExTake (b : String) : CDef String Unit :=
  fuseExDef (b ++ "/take") [⟨b ++ "/req", .one⟩, ⟨b ++ "/limit", .one⟩] (some (.place (b ++ "/out")))

/-- Three leaky-bucket instances, each with its own limiter place ([MOD-061] AC1). -/
def fuseExBuckets : FuseNet String Unit :=
  { places := ["b1/limit", "b2/limit", "b3/limit"],
    defs := [fuseExTake "b1", fuseExTake "b2", fuseExTake "b3"] }

/-- The fusion set over the three limiter places. -/
def fuseExLimiter : FusionSet String := ⟨"limiter", ["b1/limit", "b2/limit", "b3/limit"]⟩

/-- One transition that takes one token from `a` and one from `b`, depositing into `c`. -/
def fuseExBoth : FuseNet String Unit :=
  { places := ["a", "b", "c"], defs := [fuseExDef "t" [⟨"a", .one⟩, ⟨"b", .one⟩] (some (.place "c"))] }

/-- One transition that takes one token from `a` and every token from `b`. -/
def fuseExMix : FuseNet String Unit :=
  { places := ["a", "b"], defs := [fuseExDef "t" [⟨"a", .one⟩, ⟨"b", .all⟩] none] }

/-- One transition whose output specification puts a token into both `a` and `b`. -/
def fuseExAndBoth : FuseNet String Unit :=
  { places := ["a", "b", "c"],
    defs := [fuseExDef "t" [⟨"c", .one⟩] (some (.and (.place "a") (.place "b")))] }

/-- One transition that consumes from `a` and reads `b`. -/
def fuseExInRead : FuseNet String Unit :=
  { places := ["a", "b"], defs := [fuseExDef "t" [⟨"a", .one⟩] none ["b"]] }

/-- No transition; place `b` is declared terminal. -/
def fuseExTerm : FuseNet String Unit := { places := ["a", "b"], defs := [], terminals := ["b"] }

/-- **Three buckets share one limiter** ([MOD-061] AC1): after fusing the three limiter places,
every take transition draws its permit from `b1/limit`, the first declared member. -/
theorem fuseEx_buckets_inputs :
    (refFuse refBuild [fuseExLimiter] fuseExBuckets).toOption.map
        (fun Y => Y.defs.map fun d => d.core.inputs.map (·.place)) =
      some [["b1/req", "b1/limit"], ["b2/req", "b1/limit"], ["b3/req", "b1/limit"]] := by
  decide

/-- **The other limiters are gone** ([MOD-061] AC3): `b1/limit` is a place of the fused net,
`b2/limit` and `b3/limit` are not. -/
theorem fuseEx_buckets_places :
    (refFuse refBuild [fuseExLimiter] fuseExBuckets).toOption.map
        (fun Y => ["b1/limit", "b2/limit", "b3/limit"].map Y.places.contains) =
      some [true, false, false] := by
  decide

/-- **Two `one()` arcs merge to `exactly(2)`** ([MOD-061] test derivation): a transition taking one
token from `a` and one from `b`, with `a` and `b` fused, takes two tokens from `a`. -/
theorem fuseEx_both_merged :
    (refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExBoth).toOption.map
        (fun Y => Y.defs.map fun d => d.core.inputs.map fun s => (s.place, s.card)) =
      some [[("a", Card.exactly 2)]] := by
  decide

set_option maxRecDepth 20000 in
/-- **An off-table pair rejects, naming the fusion set** ([MOD-061] AC4): `one()` on `a` and
`all()` on `b` have no merge, so fusing `a` and `b` fails with the [MOD-021] diagnostic. -/
theorem fuseEx_mix_rejected :
    (match refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExMix with
      | .error m => some m | .ok _ => none) =
      some "Fusion set 'ab': input arcs one() and all() collide on place 'a' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)." := by
  decide

set_option maxRecDepth 20000 in
/-- **Overlapping sets reject** ([MOD-061] AC7): sets `ab` and `cb` both list `b`; the build fails
naming `b` and both sets. -/
theorem fuseEx_overlap_rejected :
    (match refFuse refBuild [⟨"ab", ["a", "b"]⟩, ⟨"cb", ["c", "b"]⟩] fuseExBoth with
      | .error m => some m | .ok _ => none) =
      some "Fusion overlap: place 'b' appears in two fusion sets ('ab' and 'cb'). A place may appear in at most one fusion set (MOD-060)." := by
  decide

/-- **A fused output can fail the transition builder** ([IO-011]): an output that puts a token
into both `a` and `b` names `a` twice once they are fused, and the build fails. -/
theorem fuseEx_andBoth_rejected :
    (refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExAndBoth).toOption.isNone = true := by
  decide

/-- **Input and read on one place fail the transition builder** ([EXEC-012]): consuming from `a`
and reading `b` becomes consuming from and reading `a`, and the build fails. -/
theorem fuseEx_inRead_rejected :
    (refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExInRead).toOption.isNone = true := by
  decide

/-- **A one-member set fuses nothing** ([MOD-060], ruling D54 (a)): the set `{a}` leaves the
transition's two `one()` arcs as they were. -/
theorem fuseEx_single_noop :
    (refFuse refBuild [⟨"solo", ["a"]⟩] fuseExBoth).toOption.map
        (fun Y => Y.defs.map fun d => d.core.inputs.map fun s => (s.place, s.card)) =
      some [[("a", Card.one), ("b", Card.one)]] := by
  decide

/-- **A terminal place on a removed member moves to the canonical place**: with `b` declared
terminal and `a`, `b` fused, the fused net's only place is `a`, and `a` is terminal. -/
theorem fuseEx_terminal_moved :
    (refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExTerm).toOption.map
        (fun Y => (Y.terminals, Y.places)) = some (["a"], ["a"]) := by
  decide

/-- **Mixed token types are rejected where the type is visible** ([MOD-060] item 3): with places
keyed by name and token type, a set of a type-1 and a type-2 place is rejected, a set of two
type-1 places is accepted. -/
theorem fuseEx_decl_types :
    (match refDeclFusion (N := String × Nat) Prod.snd ⟨"mixed", [("a", 1), ("b", 2)]⟩ with
      | .error _ => true | .ok _ => false) = true ∧
    (match refDeclFusion (N := String × Nat) Prod.snd ⟨"same", [("a", 1), ("b", 1)]⟩ with
      | .error _ => false | .ok _ => true) = true := by
  decide

end Examples

end Libpetri.Reference
