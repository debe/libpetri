import Libpetri.Novel.RouteB.Aligned
import Libpetri.Novel.RouteB.Classify
import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# Glossary: the ν verifier's Route B terms

The verifier-side terms of the ν requirements ([NU-051], [NU-052], [NU-055]), as readable names
for definitions the Route B model already has (`Libpetri/Novel/RouteB/`): the fragment classifier
`classifyS`, the conflict prune `dominated`, the name-alignment predicate `alignedAll`, and the
verdict of the name-partition graph `Decide.verdict`. Nothing here redefines them. Each glossary
term quotes its entry in section "ν verification" of `spec/glossary.md`.

Each wrapper is registered as a witness model with `#spec_witness`, so that a requirement block
can state its predicate over an abstract classifier, prune or decider and check it against the
shipped model. Every value parameter is an argument of the wrapper, not of the witness, because a
`holds` theorem may apply its requirement only to a registered witness.

These wrappers judge the Route B model, which places are `PlaceId`s in. The reference ν firing
(`RefNu`) does not exist yet; the lines that compare a verdict with what the executor reaches are
stated by the blocks, against the executor their design names.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB Libpetri.Novel.CanonicalKey Libpetri.Novel.ForwardDeposit

/-! ## Coloured places and the fragment classifier -/

/-- **Glossary: Coloured place.** "A place whose tokens carry a correlation name in the name
layer of Route B: a match key of a matched transition [NU-020] and, under EXTENDED, also a
declared carrier place [NU-051] and a relay target [NU-054]. Under BASE the coloured set is the
match keys alone [NU-055]. The classifier computes the coloured set for each call."

`ColouredInputs col T`: the input arcs of `T` on a place of the coloured set `col`, in
declaration order. -/
def ColouredInputs (col : PlaceId → Bool) (T : NuTrans) : List InSpec :=
  T.base.inputs.filter fun s => col s.place

/-- **Glossary: Fragment classifier.** "The function a ν verifier applies to each transition of a
net, in the fragment mode BASE or EXTENDED, to give it a role in the fragment Route B decides
exactly (a mint, a matched join, a coloured consumer or an ordinary transition), or no role, in
which case the net falls back to the sound over-approximation [NU-050], [NU-051]."

A classifier, abstractly: from the coloured set, the mode, whether the transition is a declared
mint, the places its timeout outcome writes (with what it writes there) and the transition, the
role, or `none`. -/
abbrev Classifier :=
  (PlaceId → Bool) → Mode → Bool → List (PlaceId × TW) → NuTrans → Option Role

/-- The shipped classifier, per transition (`Novel.RouteB.classifyS`, the off-key rule
included), registered as a witness model. -/
def refClassify : Classifier := fun col mode declared tw T => classifyS col mode declared tw T

#spec_witness refClassify

/-! ## Conflict priority -/

/-- A conflict prune over the classes of the Route B graph: from the coloured set, the base layer
(enablement, firing, readiness, competition and in-flight tests of the base marking), the net,
the roles, a class and a transition `L`, whether `L` is left unexpanded from the class. -/
abbrev Prune (β : Type) :=
  (co : List PlaceId) → BaseLayer β → List NuTrans → (NuTrans → Role) → NState co β → NuTrans →
    Bool

/-- The shipped prune (`Novel.RouteB.dominated`, the Rust `priority_dominated`), registered as a
witness model. -/
def refPrune {β : Type} : Prune β :=
  fun _ base net role S L => dominated base net role S L

#spec_witness refPrune

/-- **Glossary: Pre-empt.** "Under conflict-only priority, a transition H pre-empts a transition L
in a class when H is enabled, is not L, has strictly higher priority, is ready no later than L,
has no firing in flight, fires in the class and competes with L for a consumed input. L is then
not expanded from the class [NU-052]."

`PreEmpts base role S H L`, with "fires in the class" read as `willFire` (a join needs an
enabling name, a consumer a resident one) and "competes" as the base layer's `compete`. -/
def PreEmpts {co : List PlaceId} {β : Type} (base : BaseLayer β) (role : NuTrans → Role)
    (S : NState co β) (H L : NuTrans) : Prop :=
  base.enabled S.b H.base = true ∧ H.base.name ≠ L.base.name ∧
    L.base.priority < H.base.priority ∧ base.readyLe S.b H.base L.base = true ∧
    base.idle S.b H.base = true ∧ willFire co (role H) S.m S.bound = true ∧
    base.compete S.b H.base L.base = true

/-! ## Name alignment and the verdict -/

/-- **Glossary: Name-aligned.** "A list S of places is name-aligned in a marking when the places
of S together hold at most one distinct name: any two names resident in places of S, in the same
place or in two, are equal [NU-055]."

On a class of the Route B graph: `alignedAll`, every pair of places of `ps`, self pairs included,
is `aligned`. -/
def NameAligned {co : List PlaceId} {β : Type} (ps : List PlaceId) (S : NState co β) : Prop :=
  alignedAll ps S = true

instance {co : List PlaceId} {β : Type} (ps : List PlaceId) (S : NState co β) :
    Decidable (NameAligned ps S) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Glossary: Verdict.** "The answer a verifier gives for a property: `Proven`, `Violated`
or `Unknown` [VER-003]."

The verdict of the Route B graph (`Novel.RouteB.Decide.Verdict`); a `Violated` carries the index
of the violating class. -/
abbrev RouteBVerdict := Decide.Verdict

/-- One name-alignment call to Route B: the coloured set, the classified net with its roles,
whether conflict priority is on, the build limits, the places `S` and the initial count
marking. -/
structure AlignQuery where
  /-- The coloured set, in the classifier's order. -/
  co : List PlaceId
  /-- The net. -/
  net : List NuTrans
  /-- The role the classifier gave each transition. -/
  role : NuTrans → Role
  /-- Conflict priority ([NU-052]) on or off. -/
  conflict : Bool
  /-- The class bound of the build. -/
  maxClasses : ℕ
  /-- The fuel of the build. -/
  fuel : ℕ
  /-- The places `S`, in the caller's order. -/
  ps : List PlaceId
  /-- The initial count marking. -/
  a0 : AMarking

/-- A decider of `NameAligned(S)`: a verdict for each call. -/
abbrev AlignDecider := AlignQuery → RouteBVerdict

/-- The shipped decider: Route B's build on the untimed base, with the early stop at the first
class that is not name-aligned, then its verdict for the safety property "every class is
name-aligned". Registered as a witness model. -/
noncomputable def refNameAligned : AlignDecider := fun q =>
  Decide.verdict (routeB (co := q.co) untimedBase q.net q.role q.conflict)
    (Decide.build (routeB (co := q.co) untimedBase q.net q.role q.conflict) q.maxClasses
      (fun _ => false) (fun S => !alignedAll q.ps S) true q.fuel (initState q.co q.a0))
    (.safety fun S => !alignedAll q.ps S)

#spec_witness refNameAligned

/-! ## Bridge lemmas -/

/-- `refPrune` drops `L` exactly when some transition of the net pre-empts it. -/
theorem refPrune_iff {β : Type} (co : List PlaceId) (base : BaseLayer β) (net : List NuTrans)
    (role : NuTrans → Role) (S : NState co β) (L : NuTrans) :
    refPrune co base net role S L = true ↔ ∃ H ∈ net, PreEmpts base role S H L := by
  simp only [refPrune, dominated, PreEmpts, List.any_eq_true, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨H, ⟨hH, he⟩, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩
    exact ⟨H, hH, he, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨H, hH, he, h1, h2, h3, h4, h5, h6⟩
    exact ⟨H, ⟨hH, he⟩, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩

/-- `NameAligned` is the pairwise reading: any two places of `ps`, the same place included, are
`aligned`. -/
theorem nameAligned_iff {co : List PlaceId} {β : Type} (ps : List PlaceId) (S : NState co β) :
    NameAligned ps S ↔ ∀ p ∈ ps, ∀ q ∈ ps, aligned p q S = true :=
  alignedAll_eq_true_iff

end Libpetri.Spec
