import Mathlib.Data.List.Nodup
import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.Nu
import Libpetri.Reference.NuMint
import Libpetri.Reference.ComposeBind
import Libpetri.Spec.Text.NU_030

set_option linter.missingDocs true

/-!
# NU-030: Freshness scoping under composition (`spec/12-nu-nets.md`)

NU-030 is a pure-function requirement (kind F) over an abstract **ν rebuild**
`Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K`: a place rewrite `σ` and a name
map `g` take a transition definition that may carry a match specification ([NU-020]) to the
rebuilt definition. Every composition rewrite is such a rebuild: prefix renaming ([MOD-010],
`σ = Nm.pre p`, `g = preS p`), port binding ([MOD-020], `σ = bindSubst bm`, `g = id`), place
fusion ([MOD-061], `σ` the fusion owner map, `g = id`, then the input merge) and the identity
rewrite of action binding ([CORE-042], `σ = id`, `g = id`, the action replaced).

The block has four lines: the input places and the output places of the rebuilt definition are
the images under `σ` of the original ones (the arcs follow `σ`), the match specification is
the original one with every correlated place and every relay target ([NU-054]) mapped by the same
`σ`, in order, each keeping its key (a definition without a match stays without one), and the name
of the rebuilt definition is `g` of the original name (the instance prefix under prefix renaming,
the original name under every other rebuild).

The witness is `refNuRewrite`: the rewrite pass of RefCompose on the `TransDef` part
(`TransDef.map σ g`, the part `CDef.map` and so `refInst`, `rewriteDef` and `fuseDef` share) and
`MatchSpec.mapPlaces σ` on the match. Consequences for every model of the block: a composed join
still keys input places of its own (`nu030_keysOnInputs`, AC2), its relay targets are still output
places (`nu030_relaysOnOutputs`), an injective rewrite keeps the key of every correlated input
(`nu030_keyAt`), and a rewrite that sends two correlated inputs onto one place is refused by the
reference ν builder (`nu030_fusedKeys_refused`), and two instances of one subnet never mint one
name (`nu030_instanceNames_disjoint`, AC1, from line 4 and the minting layer's
`nu030_instanceMints_disjoint`). Within one execution the minter never returns one name twice,
the calls of a channel-merged transition included (`nu030_oneExecution`).

Wrong rebuilds are forbidden: one that drops the match (the regression pinned by
`bind_actions_preserves_match_spec` in `rust/libpetri-core/src/petri_net.rs`), one that invents a match on a plain transition, one
that renames the arcs and leaves the match on the author-original places, one that swaps the keys
of two correlated inputs, one that reverses the declaration order of the keys, one that merges two
keys a fusion lands on one place, one that leaves the relay targets behind, one that leaves the
input arcs behind, one that leaves the output specification behind and one that keeps the
transition name when it instantiates.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

section Vocabulary

variable {N M K : Type}

/-- A match specification through a place map: every correlated place and every relay target
mapped by `f`, in declaration order, each keeping its key. The key type `K` is untouched, so a
rewrite cannot change what a key projects. -/
def MatchSpec.mapPlaces (f : N → M) (ms : MatchSpec N K) : MatchSpec M K :=
  ⟨ms.keys.map fun k => (f k.1, k.2), ms.relays.map fun k => (f k.1, k.2)⟩

/-- The correlated places of a mapped match are the mapped correlated places, in order. -/
theorem MatchSpec.mapPlaces_keyPlaces (f : N → M) (ms : MatchSpec N K) :
    (ms.mapPlaces f).keyPlaces = ms.keyPlaces.map f := by
  simp [MatchSpec.mapPlaces, MatchSpec.keyPlaces]

/-- The relay targets of a mapped match are the mapped relay targets, in order. -/
theorem MatchSpec.mapPlaces_relayPlaces (f : N → M) (ms : MatchSpec N K) :
    (ms.mapPlaces f).relayPlaces = ms.relayPlaces.map f := by
  simp [MatchSpec.mapPlaces, MatchSpec.relayPlaces]

/-- The keys of a mapped match, in order, are the original keys. -/
theorem MatchSpec.mapPlaces_keys_snd (f : N → M) (ms : MatchSpec N K) :
    (ms.mapPlaces f).keys.map Prod.snd = ms.keys.map Prod.snd := by
  simp [MatchSpec.mapPlaces, Function.comp_def]

end Vocabulary

/-! ## NU-030: Freshness Scoping under Composition -/

requirement NU_030
  id "NU-030"
  title "Freshness Scoping under Composition"
  kind F
  scope "every rebuild of a transition through a place rewrite, such as prefix renaming, port binding, place fusion and the identity rewrite of action binding; the channel merge of two transitions (MOD-021) is not such a rebuild"
  source verbatim "spec/12-nu-nets.md"
  covers NU_030.s1, NU_030.s2, NU_030.s3, NU_030.s4, NU_030.s5
  reading "For every ν rebuild Rw (a place rewrite σ and a name map g take a transition definition with an optional match specification to the rebuilt definition), every σ, every g and every definition d:"
          "a place is an input place of the rebuilt definition exactly when it is σ of an input place of d;"
          "a place is a place of the output specification of the rebuilt definition exactly when it is σ of a place of the output specification of d;"
          "the match specification of the rebuilt definition is d's with every correlated place and every relay target replaced by its image under σ, in order, each keeping its key; when d has no match specification, the rebuilt definition has none;"
          "the name of the rebuilt definition is g of d's name."
  assumes "The model is one function Rw σ g on ν definitions (NuDef: the TransDef record of RefNetBuild and an optional match). σ is the place rewrite the rebuild applies to the arcs and g its name map: prefix renaming (MOD-010, σ = Nm.pre p and g = preS p), port binding (MOD-020, σ = bindSubst and g = id), place fusion (MOD-061, σ the fusion owner map and g = id) and the identity rewrite (σ = id, g = id) of action binding (CORE-042) and of Rust's with_added_inhibitors. The spec sentences list these rebuilds as examples; the statement covers every σ and g. A place outside the rewrite's domain maps to itself, as resolve does in Rust (rust/libpetri-core/src/rewriter.rs), Java's remap.getOrDefault in SubnetRewriter.rebuildWithName (java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java) and TypeScript's remap.get(...) ?? k.place in rebuildWithName (typescript/src/core/internal/subnet-rewriter.ts). The timing, priority and action of the rebuilt definition are not stated: action binding replaces the action, and those parts are the lines of MOD-010, MOD-020, MOD-061 and CORE-042."
          "Lines 1 and 2 state that the arcs follow σ, so that line 3's σ is 'the same place rewrite the arcs follow'. They compare places as sets: fusion merges two input arcs that land on one place into one arc (MOD-061 rule (b), fuseDef), so the list of input arcs is not the mapped list, while the set of input places is its image. MOD-010 pins the instantiated definitions as the mapped list itself, which implies lines 1 and 2 for that rebuild, so the two blocks agree and NU-030 is the weaker of the two. The inhibitor, read and reset arcs, the order, repetitions and cardinalities of the arcs, the shape of the output specification and the source of a ForwardInput (not a place of the output specification in IO-017's sense, which counts only its target) are the lines of MOD-010, MOD-020 and MOD-061, and a ForwardInput whose source is not an input place is refused by IO-014's build check; only the input places (where the keys live, NU-020) and the output places (where the relay targets live, NU-054) bear on the match."
          "Line 3 is the remap all three runtimes do in their one rebuild function, keys and relay targets alike, in declaration order and with the key projection kept: rebuild_with_name in rust/libpetri-core/src/rewriter.rs, SubnetRewriter.rebuildWithName in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java with MatchSpec.remap (java/src/main/java/org/libpetri/core/MatchSpec.java), rebuildWithName in typescript/src/core/internal/subnet-rewriter.ts; fusion goes through the same function (apply_fusion in rewriter.rs, SubnetRewriter.applyFusion in SubnetRewriter.java, applyFusion in subnet-rewriter.ts), and the identity rebuild of action binding carries the match unchanged (rebuild_with_action in rust/libpetri-core/src/transition.rs, pinned by bind_actions_preserves_match_spec in rust/libpetri-core/src/petri_net.rs and PetriNetTest.bindActions_preservesMatchSpec in java/src/test/java/org/libpetri/core/PetriNetTest.java). Python rides on the Rust rebuild. The key type K is abstract, so 'each with the key projection it had' is: the key at each position is unchanged (MatchSpec.mapPlaces_keys_snd). The rebuilt match keeps one entry per original entry: a fusion that lands two keys on one place does not merge them (the fusion merge applies to the input arcs only), so the build check below sees the place keyed twice."
          "Line 4 is the name each runtime gives the rebuild: prefix renaming prefixes the name (rewrite_transition in rust/libpetri-core/src/rewriter.rs, SubnetRewriter.rewriteTransition in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, rewriteTransition in typescript/src/core/internal/subnet-rewriter.ts), while port binding, fusion and action binding keep it (substitute_places and apply_fusion in rewriter.rs, SubnetRewriter.substitutePlaces and applyFusion in SubnetRewriter.java, substitutePlaces and applyFusion in subnet-rewriter.ts, rebuild_with_action in transition.rs). The line leaves g free; which g each rebuild passes is tied at the composition witnesses by nu030_passes_nameMaps: the reference instantiation (refInst) is the rebuild with g = preS p, port binding (rewriteDef) the rebuild with g = id, and a fusion that succeeds (fuseDef) keeps the name, g = id. So a rebuild that kept the name at instantiation would meet the line with g = id and break MOD-010's instantiation line, which is the block that fixes the instance names."
          "Rw is total: it returns the rewritten definition before the build check. Every runtime builds the rebuilt transition again, and a rewrite that sends two correlated places, or two relay targets, onto one place is refused there with the error a place keyed twice or a relay target declared twice gets: NU-020's build line (NU_020_build) and NU-054's build line. nu030_fusedKeys_refused shows it for every model of this block with the reference ν builder refNuBuild. The channel merge of two transitions (MOD-021) is not a rebuild through a place rewrite: it may give a passthrough side the match of the other side, and it is NU-060's."
          "The first paragraph's rationale (as reworded under ruling D20, clash nu-b#6: names minted in two instances never collide; the transition component of a minted name is the firing transition's post-compose name, which carries the instance prefix unless the transition is channel-merged) is not a shall sentence. AC1 (two instances of a forking subnet never mint colliding names) is proven for every model of the block, not stated: line 4 gives the two instance transitions the names preS p t and preS q t', and two such names under different valid prefixes never mint one name whatever the scopes and counters (nu030_instanceNames_disjoint, from nu030_instanceMints_disjoint, preS_inj and mintName_inj); within one execution every two freshName() calls return different names, the calls of a channel-merged transition included (nu030_oneExecution, the reference minter; NU_010_unique for every minter)."
          "AC2 (after composition a join's match correlates the renamed, host-bound places, not the author-original ones) is line 3; nu030_keysOnInputs shows that every model of the block keeps the keys on input places of the rebuilt definition, so a composed join still correlates its own renamed inputs, and NU_030_nonvacuous renames a join keyed on a and b under i1 to keys on i1/a and i1/b. The test derivation (instantiate a fork and join subnet twice and check that each instance's join merges only its own siblings) runs a composed net; that run is tested, and its two halves are AC1 and AC2 with NU-020's correlated take (NU_020_take)."
  signoff "2026-11-13 b0cf16a58e042aab ai"
  statement : ∀ {N A K : Type}, ((N → N) → (String → String) → NuDef N A K → NuDef N A K) → Prop :=
    fun Rw => ∀ σ g d,
      (∀ x, x ∈ inPlaces (Rw σ g d).toTransDef.toTrans ↔
        ∃ p ∈ inPlaces d.toTransDef.toTrans, σ p = x) ∧
      (∀ x, OutputArc (Rw σ g d).toTransDef.toTrans x ↔
        ∃ p, OutputArc d.toTransDef.toTrans p ∧ σ p = x) ∧
      (Rw σ g d).mspec = d.mspec.map (MatchSpec.mapPlaces σ) ∧
      (Rw σ g d).core.name = g d.core.name

/- The pinned readable form of NU-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_030 : {N A K : Type} → ((N → N) → (String → String) → NuDef N A K → NuDef N A K) → Prop :=
fun {N A K} Rw =>
  ∀ (σ : N → N) (g : String → String) (d : NuDef N A K),
    (∀ (x : N), x ∈ inPlaces (Rw σ g d).toTrans ↔ ∃ p ∈ inPlaces d.toTrans, σ p = x) ∧
      (∀ (x : N), OutputArc (Rw σ g d).toTrans x ↔ ∃ p, OutputArc d.toTrans p ∧ σ p = x) ∧
        (Rw σ g d).mspec = Option.map (MatchSpec.mapPlaces σ) d.mspec ∧ (Rw σ g d).core.name = g d.core.name
-/
#guard_msgs in #print NU_030

/-! ## The reference -/

section Reference

variable {N A K : Type}

/-- **The reference ν rebuild**: the `TransDef` part through RefCompose's rewrite pass
`TransDef.map σ g`, the match through `MatchSpec.mapPlaces σ`. -/
def refNuRewrite (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g, mspec := d.mspec.map (MatchSpec.mapPlaces σ) }

/- The reference ν rebuild is the witness model of NU-030. -/
#spec_witness refNuRewrite

/-- The `TransDef` part of the reference ν rebuild is RefCompose's rewrite pass. -/
theorem refNuRewrite_toTransDef (σ : N → N) (g : String → String) (d : NuDef N A K) :
    (refNuRewrite σ g d).toTransDef = d.toTransDef.map σ g := rfl

/-- **The RefCompose link.** On a composition definition with its match (`NuCDef`, read as a ν
definition by `NuCDef.toNuDef`), the reference ν rebuild rewrites the arcs exactly as one
composition rewrite pass `CDef.map σ g` does, the pass that instantiation (`refInst`), port
binding (`rewriteDef`) and fusion (`fuseDef`, before the input merge) apply. -/
theorem refNuRewrite_cdef (σ : N → N) (g : String → String) (c : NuCDef N A K) :
    (refNuRewrite σ g c.toNuDef).toTransDef = (c.toCDef.map σ g).toTransDef := rfl

/-- The places of a mapped output specification are the mapped places. -/
theorem nu030_outPlaces_mapOut {M : Type} (f : N → M) :
    ∀ o : Out N, outPlaces (mapOut f o) = (outPlaces o).map f
  | .place _ => rfl
  | .forward _ _ => rfl
  | .and l r => by simp [mapOut, outPlaces, nu030_outPlaces_mapOut f l, nu030_outPlaces_mapOut f r]
  | .xor l r => by simp [mapOut, outPlaces, nu030_outPlaces_mapOut f l, nu030_outPlaces_mapOut f r]
  | .timeout c => by simp [mapOut, outPlaces, nu030_outPlaces_mapOut f c]

/-- The input places of a mapped definition are the mapped input places. -/
theorem nu030_inPlaces_map (σ : N → N) (g : String → String) (d : TransDef N A) :
    inPlaces (d.map σ g).toTrans = (inPlaces d.toTrans).map σ := by
  simp [inPlaces, TransDef.map, TransDef.toTrans, mapCore, mapIn, Function.comp_def]

/-- A place of the output specification of a mapped definition is exactly the image of a place
of the original output specification. -/
theorem nu030_outputArc_map (σ : N → N) (g : String → String) (d : TransDef N A) (x : N) :
    OutputArc (d.map σ g).toTrans x ↔ ∃ p, OutputArc d.toTrans p ∧ σ p = x := by
  unfold OutputArc
  cases ho : d.out with
  | none => simp [TransDef.map, TransDef.toTrans, ho]
  | some o =>
    simp only [TransDef.map, TransDef.toTrans, ho, Option.map_some, Option.some.injEq,
      exists_eq_left', nu030_outPlaces_mapOut, List.mem_map]

end Reference

/-- ✓ The reference ν rebuild satisfies NU-030 at every place type, action type and key type: its
arcs are the rewrite pass `TransDef.map σ g`, so the input places and the output places are the
images under `σ`, its match is the original one with every place mapped by the same `σ`, and its
name is the original name through `g`. -/
@[evidence holds NU_030]
theorem NU_030_reference {N A K : Type} : NU_030 (refNuRewrite (N := N) (A := A) (K := K)) := by
  intro σ g d
  refine ⟨fun x => ?_, fun x => ?_, rfl, rfl⟩
  · rw [refNuRewrite_toTransDef, nu030_inPlaces_map, List.mem_map]
  · rw [refNuRewrite_toTransDef, nu030_outputArc_map]

/-! ## Which name map each composition pass gives the rebuild -/

/-- **The name map of each pass** (line 4 at the composition witnesses). Instantiation under the
prefix `p` is the rebuild with the name map `preS p`: each definition of an instance is the
rebuild of the body's definition through `Nm.pre p` and `preS p`, so a transition `fork` of the
body is `p/fork` in the instance. Port binding is the rebuild through `bindSubst bm` with the
name kept (`id`), and a fusion that succeeds keeps the name too (`id`): its arcs are the rebuild's
before the input merge, and the merge touches only the input arcs. -/
@[evidence cites "NU-030" "*When* a transition is rebuilt through a place rewrite, the name of the rebuilt transition *shall* be the original name with the instance prefix under prefix renaming ([MOD-010]) and the original name under every other rebuild."]
theorem nu030_passes_nameMaps {N A K : Type} [DecidableEq N] (Nm : Naming N)
    (bm : List (BindEntry N)) (σ : N → N) :
    (∀ (S : SubnetDef N A) (p : String) (I : Instance N A), refInst Nm S p = .ok I →
      I.defs.map CDef.toTransDef = S.defs.map fun c =>
        (refNuRewrite (Nm.pre p) (preS p) (NuCDef.ofCDef c (none : Option (MatchSpec N K))).toNuDef).toTransDef) ∧
    (∀ c : NuCDef N A K, (rewriteDef bm c.toCDef).toTransDef =
      (refNuRewrite (bindSubst bm) id c.toNuDef).toTransDef) ∧
    (∀ (c : NuCDef N A K) d', fuseDef σ c.toCDef = .ok d' →
      d'.core.name = (refNuRewrite σ id c.toNuDef).core.name) := by
  refine ⟨fun S p I h => ?_, fun c => rfl, fun c d' h => ?_⟩
  · rw [(refInst_ok h).2.2.2.2.1, List.map_map]
    rfl
  · unfold fuseDef at h
    split at h
    · obtain ⟨ins, -, rfl⟩ := except_map_ok_iff.1 h
      rfl
    · cases h
      rfl

/-! ## The four lines, named (for the mutants) -/

section Lines

variable {N A K : Type}

/-- Line 1 of NU-030: the input places follow the rewrite. -/
def nu030_line1 (Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K) : Prop :=
  ∀ σ g d, ∀ x, x ∈ inPlaces (Rw σ g d).toTransDef.toTrans ↔
    ∃ p ∈ inPlaces d.toTransDef.toTrans, σ p = x

/-- Line 2 of NU-030: the output places follow the rewrite. -/
def nu030_line2 (Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K) : Prop :=
  ∀ σ g d, ∀ x, OutputArc (Rw σ g d).toTransDef.toTrans x ↔
    ∃ p, OutputArc d.toTransDef.toTrans p ∧ σ p = x

/-- Line 3 of NU-030: the match follows the same rewrite. -/
def nu030_line3 (Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K) : Prop :=
  ∀ σ g d, (Rw σ g d).mspec = d.mspec.map (MatchSpec.mapPlaces σ)

/-- Line 4 of NU-030: the name follows the name map. -/
def nu030_line4 (Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K) : Prop :=
  ∀ σ g d, (Rw σ g d).core.name = g d.core.name

/-- NU-030 is its four lines. -/
theorem nu030_iff (Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K) :
    NU_030 Rw ↔ nu030_line1 Rw ∧ nu030_line2 Rw ∧ nu030_line3 Rw ∧ nu030_line4 Rw :=
  ⟨fun h => ⟨fun σ g d => (h σ g d).1, fun σ g d => (h σ g d).2.1, fun σ g d => (h σ g d).2.2.1,
      fun σ g d => (h σ g d).2.2.2⟩,
    fun h σ g d => ⟨h.1 σ g d, h.2.1 σ g d, h.2.2.1 σ g d, h.2.2.2 σ g d⟩⟩

end Lines

/-! ## Consequences for every model of the block -/

section Consequences

variable {N A K : Type}

/-- **AC2.** In every model of NU-030 a rebuilt join keys the images of its original correlated
places, in order, and when the original keys sat on input places (as every built match's do), the
rebuilt keys sit on input places of the rebuilt join. A join keyed on `a` and `b`, renamed under
`i1`, keys `i1/a` and `i1/b`, which are its inputs: it correlates the renamed inputs, never the
author-original ones. -/
@[evidence cites "NU-030" "AC2: after composition, a join's match correlates the renamed (host-bound) places, not the author-original ones"]
theorem nu030_keysOnInputs {Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K}
    (h : NU_030 Rw) (σ : N → N) (g : String → String) {d : NuDef N A K} {ms : MatchSpec N K}
    (hd : d.mspec = some ms) (hk : KeysOnInputs d.toNuTrans ms) :
    (Rw σ g d).mspec = some (ms.mapPlaces σ) ∧
      (ms.mapPlaces σ).keyPlaces = ms.keyPlaces.map σ ∧
      KeysOnInputs (Rw σ g d).toNuTrans (ms.mapPlaces σ) := by
  refine ⟨by rw [(h σ g d).2.2.1, hd]; rfl, MatchSpec.mapPlaces_keyPlaces σ ms, fun x hx => ?_⟩
  rw [MatchSpec.mapPlaces_keyPlaces, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ((h σ g d).1 (σ p)).2 ⟨p, hk p hp, rfl⟩

/-- In every model of NU-030 the relay targets of a rebuilt join are the images of the original
ones, and when those were output places (as [NU-054]'s build check demands), the rebuilt relay
targets are output places of the rebuilt join. -/
@[evidence cites "NU-030" "the correlated places and relay targets of a rebuilt match are the images under the same rewrite as the arcs: relay targets stay on output places"]
theorem nu030_relaysOnOutputs {Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K}
    (h : NU_030 Rw) (σ : N → N) (g : String → String) {d : NuDef N A K} {ms : MatchSpec N K}
    (hd : d.mspec = some ms) (ho : ∀ p ∈ ms.relayPlaces, OutputArc d.toTransDef.toTrans p) :
    (Rw σ g d).mspec = some (ms.mapPlaces σ) ∧
      ∀ x ∈ (ms.mapPlaces σ).relayPlaces, OutputArc (Rw σ g d).toTransDef.toTrans x := by
  refine ⟨by rw [(h σ g d).2.2.1, hd]; rfl, fun x hx => ?_⟩
  rw [MatchSpec.mapPlaces_relayPlaces, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ((h σ g d).2.1 (σ p)).2 ⟨p, ho p hp, rfl⟩

/-- In every model of NU-030 an injective rewrite (a prefix rename under a valid prefix) keeps
the key of every correlated input: the key at `σ p` after the rebuild is the key at `p` before it.
So a rename never swaps two projections. -/
theorem nu030_keyAt [DecidableEq N]
    {Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K}
    (h : NU_030 Rw) {σ : N → N} (hσ : Function.Injective σ) (g : String → String)
    {d : NuDef N A K} {ms : MatchSpec N K} (hd : d.mspec = some ms) (p : N) :
    ∃ ms', (Rw σ g d).mspec = some ms' ∧ keyAt ms' (σ p) = keyAt ms p := by
  refine ⟨ms.mapPlaces σ, by rw [(h σ g d).2.2.1, hd]; rfl, ?_⟩
  unfold keyAt MatchSpec.mapPlaces
  rw [List.find?_map]
  have he : ((fun k : N × K => decide (k.1 = σ p)) ∘ fun k : N × K => (σ k.1, k.2)) =
      fun k => decide (k.1 = p) := by
    funext k
    simp only [Function.comp_apply, decide_eq_decide]
    exact hσ.eq_iff
  rw [he, Option.map_map]
  rfl

/-- **Fused keys are refused.** In every model of NU-030, a rewrite that sends two different
correlated places of a join onto one place (a fusion, or two ports bound to one host place)
gives a rebuilt join that the reference ν builder refuses: its match keys one place twice
([NU-020]'s build line). -/
@[evidence cites "NU-030" "A rewrite that maps two correlated inputs of one join onto one place is rejected when the rebuilt transition is built"]
theorem nu030_fusedKeys_refused [DecidableEq N] [ToString N]
    {Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K}
    (h : NU_030 Rw) (σ : N → N) (g : String → String) {d : NuDef N A K} {ms : MatchSpec N K}
    (hd : d.mspec = some ms) {a b : N} (ha : a ∈ ms.keyPlaces) (hb : b ∈ ms.keyPlaces)
    (hab : a ≠ b) (hσ : σ a = σ b) :
    refNuBuild (Rw σ g d).toNuTrans ≠ none := by
  intro hn
  have hm : (Rw σ g d).toNuTrans.mspec = some (ms.mapPlaces σ) := by
    show (Rw σ g d).mspec = _
    rw [(h σ g d).2.2.1, hd]; rfl
  have hdist := (((refNuBuild_eq_none_iff _).1 hn).2 _ hm).1
  unfold KeysDistinct at hdist
  rw [MatchSpec.mapPlaces_keyPlaces] at hdist
  exact hab (List.inj_on_of_nodup_map hdist ha hb hσ)

/-- **AC1, across instances.** Two transitions of two instances under different valid prefixes
never mint one name, whatever the scopes (free of `#`, as every accepted scope is, [NU-011]) and
counters: the transition component of `<transition>#<scope>:<n>` parses back uniquely and the
prefixed transition names differ. `i1/fork` and `i2/fork` mint `i1/fork#s:0` and
`i2/fork#s:0`, never one name. -/
theorem nu030_instanceMints_disjoint {p q t t' s s' : String} {n n' : Nat}
    (hp : ValidPrefix p) (hq : ValidPrefix q) (hpq : p ≠ q) (hs : '#' ∉ s.toList)
    (hs' : '#' ∉ s'.toList) :
    mintName (preS p t) s n ≠ mintName (preS q t') s' n' := fun h =>
  hpq (preS_inj _ _ _ _ hp hq (mintName_inj hs hs' h).1).1

/-- **AC1, in every model of the block.** Instantiate one forking subnet twice, under `i1` and
under `i2`: the rebuild names the two forks `i1/fork` and `i2/fork` (line 4), so the first mints
`i1/fork#s:0` and the second `i2/fork#s:0`, never one name. The same holds for any two transitions
of the two instances, any scopes free of `#` and any counters. -/
@[evidence cites "NU-030" "AC1: two instances of a forking subnet never mint colliding names"]
theorem nu030_instanceNames_disjoint
    {Rw : (N → N) → (String → String) → NuDef N A K → NuDef N A K} (h : NU_030 Rw)
    (σ σ' : N → N) (d d' : NuDef N A K) {p q s s' : String} {n n' : Nat}
    (hp : ValidPrefix p) (hq : ValidPrefix q) (hpq : p ≠ q) (hs : '#' ∉ s.toList)
    (hs' : '#' ∉ s'.toList) :
    mintName (Rw σ (preS p) d).core.name s n ≠ mintName (Rw σ' (preS q) d').core.name s' n' := by
  rw [(h σ (preS p) d).2.2.2, (h σ' (preS q) d').2.2.2]
  exact nu030_instanceMints_disjoint hp hq hpq hs hs'

/-- **AC1, within one execution.** One execution of the reference minter never returns one name
twice, whichever transitions call it: the calls of a channel-merged transition, whose name is the
caller's and carries no instance prefix, are kept apart by the one counter the executor shares
across all its transitions ([NU-010]). -/
@[evidence cites "NU-030" "AC1: names minted in two instances never collide, channel-merged transitions included"]
theorem nu030_oneExecution {s : String} {evs : List MintEv} {xs : List String}
    (h : MintRun refMintSys (refMintSys.init s) evs xs) : xs.Nodup :=
  refRun_nodup h

end Consequences

/-! ## Worked examples -/

/-- The arcs of the example join: inputs `a` and `b`, one token each. -/
def nu030_core : NTransition String :=
  { name := "join", inputs := [⟨"a", .one⟩, ⟨"b", .one⟩], inhibitors := [], reads := [], resets := [] }

/-- The example join of a fork and join subnet: inputs `a` and `b`, output `c`, keyed on `a`
(key 0) and `b` (key 1), relaying into `c` (key 2). -/
def nu030_join : NuDef String Unit Nat :=
  { core := nu030_core
    out := some (.place "c")
    timing := .immediate
    priority := 0
    action := .passthrough
    mspec := some { keys := [("a", 0), ("b", 1)], relays := [("c", 2)] } }

/-- The same join without a match specification. -/
def nu030_plain : NuDef String Unit Nat := { nu030_join with mspec := none }

/-- The rename under the prefix `i1`. -/
def nu030_i1 : String → String := preS "i1"

/-- ✓ Every line of NU-030 is exercised by the reference: renaming the example join under `i1`
gives a join whose inputs are `i1/a` and `i1/b` (line 1), whose output is `i1/c` (line 2), whose
match keys `i1/a` with key 0 and `i1/b` with key 1 and relays into `i1/c` with key 2, in that order
(line 3), and whose name is `i1/join` (line 4). The same join without a match, rebuilt for action
binding (the identity rewrite), still has none. -/
@[evidence nonvacuous NU_030]
theorem NU_030_nonvacuous :
    inPlaces (refNuRewrite nu030_i1 nu030_i1 nu030_join).toTransDef.toTrans = ["i1/a", "i1/b"] ∧
      OutputArc (refNuRewrite nu030_i1 nu030_i1 nu030_join).toTransDef.toTrans "i1/c" ∧
      (refNuRewrite nu030_i1 nu030_i1 nu030_join).mspec.map (·.keys) =
        some [("i1/a", 0), ("i1/b", 1)] ∧
      (refNuRewrite nu030_i1 nu030_i1 nu030_join).mspec.map (·.relays) = some [("i1/c", 2)] ∧
      (refNuRewrite nu030_i1 nu030_i1 nu030_join).core.name = "i1/join" ∧
      (refNuRewrite id id nu030_plain).mspec = none := by
  refine ⟨by decide, ⟨.place "i1/c", rfl, by decide⟩, by decide, by decide, by decide, rfl⟩

/-- ✓ AC1 worked: the fork of instance `i1` and the fork of instance `i2`, both under scope `s`
and both at counter 0, mint `i1/fork#s:0` and `i2/fork#s:0`, two different names. -/
theorem nu030_ac1_example :
    mintName (preS "i1" "fork") "s" 0 = "i1/fork#s:0" ∧
      mintName (preS "i2" "fork") "s" 0 = "i2/fork#s:0" ∧
      mintName (preS "i1" "fork") "s" 0 ≠ mintName (preS "i2" "fork") "s" 0 := by
  decide

/-! ## Wrong rebuilds -/

section Wrong

variable {N A K : Type}

/-- The match-dropping rebuild (the regression `bind_actions_preserves_match_spec` pins): arcs
rewritten, the match lost. -/
def nu030_dropMatch (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g, mspec := none }

/-- The lazy rebuild: arcs rewritten, the match left on the author-original places. -/
def nu030_keysStay (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g, mspec := d.mspec }

/-- A match with the keys of its correlated inputs reversed against their places. -/
def nu030_swapK (ms : MatchSpec N K) : MatchSpec N K :=
  ⟨(ms.keys.map Prod.fst).zip (ms.keys.map Prod.snd).reverse, ms.relays⟩

/-- The key-swapping rebuild: places mapped, but the keys of the correlated inputs reversed. -/
def nu030_swapKeys (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g, mspec := d.mspec.map (fun ms => nu030_swapK (ms.mapPlaces σ)) }

/-- The relay-forgetting rebuild: keys mapped, relay targets left on the original places. -/
def nu030_relaysStay (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g,
    mspec := d.mspec.map (fun ms => { (ms.mapPlaces σ) with relays := ms.relays }) }

/-- The rebuild that leaves the input arcs on the original places. -/
def nu030_inputsStay (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := { d.toTransDef.map σ g with
      core := { (d.toTransDef.map σ g).core with inputs := d.core.inputs } },
    mspec := d.mspec.map (MatchSpec.mapPlaces σ) }

/-- The rebuild that leaves the output specification on the original places. -/
def nu030_outputsStay (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := { d.toTransDef.map σ g with out := d.out },
    mspec := d.mspec.map (MatchSpec.mapPlaces σ) }

/-- The match-inventing rebuild: a definition without a match comes back with an empty one. -/
def nu030_inventMatch (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g,
    mspec := some ((d.mspec.getD ⟨[], []⟩).mapPlaces σ) }

/-- The order-losing rebuild: every pair mapped and kept, the list of keys reversed. -/
def nu030_reverseKeys (σ : N → N) (g : String → String) (d : NuDef N A K) : NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g,
    mspec := d.mspec.map fun ms => { (ms.mapPlaces σ) with keys := (ms.mapPlaces σ).keys.reverse } }

/-- Keep the first entry for each place, drop the later ones. -/
def nu030_firstPerPlace [DecidableEq N] : List (N × K) → List (N × K)
  | [] => []
  | k :: ks => k :: (nu030_firstPerPlace ks).filter (fun e => decide (e.1 ≠ k.1))

/-- The key-merging rebuild: the fusion merge of input arcs run over the keys as well, so two keys
that the rewrite lands on one place become one. -/
def nu030_mergeKeys [DecidableEq N] (σ : N → N) (g : String → String) (d : NuDef N A K) :
    NuDef N A K :=
  { toTransDef := d.toTransDef.map σ g,
    mspec := d.mspec.map fun ms =>
      { (ms.mapPlaces σ) with keys := nu030_firstPerPlace (ms.mapPlaces σ).keys } }

/-- The name-keeping rebuild: places, outputs and match follow the rewrite, the name map is
ignored (instantiation through the port-binding rebuild). -/
def nu030_keepName (σ : N → N) (_g : String → String) (d : NuDef N A K) : NuDef N A K :=
  refNuRewrite σ id d

end Wrong

/-- ✗ A rebuild that drops the match: the join of the example, rebuilt for action binding (the
identity rewrite), loses its match and would run as a plain AND join. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_dropMatch :
    ¬ NU_030 (nu030_dropMatch (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := (h id id nu030_join).2.2.1
  simp [nu030_dropMatch, nu030_join] at this

/-- ✗ A rebuild that renames the arcs and leaves the match behind: renamed under `i1`, the join
still keys `a` and `b`, places it no longer consumes from. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_keysStay :
    ¬ NU_030 (nu030_keysStay (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := congrArg (Option.map (·.keys)) (h nu030_i1 nu030_i1 nu030_join).2.2.1
  revert this
  decide

/-- ✗ A rebuild that swaps two projections: renamed under `i1`, the join keys `i1/a` with key 1
and `i1/b` with key 0. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_swapKeys :
    ¬ NU_030 (nu030_swapKeys (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := congrArg (Option.map (·.keys)) (h nu030_i1 nu030_i1 nu030_join).2.2.1
  revert this
  decide

/-- ✗ A rebuild that leaves the relay targets behind: renamed under `i1`, the join keys its
renamed inputs but relays into `c`, a place it no longer produces into. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_relaysStay :
    ¬ NU_030 (nu030_relaysStay (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := congrArg (Option.map (·.relays)) (h nu030_i1 nu030_i1 nu030_join).2.2.1
  revert this
  decide

/-- ✗ A rebuild that leaves the input arcs behind: renamed under `i1`, the join still consumes
from `a`, which is no renamed input. Line 1 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_inputsStay :
    ¬ NU_030 (nu030_inputsStay (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := (h nu030_i1 nu030_i1 nu030_join).1 "a"
  revert this
  decide

/-- ✗ A rebuild that leaves the output specification behind: renamed under `i1`, the join still
produces into `c`, which is no renamed output. Line 2 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_outputsStay :
    ¬ NU_030 (nu030_outputsStay (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have hc : OutputArc (nu030_outputsStay nu030_i1 nu030_i1 nu030_join).toTransDef.toTrans "c" :=
    ⟨.place "c", rfl, by simp [outPlaces]⟩
  obtain ⟨p, ⟨o, ho, hp⟩, he⟩ := ((h nu030_i1 nu030_i1 nu030_join).2.1 "c").1 hc
  simp only [nu030_join, TransDef.toTrans, Option.some.injEq] at ho
  subst ho
  simp only [outPlaces, List.mem_singleton] at hp
  subst hp
  revert he
  decide

/-- ✗ A rebuild that invents a match: the example join without a match, rebuilt for action binding
(the identity rewrite), comes back with an empty match and would fire as a correlated join with no
keys instead of a plain AND join. Line 3 fails: no match must stay no match. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_inventMatch :
    ¬ NU_030 (nu030_inventMatch (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := (h id id nu030_plain).2.2.1
  simp [nu030_inventMatch, nu030_plain] at this

/-- ✗ A rebuild that loses the declaration order: renamed under `i1`, the join keys `i1/b` with
key 1 before `i1/a` with key 0. Each place keeps its key, but the order the author wrote and every
runtime keeps is reversed. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_reverseKeys :
    ¬ NU_030 (nu030_reverseKeys (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := congrArg (Option.map (·.keys)) (h nu030_i1 nu030_i1 nu030_join).2.2.1
  revert this
  decide

/-- ✗ A rebuild that merges keys: fusing `b` into `a` lands both keys of the example join on `a`,
and the rebuild keeps only `a` with key 0. The join would build and correlate on one projection,
where the reference keys `a` twice and the build refuses it. Line 3 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_mergeKeys :
    ¬ NU_030 (nu030_mergeKeys (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := congrArg (Option.map (·.keys))
    (h (fun x => if x = "b" then "a" else x) id nu030_join).2.2.1
  revert this
  decide

/-- ✗ A rebuild that keeps the transition name when it instantiates: renamed under `i1`, the join
is still called `join`, so instances `i1` and `i2` would both mint `join#s:0`. Line 4 fails. -/
@[evidence forbids NU_030]
theorem NU_030_forbids_keepName :
    ¬ NU_030 (nu030_keepName (N := String) (A := Unit) (K := Nat)) := by
  intro h
  have := (h nu030_i1 nu030_i1 nu030_join).2.2.2
  revert this
  decide

end Libpetri.Spec
