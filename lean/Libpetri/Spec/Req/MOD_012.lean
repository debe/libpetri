import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Reference.ComposeBuild
import Libpetri.Spec.Req.MOD_010

set_option linter.missingDocs true

/-!
# MOD-012: Per-instance state isolation (`spec/11-modular-composition.md`)

MOD-012 has two blocks over an abstract build-script function `BS : ScriptFn N A` (a script of
calls on an enclosing builder gives the composed net `build()` returns, or a rejection) and a
naming model `Nm : Naming N`.

* `MOD_012` (kind B) adds a firing relation `F`. Line 1 is structure: in a net `BS` builds, every
  transition that names a place *private* to the instance under prefix `b` is named `b/x`. Line 2
  is the marking frame: a firing of a transition named `a/x` leaves every place private to the
  instance under another prefix `b` as it was. Line 3 keeps the slots apart: a definition that a
  compose call adds and that names a private place of its instance still names that place, under
  its own name, in the built net, so the build merges no private place into another place.
* `MOD_012_clock` (kind T) adds a timed step relation `R`. A firing of a transition named `a/x`
  leaves every transition named `b/y` whose arc places are all private to `b` enabled as before,
  armed as before and, when armed, with its stamp; a reap of a transition named `a/x`, or a delay,
  leaves the armed state and the stamp of every transition named `b/y` as they were.

*Private* is ruling D79 (a) (`PrivateTo`): a place is private to the instance under `b` when no
call of the script binds a port to it, lists it in a fusion set, or adds a transition outside the
instance that names it. Port bindings, channels and fusion sets are the ways composition shares
state, and isolation covers the rest. The witnesses are the reference build script (`buildScript`
with the reference transition check and channel merge), the reference firing relation `RefFire`
and the reference timed step `RefTStep`. The reference holds because composition is local: a
compose call adds an instance's transitions rewritten only through its bindings, a channel merge
names only the places of its two sides, and fusion moves only listed places
(`buildScript_local`, `buildScript_keeps`). For instances made by `instantiate`, another instance's transitions never
name a place of `b` (`mod012_inst_leaves`, from [MOD-010]).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Private places -/

section Private

variable {N A : Type}

/-- The transition name `n` lies under prefix `pb`: it is `pb/x` for some `x`. -/
def NamedUnder (pb n : String) : Prop := ∃ x, n = preS pb x

/-- **One call of a build script leaves place `p` to the instance under prefix `pb`** (ruling
D79 (a)): a hand-added transition does not name `p`; a fusion set does not list it; a compose
call binds no port to `p`, its caller-side channel definitions do not name it, and an instance
definition that names `p` belongs to an instance under `pb`, carries a name `pb/x` and is bound
by no channel; an auto-composition binds no port to `p` (by its interface or by inference) and
an instance definition that names `p` is as above; a direct composition's body does not name
`p`. Declaring a place or a terminal place touches no token. -/
def OpLeaves (Nm : Naming N) (pb : String) (p : N) : Op N A → Prop
  | .place _ => True
  | .trans d => p ∉ d.namedPlaces
  | .terminal _ => True
  | .fuse s => p ∉ s.members
  | .compose I ports chans =>
      (∀ e ∈ ports, e.2 ≠ p) ∧ (∀ c ∈ chans, p ∉ c.2.namedPlaces) ∧
      ∀ d ∈ I.defs, p ∈ d.namedPlaces →
        I.pfx = pb ∧ NamedUnder pb d.core.name ∧ ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name
  | .composeAuto I _ =>
      (∀ q ∈ I.iface, q.place ≠ p) ∧ Nm.pre I.pfx p ∉ I.places ∧
      ∀ d ∈ I.defs, p ∈ d.namedPlaces → I.pfx = pb ∧ NamedUnder pb d.core.name
  | .composeDirect S => ∀ d ∈ S.defs, p ∉ d.namedPlaces

/-- **Private place** (ruling D79 (a)). Place `p` is private to the instance under prefix `pb` in
the script `ops` when every call of the script leaves it to that instance: no port binding and no
fusion set names it, and no transition outside the instance names it. -/
def PrivateTo (Nm : Naming N) (pb : String) (ops : List (Op N A)) (p : N) : Prop :=
  ∀ op ∈ ops, OpLeaves Nm pb p op

/-- A channel merge is local: the merged definition carries the caller's name and names only
places the caller-side or the instance-side definition names. -/
def MergeLocal (Mg : MergeFn N A) : Prop :=
  ∀ c i m, Mg c i = .ok m →
    m.core.name = c.core.name ∧ ∀ q ∈ m.namedPlaces, q ∈ c.namedPlaces ∨ q ∈ i.namedPlaces

end Private

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N A : Type}

/-! ## Locality of the reference build script -/

section Locality

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- What the locality proof keeps along a script: every definition that names `p` carries a name
under `pb`, and no fusion set lists `p`. -/
def LocalInv (pb : String) (p : N) (b : Bld N A) : Prop :=
  (∀ d ∈ b.defs, p ∈ d.namedPlaces → NamedUnder pb d.core.name) ∧
    ∀ s ∈ b.fusions, p ∉ s.members

omit [ToString N] in
/-- A merged definition names only places one of the two sides names. -/
theorem mergedDef_namedPlaces_sub {sq : Act A → Act A → Act A} {c i : CDef N A} {tm : Timing}
    {ins : List (NInSpec N)} {corr : Option (List (N × N))}
    (hins : ∀ s ∈ ins, s.place ∈ (c.core.inputs ++ i.core.inputs).map (·.place)) (q : N)
    (hq : q ∈ (mergedDef sq c i tm ins corr).namedPlaces) :
    q ∈ c.namedPlaces ∨ q ∈ i.namedPlaces := by
  have ho := outPlaces_mergeOut c.out i.out
  simp only [TransDef.namedPlaces, mergedDef] at ho hq ⊢
  rw [ho] at hq
  simp only [List.mem_append, mem_unionArcs, List.mem_map] at hq ⊢
  rcases hq with ((((⟨s, hs, rfl⟩ | h) | h) | h) | h)
  · have := hins s hs
    simp only [List.map_append, List.mem_append, List.mem_map] at this
    rcases this with ⟨a, ha, e⟩ | ⟨a, ha, e⟩
    · exact .inl (.inl (.inl (.inl (.inl ⟨a, ha, e⟩))))
    · exact .inr (.inl (.inl (.inl (.inl ⟨a, ha, e⟩))))
  · rcases h with h | h
    · exact .inl (.inl (.inl (.inl (.inr h))))
    · exact .inr (.inl (.inl (.inl (.inr h))))
  · rcases h with h | h
    · exact .inl (.inl (.inl (.inr h)))
    · exact .inr (.inl (.inl (.inr h)))
  · rcases h with h | h
    · exact .inl (.inl (.inr h))
    · exact .inr (.inl (.inr h))
  · rcases h with h | h
    · exact .inl (.inr h)
    · exact .inr (.inr h)

/-- **The reference channel merge is local**: the merged definition carries the caller's name and
names only places one side names. -/
theorem refMerge_local (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) :
    MergeLocal (refMerge Build sq cm) := by
  intro c i m h
  obtain ⟨tm, corr, ins, -, -, -, hi, rfl, -⟩ := refMerge_ok_iff.1 h
  exact ⟨rfl, mergedDef_namedPlaces_sub (sq := sq) (tm := tm) (corr := corr)
    (fun s hs => mergeInputsE_places hi s hs)⟩

omit [ToString N] in
/-- A definition rewritten through a binding that sends no port to `p` names `p` only where the
original does. -/
theorem rewriteDef_names {bm : List (BindEntry N)} {d : CDef N A} {p : N}
    (hb : ∀ e ∈ bm, e.caller ≠ p) (h : p ∈ (rewriteDef bm d).namedPlaces) : p ∈ d.namedPlaces := by
  rw [rewriteDef_namedPlaces] at h
  obtain ⟨q, hq, e⟩ := List.mem_map.1 h
  rcases bindSubst_cases bm q with ⟨e', he', -, hs⟩ | ⟨-, hs⟩
  · rw [hs] at e; exact absurd e (hb e' he')
  · rw [hs] at e; exact e ▸ hq

omit [ToString N] in
/-- **A compose-shaped call keeps the invariant**: the definitions it adds are an instance's,
rewritten through a binding that sends no port to `p` and merged through a local merge with
caller-side definitions that do not name `p`, where an instance definition that names `p` lies
under `pb` and is bound by no channel. -/
theorem localInv_bind {pb : String} {p : N} {b b' : Bld N A} (hM : MergeLocal Mg)
    {I : Instance N A} {bm : List (BindEntry N)} {chans : List (String × CDef N A)}
    {ms : List (CDef N A)} (hb : LocalInv pb p b) (hd : b'.defs = b.defs ++ ms)
    (hf : b'.fusions = b.fusions)
    (h2 : List.Forall₂ (fun d m => mergeStep Mg I chans (rewriteDef bm d) = .ok m) I.defs ms)
    (hbm : ∀ e ∈ bm, e.caller ≠ p) (hch : ∀ c ∈ chans, p ∉ c.2.namedPlaces)
    (hdefs : ∀ d ∈ I.defs, p ∈ d.namedPlaces →
      NamedUnder pb d.core.name ∧ ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name) :
    LocalInv pb p b' := by
  refine ⟨fun m hm hp => ?_, by rw [hf]; exact hb.2⟩
  rw [hd, List.mem_append] at hm
  rcases hm with hm | hm
  · exact hb.1 m hm hp
  obtain ⟨d, hdI, hstep⟩ := forall₂_mem_right h2 m hm
  by_cases hc : ∃ c ∈ chans, I.chan c.1 = some (rewriteDef bm d).core.name
  · obtain ⟨c, hcm, he, hs⟩ := mergeStep_some (Mg := Mg) hc
    rw [hs] at hstep
    obtain ⟨-, hpl⟩ := hM _ _ _ hstep
    rcases hpl p hp with hq | hq
    · exact absurd hq (hch c hcm)
    · exact absurd he ((hdefs d hdI (rewriteDef_names hbm hq)).2 c hcm)
  · rw [mergeStep_none (fun c hcm he => hc ⟨c, hcm, he⟩)] at hstep
    cases hstep
    exact (hdefs d hdI (rewriteDef_names hbm hp)).1

omit [DecidableEq N] [ToString N] in
/-- The callers of a binding are the bound caller places. -/
theorem bindEntries_caller {I : Instance N A} {ports : List (String × N)} {p : N}
    (h : ∀ e ∈ ports, e.2 ≠ p) : ∀ e ∈ bindEntries I ports, e.caller ≠ p := fun _ he =>
  h _ (mem_bindEntries.1 he).1

/-- **Every call that leaves `p` to `pb` keeps the invariant.** -/
theorem step_localInv (hM : MergeLocal Mg) {pb : String} {p : N} {b b' : Bld N A}
    {op : Op N A} (hop : OpLeaves Nm pb p op) (hb : LocalInv pb p b)
    (h : scriptStep Nm tyOf Build Mg b op = .ok b') : LocalInv pb p b' := by
  cases op with
  | place q => cases h; exact hb
  | terminal q => cases h; exact hb
  | trans d =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · cases h
      refine ⟨fun m hm hp => ?_, hb.2⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact hb.1 m hm hp
      · rw [List.mem_singleton] at hm; subst hm; exact absurd hp hop
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', hs', rfl⟩ := except_map_ok_iff.1 h
    obtain ⟨-, -, rfl⟩ := (refDeclFusion_ok_iff tyOf s s').1 hs'
    refine ⟨hb.1, fun s'' hs'' => ?_⟩
    rcases List.mem_append.1 hs'' with h' | h'
    · exact hb.2 s'' h'
    · rw [List.mem_singleton] at h'; subst h'; exact hop
  | compose I ports chans =>
    obtain ⟨hports, hch, hdefs⟩ := hop
    obtain ⟨ms, hd, -, -, -, hf, h2⟩ := refCompose_shape h
    exact localInv_bind hM hb hd hf h2 (bindEntries_caller hports) hch
      (fun d hdI hp => ⟨(hdefs d hdI hp).2.1, (hdefs d hdI hp).2.2⟩)
  | composeAuto I cs =>
    obtain ⟨hif, hinf, hdefs⟩ := hop
    simp only [scriptStep] at h
    unfold refAuto at h
    split at h
    · split at h
      · obtain ⟨-, ms, hms, rfl⟩ := applyBind_ok_iff.1 h
        rw [mapM_except_ok_iff] at hms
        refine localInv_bind (chans := []) hM hb (bindAssemble_defs b ms) rfl
          (List.forall₂_map_left_iff.1 hms) ?_ (by simp)
          (fun d hdI hp => ⟨(hdefs d hdI hp).2, by simp⟩)
        intro e he hc
        simp only [inferEntries, List.mem_filterMap] at he
        obtain ⟨q, -, hq⟩ := he
        split at hq
        · rename_i hin
          cases hq
          exact hinf (hc ▸ hin)
        · cases hq
      · obtain ⟨ms, hd, -, -, -, hf, h2⟩ := refCompose_shape h
        refine localInv_bind hM hb hd hf h2 ?_ (by simp)
          (fun d hdI hp => ⟨(hdefs d hdI hp).2, by simp⟩)
        intro e he hc
        obtain ⟨hx, -⟩ := mem_bindEntries.1 he
        obtain ⟨pt, hpt, he'⟩ := List.mem_map.1 hx
        simp only [Prod.mk.injEq] at he'
        exact hif pt hpt (he'.2.trans hc)
    · cases h
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
      refine ⟨fun m hm hp => ?_, hb.2⟩
      simp only [directAssemble, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hb.1 m hm hp
      · exact absurd hp (hop m hm)

/-- **A script that leaves `p` to `pb` keeps the invariant.** -/
theorem script_localInv (hM : MergeLocal Mg) {pb : String} {p : N} :
    ∀ (ops : List (Op N A)) (b b' : Bld N A), (∀ op ∈ ops, OpLeaves Nm pb p op) →
      LocalInv pb p b → ops.foldlM (scriptStep Nm tyOf Build Mg) b = .ok b' → LocalInv pb p b'
  | [], b, b', _, hb, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | op :: ops, b, b', hops, hb, h => by
    rw [foldlM_except_cons] at h
    cases ha : scriptStep Nm tyOf Build Mg b op with
    | error e => rw [ha] at h; cases h
    | ok b₁ =>
      rw [ha] at h
      exact script_localInv hM ops b₁ b' (fun o ho => hops o (List.mem_cons_of_mem _ ho))
        (step_localInv hM (hops op List.mem_cons_self) hb ha) h

omit [ToString N] in
/-- A place no fusion set lists is the image of itself only. -/
theorem refSubst_eq_self_of {sets : List (FusionSet N)} {p q : N}
    (hp : ∀ s ∈ sets, p ∉ s.members) (h : refSubst sets q = p) : q = p := by
  unfold refSubst at h
  cases ho : fusionOwner sets q with
  | none => rw [ho] at h; exact h
  | some s =>
    rw [ho] at h
    obtain ⟨hs, hq⟩ := fusionOwner_some ho
    have hne : s.members ≠ [] := List.ne_nil_of_mem hq
    exact absurd (h ▸ FusionSet.canonical_mem hne q) (hp s hs)

/-- **Build keeps the invariant**: a definition of the fused net that names `p` carries a name
under `pb`, when no fusion set lists `p`. -/
theorem fuseStage_localInv {pb : String} {p : N} {b : Bld N A} {X : FuseNet N A}
    (hb : LocalInv pb p b) (h : fuseStage Build b = .ok X) :
    ∀ d ∈ X.defs, p ∈ d.namedPlaces → NamedUnder pb d.core.name := by
  by_cases hf : b.fusions = []
  · rw [fuseStage_nil hf] at h; cases h; exact hb.1
  · rw [fuseStage_cons hf] at h
    obtain ⟨-, hmap, -, -⟩ := refFuse_ok_iff.1 h
    rw [mapM_except_ok_iff] at hmap
    intro d' hd' hp
    obtain ⟨d, hd, hfd⟩ := forall₂_mem_right hmap d' hd'
    obtain ⟨q, hq, e⟩ := fuseDef_namedPlaces hfd p hp
    have hqp := refSubst_eq_self_of hb.2 e.symm
    rw [(fuseDef_kept hfd).1]
    exact hb.1 d hd (hqp ▸ hq)

/-- **The locality of the reference build script** ([MOD-012] line 1): in a net the script builds,
a transition that names a place private to the instance under `pb` carries a name under `pb`. -/
theorem buildScript_local (hM : MergeLocal Mg) {ops : List (Op N A)} {c : ComposedNet N A}
    (h : buildScript Nm tyOf Build Mg ops = .ok c) {pb : String} {p : N}
    (hp : PrivateTo Nm pb ops p) : ∀ t ∈ c.trans, p ∈ t.namedPlaces → NamedUnder pb t.core.name := by
  obtain ⟨b, hb, hfin⟩ := buildScript_ok_iff.1 h
  have h0 : LocalInv pb p (Bld.empty : Bld N A) := by
    refine ⟨?_, ?_⟩ <;> intro _ h <;> cases h
  have hinv := script_localInv hM ops Bld.empty b hp h0 hb
  obtain ⟨X, hX, htr, -⟩ := finish_trans hfin
  intro t ht hpt
  rw [htr] at ht
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht
  exact fuseStage_localInv hinv hX d hd hpt

end Locality

/-! ## The reference build keeps a private place in its own slot -/

section Keeping

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

omit [ToString N] in
/-- Inserting an input arc keeps the inserted arc's place and every place the list held. -/
theorem insertInE_keeps :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N) (acc' : List (NInSpec N)),
      insertInE acc s = .ok acc' →
        s.place ∈ acc'.map (·.place) ∧ ∀ q ∈ acc.map (·.place), q ∈ acc'.map (·.place)
  | [], s, acc', h => by
    simp only [insertInE, Except.ok.injEq] at h
    subst h
    simp
  | a :: rest, s, acc', h => by
    unfold insertInE at h
    split at h
    · rename_i he
      split at h
      · cases h
        refine ⟨by simp [he], fun q hq => ?_⟩
        simpa using hq
      · cases h
    · obtain ⟨r, hr, rfl⟩ := except_map_ok_iff.1 h
      obtain ⟨h1, h2⟩ := insertInE_keeps rest s r hr
      refine ⟨List.mem_cons_of_mem _ h1, fun q hq => ?_⟩
      simp only [List.map_cons, List.mem_cons] at hq ⊢
      rcases hq with hq | hq
      · exact Or.inl hq
      · exact Or.inr (h2 q hq)

omit [ToString N] in
/-- **Merging input arcs drops no place**: every place of the list and of the inserted arcs is a
place of the merged arcs. -/
theorem foldlM_insertInE_keeps :
    ∀ (xs acc ys : List (NInSpec N)), xs.foldlM insertInE acc = .ok ys →
      ∀ q ∈ acc.map (·.place) ++ xs.map (·.place), q ∈ ys.map (·.place)
  | [], acc, ys, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | x :: xs, acc, ys, h => by
    rw [List.foldlM_cons] at h
    cases hx : insertInE acc x with
    | error e => rw [hx] at h; cases h
    | ok acc' =>
      rw [hx] at h
      simp only [bind, Except.bind] at h
      obtain ⟨h1, h2⟩ := insertInE_keeps acc x acc' hx
      intro q hq
      refine foldlM_insertInE_keeps xs acc' ys h q ?_
      simp only [List.mem_append, List.map_cons, List.mem_cons] at hq ⊢
      rcases hq with hq | rfl | hq
      · exact Or.inl (h2 q hq)
      · exact Or.inl h1
      · exact Or.inr hq

omit [ToString N] in
/-- **A fusion keeps a place it does not move**: a place the original definition names and the
substitution fixes is a place the rewritten definition names. -/
theorem fuseDef_keeps_fixed {σ : N → N} {d d' : CDef N A} (h : fuseDef σ d = .ok d') {p : N}
    (hσ : σ p = p) (hp : p ∈ d.namedPlaces) : p ∈ d'.namedPlaces := by
  obtain ⟨-, hinh, hrd, hrs, hout, -⟩ := fuseDef_kept h
  simp only [TransDef.namedPlaces, List.mem_append] at hp ⊢
  rcases hp with (((hq | hq) | hq) | hq) | hq
  · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hq
    have hm : s.place ∈ d.core.inputs.map (fun s => (mapIn σ s).place) :=
      List.mem_map.2 ⟨s, hs, by simp [mapIn, hσ]⟩
    rcases fuseDef_inputs h with ⟨-, he⟩ | ⟨-, he⟩
    · rw [he, List.map_map]; exact hm
    · unfold mergeInputsE at he
      refine foldlM_insertInE_keeps _ [] _ he s.place ?_
      simpa [List.map_map, Function.comp_def] using hm
  · rw [hinh]; exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨p, hq, hσ⟩))))
  · rw [hrd]; exact Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨p, hq, hσ⟩)))
  · rw [hrs]; exact Or.inl (Or.inr (List.mem_map.2 ⟨p, hq, hσ⟩))
  · refine Or.inr ?_
    rw [hout]
    cases ho : d.out with
    | none => rw [ho] at hq; simp at hq
    | some o =>
      rw [ho] at hq
      simp only [Option.map_some, Option.getD_some, outPlaces_mapOut] at hq ⊢
      exact List.mem_map.2 ⟨p, hq, hσ⟩

/-- Every call keeps the definitions the builder already holds. -/
theorem step_defs_keep {b b' : Bld N A} {op : Op N A}
    (h : scriptStep Nm tyOf Build Mg b op = .ok b') : ∀ m ∈ b.defs, m ∈ b'.defs := by
  intro m hm
  cases op with
  | place q => cases h; exact hm
  | terminal q => cases h; exact hm
  | trans d =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · cases h; exact List.mem_append_left _ hm
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', -, rfl⟩ := except_map_ok_iff.1 h
    exact hm
  | compose I ports chans =>
    obtain ⟨ms, hd, -⟩ := refCompose_shape h
    rw [hd]; exact List.mem_append_left _ hm
  | composeAuto I cs =>
    simp only [scriptStep] at h
    unfold refAuto at h
    split at h
    · split at h
      · obtain ⟨-, ms, -, rfl⟩ := applyBind_ok_iff.1 h
        rw [bindAssemble_defs]; exact List.mem_append_left _ hm
      · obtain ⟨ms, hd, -⟩ := refCompose_shape h
        rw [hd]; exact List.mem_append_left _ hm
    · cases h
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
      exact List.mem_append_left _ hm

/-- Every script keeps the definitions the builder already holds. -/
theorem script_defs_keep :
    ∀ (ops : List (Op N A)) (b b' : Bld N A), ops.foldlM (scriptStep Nm tyOf Build Mg) b = .ok b' →
      ∀ m ∈ b.defs, m ∈ b'.defs
  | [], b, b', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ fun _ hm => hm
  | op :: ops, b, b', h => by
    rw [foldlM_except_cons] at h
    cases ha : scriptStep Nm tyOf Build Mg b op with
    | error e => rw [ha] at h; cases h
    | ok b₁ =>
      rw [ha] at h
      exact fun m hm => script_defs_keep ops b₁ b' h m (step_defs_keep ha m hm)

/-- **A compose call adds a definition that names a place no binding sends elsewhere as it
is**: the call's rewrite leaves the place, and no channel merges the definition. -/
theorem compose_adds {b b' : Bld N A} {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {p : N}
    (h : scriptStep Nm tyOf Build Mg b (.compose I ports chans) = .ok b')
    (hport : ∀ e ∈ ports, I.port e.1 ≠ some p) {d : CDef N A} (hd : d ∈ I.defs)
    (hp : p ∈ d.namedPlaces) (hch : ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name) :
    ∃ m ∈ b'.defs, m.core.name = d.core.name ∧ p ∈ m.namedPlaces := by
  obtain ⟨ms, hdefs, -, -, -, -, h2⟩ := refCompose_shape h
  obtain ⟨m, hm, hstep⟩ := forall₂_mem_left h2 d hd
  rw [mergeStep_none (d := rewriteDef (bindEntries I ports) d) hch] at hstep
  cases hstep
  refine ⟨rewriteDef (bindEntries I ports) d, hdefs ▸ List.mem_append_right _ hm, rfl, ?_⟩
  rw [rewriteDef_namedPlaces]
  refine List.mem_map.2 ⟨p, hp, bindSubst_of_none fun e he hep => ?_⟩
  obtain ⟨hx, hq⟩ := mem_bindEntries.1 he
  exact hport _ hx (hep ▸ hq)

/-- A script that holds the compose call ends with a definition of the call's name that names the
place. -/
theorem script_compose_adds {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} {p : N} (hport : ∀ e ∈ ports, I.port e.1 ≠ some p)
    {d : CDef N A} (hd : d ∈ I.defs) (hp : p ∈ d.namedPlaces)
    (hch : ∀ c ∈ chans, I.chan c.1 ≠ some d.core.name) :
    ∀ (ops : List (Op N A)) (b b' : Bld N A), Op.compose I ports chans ∈ ops →
      ops.foldlM (scriptStep Nm tyOf Build Mg) b = .ok b' →
        ∃ m ∈ b'.defs, m.core.name = d.core.name ∧ p ∈ m.namedPlaces
  | [], _, _, hmem, _ => by cases hmem
  | op :: ops, b, b', hmem, h => by
    rw [foldlM_except_cons] at h
    cases ha : scriptStep Nm tyOf Build Mg b op with
    | error e => rw [ha] at h; cases h
    | ok b₁ =>
      rw [ha] at h
      rcases List.mem_cons.1 hmem with rfl | hmem
      · obtain ⟨m, hm, hn, hpm⟩ := compose_adds ha hport hd hp hch
        exact ⟨m, script_defs_keep ops b₁ b' h m hm, hn, hpm⟩
      · exact script_compose_adds hport hd hp hch ops b₁ b' hmem h

/-- The fusion stage of `build()` keeps a definition's name, and a place no fusion set lists. -/
theorem fuseStage_keeps {b : Bld N A} {X : FuseNet N A} (h : fuseStage Build b = .ok X) {p : N}
    (hf : ∀ s ∈ b.fusions, p ∉ s.members) {m : CDef N A} (hm : m ∈ b.defs)
    (hp : p ∈ m.namedPlaces) : ∃ m' ∈ X.defs, m'.core.name = m.core.name ∧ p ∈ m'.namedPlaces := by
  by_cases hf0 : b.fusions = []
  · rw [fuseStage_nil hf0] at h; cases h; exact ⟨m, hm, rfl, hp⟩
  · rw [fuseStage_cons hf0] at h
    obtain ⟨-, hmap, -, -⟩ := refFuse_ok_iff.1 h
    rw [mapM_except_ok_iff] at hmap
    obtain ⟨m', hm', hfd⟩ := forall₂_mem_left hmap m hm
    have hσ : refSubst b.fusions p = p := by
      unfold refSubst; rw [fusionOwner_eq_none_iff.2 hf]
    exact ⟨m', hm', (fuseDef_kept hfd).1, fuseDef_keeps_fixed hfd hσ hp⟩

/-- **The reference build keeps a private place** ([MOD-012] line 3): when a compose call of the
script adds an instance definition that names a place private to the instance and not bound as a
port of that call, the built net holds a transition of that definition's name that still names the
place. -/
theorem buildScript_keeps (hM : MergeLocal Mg) {ops : List (Op N A)} {c : ComposedNet N A}
    (h : buildScript Nm tyOf Build Mg ops = .ok c) {pb : String} {p : N}
    (hp : PrivateTo Nm pb ops p) {I : Instance N A} {ports : List (String × N)}
    {chans : List (String × CDef N A)} (hmem : Op.compose I ports chans ∈ ops)
    (hport : ∀ e ∈ ports, I.port e.1 ≠ some p) {d : CDef N A} (hd : d ∈ I.defs)
    (hpd : p ∈ d.namedPlaces) :
    ∃ t ∈ c.trans, t.core.name = d.core.name ∧ p ∈ t.namedPlaces := by
  obtain ⟨b, hb, hfin⟩ := buildScript_ok_iff.1 h
  have hop := hp _ hmem
  obtain ⟨-, -, hdefs⟩ := hop
  obtain ⟨m, hm, hn, hpm⟩ :=
    script_compose_adds (Nm := Nm) (tyOf := tyOf) (Build := Build) (Mg := Mg) hport hd hpd
      (hdefs d hd hpd).2.2 ops Bld.empty b hmem hb
  have h0 : LocalInv pb p (Bld.empty : Bld N A) := by
    refine ⟨?_, ?_⟩ <;> intro _ h <;> cases h
  have hinv := script_localInv hM ops Bld.empty b hp h0 hb
  obtain ⟨X, hX, htr, -⟩ := finish_trans hfin
  obtain ⟨m', hm', hn', hpm'⟩ := fuseStage_keeps hX hinv.2 hm hpm
  exact ⟨m'.toTransDef, htr ▸ List.mem_map_of_mem hm', hn'.trans hn, hpm'⟩

end Keeping

/-! ## Frames of a firing and of the timed step -/

section Frames

variable [DecidableEq N]

omit [DecidableEq N] in
/-- A place a definition does not name carries none of its arcs and is not an output place. -/
theorem not_named_arcs {t : TransDef N A} {p : N} (hp : p ∉ t.namedPlaces) :
    p ∉ inPlaces t.toTrans ∧ ¬ ResetArc t.toTrans p ∧ ¬ OutputArc t.toTrans p ∧
      ¬ ReadArc t.toTrans p ∧ ¬ InhibitorArc t.toTrans p := by
  rw [mem_namedPlaces] at hp
  tauto

/-- No input arc of `t` is on a place `t` does not name. -/
theorem nspecAt_not_named {t : TransDef N A} {p : N} (hp : p ∉ t.namedPlaces) :
    nspecAt t.toTrans.core p = none := by
  obtain ⟨hin, -⟩ := not_named_arcs hp
  unfold nspecAt
  rw [List.find?_eq_none]
  intro s hs he
  exact hin (List.mem_map.2 ⟨s, hs, by simpa using he⟩)

/-- **A firing leaves every place its transition does not name**, and deposits nothing there. -/
theorem refFire_frame {t : TransDef N A} {p : N} (hp : p ∉ t.namedPlaces) {m m' : N → Nat}
    {d : List N} (h : RefFire t.toTrans m d m') : m' p = m p ∧ p ∉ d := by
  obtain ⟨-, hres, hout, -, -⟩ := not_named_arcs hp
  have hd : p ∉ d := fun hd => hout (refFire_outputs h p hd)
  refine ⟨?_, hd⟩
  rw [refFire_apply h p, if_neg hres]
  simp [Consumes, nconsumed, nspecAt_not_named hp, Deposits, depProd, List.count_eq_zero.2 hd]

/-- The intermediate marking of a firing holds every place the transition does not name as it
was. -/
theorem mid_frame {t : TransDef N A} {p : N} (hp : p ∉ t.namedPlaces) (m : N → Nat) :
    Mid t.toTrans m p = m p := by
  obtain ⟨-, hres, -⟩ := not_named_arcs hp
  simp [Mid, hres, Consumes, nconsumed, nspecAt_not_named hp]

omit [DecidableEq N] in
/-- `all` over a list reads its predicate on the list's elements only. -/
theorem mod012_all_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [DecidableEq N] in
/-- **Enablement is local**: two markings that agree on a transition's arc places enable it
alike. -/
theorem enabled_congr_arc {u : Trans N} {m₁ m₂ : N → Nat}
    (h : ∀ q, ArcPlace u q → m₁ q = m₂ q) : Enabled u m₁ ↔ Enabled u m₂ := by
  have e : enabledNA m₁ u.core = enabledNA m₂ u.core := by
    unfold enabledNA
    rw [mod012_all_congr (l := u.core.inputs) (g := fun s => decide (s.card.required ≤ m₂ s.place))
        (fun s hs => by rw [h s.place (Or.inl (List.mem_map_of_mem hs))]),
      mod012_all_congr (l := u.core.inhibitors) (g := fun q => m₂ q == 0)
        (fun q hq => by rw [h q (Or.inr (Or.inr (Or.inl hq)))]),
      mod012_all_congr (l := u.core.reads) (g := fun q => decide (1 ≤ m₂ q))
        (fun q hq => by rw [h q (Or.inr (Or.inl hq))])]
  simp only [Enabled, e]

/-- **The clock frame of a foreign firing** (reference step): a firing of `t` that names none of
`u`'s arc places, `u` the net's transition of its name and named differently from `t`, leaves `u`
enabled as before, armed as before and, when armed, with its stamp. -/
theorem refTStep_fire_frame {X : TimedNet N} {s s' : TSt N} {t : TransDef N A} {u : Trans N}
    {d : List N} (h : RefTStep X s (.fire t.toTrans d) s') (hu : InNet X u)
    (hne : t.core.name ≠ u.core.name) (hloc : ∀ q, ArcPlace u q → q ∉ t.namedPlaces) :
    (Enabled u s'.m ↔ Enabled u s.m) ∧ (Armed s' u ↔ Armed s u) ∧
      (Armed s u → s'.stamp u.core.name = s.stamp u.core.name) := by
  obtain ⟨-, hf, -, -, -, he⟩ := refTStepW_fire_inv h
  have hen : Enabled u s'.m ↔ Enabled u s.m :=
    enabled_congr_arc fun q hq => (refFire_frame (hloc q hq) hf).1
  have hmid : Enabled u (Mid t.toTrans s.m) ↔ Enabled u s.m :=
    enabled_congr_arc fun q hq => mid_frame (hloc q hq) s.m
  have hw : writesArc t.toTrans d u = false := by
    rw [Bool.eq_false_iff]
    intro hw
    obtain ⟨q, hq, hwq⟩ := (writesArc_iff _ _ _).1 hw
    have hn := hloc q hq
    obtain ⟨hin, hres, -⟩ := not_named_arcs hn
    rcases hwq with h1 | h1 | h1
    · exact hin h1
    · exact hres h1
    · exact (refFire_frame hn hf).2 h1
  have hst : s'.stamp u.core.name = restampW refPolicy X s t.toTrans d s'.m u := by
    rw [he]
    exact restampAll_inNet hu _ _ _ _
  refine ⟨hen, ?_, fun ha => ?_⟩
  · by_cases ha : Armed s u
    · have hk : (refPolicy (N := N)).keep X s t.toTrans d s'.m u = true := by
        simp only [refPolicy, Bool.and_eq_true]
        refine ⟨⟨⟨(armed_iff s u).1 ha, by simpa [TransDef.toTrans] using Ne.symm hne⟩, ?_⟩, hen.2 ha.1⟩
        rw [← mid_eq]
        exact hmid.2 ha.1
      have hs : s'.stamp u.core.name = s.stamp u.core.name := by
        rw [hst]; unfold restampW; rw [if_pos hk]
      refine iff_of_true ⟨hen.2 ha.1, ?_⟩ ha
      rw [hs]; exact ha.2
    · have hna : s.armed u = false := by
        rw [Bool.eq_false_iff]; exact fun h' => ha ((armed_iff s u).2 h')
      have hk : (refPolicy (N := N)).keep X s t.toTrans d s'.m u = false := by
        simp [refPolicy, hna]
      have hr : (refPolicy (N := N)).rearm X s t.toTrans d s'.m u = false := by
        simp [refPolicy, hna, hw]
      have hs : s'.stamp u.core.name = none := by
        rw [hst]; unfold restampW; rw [if_neg (by simp [hk]), if_neg (by simp [hr])]
      refine iff_of_false (fun h' => ?_) ha
      have := h'.2
      rw [hs] at this
      exact absurd this (by simp)
  · have hk : (refPolicy (N := N)).keep X s t.toTrans d s'.m u = true := by
      simp only [refPolicy, Bool.and_eq_true]
      refine ⟨⟨⟨(armed_iff s u).1 ha, by simpa [TransDef.toTrans] using Ne.symm hne⟩, ?_⟩, hen.2 ha.1⟩
      rw [← mid_eq]
      exact hmid.2 ha.1
    rw [hst]; unfold restampW; rw [if_pos hk]

/-- **A reap of another transition or a delay**, under any policy, leaves `u` armed as before and
its stamp as it was. -/
theorem refTStepW_reapDelay_frame {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t u : Trans N}
    (hne : t.core.name ≠ u.core.name)
    (h : RefTStepW P X s (.reap t) s' ∨ ∃ δ, RefTStepW P X s (.delay δ) s') :
    (Armed s' u ↔ Armed s u) ∧ s'.stamp u.core.name = s.stamp u.core.name := by
  rcases h with h | ⟨δ, h⟩
  · have hm := refTStepW_marking h (fun _ _ e => nomatch e)
    have hs := frame_reapOther h (Ne.symm hne)
    exact ⟨by unfold Armed Enabled; rw [hm, hs], hs⟩
  · have hm := refTStepW_marking h (fun _ _ e => nomatch e)
    have hs := frame_delay h u.core.name
    exact ⟨by unfold Armed Enabled; rw [hm, hs], hs⟩

end Frames

/-! ## A script of bare compose calls -/

section ComposeNil

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

omit [ToString N] [DecidableEq T] [ToString T] in
/-- A compose call with no binding adds the instance's definitions as they are. -/
theorem rewriteDef_nil_toTransDef (I : Instance N A) (d : CDef N A) :
    (rewriteDef (bindEntries I ([] : List (String × N))) d).toTransDef = d.toTransDef := by
  have hs : bindSubst ([] : List (BindEntry N)) = id := funext fun _ => rfl
  show (d.map (bindSubst []) id).toTransDef = _
  rw [hs, CDef.map_id_toTransDef]

omit [DecidableEq N] [ToString N] [DecidableEq T] [ToString T] in
/-- Related lists whose related elements agree under `f` agree under `f`. -/
theorem mod012_forall₂_map {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b → g b = f a) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l'.map g = l.map f
  | _, _, .nil => rfl
  | _, _, .cons hab hrest => by
    simp only [List.map_cons, hR _ _ hab, mod012_forall₂_map hR hrest]

/-- **A script of compose calls with no binding** adds every instance's definitions, in order,
and declares no fusion set. -/
theorem script_composeNil :
    ∀ (Is : List (Instance N A)) (b b' : Bld N A),
      (Is.map fun I => (Op.compose I [] [] : Op N A)).foldlM (scriptStep Nm tyOf Build Mg) b = .ok b' →
      b'.defs.map (·.toTransDef) =
          b.defs.map (·.toTransDef) ++ (Is.flatMap (·.defs)).map (·.toTransDef) ∧
        b'.fusions = b.fusions
  | [], b, b', h => by
    simp only [List.map_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | I :: Is, b, b', h => by
    rw [List.map_cons, foldlM_except_cons] at h
    cases ha : scriptStep Nm tyOf Build Mg b (.compose I [] []) with
    | error e => rw [ha] at h; cases h
    | ok b₁ =>
      rw [ha] at h
      obtain ⟨ms, hd, -, -, -, hf, h2⟩ := refCompose_shape (tyOf := tyOf) (Build := Build)
        (Mg := Mg) (b := b) (I := I) (ports := []) (chans := []) ha
      obtain ⟨ih1, ih2⟩ := script_composeNil Is b₁ b' h
      have hms : ms.map (·.toTransDef) = I.defs.map (·.toTransDef) := by
        refine mod012_forall₂_map (fun d m hm => ?_) h2
        rw [mergeStep_none (chans := []) (fun _ hc => by cases hc)] at hm
        cases hm
        exact rewriteDef_nil_toTransDef I d
      refine ⟨?_, ih2.trans hf⟩
      rw [ih1, hd, List.map_append, hms, List.flatMap_cons, List.map_append, List.append_assoc]

/-- **What a script of compose calls with no binding builds**: the instances' definitions, in
order. -/
theorem buildScript_composeNil (Is : List (Instance N A)) {c : ComposedNet N A}
    (h : buildScript Nm tyOf Build Mg (Is.map fun I => .compose I [] []) = .ok c) :
    c.trans = (Is.flatMap (·.defs)).map (·.toTransDef) := by
  obtain ⟨b, hb, hfin⟩ := buildScript_ok_iff.1 h
  obtain ⟨hd, hf⟩ := script_composeNil Is Bld.empty b hb
  obtain ⟨X, hX, htr, -⟩ := finish_trans hfin
  rw [fuseStage_nil (hf.trans rfl)] at hX
  cases hX
  rw [htr]
  simpa [Bld.empty] using hd

end ComposeNil

end Libpetri.Reference

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## MOD-012: Per-Instance State Isolation -/

requirement MOD_012
  id "MOD-012"
  title "Per-Instance State Isolation"
  kind B
  scope "every net built by composition"
  source verbatim "spec/11-modular-composition.md"
  quote "A place of an instance is **private** to it when no port binding names it, as the caller place or as the port place the binding replaces ([MOD-020]), no fusion set lists it ([MOD-060]), no transition of the instance that a channel binding merges names it ([MOD-021]), and no transition outside the instance names it: no hand-added transition, no caller-side definition of a channel binding, no transition of another instance and no directly composed subnet ([MOD-025])."
        "An auto-composition ([MOD-024]) of an instance under prefix `q` counts as binding a place `x` when `x` is the unrenamed place of one of that instance's ports or when `q/x` is a place of that instance, whether or not the call binds it."
        "Port bindings, channels and fusion sets are how instances share state on purpose, so isolation covers private places only."
        "After composition into a flat net, private places of two distinct instances MUST occupy distinct slots in the compiled net's place index, hold disjoint token bags, and evolve independently under the executor."
        "This isolation is a structural consequence of name-prefixing per [MOD-010] (distinct prefixed names → distinct place identities → distinct slots)."
        "No additional runtime mechanism is required."
        "In the sentences below, `a` and `b` are single-segment prefixes: non-empty and without `/` ([MOD-010])."
        "For two instances nested in one outer instance ([MOD-013]), the sentences apply to the build of the outer subnet's body, where their prefixes are single segments."
        "*When* a net is built by composition, each of its transitions that names a place private to the instance under prefix `b` *shall* have a name of the form `b/x`."
        "*When* a transition whose name has the form `a/x` fires in a net built by composition, every place private to the instance under another prefix `b` *shall* keep its token count."
        "*When* a `compose(instance, bindings)` call ([MOD-020]) adds a transition of the instance under prefix `b` that names a place private to that instance, the built net *shall* hold a transition of the same name that names that place."
  reading "For every naming model Nm, build-script function BS (a script of calls on an enclosing builder gives the composed net build() returns, or a rejection) and firing relation F:"
          "if BS builds the net c from the script ops and the place p is private to the instance under prefix pb in ops (PrivateTo Nm pb ops p: every call of ops leaves p to that instance), then every transition of c that names p (an input, inhibitor, read, reset or output place) has a name pb/x;"
          "if BS builds c from ops, pa and pb are valid and different prefixes, p is private to the instance under pb in ops and t is a transition of c named pa/x, then every firing of t under F leaves the token count of p as it was;"
          "if BS builds c from ops, p is private to the instance under pb in ops, ops holds the call compose I ports chans, no port binding of that call names p as the instance's port place (I.port of no bound port name is p), and d is a definition of I that names p, then c holds a transition with d's name that names p."
  assumes "Ruling D79 (a): isolation covers private places only. PrivateTo reads privacy off the script of calls, before build, one call at a time (OpLeaves): a hand-added transition does not name the place; a fusion set does not list it; a compose call binds no port to it as the caller place, its caller-side channel definitions do not name it, and an instance definition that names it belongs to an instance under pb, is named pb/x and is bound by no channel; an auto-composition binds no port to it as the caller place, through the interface or by inference (the markdown's sentence on auto-composition: the place is not the unrenamed place of an interface port, and its renamed copy is not a place of the instance, whether or not the inference runs); a directly composed body does not name it. Auto-composition with channels is rejected (MOD-024), so it has no channel clause. These are the sharing paths the runtimes offer: a compose call takes any caller place (rust/libpetri-core/src/petri_net.rs:1050-1069), fusion sets list places of the composed net by name (MOD-060), a channel merge gives the caller's transition the instance transition's arcs (MOD-021), and direct composition is unrenamed (MOD-025). A hand-added transition named pb/x counts as outside the instance."
          "PrivateTo is broader than the markdown definition in two ways, both harmless. It has no membership condition: a place no call names is private to every prefix, which only widens lines 1 and 2 (safety lines), while line 3 asks for a definition of the instance that names the place. And it does not exclude the instance's own bound port places, which a compose call replaces by their caller places (MOD-020 item 2, retired per MOD-027) so that no transition names them after build: lines 1 and 2 hold of them vacuously, and line 3 states the exclusion as its premise. The condition that an instance definition naming the place is named pb/x holds for every instance made by instantiate (MOD-010 AC1); for an abstract Instance it is part of being the instance's transition."
          "A transition of the instance under a is a transition of the flat net whose name has the form a/x (transitions are identified by name, rulings D10 and D23); a channel-merged transition carries the caller's name (MOD-021 clause 5) and belongs to the caller. The prefixes are valid, that is single segments (MOD-010 line 1: instantiate refuses any other), and two valid and different prefixes never give one name (preS_inj), which is what line 2 uses. Two sibling instances nested in one outer instance lie under one valid prefix of the flat net, so line 2 and the clock block say nothing between them there; the markdown sends them to the build of the outer subnet's body, where their prefixes are single segments and both blocks apply. Line 1 does not need the place to be named pb/y: for instances made by instantiate it is (MOD-010 AC1), and another instance's definitions never name it (mod012_inst_leaves)."
          "'Distinct slots in the compiled net's place index' and 'hold disjoint token bags' are line 3 with MOD-010 AC2: the build merges no private place into another place, since a definition of the instance that names its private place still names it, under its own name, in the built net (buildScript_keeps: a compose call adds the definition through its binding, which leaves the place, no channel merges it, and fusion moves only listed places); two instances under different prefixes share no place name (mod010_disjoint), and the place index is keyed by place identity (Novel.Seam.PlaceIndex.idx_inj). Line 3 covers compose(instance, bindings) calls; the definitions an auto-composition adds are bound by inference against the builder's places at the time of the call, which the call alone does not show, so they are not covered here. 'No additional runtime mechanism is required' is the holds theorem: the plain reference firing relation RefFire and the reference build script satisfy all three lines (MOD_012_reference, and mod012_buildScript for every transition check and every channel merge that names only its two sides' places)."
          "'Evolve independently under the executor' is read as non-interference of the marking (line 2), and of enablement and clocks (the companion block MOD_012_clock). The order in which a firing pass picks ready transitions (EXEC-002; ruling D14: the all-immediate fast path is not preserved by composition), actions shared by reference between instances (MOD-010 item 5, MOD-030), a blocking Java action that stalls the whole net, and per-instance ν name pools (NU-030) are not part of this block. Tokens injected through environment places are ENV's (ENV-003)."
          "AC1 (tokens added to instance A's private place do not appear in instance B's corresponding private place): tokens a firing of A's transitions adds are line 2 (MOD_012_nonvacuous fires a/work and leaves b/IN as it was); tokens the caller adds to the initial marking land in one named place, and A's and B's places have different names (MOD-010 AC2) that the build keeps (line 3). AC4 (a fusion with a place of a third instance C leaves each transition of A and B naming its own private place) is line 3 (MOD_012_mutant_noKeep_killed: a fusion keyed by local names also fuses a/IN and b/IN into the caller place). AC2 and AC3 are the companion block MOD_012_clock."
  signoff "pending"
  statement : ∀ {N A : Type}, Naming N → ScriptFn N A → FireRel N → Prop :=
    fun {N A} Nm BS F =>
      (∀ (ops : List (Op N A)) c pb p, BS ops = .ok c → PrivateTo Nm pb ops p →
        ∀ t ∈ c.trans, p ∈ t.namedPlaces → NamedUnder pb t.core.name) ∧
      (∀ (ops : List (Op N A)) c pa pb p, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
        pa ≠ pb → PrivateTo Nm pb ops p → ∀ t ∈ c.trans, NamedUnder pa t.core.name →
          on (fun m m' => Fire F t.toTrans m m'), shall (fun m m' => m' p = m p)) ∧
      (∀ (ops : List (Op N A)) c pb p I ports chans, BS ops = .ok c → PrivateTo Nm pb ops p →
        Op.compose I ports chans ∈ ops → (∀ e ∈ ports, I.port e.1 ≠ some p) →
        ∀ d ∈ I.defs, p ∈ d.namedPlaces →
          ∃ t ∈ c.trans, t.core.name = d.core.name ∧ p ∈ t.namedPlaces)

/- The pinned readable form of MOD-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_012 : {N A : Type} → Naming N → ScriptFn N A → FireRel N → Prop :=
fun {N A} Nm BS F =>
  (∀ (ops : List (Op N A)) (c : ComposedNet N A) (pb : String) (p : N),
      BS ops = Except.ok c → PrivateTo Nm pb ops p → ∀ t ∈ c.trans, p ∈ t.namedPlaces → NamedUnder pb t.core.name) ∧
    (∀ (ops : List (Op N A)) (c : ComposedNet N A) (pa pb : String) (p : N),
        BS ops = Except.ok c →
          ValidPrefix pa →
            ValidPrefix pb →
              pa ≠ pb →
                PrivateTo Nm pb ops p →
                  ∀ t ∈ c.trans,
                    NamedUnder pa t.core.name → on fun m m' => Fire F t.toTrans m m', shall fun m m' => m' p = m p) ∧
      ∀ (ops : List (Op N A)) (c : ComposedNet N A) (pb : String) (p : N) (I : Instance N A) (ports : List (String × N))
        (chans : List (String × CDef N A)),
        BS ops = Except.ok c →
          PrivateTo Nm pb ops p →
            Op.compose I ports chans ∈ ops →
              (∀ e ∈ ports, I.port e.1 ≠ some p) →
                ∀ d ∈ I.defs, p ∈ d.namedPlaces → ∃ t ∈ c.trans, t.core.name = d.core.name ∧ p ∈ t.namedPlaces
-/
#guard_msgs in #print MOD_012

requirement MOD_012_clock
  id "MOD-012"
  title "Per-Instance State Isolation (clocks)"
  kind T
  scope "every net built by composition"
  source verbatim "spec/11-modular-composition.md"
  quote "Private place token state, the enablement state of a transition whose arc places are all private, and the timing clock of such a transition (per [TIME-010], [TIME-011]) MUST all be per-instance."
        "*When* a transition whose name has the form `a/x` fires in a net built by composition, each transition named `b/y`, for another prefix `b`, whose arc places are all private to the instance under `b` *shall* keep its enablement and its armed state, and its stamp if it is armed."
        "*When* a transition whose name has the form `a/x` is reaped, or the firing clock advances in a net that holds such a transition, each transition named `b/y`, for another prefix `b`, *shall* keep its armed state and its stamp."
  reading "For every naming model Nm, build-script function BS and timed step relation R, when BS builds the net c from the script ops, pa and pb are valid and different prefixes, t is a transition of c named pa/x and the timed net is c with deadline tolerance tol:"
          "for every transition u of the timed net that is the net's transition of its name (InNet), is named pb/y and has all its arc places private to the instance under pb in ops, every firing of t leaves u enabled exactly when it was, armed exactly when it was and, when it was armed, with its stamp;"
          "for every transition u named pb/y, every reap of t and every delay leaves u armed exactly when it was and with the stamp it held."
  assumes "A step of R relates two states of the timed executor, each holding a marking, the reading of the firing clock and a stamp per transition name (TSt); a step is a delay, a firing or a reap (TRel, the Phase 1 timed step whose witness is RefTStep). 'Timing clock' is the stamp of TIME-010, Armed and Enabled are the glossary terms; 'enablement state' is Enabled at the marking. The composed net is run as BuiltNet.toTimed: the transitions of the built net, each with the timing of its definition."
          "Transitions are identified by name (ruling D10): u is the net's transition of its name (InNet), which holds of every transition when the names are distinct (NamesDistinct, inNet_iff_mem). Neither builder checks transition names (composition design, skeptic S8), so the premise is stated, not proved; t and u carry different names because they lie under different valid prefixes."
          "Line 1 needs every arc place of u (input, read, inhibitor, reset) private: u's enablement reads only those places, and the firing of t writes none of them (line 1 of MOD_012), so no firing of t restarts u's clock through TIME-012. A transition of b with an arc on a bound caller place or a fused place may be disabled or restarted by a's firing, as it shares that place on purpose. A transition armed with a stale stamp while disabled is not a reachable state of RefTStep and is not claimed: line 1 keeps the stamp of an armed u only."
          "Line 2 needs no privacy: a reap removes only the reaped transition's stamp (TIME-013) and a delay keeps every stamp (TIME-010); together with line 1 the clocks of b's transitions never depend on a's steps. Under a delay the clocks of all transitions advance together, so 'independent' means that no step of a changes a stamp of b."
          "Line 2 is stated for a net that holds a transition t named pa/x, as the markdown sentence says ('in a net that holds such a transition'); a delay keeping every stamp in any net is TIME-010's own content. Its delay half has its own mutant (MOD_012_clock_mutant_noDelayFrame_killed: a delay that clears every stamp)."
          "The block takes the build's structure as given and states steps only. A build that merged a private place of b into a shared place leaves b's transitions with an arc place that is not private, outside line 1's premise, so this block alone does not reject it; MOD_012 line 3 does (MOD_012_mutant_noKeep_killed). The prefixes are single segments, as the markdown says; sibling instances nested in one outer instance are covered in the build of the outer subnet's body."
          "AC2 (firing a transition in instance A does not affect the enablement of a transition in instance B whose arc places are all private to B) is line 1's first conjunct. AC3 has two parts: firing a transition of A keeps the timing clock of a transition of B whose arc places are all private to B (line 1's second and third conjuncts; MOD_012_clock_nonvacuous fires a/work and b/work keeps its stamp 0), and reaping a transition of A or advancing the clock keeps every timing clock of B (line 2). TIME-011 is cited for the per-instance clocks; its own lines are TIME-011's block. TIME-013 (a reap removes only the reaped transition's stamp) carries the reap half of line 2."
  signoff "pending"
  statement : ∀ {N A : Type}, Naming N → ScriptFn N A → TRel N → Prop :=
    fun {N A} Nm BS R =>
      (∀ (ops : List (Op N A)) c tol pa pb, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
        pa ≠ pb → ∀ t ∈ c.trans, NamedUnder pa t.core.name →
        ∀ u, InNet (c.toTimed tol) u → NamedUnder pb u.core.name →
          (∀ q, ArcPlace u q → PrivateTo Nm pb ops q) → ∀ d,
          on (fun s s' => R (c.toTimed tol) s (.fire t.toTrans d) s'), shall (fun s s' =>
            (Enabled u s'.m ↔ Enabled u s.m) ∧ (Armed s' u ↔ Armed s u) ∧
              (Armed s u → s'.stamp u.core.name = s.stamp u.core.name))) ∧
      (∀ (ops : List (Op N A)) c tol pa pb, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
        pa ≠ pb → ∀ t ∈ c.trans, NamedUnder pa t.core.name → ∀ u, NamedUnder pb u.core.name →
          on (fun s s' => R (c.toTimed tol) s (.reap t.toTrans) s' ∨
              ∃ δ, R (c.toTimed tol) s (.delay δ) s'), shall (fun s s' =>
            (Armed s' u ↔ Armed s u) ∧ s'.stamp u.core.name = s.stamp u.core.name))

/- The pinned readable form of MOD-012's clock block. -/
/--
info: def Libpetri.Spec.MOD_012_clock : {N A : Type} → Naming N → ScriptFn N A → TRel N → Prop :=
fun {N A} Nm BS R =>
  (∀ (ops : List (Op N A)) (c : ComposedNet N A) (tol : ℕ) (pa pb : String),
      BS ops = Except.ok c →
        ValidPrefix pa →
          ValidPrefix pb →
            pa ≠ pb →
              ∀ t ∈ c.trans,
                NamedUnder pa t.core.name →
                  ∀ (u : Reference.Trans N),
                    InNet (c.toTimed tol) u →
                      NamedUnder pb u.core.name →
                        (∀ (q : N), ArcPlace u q → PrivateTo Nm pb ops q) →
                          ∀ (d : List N),
                            on fun s s' => R (c.toTimed tol) s (TLbl.fire t.toTrans d) s', shall fun s s' =>
                              (Enabled u s'.m ↔ Enabled u s.m) ∧
                                (Armed s' u ↔ Armed s u) ∧ (Armed s u → s'.stamp u.core.name = s.stamp u.core.name)) ∧
    ∀ (ops : List (Op N A)) (c : ComposedNet N A) (tol : ℕ) (pa pb : String),
      BS ops = Except.ok c →
        ValidPrefix pa →
          ValidPrefix pb →
            pa ≠ pb →
              ∀ t ∈ c.trans,
                NamedUnder pa t.core.name →
                  ∀ (u : Reference.Trans N),
                    NamedUnder pb u.core.name →
                      on fun s s' =>
                        R (c.toTimed tol) s (TLbl.reap t.toTrans) s' ∨ ∃ δ, R (c.toTimed tol) s (TLbl.delay δ) s', shall
                        fun s s' => (Armed s' u ↔ Armed s u) ∧ s'.stamp u.core.name = s.stamp u.core.name
-/
#guard_msgs in #print MOD_012_clock

/-! ### The lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-012: a transition that names a private place of `pb` is named `pb/x`. -/
def mod012_line1 (Nm : Naming N) (BS : ScriptFn N A) (_F : FireRel N) : Prop :=
  ∀ (ops : List (Op N A)) c pb p, BS ops = .ok c → PrivateTo Nm pb ops p →
    ∀ t ∈ c.trans, p ∈ t.namedPlaces → NamedUnder pb t.core.name

/-- Line 2 of MOD-012: a firing of a transition of `pa` leaves every private place of `pb`. -/
def mod012_line2 (Nm : Naming N) (BS : ScriptFn N A) (F : FireRel N) : Prop :=
  ∀ (ops : List (Op N A)) c pa pb p, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
    pa ≠ pb → PrivateTo Nm pb ops p → ∀ t ∈ c.trans, NamedUnder pa t.core.name →
      on (fun m m' => Fire F t.toTrans m m'), shall (fun m m' => m' p = m p)

/-- Line 3 of MOD-012: a compose call's definition that names a private place of `pb`, not bound
as a port place of that call, gives a transition of the built net with its name that names the
place. -/
def mod012_line3 (Nm : Naming N) (BS : ScriptFn N A) (_F : FireRel N) : Prop :=
  ∀ (ops : List (Op N A)) c pb p I ports chans, BS ops = .ok c → PrivateTo Nm pb ops p →
    Op.compose I ports chans ∈ ops → (∀ e ∈ ports, I.port e.1 ≠ some p) →
    ∀ d ∈ I.defs, p ∈ d.namedPlaces →
      ∃ t ∈ c.trans, t.core.name = d.core.name ∧ p ∈ t.namedPlaces

/-- MOD-012 is its three lines. -/
theorem mod012_iff (Nm : Naming N) (BS : ScriptFn N A) (F : FireRel N) :
    MOD_012 Nm BS F ↔ mod012_line1 Nm BS F ∧ mod012_line2 Nm BS F ∧ mod012_line3 Nm BS F :=
  Iff.rfl

/-- Line 1 of the clock block: a firing of a transition of `pa`. -/
def mod012c_line1 (Nm : Naming N) (BS : ScriptFn N A) (R : TRel N) : Prop :=
  ∀ (ops : List (Op N A)) c tol pa pb, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
    pa ≠ pb → ∀ t ∈ c.trans, NamedUnder pa t.core.name →
    ∀ u, InNet (c.toTimed tol) u → NamedUnder pb u.core.name →
      (∀ q, ArcPlace u q → PrivateTo Nm pb ops q) → ∀ d,
      on (fun s s' => R (c.toTimed tol) s (.fire t.toTrans d) s'), shall (fun s s' =>
        (Enabled u s'.m ↔ Enabled u s.m) ∧ (Armed s' u ↔ Armed s u) ∧
          (Armed s u → s'.stamp u.core.name = s.stamp u.core.name))

/-- Line 2 of the clock block: a reap of a transition of `pa`, or a delay. -/
def mod012c_line2 (_Nm : Naming N) (BS : ScriptFn N A) (R : TRel N) : Prop :=
  ∀ (ops : List (Op N A)) c tol pa pb, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
    pa ≠ pb → ∀ t ∈ c.trans, NamedUnder pa t.core.name → ∀ u, NamedUnder pb u.core.name →
      on (fun s s' => R (c.toTimed tol) s (.reap t.toTrans) s' ∨
          ∃ δ, R (c.toTimed tol) s (.delay δ) s'), shall (fun s s' =>
        (Armed s' u ↔ Armed s u) ∧ s'.stamp u.core.name = s.stamp u.core.name)

/-- The clock block is its two lines. -/
theorem mod012c_iff (Nm : Naming N) (BS : ScriptFn N A) (R : TRel N) :
    MOD_012_clock Nm BS R ↔ mod012c_line1 Nm BS R ∧ mod012c_line2 Nm BS R := Iff.rfl

/-- Two valid and different prefixes never name one transition. -/
theorem namedUnder_ne {pa pb n : String} (va : ValidPrefix pa) (vb : ValidPrefix pb)
    (hne : pa ≠ pb) (ha : NamedUnder pa n) : ¬ NamedUnder pb n := by
  rintro ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := ha
  exact hne (preS_inj _ _ _ _ va vb hx.symm).1

end Lines

/-! ### The reference -/

section Reference

variable {N A : Type} [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- The reference build script satisfies MOD-012 with the reference firing relation, for every
transition check and every local channel merge. -/
theorem mod012_buildScript (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    {Mg : MergeFn N A} (hM : MergeLocal Mg) : MOD_012 Nm (buildScript Nm tyOf Build Mg) RefFire := by
  refine ⟨fun ops c pb p h hp => buildScript_local hM h hp, ?_,
    fun ops c pb p I ports chans h hp hmem hport d hd hpd =>
      buildScript_keeps hM h hp hmem hport hd hpd⟩
  intro ops c pa pb p h va vb hne hp t ht hta m m' ⟨d, hf⟩
  have hn : p ∉ t.namedPlaces := fun hpt =>
    namedUnder_ne va vb hne hta (buildScript_local hM h hp t ht hpt)
  exact (refFire_frame hn hf).1

/-- The reference build script satisfies the clock block with the reference timed step, for every
transition check and every local channel merge. -/
theorem mod012_clock_buildScript (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    {Mg : MergeFn N A} (hM : MergeLocal Mg) :
    MOD_012_clock Nm (buildScript Nm tyOf Build Mg) RefTStep := by
  refine ⟨?_, ?_⟩
  · intro ops c tol pa pb h va vb hne t ht hta u hu hub hpriv d s s' hs
    have htu : t.core.name ≠ u.core.name := fun e =>
      namedUnder_ne va vb hne hta (e ▸ hub)
    exact refTStep_fire_frame hs hu htu fun q hq hqt =>
      namedUnder_ne va vb hne hta (buildScript_local hM h (hpriv q hq) t ht hqt)
  · intro ops c tol pa pb h va vb hne t ht hta u hub s s' hs
    have htu : t.core.name ≠ u.core.name := fun e =>
      namedUnder_ne va vb hne hta (e ▸ hub)
    exact refTStepW_reapDelay_frame htu hs

/-- ✓ **The reference satisfies MOD-012**: in every net the reference build script builds, a
transition that names a place private to `b` is one of `b`'s own, named `b/x`, so the reference
firing of a transition named `a/x` never changes such a place. Composing two buffers `a` and `b`,
firing `a/work` leaves `b/IN` as it was. -/
@[evidence holds MOD_012]
theorem MOD_012_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N) :
    MOD_012 Nm (buildScript Nm (fun _ : N => ()) refBuild
      (refMerge (A := A) refBuild (seqAct fun a _ => a) (fun _ _ => .ok none))) RefFire :=
  mod012_buildScript Nm _ refBuild (refMerge_local _ _)

/-- ✓ **The reference satisfies the clock block**: in every net the reference build script
builds, firing a transition named `a/x` keeps the enablement, the armed state and the stamp of
every transition named `b/y` whose arc places are private to `b`, and a reap of `a/x` or a delay
keeps every stamp of `b`. When `a/work` fires at clock 5, `b/work` keeps its stamp 0. -/
@[evidence holds MOD_012_clock]
theorem MOD_012_clock_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N) :
    MOD_012_clock Nm (buildScript Nm (fun _ : N => ()) refBuild
      (refMerge (A := A) refBuild (seqAct fun a _ => a) (fun _ _ => .ok none))) RefTStep :=
  mod012_clock_buildScript Nm _ refBuild (refMerge_local _ _)

end Reference

/-! ### Instances made by `instantiate` -/

section Instances

variable {N A : Type}

/-- The places a renamed definition names are the original's, renamed. -/
theorem transDef_map_namedPlaces (f : N → N) (g : String → String) (d : TransDef N A) :
    (d.map f g).namedPlaces = d.namedPlaces.map f := by
  obtain ⟨core, out, timing, priority, action⟩ := d
  cases out <;>
    simp [TransDef.map, TransDef.namedPlaces, mapCore, mapIn, outPlaces_mapOut, List.map_map,
      Function.comp_def]

/-- **Another instance's transitions never name a place of `b`**: in every model of [MOD-010], a
definition of an instance under `pa` names no place renamed under another valid prefix `pb`. So in
a compose call of that instance, the last clause of `OpLeaves` holds for every place of `b`.
Instance `a` of the buffer names `a/IN` and `a/OUT`, never `b/IN`. -/
theorem mod012_inst_leaves {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst)
    {S : SubnetDef N A} {pa pb : String} {I : Instance N A} (hI : Inst S pa = .ok I)
    (vb : ValidPrefix pb) (hne : pa ≠ pb) (y : N) : ∀ d ∈ I.defs, Nm.pre pb y ∉ d.namedPlaces := by
  intro d hd hp
  have va := mod010_ok_valid h.1 hI
  have hmem : d.toTransDef ∈ S.defs.map (fun d => d.toTransDef.map (Nm.pre pa) (preS pa)) := by
    rw [← (h.2.2.2 S pa I hI).2]
    exact List.mem_map_of_mem hd
  obtain ⟨d₀, -, he⟩ := List.mem_map.1 hmem
  have hp' : Nm.pre pb y ∈ d.toTransDef.namedPlaces := hp
  rw [← he, transDef_map_namedPlaces] at hp'
  obtain ⟨x, -, hx⟩ := List.mem_map.1 hp'
  exact hne (Nm.pre_inj _ _ _ _ va vb hx).1

end Instances

/-! ### The example: two instances of one buffer -/

section Example

/-- The buffer's one transition: `work` takes a token from `IN` and puts one in `OUT`. -/
def mod012Def : CDef String Unit :=
  { core := ⟨"work", [⟨"IN", .one⟩], [], [], []⟩, out := some (.place "OUT"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The buffer subnet: places `IN` and `OUT`, the transition `work`, no interface. -/
def mod012Body : SubnetDef String Unit :=
  { name := "buf", places := ["IN", "OUT"], defs := [mod012Def], ports := [], chans := [] }

/-- The buffer instantiated under prefix `p`. -/
def mod012Inst (p : String) : Instance String Unit := renamedInstance strNaming mod012Body p

/-- The script: compose the instances `a` and `b`, with no binding. -/
def mod012Ops : List (Op String Unit) :=
  [mod012Inst "a", mod012Inst "b"].map fun I => .compose I [] []

/-- The reference build script at places keyed by name. -/
def mod012BS : ScriptFn String Unit :=
  buildScript strNaming (fun _ => ()) refBuild
    (refMerge refBuild (seqAct fun a _ => a) (fun _ _ => .ok none))

/-- The transition `p/work` of the composed net. -/
def mod012T (p : String) : TransDef String Unit :=
  { core := ⟨preS p "work", [⟨preS p "IN", .one⟩], [], [], []⟩, out := some (.place (preS p "OUT")),
    timing := .immediate, priority := 0, action := .passthrough }

set_option maxRecDepth 20000 in
/-- The reference builds the script, with the transitions `a/work` and `b/work` in order. -/
theorem mod012_built : ∃ c, mod012BS mod012Ops = .ok c ∧ c.trans = [mod012T "a", mod012T "b"] := by
  have hok : (mod012BS mod012Ops).toOption.isSome = true := by decide
  cases h : mod012BS mod012Ops with
  | error m => rw [h] at hok; cases hok
  | ok c => exact ⟨c, rfl, by rw [buildScript_composeNil _ h]; rfl⟩

/-- `b/IN` is private to `b` in the script: `a`'s transition does not name it, and `b`'s is
named `b/work` and bound by no channel. -/
theorem mod012_private : PrivateTo strNaming "b" mod012Ops "b/IN" := by
  intro op hop
  simp only [mod012Ops, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false] at hop
  rcases hop with rfl | rfl
  · refine And.intro (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) ?_)
    intro d hd hp
    refine absurd hp ?_
    simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
      List.mem_singleton] at hd
    subst hd
    decide
  · refine And.intro (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) ?_)
    intro d hd _
    refine ⟨rfl, ⟨"work", ?_⟩, fun _ h => nomatch h⟩
    simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
      List.mem_singleton] at hd
    subst hd
    rfl

/-- The only arc place of `b/work` is `b/IN`. -/
theorem mod012_arc_b (q : String) (h : ArcPlace (mod012T "b").toTrans q) : q = "b/IN" := by
  simp [ArcPlace, inPlaces, mod012T, TransDef.toTrans, ReadArc, InhibitorArc, ResetArc] at h
  rw [h]
  rfl

/-- `a/work` lies under `a`. -/
theorem mod012_namedA : NamedUnder "a" (mod012T "a").core.name := ⟨"work", rfl⟩

/-- `b/work` lies under `b`. -/
theorem mod012_namedB : NamedUnder "b" (mod012T "b").toTrans.core.name := ⟨"work", rfl⟩

/-- The marking with one token in `a/IN` and one in `b/IN`. -/
def mod012M0 : String → Nat := fun q => if q = "a/IN" ∨ q = "b/IN" then 1 else 0

/-- The marking after `a/work` fires from `mod012M0`. -/
def mod012M1 : String → Nat := fireNC mod012M0 (mod012T "a").core (depProd ["a/OUT"])

/-- `a/work` fires from `mod012M0`, depositing in `a/OUT`. -/
theorem mod012_fires : RefFire (mod012T "a").toTrans mod012M0 ["a/OUT"] mod012M1 :=
  ⟨by decide, ⟨.action 0, by decide⟩, rfl⟩

/-- The timed state: the marking `mod012M0`, the clock at 5, `a/work` and `b/work` stamped 0. -/
def mod012S0 : TSt String :=
  { m := mod012M0, now := 5, stamp := fun n => if n = "a/work" ∨ n = "b/work" then some 0 else none }

variable {c : ComposedNet String Unit}

/-- The timed net's transitions. -/
theorem mod012_net (hc : c.trans = [mod012T "a", mod012T "b"]) (tol : Nat) :
    (c.toTimed tol).net.transitions = [(mod012T "a").toTrans, (mod012T "b").toTrans] := by
  simp [BuiltNet.toTimed, BuiltNet.toNet, hc]

/-- Every transition of the timed net is `Immediate`. -/
theorem mod012_timing (hc : c.trans = [mod012T "a", mod012T "b"]) (tol : Nat)
    (t : Reference.Trans String) : (c.toTimed tol).timing t = .immediate := by
  show ((c.trans.find? (·.core.name == t.core.name)).map (·.timing)).getD .immediate = .immediate
  cases hf : c.trans.find? (·.core.name == t.core.name) with
  | none => rfl
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    rw [hc] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> rfl

/-- `b/work` is the timed net's transition of its name. -/
theorem mod012_inNet (hc : c.trans = [mod012T "a", mod012T "b"]) (tol : Nat) :
    InNet (c.toTimed tol) (mod012T "b").toTrans := by
  unfold InNet
  rw [mod012_net hc]
  rfl

/-- Under every policy with the spec's gate and expiry test, `a/work` fires from `mod012S0`. -/
theorem mod012_fireStep (hc : c.trans = [mod012T "a", mod012T "b"]) (P : Policy String)
    (hg : P.gate = refPolicy.gate) (hx : P.expired = refPolicy.expired) :
    RefTStepW P (c.toTimed 0) mod012S0 (.fire (mod012T "a").toTrans ["a/OUT"])
      { m := mod012M1, now := mod012S0.now,
        stamp := restampAll P (c.toTimed 0) mod012S0 (mod012T "a").toTrans ["a/OUT"] mod012M1 } := by
  refine RefTStepW.fire _ _ _ _ _ (by rw [mod012_net hc]; simp) mod012_fires (by decide) ?_ ?_
  · rw [hg]
    show decide (((c.toTimed 0).timing _).earliest ≤ _) = true
    rw [mod012_timing hc]
    decide
  · rw [hx]
    show tExpired _ _ _ = false
    unfold tExpired
    rw [mod012_timing hc]
    rfl

end Example

/-! ### Non-vacuity -/

set_option maxRecDepth 20000 in
/-- ✓ **Every premise of MOD-012 is met by the reference**: the reference builds two instances
`a` and `b` of one buffer, `b/IN` is private to `b`, and `a/work` fires from the marking with one
token in `a/IN` and one in `b/IN`: `a/IN` is emptied, `b/IN` still holds its token (AC1). The
compose call of `b` adds the definition `b/work`, which names `b/IN`, and the built net's `b/work`
still names `b/IN` (AC4). -/
@[evidence nonvacuous MOD_012]
theorem MOD_012_nonvacuous :
    ∃ c, mod012BS mod012Ops = .ok c ∧ mod012T "a" ∈ c.trans ∧
      PrivateTo strNaming "b" mod012Ops "b/IN" ∧
      (∃ m', RefFire (mod012T "a").toTrans mod012M0 ["a/OUT"] m' ∧ m' "a/IN" = 0 ∧
        m' "b/IN" = mod012M0 "b/IN") ∧
      Op.compose (mod012Inst "b") [] [] ∈ mod012Ops ∧
      (∃ d ∈ (mod012Inst "b").defs, "b/IN" ∈ d.namedPlaces ∧ d.core.name = "b/work") ∧
      ∃ t ∈ c.trans, t.core.name = "b/work" ∧ "b/IN" ∈ t.namedPlaces := by
  obtain ⟨c, hc, hct⟩ := mod012_built
  refine ⟨c, hc, by rw [hct]; simp, mod012_private,
    ⟨mod012M1, mod012_fires, by decide, by decide⟩, by simp [mod012Ops], ?_,
    ⟨mod012T "b", by rw [hct]; simp, rfl, by decide⟩⟩
  simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
    List.mem_singleton, exists_eq_left]
  exact ⟨by decide, rfl⟩

/-- ✓ **Every premise of the clock block is met by the reference**: in the net the reference
builds, with `a/work` and `b/work` both armed with stamp 0 and the clock at 5, `a/work` fires
under the reference timed step; `b/work`, whose one arc place `b/IN` is private to `b`, stays
armed with stamp 0 (AC2, AC3). -/
@[evidence nonvacuous MOD_012_clock]
theorem MOD_012_clock_nonvacuous :
    ∃ c, mod012BS mod012Ops = .ok c ∧ mod012T "a" ∈ c.trans ∧
      InNet (c.toTimed 0) (mod012T "b").toTrans ∧
      (∀ q, ArcPlace (mod012T "b").toTrans q → PrivateTo strNaming "b" mod012Ops q) ∧
      ∃ s', RefTStep (c.toTimed 0) mod012S0 (.fire (mod012T "a").toTrans ["a/OUT"]) s' ∧
        Armed mod012S0 (mod012T "b").toTrans ∧ Armed s' (mod012T "b").toTrans ∧
        s'.stamp "b/work" = some 0 := by
  obtain ⟨c, hc, hct⟩ := mod012_built
  have hstep := mod012_fireStep hct refPolicy rfl rfl
  have ha : Armed mod012S0 (mod012T "b").toTrans := by
    rw [armed_iff]; decide
  have hpriv : ∀ q, ArcPlace (mod012T "b").toTrans q → PrivateTo strNaming "b" mod012Ops q :=
    fun q hq => mod012_arc_b q hq ▸ mod012_private
  have hfr := mod012_clock_buildScript strNaming (fun _ => ()) refBuild
    (refMerge_local (Build := refBuild) (A := Unit) (seqAct fun a _ => a) (fun _ _ => .ok none))
  obtain ⟨-, hA, hS⟩ := hfr.1 mod012Ops c 0 "a" "b" hc (by decide) (by decide) (by decide)
    (mod012T "a") (by rw [hct]; simp) mod012_namedA (mod012T "b").toTrans (mod012_inNet hct 0)
    mod012_namedB hpriv ["a/OUT"] _ _ hstep
  refine ⟨c, hc, by rw [hct]; simp, mod012_inNet hct 0, hpriv, _, hstep, ha, hA.2 ha, ?_⟩
  have := hS ha
  exact this

/-! ### Mutant: line 1 dropped (structure) -/

/-- A firing relation that never fires. -/
def mod012NoFire : FireRel String := fun _ _ _ _ => False

/-- A transition named `a/work` with an input arc on `b/IN`. -/
def mod012Foreign : TransDef String Unit :=
  { core := ⟨"a/work", [⟨"b/IN", .one⟩], [], [], []⟩, out := some (.place "a/OUT"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- A build that adds an arc from `a`'s transition to a place of `b` that no call names: the empty
script gives the net holding `mod012Foreign` alone, and every other script is rejected. -/
def mod012ForeignBS : ScriptFn String Unit
  | [] => .ok { places := ["b/IN", "a/OUT"], trans := [mod012Foreign], terminals := [],
                corrs := [none], member := fun _ => none }
  | _ :: _ => .error "rejected"

/-- Mutant reading: MOD-012 without line 1, the marking frame and the kept places alone. -/
def MOD_012_mutant_noStructure (Nm : Naming String) (BS : ScriptFn String Unit)
    (F : FireRel String) : Prop :=
  mod012_line2 Nm BS F ∧ mod012_line3 Nm BS F

/-- The foreign-arc build kills the mutant: with a firing relation that never fires it meets
line 2, and line 3 holds because its only built script holds no compose call; but on the empty
script `b/IN` is private to `b` and the transition `a/work` names it (line 1). -/
@[evidence mutant MOD_012]
theorem MOD_012_mutant_noStructure_killed :
    MOD_012_mutant_noStructure strNaming mod012ForeignBS mod012NoFire ∧
      ¬ MOD_012 strNaming mod012ForeignBS mod012NoFire := by
  refine ⟨⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, h⟩ => (h : False).elim, ?_⟩, fun h => ?_⟩
  · intro ops c pb p I ports chans hc _ hmem
    cases ops with
    | nil => cases hmem
    | cons _ _ => cases hc
  have := h.1 [] _ "b" "b/IN" rfl (fun _ h => nomatch h) mod012Foreign (by simp) (by decide)
  exact namedUnder_ne (pa := "a") (by decide) (by decide) (by decide) ⟨"work", by decide⟩ this

/-! ### Mutant: line 2 dropped (marking frame) -/

/-- A firing relation that also empties every other place, as one token store shared by all
instances would. -/
def mod012DrainFire : FireRel String := fun t m d m' => ∃ m₀, RefFire t m d m₀ ∧ m' = fun _ => 0

/-- Mutant reading: MOD-012 without line 2, the structure and the kept places alone. -/
def MOD_012_mutant_noFrame (Nm : Naming String) (BS : ScriptFn String Unit)
    (F : FireRel String) : Prop :=
  mod012_line1 Nm BS F ∧ mod012_line3 Nm BS F

/-- The draining firing relation kills the mutant: the reference build meets line 1, but `a/work`
fires and empties `b/IN`, which is private to `b` (line 2). -/
@[evidence mutant MOD_012]
theorem MOD_012_mutant_noFrame_killed :
    MOD_012_mutant_noFrame strNaming mod012BS mod012DrainFire ∧
      ¬ MOD_012 strNaming mod012BS mod012DrainFire := by
  refine ⟨⟨(MOD_012_reference (A := Unit) strNaming).1, (MOD_012_reference (A := Unit) strNaming).2.2⟩,
    fun h => ?_⟩
  obtain ⟨c, hc, hct⟩ := mod012_built
  have := h.2.1 mod012Ops c "a" "b" "b/IN" hc (by decide) (by decide) (by decide) mod012_private
    (mod012T "a") (by rw [hct]; simp) mod012_namedA mod012M0 (fun _ => 0)
    ⟨["a/OUT"], mod012M1, mod012_fires, rfl⟩
  exact absurd this (by decide)

/-! ### Mutant: clock line 1 dropped (re-arm on every firing) -/

/-- A policy that keeps no stamp across a firing: every armed transition that stays enabled is
re-armed with a fresh stamp whenever any transition fires. -/
def mod012RearmPolicy : Policy String := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- Mutant reading: the clock block without line 1, the reap and delay frame alone. -/
def MOD_012_clock_mutant_noFireFrame (Nm : Naming String) (BS : ScriptFn String Unit)
    (R : TRel String) : Prop :=
  mod012c_line2 Nm BS R

/-- The re-arming step kills the mutant: reaps and delays keep stamps as the reference does, but
`a/work` firing at clock 5 restamps `b/work` from 0 to 5 (line 1). -/
@[evidence mutant MOD_012_clock]
theorem MOD_012_clock_mutant_noFireFrame_killed :
    MOD_012_clock_mutant_noFireFrame strNaming mod012BS (RefTStepW mod012RearmPolicy) ∧
      ¬ MOD_012_clock strNaming mod012BS (RefTStepW mod012RearmPolicy) := by
  refine ⟨fun ops c tol pa pb _ va vb hne t _ hta u hub s s' hs =>
    refTStepW_reapDelay_frame (t := t.toTrans)
      (fun e => namedUnder_ne va vb hne hta (show NamedUnder pb t.core.name from e ▸ hub)) hs,
    fun h => ?_⟩
  obtain ⟨c, hc, hct⟩ := mod012_built
  have hstep := mod012_fireStep hct mod012RearmPolicy rfl rfl
  obtain ⟨-, -, hS⟩ := h.1 mod012Ops c 0 "a" "b" hc (by decide) (by decide) (by decide)
    (mod012T "a") (by rw [hct]; simp) mod012_namedA (mod012T "b").toTrans (mod012_inNet hct 0)
    mod012_namedB (fun q hq => mod012_arc_b q hq ▸ mod012_private) ["a/OUT"] _ _ hstep
  have ha : Armed mod012S0 (mod012T "b").toTrans := by rw [armed_iff]; decide
  have h1 := hS ha
  simp only at h1
  rw [restampAll_inNet (mod012_inNet hct 0)] at h1
  revert h1
  unfold restampW
  simp only [mod012RearmPolicy, refPolicy]
  decide

/-! ### Mutant: clock line 2 dropped (one clock per net) -/

/-- A timed step whose reap disarms every transition of the net, as one clock shared by all
instances would; delays and firings are the reference's. -/
def mod012ReapAll : TRel String := fun X s l s' =>
  match l with
  | .reap t => t ∈ X.net.transitions ∧ s' = { s with stamp := fun _ => none }
  | l => RefTStep X s l s'

/-- Mutant reading: the clock block without line 2, the firing frame alone. -/
def MOD_012_clock_mutant_noReapFrame (Nm : Naming String) (BS : ScriptFn String Unit)
    (R : TRel String) : Prop :=
  mod012c_line1 Nm BS R

/-- The net-wide reap kills the mutant: its firings are the reference's, so it meets line 1, but
reaping `a/work` removes the stamp of `b/work` (line 2). -/
@[evidence mutant MOD_012_clock]
theorem MOD_012_clock_mutant_noReapFrame_killed :
    MOD_012_clock_mutant_noReapFrame strNaming mod012BS mod012ReapAll ∧
      ¬ MOD_012_clock strNaming mod012BS mod012ReapAll := by
  refine ⟨fun ops c tol pa pb h va vb hne t ht hta u hu hub hpriv d s s' hs =>
    (MOD_012_clock_reference (A := Unit) strNaming).1 ops c tol pa pb h va vb hne t ht hta u hu hub
      hpriv d s s' hs, fun h => ?_⟩
  obtain ⟨c, hc, hct⟩ := mod012_built
  have hs : mod012ReapAll (c.toTimed 0) mod012S0 (.reap (mod012T "a").toTrans)
      { mod012S0 with stamp := fun _ => none } :=
    ⟨by rw [mod012_net hct]; simp, rfl⟩
  have := (h.2 mod012Ops c 0 "a" "b" hc (by decide) (by decide) (by decide) (mod012T "a")
    (by rw [hct]; simp) mod012_namedA (mod012T "b").toTrans mod012_namedB _ _ (.inl hs)).2
  exact absurd this (by decide)

/-! ### Mutant: clock line 2's delay half dropped (a delay clears every clock) -/

/-- A timed step whose delay disarms every transition of the net, as one clock shared by all
instances that a delay restarts would; firings and reaps are the reference's. -/
def mod012DelayAll : TRel String := fun X s l s' =>
  match l with
  | .delay δ => s' = { s with now := s.now + δ, stamp := fun _ => none }
  | l => RefTStep X s l s'

/-- Line 2 of the clock block without its delay half: a reap of a transition of `pa`. -/
def mod012c_line2_reap (_Nm : Naming String) (BS : ScriptFn String Unit) (R : TRel String) :
    Prop :=
  ∀ (ops : List (Op String Unit)) c tol pa pb, BS ops = .ok c → ValidPrefix pa → ValidPrefix pb →
    pa ≠ pb → ∀ t ∈ c.trans, NamedUnder pa t.core.name → ∀ u, NamedUnder pb u.core.name →
      on (fun s s' => R (c.toTimed tol) s (.reap t.toTrans) s'), shall (fun s s' =>
        (Armed s' u ↔ Armed s u) ∧ s'.stamp u.core.name = s.stamp u.core.name)

/-- Mutant reading: the clock block with line 1 and only the reap half of line 2. -/
def MOD_012_clock_mutant_noDelayFrame (Nm : Naming String) (BS : ScriptFn String Unit)
    (R : TRel String) : Prop :=
  mod012c_line1 Nm BS R ∧ mod012c_line2_reap Nm BS R

/-- The clearing delay kills the mutant: its firings and reaps are the reference's, so it meets
line 1 and the reap half, but when the clock advances by 1 from 5 the stamp 0 of `b/work` is
gone (line 2, delay half). -/
@[evidence mutant MOD_012_clock]
theorem MOD_012_clock_mutant_noDelayFrame_killed :
    MOD_012_clock_mutant_noDelayFrame strNaming mod012BS mod012DelayAll ∧
      ¬ MOD_012_clock strNaming mod012BS mod012DelayAll := by
  refine ⟨⟨fun ops c tol pa pb h va vb hne t ht hta u hu hub hpriv d s s' hs =>
    (MOD_012_clock_reference (A := Unit) strNaming).1 ops c tol pa pb h va vb hne t ht hta u hu hub
      hpriv d s s' hs,
    fun ops c tol pa pb h va vb hne t ht hta u hub s s' hs =>
    (MOD_012_clock_reference (A := Unit) strNaming).2 ops c tol pa pb h va vb hne t ht hta u hub
      s s' (.inl hs)⟩, fun h => ?_⟩
  obtain ⟨c, hc, hct⟩ := mod012_built
  have hs : mod012DelayAll (c.toTimed 0) mod012S0 (.delay 1)
      { mod012S0 with now := mod012S0.now + 1, stamp := fun _ => none } := rfl
  have := (h.2 mod012Ops c 0 "a" "b" hc (by decide) (by decide) (by decide) (mod012T "a")
    (by rw [hct]; simp) mod012_namedA (mod012T "b").toTrans mod012_namedB _ _ (.inr ⟨1, hs⟩)).2
  exact absurd this (by decide)

/-! ### Mutant: line 3 dropped (fusion keyed by local name) -/

/-- The local name of a place: the part after the last `/`. -/
def mod012LocName (q : String) : String :=
  String.ofList ((q.toList.reverse.takeWhile (· ≠ '/')).reverse)

/-- The fusion sets a script declares. -/
def mod012FusionsOf (ops : List (Op String Unit)) : List (FusionSet String) :=
  ops.filterMap fun | .fuse s => some s | _ => none

/-- A fusion set the script declares is one of its calls. -/
theorem mod012_mem_fusionsOf {ops : List (Op String Unit)} {s : FusionSet String}
    (h : s ∈ mod012FusionsOf ops) : Op.fuse s ∈ ops := by
  unfold mod012FusionsOf at h
  obtain ⟨o, ho, he⟩ := List.mem_filterMap.1 h
  cases o <;> simp at he
  subst he; exact ho

/-- The slip: a place goes to the canonical member of the first set one of whose non-canonical
members has the same local name. -/
def mod012LocSubst (fs : List (FusionSet String)) (q : String) : String :=
  match fs.find? (fun s => s.members.tail.any (fun m => mod012LocName m == mod012LocName q)) with
  | some s => s.members.headD q
  | none => q

/-- A place the slip moves lands on a member of a declared fusion set. -/
theorem mod012_locSubst_moved {fs : List (FusionSet String)} {q : String}
    (h : mod012LocSubst fs q ≠ q) : ∃ s ∈ fs, mod012LocSubst fs q ∈ s.members := by
  unfold mod012LocSubst at h ⊢
  cases hf : fs.find? (fun s => s.members.tail.any (fun m => mod012LocName m == mod012LocName q))
    with
  | none => rw [hf] at h; exact absurd rfl h
  | some s =>
    refine ⟨s, List.mem_of_find?_eq_some hf, ?_⟩
    have ht := List.find?_some hf
    cases hm : s.members with
    | nil => rw [hm] at ht; simp at ht
    | cons x xs => simp [hm]

/-- The mutant's pass over the reference's built net: every place through the slip. -/
def mod012LocalFuse (fs : List (FusionSet String)) (c : ComposedNet String Unit) :
    ComposedNet String Unit :=
  { c with places := c.places.map (mod012LocSubst fs),
           trans := c.trans.map fun t => t.map (mod012LocSubst fs) id }

/-- **The mutant build script**: the reference build, then a fusion keyed by local names, as a
slip of `fusionMap.set(nc.name, canonical)` into a map keyed by the local name would give
(typescript/src/core/petri-net.ts:812-818, rust/libpetri-core/src/petri_net.rs:897-907). -/
def mod012LocalFuseBS : ScriptFn String Unit := fun ops =>
  (mod012BS ops).map (mod012LocalFuse (mod012FusionsOf ops))

/-- The mutant meets line 1: a moved place lands on a listed place, which is private to no
instance. -/
theorem mod012_localFuse_line1 : mod012_line1 strNaming mod012LocalFuseBS RefFire := by
  intro ops c pb p h hp t ht hpt
  obtain ⟨c0, h0, rfl⟩ := except_map_ok_iff.1 h
  simp only [mod012LocalFuse, List.mem_map] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  rw [transDef_map_namedPlaces] at hpt
  obtain ⟨q, hq, hqp⟩ := List.mem_map.1 hpt
  rw [TransDef.map_name]
  by_cases hm : mod012LocSubst (mod012FusionsOf ops) q = q
  · rw [hm] at hqp; subst hqp
    exact (MOD_012_reference (A := Unit) strNaming).1 ops c0 pb q h0 hp t0 ht0 hq
  · obtain ⟨s, hs, hmem⟩ := mod012_locSubst_moved hm
    exact absurd (hqp ▸ hmem) (hp _ (mod012_mem_fusionsOf hs))

/-- The mutant meets line 2: it follows from line 1 for the reference firing. -/
theorem mod012_localFuse_line2 : mod012_line2 strNaming mod012LocalFuseBS RefFire := by
  intro ops c pa pb p h va vb hne hp t ht hta m m' ⟨d, hf⟩
  have hn : p ∉ t.namedPlaces := fun hpt =>
    namedUnder_ne va vb hne hta (mod012_localFuse_line1 ops c pb p h hp t ht hpt)
  exact (refFire_frame hn hf).1

/-- Caller place `x`, three buffers `a`, `b` and `c`, and the fusion set `{x, c/IN}`. -/
def mod012FuseOps : List (Op String Unit) :=
  [.place "x"] ++ [mod012Inst "a", mod012Inst "b", mod012Inst "c"].map (fun I => .compose I [] [])
    ++ [.fuse ⟨"f", ["x", "c/IN"]⟩]

set_option maxRecDepth 40000 in
/-- In the mutant's net, `a/work`, `b/work` and `c/work` all consume from `x`. -/
theorem mod012_localFuse_built :
    ((mod012LocalFuseBS mod012FuseOps).toOption.map fun c =>
        c.trans.map fun t => (t.core.name, t.namedPlaces))
      = some [("a/work", ["x", "a/OUT"]), ("b/work", ["x", "b/OUT"]),
              ("c/work", ["x", "c/OUT"])] := by
  decide

/-- `a/IN` is private to `a` in the fusing script: no fusion set lists it, no binding names it,
and only `a/work` names it. -/
theorem mod012_fuse_private_aIN : PrivateTo strNaming "a" mod012FuseOps "a/IN" := by
  intro op hop
  simp only [mod012FuseOps, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · trivial
  · refine And.intro (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) ?_)
    intro d hd _
    refine ⟨rfl, ⟨"work", ?_⟩, fun _ h => nomatch h⟩
    simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
      List.mem_singleton] at hd
    subst hd; rfl
  · refine And.intro (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) ?_)
    intro d hd hp
    simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
      List.mem_singleton] at hd
    subst hd; exact absurd hp (by decide)
  · refine And.intro (fun _ h => nomatch h) (And.intro (fun _ h => nomatch h) ?_)
    intro d hd hp
    simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
      List.mem_singleton] at hd
    subst hd; exact absurd hp (by decide)
  · show "a/IN" ∉ ["x", "c/IN"]; decide

/-- Mutant reading: MOD-012 without line 3, the structure and the marking frame alone. -/
def MOD_012_mutant_noKeep (Nm : Naming String) (BS : ScriptFn String Unit)
    (F : FireRel String) : Prop :=
  mod012_line1 Nm BS F ∧ mod012_line2 Nm BS F

/-- The fusion keyed by local names kills the mutant. Compose three buffers `a`, `b` and `c` and
fuse the caller place `x` with `c/IN`: the slip also moves `a/IN` and `b/IN` into `x`, which no
fusion set lists them for. Lines 1 and 2 still hold, because after the move no transition names
a private place of another instance; but `a/work` no longer names `a/IN` (line 3), and `a/work` and
`b/work` now take their tokens from the one place `x`. -/
@[evidence mutant MOD_012]
theorem MOD_012_mutant_noKeep_killed :
    MOD_012_mutant_noKeep strNaming mod012LocalFuseBS RefFire ∧
      ¬ MOD_012 strNaming mod012LocalFuseBS RefFire := by
  refine ⟨⟨mod012_localFuse_line1, mod012_localFuse_line2⟩, fun h => ?_⟩
  have hb := mod012_localFuse_built
  cases hc : mod012LocalFuseBS mod012FuseOps with
  | error e => rw [hc] at hb; cases hb
  | ok c =>
    rw [hc] at hb
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at hb
    have hd : ∃ d ∈ (mod012Inst "a").defs, "a/IN" ∈ d.namedPlaces ∧ d.core.name = "a/work" := by
      simp only [mod012Inst, renamedInstance, mod012Body, List.map_cons, List.map_nil,
        List.mem_singleton, exists_eq_left]
      exact ⟨by decide, rfl⟩
    obtain ⟨d, hdm, hpd, hdn⟩ := hd
    obtain ⟨t, ht, htn, hpt⟩ := h.2.2 mod012FuseOps c "a" "a/IN" (mod012Inst "a") [] [] hc
      mod012_fuse_private_aIN (by simp [mod012FuseOps]) (fun _ h => nomatch h) d hdm hpd
    have hmem := List.mem_map_of_mem (f := fun t : TransDef String Unit =>
      (t.core.name, t.namedPlaces)) ht
    rw [hb, htn, hdn] at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, he⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hpt; exact absurd hpt (by decide)
    · exact absurd he (by decide)
    · exact absurd he (by decide)

end Libpetri.Spec
