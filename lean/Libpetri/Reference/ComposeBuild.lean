import Libpetri.Reference.ComposeBind
import Libpetri.Reference.ComposeMerge

set_option linter.missingDocs true

/-!
# RefCompose: the build script

The last slice of the composition model ([MOD-023], [MOD-026], [MOD-027], [MOD-050], and the
order questions of [MOD-012], [MOD-024], [MOD-025], [MOD-061]). An enclosing builder is a fold
over a script of calls (`Op`): declare a place, add a transition, declare a terminal place,
declare a fusion set, compose an instance (explicitly or by auto-binding) or a definition
directly. `build()` is `finish`. Writing the builder as a fold is what makes the order questions
statable: the retired-port check runs at build, after fusion, whatever the order of the arc and
the compose call; fusion runs after every compose call.

* `scriptStep Nm tyOf Build Mg b op` is one call ([CORE-040], [EXEC-042], [MOD-020], [MOD-024],
  [MOD-025], [MOD-060]):
  - `place p` adds `p` to the builder's places, where missing (Rust `insert_place`);
  - `trans d` adds `d` and every place an arc of `d` names (Rust `transition`, which
    auto-collects places); `d` must pass the transition builder's check `Build` (a transition
    exists only once built; a failure carries `Build`'s message);
  - `terminal p` declares `p` terminal and adds it to the places;
  - `fuse s` runs the declaration check `refDeclFusion tyOf` and records the set;
  - `compose I ports chans` is `refCompose`, `composeAuto I cs` is `refAuto`;
  - `composeDirect S` is `refDirect`, after checking that every body definition passes `Build`
    (a body holds built transitions).
* `finish Nm Build b` is `build()`, in the order of Rust (`rust/libpetri-core/src/petri_net.rs`
  `build`) and Java (`PetriNet.java` `build`): fusion (`refFuse`, only when a set is declared, as
  every runtime skips it otherwise), then the reference net builder `refNetBuild` on the fused
  content (the [EXEC-042] AC5 terminal check and the collected places, the same function core's
  blocks use), then the retired-port check of [MOD-027] on the fused definitions, with the shared
  message. TypeScript checks the retired ports before the terminal places; only a sole offender's
  message is claimed by any block.
* The result is a `ComposedNet`: core's `BuiltNet` (places, definitions, terminal places), the
  [MOD-031] correspondence of each transition by position, and the [MOD-026] membership map
  (a node with exactly one recorded owner, minus the fusion members fusion removed, by name).

What the blocks read: `Bld.Builds` is invariant (`step_builds`), so every definition of a built
net passes `Build` (`buildScript_builds`, [MOD-023] line 1); re-declaring a built net by hand
builds the same transitions and places (`buildScript_redeclare`, [MOD-023] line 2); on a script
of `place`, `trans` and `terminal` calls only, `buildScript` agrees with the reference net builder
(`buildScript_core`, `buildScript_core_ref`, [CORE-040]); `finish_ok_iff` characterises
`build()`; a call only appends definitions and retired records (`step_prefix`, `script_prefix`);
`finish_retired`, `finish_retired_rejects` and `finish_retired_msg` give [MOD-027];
`memberOf_eq_some_iff`, `memberOf_perm` and `memberMap_removed` give [MOD-026]'s map.

Not modelled: the net's name; which offender a message names when there are several; place
order (ruling D32: only transition order is normative), so agreement with the reference net
builder is stated up to the order of places.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-! ## Calls, results, the invariant -/

/-- **One call on an enclosing builder before `build()`** ([CORE-040], [EXEC-042], [MOD-020],
[MOD-024], [MOD-025], [MOD-060]). -/
inductive Op (N A : Type) where
  /-- Declare a place. -/
  | place (p : N)
  /-- Add a transition definition. -/
  | trans (d : CDef N A)
  /-- Declare a terminal place ([EXEC-042]). -/
  | terminal (p : N)
  /-- Declare a fusion set ([MOD-060]). -/
  | fuse (s : FusionSet N)
  /-- Compose an instance with port bindings (port name, caller place) and channel bindings
  (channel name, caller-side definition) ([MOD-020]). -/
  | compose (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A))
  /-- Compose an instance by auto-binding ([MOD-024]); `cs` names the channels its definition
  declares. -/
  | composeAuto (I : Instance N A) (cs : List String)
  /-- Compose a subnet definition directly, unrenamed ([MOD-025]). -/
  | composeDirect (S : SubnetDef N A)

/-- **A composed net**: core's built net (places, transition definitions in order, terminal
places), the [MOD-031] correspondence of each transition (by position, `none` for a hand-written
one) and the [MOD-026] membership map (`none`: no entry). -/
structure ComposedNet (N A : Type) extends BuiltNet N A where
  /-- The correspondence of each transition, by position ([MOD-031]). -/
  corrs  : List (Option (List (N × N)))
  /-- The owning subnet of a node name ([MOD-026]); `none`: no entry. -/
  member : String → Option String

/-- **A build-script function**: a script of calls from a new builder gives the composed net
`build()` returns, or a rejection with a message. -/
abbrev ScriptFn (N A : Type) := List (Op N A) → Except String (ComposedNet N A)

/-- **The builder invariant** ([MOD-023] line 1): every definition the builder holds passes the
transition builder's check `Build`. -/
def Bld.Builds (Build : Trans N → Option String) (b : Bld N A) : Prop :=
  ∀ d ∈ b.defs, Build d.toTrans = none

/-- A channel merge returns only definitions the transition builder's check `Build` accepts
(`refMerge` re-runs `Build` on the merged definition, [MOD-021]). -/
def MergeBuilds (Build : Trans N → Option String) (Mg : MergeFn N A) : Prop :=
  ∀ c i d, Mg c i = .ok d → Build d.toTrans = none

/-- The subnets recorded for node name `n`, in the order recorded. -/
def memberOwners (c : List (String × String)) (n : String) : List String :=
  (c.filter fun e => e.1 == n).map (·.2)

/-- The one name a list holds, possibly repeated; `none` for an empty list or two different
names. -/
def soleOwner : List String → Option String
  | [] => none
  | s :: rest => if rest.all (· == s) then some s else none

/-- **The membership entry of a node** ([MOD-026]): the subnet recorded for `n` when exactly one
subnet is recorded for it (possibly more than once); `none` when none is, or several are (a place
two direct compositions share). Rust `resolve_subnet_membership`, Java and TypeScript alike. -/
def memberOf (c : List (String × String)) (n : String) : Option String :=
  soleOwner (memberOwners c n)

/-- The first retired record an arc of `ds` names: the first definition in order with such an
arc, its first such place (input, inhibitor, read, reset, then output places), that place's first
record. -/
def retiredHit [DecidableEq N] (rs : List (Retired N)) (ds : List (CDef N A)) :
    Option (Retired N) :=
  ds.findSome? fun d => d.namedPlaces.findSome? fun p => rs.find? fun r => decide (r.place = p)

/-- Two outcomes of a net build agree up to the order of places: the same rejection message, or
two nets with the same transitions in order, the same terminal places and the same places in some
order (ruling D32: only transition order is normative). -/
def BuiltAgree : Except String (BuiltNet N A) → Except String (BuiltNet N A) → Prop
  | .error m, .error m' => m = m'
  | .ok b, .ok b' => b.trans = b'.trans ∧ b.terminals = b'.terminals ∧ b.places.Perm b'.places
  | _, _ => False

/-- A call on core's net builder as a call on the enclosing builder: a transition instance is
added as its definition, with no correspondence (hand-written). -/
def Op.ofBOp {B : TBuilder N A} : BOp B → Op N A
  | .place p => .place p
  | .trans x => .trans { toTransDef := B.defOf x, corr := none }
  | .terminal p => .terminal p

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N A : Type}

/-- The net builder's view of definitions that already passed `Build`: an instance is its
definition. `finish` hands the fused content to `refNetBuild` through it. -/
def defBuilder : TBuilder N A where
  I := TransDef N A
  build _ i := .ok i.resolve
  defOf := id
  same := (· = ·)

/-- The content a fusion stage returns, as an input of the reference net builder. -/
def netOf (X : FuseNet N A) : NetIn (defBuilder (N := N) (A := A)) :=
  ⟨X.places, X.defs.map (·.toTransDef), X.terminals⟩

/-- The relation the agreement with the reference net builder keeps along a script of `place`,
`trans` and `terminal` calls: the same definitions in order, the same terminal places, the same
places as a set (the declared ones, the terminal ones, those an arc names), nothing retired, no
fusion set. -/
def CoreRel {B : TBuilder N A} (b : Bld N A) (inp : NetIn B) : Prop :=
  b.defs.map (·.toTransDef) = inp.trans.map B.defOf ∧ b.terminals = inp.terminals ∧
    (∀ p, p ∈ b.places ↔ p ∈ inp.places ∨ p ∈ inp.terminals ∨
      ∃ d ∈ inp.trans.map B.defOf, p ∈ d.namedPlaces) ∧
    b.retired = [] ∧ b.fusions = []

/-! ## One call, `build()`, the script -/

section Script

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- **One call on the enclosing builder.** `place` and `terminal` add their place where missing;
`trans d` adds `d` and its arc places once `Build` accepts `d`; `fuse` records a set the
declaration check accepts; the compose calls are `refCompose`, `refAuto` and `refDirect` (the
last after checking that the body's definitions pass `Build`). -/
def scriptStep (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String) (Mg : MergeFn N A)
    (b : Bld N A) : Op N A → Except String (Bld N A)
  | .place p => .ok { b with places := appendNew b.places [p] }
  | .trans d =>
    match Build d.toTrans with
    | some m => .error m
    | none => .ok { b with places := appendNew b.places d.namedPlaces, defs := b.defs ++ [d] }
  | .terminal p => .ok { b with places := appendNew b.places [p], terminals := b.terminals ++ [p] }
  | .fuse s => (refDeclFusion tyOf s).map fun s' => { b with fusions := b.fusions ++ [s'] }
  | .compose I ports chans => refCompose tyOf Build Mg b I ports chans
  | .composeAuto I cs => refAuto Nm tyOf Build Mg b I cs
  | .composeDirect S =>
    match S.defs.findSome? (fun d => Build d.toTrans) with
    | some m => .error m
    | none => refDirect Nm tyOf b S

/-- The fusion stage of `build()`: the builder's content unchanged when no set is declared (every
runtime skips fusion then), `refFuse` otherwise. -/
def fuseStage (Build : Trans N → Option String) (b : Bld N A) : Except String (FuseNet N A) :=
  if b.fusions.isEmpty then .ok ⟨b.places, b.defs, b.terminals⟩
  else refFuse Build b.fusions ⟨b.places, b.defs, b.terminals⟩

/-- The names of the fusion members fusion removes: every member the substitution moves. -/
def removedNames (Nm : Naming N) (b : Bld N A) : List String :=
  ((b.fusions.flatMap (·.members)).filter fun p => decide (refSubst b.fusions p ≠ p)).map Nm.name

/-- The membership map of the built net ([MOD-026]): the entry of `memberOf`, dropped for a
fusion member fusion removed (Rust `build_with_fusion`, by name). -/
def memberMap (Nm : Naming N) (b : Bld N A) (n : String) : Option String :=
  if n ∈ removedNames Nm b then none else memberOf b.contrib n

/-- **The [MOD-027] rejection**, the text all three runtimes share: the retired place, its port,
the instance and the caller place to use instead. -/
def retiredMsg (Nm : Naming N) (r : Retired N) : String :=
  s!"place '{Nm.name r.place}' is port '{r.port}' of instance '{r.pfx}', bound to host place '{Nm.name r.caller}' at compose; reference '{Nm.name r.caller}' instead"

/-- **`build()`**: fusion, then the reference net builder on the fused content (the [EXEC-042]
terminal check and the collected places), then the [MOD-027] retired-port check on the fused
definitions; the composed net carries the correspondences and the membership map. -/
def finish (Nm : Naming N) (Build : Trans N → Option String) (b : Bld N A) :
    Except String (ComposedNet N A) :=
  match fuseStage Build b with
  | .error m => .error m
  | .ok X =>
    match refNetBuild (netOf X) with
    | .error m => .error m
    | .ok net =>
      match retiredHit b.retired X.defs with
      | some r => .error (retiredMsg Nm r)
      | none => .ok ⟨net, X.defs.map (·.corr), memberMap Nm b⟩

/-- **The reference build script** ([MOD-023]): the calls folded over a new builder, then
`build()`. -/
def buildScript (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) : ScriptFn N A := fun ops =>
  match ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | .error m => .error m
  | .ok b => finish Nm Build b

/- The reference build script is the witness model of the build-script blocks. -/
#spec_witness buildScript

end Script

/-! ## The calls, one by one -/

section StepEq

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}
  {b : Bld N A}

theorem step_compose (I : Instance N A) (ports : List (String × N))
    (chans : List (String × CDef N A)) :
    scriptStep Nm tyOf Build Mg b (.compose I ports chans) = refCompose tyOf Build Mg b I ports chans :=
  rfl

theorem step_composeAuto (I : Instance N A) (cs : List String) :
    scriptStep Nm tyOf Build Mg b (.composeAuto I cs) = refAuto Nm tyOf Build Mg b I cs := rfl

/-- A direct composition whose body passes `Build` is `refDirect`. -/
theorem step_composeDirect {S : SubnetDef N A} (hS : ∀ d ∈ S.defs, Build d.toTrans = none) :
    scriptStep Nm tyOf Build Mg b (.composeDirect S) = refDirect Nm tyOf b S := by
  have : S.defs.findSome? (fun d => Build d.toTrans) = none := List.findSome?_eq_none_iff.2 hS
  simp only [scriptStep, this]

/-- A transition `Build` accepts is added with its arc places. -/
theorem step_trans {d : CDef N A} (hd : Build d.toTrans = none) :
    scriptStep Nm tyOf Build Mg b (.trans d) =
      .ok { b with places := appendNew b.places d.namedPlaces, defs := b.defs ++ [d] } := by
  simp only [scriptStep, hd]

/-- A transition `Build` rejects fails the call with `Build`'s message. -/
theorem step_trans_error {d : CDef N A} {m : String} (hd : Build d.toTrans = some m) :
    scriptStep Nm tyOf Build Mg b (.trans d) = .error m := by
  simp only [scriptStep, hd]

end StepEq

/-! ## Lemmas: folds in `Except` -/

section FoldLemmas

variable {ε α β : Type}

theorem foldlM_except_cons (f : β → α → Except ε β) (s : β) (a : α) (l : List α) :
    (a :: l).foldlM f s = (match f s a with | .error e => .error e | .ok s' => l.foldlM f s') := by
  rw [List.foldlM_cons]
  cases f s a <;> rfl

/-- A property every successful call keeps holds after every successful fold. -/
theorem foldlM_except_inv (f : β → α → Except ε β) (P : β → Prop)
    (hf : ∀ s a s', P s → f s a = .ok s' → P s') :
    ∀ (l : List α) (s s' : β), P s → l.foldlM f s = .ok s' → P s'
  | [], s, s', hs, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hs
  | a :: l, s, s', hs, h => by
    rw [foldlM_except_cons] at h
    cases ha : f s a with
    | error e => rw [ha] at h; cases h
    | ok t =>
      rw [ha] at h
      exact foldlM_except_inv f P hf l t s' (hf s a t hs ha) h

/-- A fold whose calls all succeed and keep a relation to a pure fold succeeds, related to it. -/
theorem foldlM_except_sim {γ : Type} (f : β → α → Except ε β) (g : γ → α → γ)
    (R : β → γ → Prop) (Q : α → Prop)
    (hf : ∀ s c a, R s c → Q a → ∃ s', f s a = .ok s' ∧ R s' (g c a)) :
    ∀ (l : List α) (s : β) (c : γ), R s c → (∀ a ∈ l, Q a) →
      ∃ s', l.foldlM f s = .ok s' ∧ R s' (l.foldl g c)
  | [], s, c, hs, _ => ⟨s, rfl, hs⟩
  | a :: l, s, c, hs, hq => by
    obtain ⟨t, ht, hr⟩ := hf s c a hs (hq a List.mem_cons_self)
    obtain ⟨s', h1, h2⟩ :=
      foldlM_except_sim f g R Q hf l t (g c a) hr (fun a' ha' => hq a' (List.mem_cons_of_mem _ ha'))
    refine ⟨s', ?_, h2⟩
    rw [foldlM_except_cons, ht]
    exact h1

end FoldLemmas

/-! ## Lemmas: the invariant -/

section Invariant

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- The reference channel merge returns only definitions `Build` accepts. -/
theorem refMerge_builds (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) :
    MergeBuilds Build (refMerge Build sq cm) :=
  fun _ _ _ h => (refMerge_ok_fields h).2.2.2.2.2.2.2.2.2.2.2

omit [DecidableEq N] [ToString N] in
/-- The empty builder holds no definition. -/
theorem empty_builds : (Bld.empty : Bld N A).Builds Build := fun _ h => by cases h

omit [DecidableEq N] [ToString N] in
/-- A channel merge step keeps a definition `Build` accepts, or replaces it by a merge. -/
theorem mergeStep_builds (hM : MergeBuilds Build Mg) {I : Instance N A}
    {chans : List (String × CDef N A)} {d m : CDef N A} (hd : Build d.toTrans = none)
    (h : mergeStep Mg I chans d = .ok m) : Build m.toTrans = none := by
  unfold mergeStep at h
  split at h
  · exact hM _ _ _ h
  · cases h; exact hd

omit [ToString N] in
/-- The definitions a compose call adds pass `Build`: every rewritten instance definition does,
and so does every merge. -/
theorem bindAssemble_builds (hM : MergeBuilds Build Mg) {b : Bld N A} (hb : b.Builds Build)
    {I : Instance N A} {bm : List (BindEntry N)} {chans : List (String × CDef N A)}
    {ms : List (CDef N A)} (hall : ∀ d ∈ I.defs, Build (rewriteDef bm d).toTrans = none)
    (hms : (I.defs.map (rewriteDef bm)).mapM (mergeStep Mg I chans) = .ok ms) :
    (bindAssemble b ms).Builds Build := by
  intro d hd
  rw [bindAssemble_defs, List.mem_append] at hd
  rcases hd with hd | hd
  · exact hb d hd
  · obtain ⟨x, hx, hxd⟩ := forall₂_mem_right ((mapM_except_ok_iff _ _ _).1 hms) d hd
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hx
    exact mergeStep_builds hM (hall d₀ hd₀) hxd

/-- A successful compose call keeps the invariant. -/
theorem refCompose_builds (hM : MergeBuilds Build Mg) {b b' : Bld N A} (hb : b.Builds Build)
    {I : Instance N A} {ports : List (String × N)} {chans : List (String × CDef N A)}
    (h : refCompose tyOf Build Mg b I ports chans = .ok b') : b'.Builds Build := by
  obtain ⟨-, -, -, -, hall, ms, hms, rfl⟩ := refCompose_ok_iff.1 h
  exact bindAssemble_builds hM hb (fun d hd => (hall d hd).2.2) hms

/-- A successful auto-composition keeps the invariant. -/
theorem refAuto_builds (hM : MergeBuilds Build Mg) {b b' : Bld N A} (hb : b.Builds Build)
    {I : Instance N A} {cs : List String} (h : refAuto Nm tyOf Build Mg b I cs = .ok b') :
    b'.Builds Build := by
  unfold refAuto at h
  split at h
  · split at h
    · obtain ⟨hall, ms, hms, rfl⟩ := applyBind_ok_iff.1 h
      exact bindAssemble_builds hM hb (fun d hd => (hall d hd).2.2) hms
    · exact refCompose_builds hM hb h
  · cases h

omit [ToString N] [ToString T] in
/-- A successful direct composition whose body passes `Build` keeps the invariant. -/
theorem refDirect_builds {b b' : Bld N A} (hb : b.Builds Build) {S : SubnetDef N A}
    (hS : ∀ d ∈ S.defs, Build d.toTrans = none) (h : refDirect Nm tyOf b S = .ok b') :
    b'.Builds Build := by
  obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
  intro d hd
  simp only [directAssemble, List.mem_append] at hd
  rcases hd with hd | hd
  · exact hb d hd
  · exact hS d hd

/-- **Every call keeps the invariant** ([MOD-023] line 1): a builder whose definitions pass
`Build` holds, after any successful call, only definitions that pass `Build`. -/
theorem step_builds (hM : MergeBuilds Build Mg) {b b' : Bld N A} (hb : b.Builds Build)
    {op : Op N A} (h : scriptStep Nm tyOf Build Mg b op = .ok b') : b'.Builds Build := by
  cases op with
  | place p => cases h; exact hb
  | trans d =>
    simp only [scriptStep] at h
    cases hd : Build d.toTrans with
    | some m => rw [hd] at h; cases h
    | none =>
      rw [hd] at h; cases h
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hb e he
      · rw [List.mem_singleton.1 he]; exact hd
  | terminal p => cases h; exact hb
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', -, rfl⟩ := except_map_ok_iff.1 h
    exact hb
  | compose I ports chans => exact refCompose_builds hM hb h
  | composeAuto I cs => exact refAuto_builds hM hb h
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · rename_i hn
      rw [List.findSome?_eq_none_iff] at hn
      exact refDirect_builds hb hn h

/-- Every builder a script reaches holds only definitions that pass `Build`. -/
theorem script_builds (hM : MergeBuilds Build Mg) {ops : List (Op N A)} {b : Bld N A}
    (h : ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty = .ok b) : b.Builds Build :=
  foldlM_except_inv _ _ (fun _ _ _ hs ha => step_builds hM hs ha) ops _ _ empty_builds h

end Invariant

/-! ## Lemmas: `build()` -/

theorem exists_named_map {α : Type} (l : List α) (f : α → TransDef N A) (p : N) :
    (∃ x ∈ l, p ∈ (f x).namedPlaces) ↔ ∃ d ∈ l.map f, p ∈ d.namedPlaces := by
  simp [List.mem_map]


section Finish

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

omit [ToString N] in
/-- The transitions the reference net builder collects from a fused content are its definitions,
in order. -/
theorem netOf_collect_trans (X : FuseNet N A) :
    (netOf X).collect.trans = X.defs.map (·.toTransDef) := by
  simp [NetIn.collect, netOf, defBuilder]

omit [DecidableEq N] [ToString N] in
/-- The terminal clash of a net input reads its transitions only through their definitions. -/
theorem terminalClash_iff_defs {B : TBuilder N A} (inp : NetIn B) :
    inp.TerminalClash ↔ ∃ p ∈ inp.terminals, ∃ d ∈ inp.trans.map B.defOf, d.ConsumesOrReads p := by
  simp only [NetIn.TerminalClash, List.mem_map]
  constructor
  · rintro ⟨p, hp, x, hx, h⟩; exact ⟨p, hp, _, ⟨x, hx, rfl⟩, h⟩
  · rintro ⟨p, hp, _, ⟨x, hx, rfl⟩, h⟩; exact ⟨p, hp, x, hx, h⟩

omit [ToString N] in
/-- The reference net builder rejects a terminal clash with its one message. -/
theorem refNetBuild_of_clash {B : TBuilder N A} {inp : NetIn B} (h : inp.TerminalClash) :
    refNetBuild inp = .error "EXEC-042" := by
  unfold refNetBuild
  rw [if_pos ((terminalClash_iff_any inp).2 h)]

/-- **What `build()` is**: the fusion stage succeeds with `X`, no terminal place of `X` is
consumed from or read, no definition of `X` names a retired place, and the composed net is the
reference net builder's collection of `X` with the correspondences and the membership map. -/
theorem finish_ok_iff {b : Bld N A} {c : ComposedNet N A} :
    finish Nm Build b = .ok c ↔
      ∃ X, fuseStage Build b = .ok X ∧ ¬ (netOf X).TerminalClash ∧
        retiredHit b.retired X.defs = none ∧
        c = ⟨(netOf X).collect, X.defs.map (·.corr), memberMap Nm b⟩ := by
  unfold finish
  cases hf : fuseStage Build b with
  | error m => simp
  | ok X =>
    simp only [Except.ok.injEq, exists_eq_left']
    cases hn : refNetBuild (netOf X) with
    | error m =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hc
      exact absurd (refNetBuild_error_iff.1 ⟨m, hn⟩) hc
    | ok net =>
      obtain ⟨hnc, rfl⟩ := refNetBuild_eq_ok_iff.1 hn
      simp only [hnc, not_false_eq_true, true_and]
      cases hr : retiredHit b.retired X.defs with
      | some r => simp
      | none =>
        simp only [Except.ok.injEq, true_and]
        exact eq_comm

omit [ToString N] in
/-- No definition of `ds` names a retired place exactly when `retiredHit` finds none. -/
theorem retiredHit_eq_none_iff {rs : List (Retired N)} {ds : List (CDef N A)} :
    retiredHit rs ds = none ↔ ∀ d ∈ ds, ∀ p ∈ d.namedPlaces, ∀ r ∈ rs, r.place ≠ p := by
  simp only [retiredHit, List.findSome?_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, ne_eq]

omit [ToString N] in
/-- A record `retiredHit` finds is a record, and an arc of some definition names its place. -/
theorem retiredHit_some {rs : List (Retired N)} {ds : List (CDef N A)} {r : Retired N}
    (h : retiredHit rs ds = some r) : r ∈ rs ∧ ∃ d ∈ ds, r.place ∈ d.namedPlaces := by
  obtain ⟨d, hd, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨p, hp, h2⟩ := List.exists_of_findSome?_eq_some h1
  have he : r.place = p := by simpa using List.find?_some h2
  exact ⟨List.mem_of_find?_eq_some h2, d, hd, he ▸ hp⟩

/-- With no fusion set declared, the fusion stage returns the builder's content unchanged. -/
theorem fuseStage_nil {b : Bld N A} (h : b.fusions = []) :
    fuseStage Build b = .ok ⟨b.places, b.defs, b.terminals⟩ := by
  simp [fuseStage, h]

/-- With a fusion set declared, the fusion stage is the reference fusion. -/
theorem fuseStage_cons {b : Bld N A} (h : b.fusions ≠ []) :
    fuseStage Build b = refFuse Build b.fusions ⟨b.places, b.defs, b.terminals⟩ := by
  simp [fuseStage, List.isEmpty_iff, h]

/-- The fusion stage of a builder whose definitions pass `Build` returns only definitions that
pass `Build` (fusion re-runs `Build` on every rewritten definition, [MOD-061]). -/
theorem fuseStage_builds {b : Bld N A} (hb : b.Builds Build) {X : FuseNet N A}
    (h : fuseStage Build b = .ok X) : ∀ d ∈ X.defs, Build d.toTrans = none := by
  by_cases hf : b.fusions = []
  · rw [fuseStage_nil hf] at h; cases h; exact hb
  · rw [fuseStage_cons hf] at h; exact (refFuse_ok_iff.1 h).2.2.1

/-- A failing fusion stage fails `build()` with its message. -/
theorem finish_fuseError {b : Bld N A} {m : String} (h : fuseStage Build b = .error m) :
    finish Nm Build b = .error m := by
  simp only [finish, h]

/-- **A terminal clash fails `build()`** ([EXEC-042] AC5), after fusion and before the retired
check. -/
theorem finish_terminal {b : Bld N A} {X : FuseNet N A} (hX : fuseStage Build b = .ok X)
    (hc : (netOf X).TerminalClash) : finish Nm Build b = .error "EXEC-042" := by
  simp only [finish, hX, refNetBuild_of_clash hc]

/-- The parts of a built net: the fused definitions in order, their correspondences, the
membership map. -/
theorem finish_trans {b : Bld N A} {c : ComposedNet N A} (h : finish Nm Build b = .ok c) :
    ∃ X, fuseStage Build b = .ok X ∧ c.trans = X.defs.map (·.toTransDef) ∧
      c.corrs = X.defs.map (·.corr) ∧ c.member = memberMap Nm b ∧
      c.terminals = X.terminals.eraseDups := by
  obtain ⟨X, hX, -, -, rfl⟩ := finish_ok_iff.1 h
  exact ⟨X, hX, netOf_collect_trans X, rfl, rfl, rfl⟩

/-- The places of a built net: the fused content's places and terminal places, and every place a
fused definition names, once each. -/
theorem finish_places {b : Bld N A} {c : ComposedNet N A} (h : finish Nm Build b = .ok c) :
    ∃ X, fuseStage Build b = .ok X ∧ c.places.Nodup ∧ ∀ p, p ∈ c.places ↔
      p ∈ X.places ∨ p ∈ X.terminals ∨ ∃ d ∈ X.defs, p ∈ d.namedPlaces := by
  obtain ⟨X, hX, -, -, rfl⟩ := finish_ok_iff.1 h
  refine ⟨X, hX, collect_places_nodup _, fun p => ?_⟩
  show p ∈ (netOf X).collect.places ↔ _
  rw [mem_collect_places]
  constructor
  · rintro (h | h | ⟨x, hx, hp⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · have hx' : x ∈ X.defs.map (·.toTransDef) := hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx'
      exact .inr (.inr ⟨d, hd, hp⟩)
  · rintro (h | h | ⟨d, hd, hp⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨d.toTransDef, List.mem_map.2 ⟨d, hd, rfl⟩, hp⟩)

/-- **Every transition of a built net passes `Build`**, when the builder's do. -/
theorem finish_builds {b : Bld N A} (hb : b.Builds Build) {c : ComposedNet N A}
    (h : finish Nm Build b = .ok c) : ∀ d ∈ c.trans, Build d.toTrans = none := by
  obtain ⟨X, hX, ht, -⟩ := finish_trans h
  intro d hd
  rw [ht, List.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  exact fuseStage_builds hb hX e he

/-- **No arc of a built net names a retired place** ([MOD-027]). -/
theorem finish_retired {b : Bld N A} {c : ComposedNet N A} (h : finish Nm Build b = .ok c) :
    ∀ d ∈ c.trans, ∀ p ∈ d.namedPlaces, ∀ r ∈ b.retired, r.place ≠ p := by
  obtain ⟨X, hX, ht, -⟩ := finish_trans h
  obtain ⟨X', hX', -, hr, -⟩ := finish_ok_iff.1 h
  rw [hX] at hX'; cases hX'
  intro d hd
  rw [ht, List.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  exact retiredHit_eq_none_iff.1 hr e he

/-- **An arc on a retired place fails `build()`** ([MOD-027]): when an arc of a fused definition
names a retired place, the build fails (with the terminal message or the retired one). -/
theorem finish_retired_rejects {b : Bld N A} {X : FuseNet N A} (hX : fuseStage Build b = .ok X)
    {d : CDef N A} (hd : d ∈ X.defs) {p : N} (hp : p ∈ d.namedPlaces) {r : Retired N}
    (hr : r ∈ b.retired) (he : r.place = p) : ∃ m, finish Nm Build b = .error m := by
  apply except_error_of_not_ok
  intro c hc
  obtain ⟨X', hX', -, hn, -⟩ := finish_ok_iff.1 hc
  rw [hX] at hX'; cases hX'
  exact retiredHit_eq_none_iff.1 hn d hd p hp r hr he

/-- **The [MOD-027] message**: with no terminal clash, the first retired record an arc names
fails `build()` with the shared message. -/
theorem finish_retired_msg {b : Bld N A} {X : FuseNet N A} (hX : fuseStage Build b = .ok X)
    (hc : ¬ (netOf X).TerminalClash) {r : Retired N} (hr : retiredHit b.retired X.defs = some r) :
    finish Nm Build b = .error (retiredMsg Nm r) := by
  have hn : refNetBuild (netOf X) = .ok (netOf X).collect := refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩
  simp only [finish, hX, hn, hr]

/-- With nothing retired, the retired check rejects nothing. -/
theorem finish_of_retired_nil {b : Bld N A} (hr : b.retired = []) {X : FuseNet N A}
    (hX : fuseStage Build b = .ok X) (hc : ¬ (netOf X).TerminalClash) :
    finish Nm Build b = .ok ⟨(netOf X).collect, X.defs.map (·.corr), memberMap Nm b⟩ :=
  finish_ok_iff.2 ⟨X, hX, hc, retiredHit_eq_none_iff.2 (fun _ _ _ _ r h => by
    rw [hr] at h; cases h), rfl⟩

end Finish

/-! ## Lemmas: the membership map -/

section Membership

/-- `soleOwner` names `s` exactly when the list holds `s` and nothing else. -/
theorem soleOwner_eq_some_iff {l : List String} {s : String} :
    soleOwner l = some s ↔ s ∈ l ∧ ∀ y ∈ l, y = s := by
  cases l with
  | nil => simp [soleOwner]
  | cons a rest =>
    simp only [soleOwner]
    by_cases h : rest.all (· == a) = true
    · rw [if_pos h]
      rw [List.all_eq_true] at h
      have h' : ∀ x ∈ rest, x = a := fun x hx => by simpa using h x hx
      constructor
      · rintro ⟨⟩
        refine ⟨List.mem_cons_self, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · rfl
        · exact h' y hy
      · rintro ⟨-, hall⟩
        rw [hall a List.mem_cons_self]
    · rw [if_neg h]
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ hall
      apply h
      rw [List.all_eq_true]
      intro y hy
      have h1 := hall y (List.mem_cons_of_mem _ hy)
      have h2 := hall a List.mem_cons_self
      simp [h1, h2]

/-- **The membership entry** ([MOD-026]): node `n` has entry `s` exactly when `s` is recorded for
`n` and no other subnet is. -/
theorem memberOf_eq_some_iff {c : List (String × String)} {n s : String} :
    memberOf c n = some s ↔ (n, s) ∈ c ∧ ∀ s', (n, s') ∈ c → s' = s := by
  have hm : ∀ x, x ∈ memberOwners c n ↔ (n, x) ∈ c := by
    intro x
    simp only [memberOwners, List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨⟨a, x'⟩, ⟨hmem, ha⟩, rfl⟩
      simp only at ha
      subst ha
      exact hmem
    · intro h
      exact ⟨(n, x), ⟨h, rfl⟩, rfl⟩
  rw [memberOf, soleOwner_eq_some_iff, hm]
  simp only [hm]

/-- **The membership map does not depend on the order of the records** ([MOD-026]). -/
theorem memberOf_perm {c c' : List (String × String)} (hp : c.Perm c') (n : String) :
    memberOf c n = memberOf c' n :=
  Option.ext fun s => by simp only [memberOf_eq_some_iff, hp.mem_iff]

variable [DecidableEq N] {Nm : Naming N}

/-- With no fusion set declared, the membership map is the recorded one. -/
theorem memberMap_nil {b : Bld N A} (h : b.fusions = []) (n : String) :
    memberMap Nm b n = memberOf b.contrib n := by
  simp [memberMap, removedNames, h]

/-- The name of a fusion member that fusion removes has no membership entry ([MOD-026], Rust
`build_with_fusion`). -/
theorem memberMap_removed {b : Bld N A} {s : FusionSet N} (hs : s ∈ b.fusions) {p : N}
    (hp : p ∈ s.members) (hne : refSubst b.fusions p ≠ p) : memberMap Nm b (Nm.name p) = none :=
  if_pos (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨s, hs, hp⟩,
    by simpa using hne⟩, rfl⟩)

/-- Any other name keeps its recorded entry. -/
theorem memberMap_kept {b : Bld N A} {n : String} (hn : n ∉ removedNames Nm b) :
    memberMap Nm b n = memberOf b.contrib n :=
  if_neg hn

end Membership

/-! ## Lemmas: what a call keeps -/

section Prefix

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- **A call only appends**: the definitions and the retired records after a successful call are
the old ones followed by new ones ([MOD-027]: a record, once made, stays first). -/
theorem step_prefix {b b' : Bld N A} {op : Op N A} (h : scriptStep Nm tyOf Build Mg b op = .ok b') :
    (∃ l, b'.defs = b.defs ++ l) ∧ ∃ l, b'.retired = b.retired ++ l := by
  cases op with
  | place p => cases h; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | trans d =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · cases h; exact ⟨⟨[d], rfl⟩, ⟨[], by simp⟩⟩
  | terminal p => cases h; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | fuse s =>
    simp only [scriptStep] at h
    obtain ⟨s', -, rfl⟩ := except_map_ok_iff.1 h
    exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | compose I ports chans =>
    obtain ⟨ms, hd, -⟩ := refCompose_shape h
    exact ⟨⟨ms, hd⟩, by rw [refCompose_retired h]; exact addRetired_prefix _ _⟩
  | composeAuto I cs =>
    simp only [scriptStep] at h
    unfold refAuto at h
    split at h
    · split at h
      · obtain ⟨-, ms, -, rfl⟩ := applyBind_ok_iff.1 h
        exact ⟨⟨ms, rfl⟩, ⟨[], by simp [bindAssemble]⟩⟩
      · obtain ⟨ms, hd, -⟩ := refCompose_shape h
        exact ⟨⟨ms, hd⟩, by rw [refCompose_retired h]; exact addRetired_prefix _ _⟩
    · cases h
  | composeDirect S =>
    simp only [scriptStep] at h
    split at h
    · cases h
    · obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
      exact ⟨⟨S.defs, rfl⟩, ⟨[], by simp [directAssemble]⟩⟩

/-- **A script only appends**: after any successful script from `b₀`, the definitions and retired
records of `b₀` come first, as they were. -/
theorem script_prefix {ops : List (Op N A)} {b₀ b : Bld N A}
    (h : ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok b) :
    (∃ l, b.defs = b₀.defs ++ l) ∧ ∃ l, b.retired = b₀.retired ++ l := by
  refine foldlM_except_inv _ (fun s : Bld N A => (∃ l, s.defs = b₀.defs ++ l) ∧
    ∃ l, s.retired = b₀.retired ++ l) ?_ ops b₀ b ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩ h
  rintro s a s' ⟨⟨l, hl⟩, ⟨k, hk⟩⟩ ha
  obtain ⟨⟨l', hl'⟩, ⟨k', hk'⟩⟩ := step_prefix ha
  exact ⟨⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩, ⟨k ++ k', by rw [hk', hk, List.append_assoc]⟩⟩

end Prefix

/-! ## Lemmas: the script -/

section ScriptLemmas

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

/-- **What the build script is**: every call succeeds from a new builder, reaching `b`, and
`build()` on `b` returns the net. -/
theorem buildScript_ok_iff {ops : List (Op N A)} {c : ComposedNet N A} :
    buildScript Nm tyOf Build Mg ops = .ok c ↔
      ∃ b, ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty = .ok b ∧ finish Nm Build b = .ok c := by
  unfold buildScript
  cases h : ops.foldlM (scriptStep Nm tyOf Build Mg) Bld.empty with
  | error m => simp
  | ok b => simp

/-- **Every transition of a composed net passes the transition builder's check** ([MOD-023] line
1): whatever the script, when the merge returns only definitions `Build` accepts. -/
theorem buildScript_builds (hM : MergeBuilds Build Mg) {ops : List (Op N A)}
    {c : ComposedNet N A} (h : buildScript Nm tyOf Build Mg ops = .ok c) :
    ∀ d ∈ c.trans, Build d.toTrans = none := by
  obtain ⟨b, hb, hf⟩ := buildScript_ok_iff.1 h
  exact finish_builds (script_builds hM hb) hf

/-- The reference build script over the reference channel merge: every transition of a composed
net passes `Build`. -/
theorem buildScript_refMerge_builds (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A)
    {ops : List (Op N A)} {c : ComposedNet N A}
    (h : buildScript Nm tyOf Build (refMerge Build sq cm) ops = .ok c) :
    ∀ d ∈ c.trans, Build d.toTrans = none :=
  buildScript_builds (refMerge_builds sq cm) h

end ScriptLemmas

/-! ## Agreement with the reference net builder -/

section Core

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}
  {B : TBuilder N A}

omit [DecidableEq N] [ToString N] [DecidableEq T] [ToString T] in
theorem coreRel_empty : CoreRel (Bld.empty : Bld N A) (NetIn.empty (B := B)) := by
  simp [CoreRel, Bld.empty, NetIn.empty]

/-- One `place`, `trans` or `terminal` call keeps the relation, and succeeds when a transition it
adds passes `Build`. -/
theorem step_ofBOp {b : Bld N A} {inp : NetIn B} (hr : CoreRel b inp) (op : BOp B)
    (hop : ∀ x, op = .trans x → Build (B.defOf x).toTrans = none) :
    ∃ b', scriptStep Nm tyOf Build Mg b (Op.ofBOp op) = .ok b' ∧ CoreRel b' (inp.addOp op) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  cases op with
  | place p =>
    refine ⟨_, rfl, h1, h2, fun q => ?_, h4, h5⟩
    simp only [mem_appendNew, h3, NetIn.addOp, List.mem_append, List.mem_singleton]
    constructor
    · rintro ((h | h | h) | h)
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inl (.inr h)
    · rintro ((h | h) | h | h)
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr (.inl h))
      · exact .inl (.inr (.inr h))
  | trans x =>
    have hb := hop x rfl
    refine ⟨{ b with
        places := appendNew b.places (B.defOf x).namedPlaces
        defs := b.defs ++ [{ toTransDef := B.defOf x, corr := none }] }, ?_, ?_⟩
    · simp only [Op.ofBOp, scriptStep]
      rw [show Build ({ toTransDef := B.defOf x, corr := none } : CDef N A).toTrans =
        Build (B.defOf x).toTrans from rfl, hb]
    · refine ⟨?_, h2, fun q => ?_, h4, h5⟩
      · simp [NetIn.addOp, h1]
      · simp only [mem_appendNew, h3, NetIn.addOp, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ((h | h | ⟨d, hd, hq⟩) | hq)
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr ⟨d, .inl hd, hq⟩)
          · exact .inr (.inr ⟨_, .inr rfl, hq⟩)
        · rintro (h | h | ⟨d, (hd | rfl), hq⟩)
          · exact .inl (.inl h)
          · exact .inl (.inr (.inl h))
          · exact .inl (.inr (.inr ⟨d, hd, hq⟩))
          · exact .inr hq
  | terminal p =>
    refine ⟨_, rfl, h1, ?_, fun q => ?_, h4, h5⟩
    · simp [NetIn.addOp, h2]
    · simp only [mem_appendNew, h3, NetIn.addOp, List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h | h) | h)
        · exact .inl h
        · exact .inr (.inl (.inl h))
        · exact .inr (.inr h)
        · exact .inr (.inl (.inr h))
      · rintro (h | (h | h) | h)
        · exact .inl (.inl h)
        · exact .inl (.inr (.inl h))
        · exact .inr h
        · exact .inl (.inr (.inr h))

/-- A script of `place`, `trans` and `terminal` calls whose transitions pass `Build` succeeds and
reaches a builder related to the reference net builder's input. -/
theorem script_ofBOp (ops : List (BOp B))
    (hB : ∀ x, BOp.trans x ∈ ops → Build (B.defOf x).toTrans = none) :
    ∃ b, (ops.map Op.ofBOp).foldlM (scriptStep Nm tyOf Build Mg) Bld.empty = .ok b ∧
      CoreRel b (NetIn.ofOps ops) := by
  rw [List.foldlM_map]
  exact foldlM_except_sim _ NetIn.addOp CoreRel
    (fun op => ∀ x, op = .trans x → Build (B.defOf x).toTrans = none)
    (fun s c a hs ha => step_ofBOp hs a ha) ops Bld.empty NetIn.empty coreRel_empty
    (fun op hop x hx => hB x (hx ▸ hop))

/-- **Agreement with the reference net builder** ([CORE-040]): on a script of `place`, `trans`
and `terminal` calls whose transitions pass `Build`, the build script fails exactly when the
reference net builder does, with the same message, and otherwise builds the same transitions in
order, the same terminal places and the same places (in some order). There is one net builder:
composition adds calls, not a second builder state. -/
theorem buildScript_core (ops : List (BOp B))
    (hB : ∀ x, BOp.trans x ∈ ops → Build (B.defOf x).toTrans = none) :
    BuiltAgree ((buildScript Nm tyOf Build Mg (ops.map Op.ofBOp)).map (·.toBuiltNet))
      (refNetBuild (NetIn.ofOps ops)) := by
  obtain ⟨b, hfold, h1, h2, h3, h4, h5⟩ := script_ofBOp (Nm := Nm) (tyOf := tyOf) (Mg := Mg) ops hB
  have hX := fuseStage_nil (Build := Build) h5
  have hclash : (netOf ⟨b.places, b.defs, b.terminals⟩).TerminalClash ↔
      (NetIn.ofOps ops).TerminalClash := by
    rw [terminalClash_iff_defs, terminalClash_iff_defs, ← h2, ← h1]
    simp [netOf, defBuilder]
  have hs : buildScript Nm tyOf Build Mg (ops.map Op.ofBOp) = finish Nm Build b := by
    simp only [buildScript, hfold]
  rw [hs]
  by_cases hc : (NetIn.ofOps ops).TerminalClash
  · rw [finish_terminal hX (hclash.2 hc), refNetBuild_of_clash hc]
    rfl
  · rw [finish_of_retired_nil h4 hX (fun h => hc (hclash.1 h)),
      (refNetBuild_eq_ok_iff.2 ⟨hc, rfl⟩ : refNetBuild (NetIn.ofOps ops) = .ok _)]
    refine ⟨?_, ?_, ?_⟩
    · show (netOf ⟨b.places, b.defs, b.terminals⟩).collect.trans = _
      rw [netOf_collect_trans]
      exact h1
    · show (b.terminals).eraseDups = (NetIn.ofOps ops).terminals.eraseDups
      rw [h2]
    · rw [List.perm_ext_iff_of_nodup (collect_places_nodup _) (collect_places_nodup _)]
      intro p
      rw [mem_collect_places, mem_collect_places]
      have ht : (∃ x ∈ (netOf ⟨b.places, b.defs, b.terminals⟩ :
            NetIn (defBuilder (N := N) (A := A))).trans,
            p ∈ (defBuilder.defOf x).namedPlaces) ↔
          ∃ d ∈ b.defs.map (·.toTransDef), p ∈ d.namedPlaces := Iff.rfl
      rw [ht, h1, exists_named_map (NetIn.ofOps ops).trans B.defOf p]
      show (p ∈ b.places ∨ p ∈ b.terminals ∨ _) ↔ _
      rw [h3 p, h2]
      constructor
      · rintro ((h | h | h) | h | h)
        exacts [.inl h, .inr (.inl h), .inr (.inr h), .inr (.inl h), .inr (.inr h)]
      · intro h
        exact .inl h

/-- **Agreement with the reference builders** ([CORE-040]): a script of `place`, `trans` and
`terminal` calls on the reference transition builder's instances, run through the build script
with the reference transition check `refBuild`, gives what the reference net builder gives, up to
the order of places. No premise is left: every instance of the reference transition builder
passes `refBuild`. -/
theorem buildScript_core_ref (Nm : Naming N) (tyOf : N → T) (Mg : MergeFn N A)
    (ops : List (BOp (refTransBuild (N := N) (A := A)))) :
    BuiltAgree ((buildScript Nm tyOf refBuild Mg (ops.map Op.ofBOp)).map (·.toBuiltNet))
      (refNetBuild (NetIn.ofOps ops)) :=
  buildScript_core ops fun x _ => (refBuild_eq_none_iff _).2 (refTransBuild_inst_ok x).1

end Core

/-! ## Re-declaring a built net -/

section Redeclare

variable [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]
  {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String} {Mg : MergeFn N A}

omit [DecidableEq N] [ToString N] in
theorem foldl_addOp_places {B : TBuilder N A} (ps : List N) (inp : NetIn B) :
    (ps.map BOp.place).foldl NetIn.addOp inp = { inp with places := inp.places ++ ps } := by
  induction ps generalizing inp with
  | nil => simp
  | cons p ps ih => simp [NetIn.addOp, ih]

omit [DecidableEq N] [ToString N] in
theorem foldl_addOp_trans {B : TBuilder N A} (xs : List B.I) (inp : NetIn B) :
    (xs.map BOp.trans).foldl NetIn.addOp inp = { inp with trans := inp.trans ++ xs } := by
  induction xs generalizing inp with
  | nil => simp
  | cons x xs ih => simp [NetIn.addOp, ih]

omit [DecidableEq N] [ToString N] in
theorem foldl_addOp_terminals {B : TBuilder N A} (ps : List N) (inp : NetIn B) :
    (ps.map BOp.terminal).foldl NetIn.addOp inp = { inp with terminals := inp.terminals ++ ps } := by
  induction ps generalizing inp with
  | nil => simp
  | cons p ps ih => simp [NetIn.addOp, ih]

/-- The calls that re-declare a built net by hand: its places, then its transitions as
hand-written definitions, then its terminal places. -/
def redeclareOps (c : ComposedNet N A) : List (BOp (defBuilder (N := N) (A := A))) :=
  c.places.map BOp.place ++ c.trans.map BOp.trans ++ c.terminals.map BOp.terminal

omit [DecidableEq N] [ToString N] in
theorem ofOps_redeclare (c : ComposedNet N A) :
    NetIn.ofOps (redeclareOps c) = ⟨c.places, c.trans, c.terminals⟩ := by
  simp only [NetIn.ofOps, redeclareOps, List.foldl_append, foldl_addOp_places, foldl_addOp_trans,
    foldl_addOp_terminals, NetIn.empty, List.nil_append]

/-- **Re-declaring a built net by hand builds the same net** ([MOD-023] line 2): when a script
builds `c`, the script that declares `c`'s places, adds `c`'s transitions as hand-written
definitions and declares `c`'s terminal places builds a net with the same transitions in order,
the same places in some order and the same terminal places, so the same structure for every
firing, timing and verifier facility. -/
theorem buildScript_redeclare (hM : MergeBuilds Build Mg) {ops : List (Op N A)}
    {c : ComposedNet N A} (h : buildScript Nm tyOf Build Mg ops = .ok c) :
    ∃ c', buildScript Nm tyOf Build Mg ((redeclareOps c).map Op.ofBOp) = .ok c' ∧
      c'.trans = c.trans ∧ c'.places.Perm c.places ∧ ∀ p, p ∈ c'.terminals ↔ p ∈ c.terminals := by
  have hbuilt := buildScript_builds hM h
  obtain ⟨b, -, hf⟩ := buildScript_ok_iff.1 h
  obtain ⟨X, hX, hnc, -, hc⟩ := finish_ok_iff.1 hf
  obtain ⟨X', hX', hnodup, hmem⟩ := finish_places hf
  rw [hX] at hX'; cases hX'
  obtain ⟨X'', hX'', ht, -, -, hterm⟩ := finish_trans hf
  rw [hX] at hX''; cases hX''
  have hagree := buildScript_core (Nm := Nm) (tyOf := tyOf) (Mg := Mg) (redeclareOps c)
    (fun x hx => by
      simp only [redeclareOps, List.mem_append, List.mem_map, reduceCtorEq, and_false,
        exists_false, false_or, or_false, BOp.trans.injEq, exists_eq_right] at hx
      exact hbuilt x hx)
  rw [ofOps_redeclare] at hagree
  have hcl : ¬ (⟨c.places, c.trans, c.terminals⟩ :
      NetIn (defBuilder (N := N) (A := A))).TerminalClash := by
    intro hcl'
    apply hnc
    rw [terminalClash_iff_defs] at hcl' ⊢
    obtain ⟨p, hp, d, hd, hcr⟩ := hcl'
    refine ⟨p, ?_, d, ?_, hcr⟩
    · rw [hterm] at hp
      exact List.mem_eraseDups.1 hp
    · have hd' : d ∈ c.trans := by simpa [defBuilder] using hd
      rw [ht] at hd'
      simpa [netOf, defBuilder] using hd'
  rw [(refNetBuild_eq_ok_iff.2 ⟨hcl, rfl⟩ : refNetBuild _ = .ok _)] at hagree
  cases hs : buildScript Nm tyOf Build Mg ((redeclareOps c).map Op.ofBOp) with
  | error m => rw [hs] at hagree; exact absurd hagree (by simp [BuiltAgree, Except.map])
  | ok c' =>
    rw [hs] at hagree
    obtain ⟨h1, h2, h3⟩ := hagree
    refine ⟨c', rfl, ?_, ?_, ?_⟩
    · rw [h1]; simp [NetIn.collect, defBuilder]
    · refine h3.trans ?_
      rw [List.perm_ext_iff_of_nodup (collect_places_nodup _) hnodup]
      intro p
      rw [mem_collect_places]
      constructor
      · rintro (hp | hp | ⟨d, hd, hp⟩)
        · exact hp
        · rw [hmem]; rw [hterm] at hp; exact .inr (.inl (List.mem_eraseDups.1 hp))
        · rw [hmem]
          have hd0 : (show TransDef N A from d) ∈ c.trans := hd
          have hp0 : p ∈ TransDef.namedPlaces (show TransDef N A from d) := hp
          rw [ht] at hd0
          obtain ⟨e, he, hde⟩ := List.mem_map.1 hd0
          rw [← hde] at hp0
          exact .inr (.inr ⟨e, he, hp0⟩)
      · intro hp; exact .inl hp
    · intro p
      rw [h2]
      show p ∈ c.terminals.eraseDups ↔ _
      exact List.mem_eraseDups

end Redeclare

/-! ## Worked examples -/

section Examples

/-- An example definition over named places: name, input arcs, output specification and reset
arcs; `Immediate`, priority 0, passthrough action. -/
def buildExDef (nm : String) (ins : List (NInSpec String)) (out : Option (Out String))
    (resets : List String := []) : CDef String Unit :=
  { core := ⟨nm, ins, [], [], resets⟩, out := out, timing := .immediate, priority := 0,
    action := .passthrough }

/-- The subnet of [MOD-027]'s example: input port `in` over place `IN`, a transition `work` from
`IN` to `OUT`. -/
def buildExAns : SubnetDef String Unit :=
  { name := "ans", places := ["IN", "OUT"],
    defs := [buildExDef "work" [⟨"IN", .one⟩] (some (.place "OUT"))],
    ports := [⟨"in", .input, "IN"⟩], chans := [] }

/-- The subnet instantiated under prefix `answer`. -/
def buildExInst : Instance String Unit := renamedInstance strNaming buildExAns "answer"

/-- The host transition `hub_kill`: takes a token from `go` and clears place `pl`. -/
def buildExKill (pl : String) : CDef String Unit := buildExDef "hub_kill" [⟨"go", .one⟩] none [pl]

/-- The reference build script at places keyed by name, with the reference transition check and
the reference channel merge. -/
def buildExScript : ScriptFn String Unit :=
  buildScript strNaming (fun _ => ()) refBuild
    (refMerge refBuild (seqAct fun a _ => a) (fun _ _ => .ok none))

/-- The error a script ends with, if any. -/
def buildExErr (ops : List (Op String Unit)) : Option String :=
  match buildExScript ops with
  | .error m => some m
  | .ok _ => none

set_option maxRecDepth 20000 in
/-- **An arc on a bound port fails the build** ([MOD-027] AC1): after `answer` is composed with
`in` bound to `A_IN`, a host transition that clears `answer/IN` makes `build()` fail with the
shared message. -/
theorem buildEx_retired_after :
    buildExErr [.compose buildExInst [("in", "A_IN")] [], .trans (buildExKill "answer/IN")] =
      some "place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN' at compose; reference 'A_IN' instead" := by
  decide

set_option maxRecDepth 20000 in
/-- **The same when the arc comes first** ([MOD-027] AC2): adding `hub_kill` before the compose
call fails the same way. -/
theorem buildEx_retired_before :
    buildExErr [.trans (buildExKill "answer/IN"), .compose buildExInst [("in", "A_IN")] []] =
      some "place 'answer/IN' is port 'in' of instance 'answer', bound to host place 'A_IN' at compose; reference 'A_IN' instead" := by
  decide

/-- **Referencing the caller place builds** ([MOD-027] AC4, [MOD-020]): with `hub_kill` clearing
`A_IN`, the net builds; `answer/work` now takes from `A_IN`, and `hub_kill` is added after it. -/
theorem buildEx_host_ok :
    (buildExScript [.compose buildExInst [("in", "A_IN")] [], .trans (buildExKill "A_IN")]).toOption.map
        (fun c => c.trans.map fun d => (d.core.name, d.core.inputs.map (·.place))) =
      some [("answer/work", ["A_IN"]), ("hub_kill", ["go"])] := by
  decide

/-- **The check sees the fused net** ([MOD-027] AC7, first half): when a fusion set lists the
retired place `answer/IN` after `X`, the arc on it now names `X`, and the net builds. -/
theorem buildEx_fused_member :
    (buildExErr [.compose buildExInst [("in", "A_IN")] [], .trans (buildExKill "answer/IN"),
      .fuse ⟨"f", ["X", "answer/IN"]⟩]) = none := by
  decide

/-- **A retired canonical member still fails** ([MOD-027] AC7, second half): when the retired
place is the first member, an arc on the other member is fused onto it and the build fails. -/
theorem buildEx_fused_canonical :
    (buildExErr [.compose buildExInst [("in", "A_IN")] [], .trans (buildExKill "Y"),
      .fuse ⟨"f", ["answer/IN", "Y"]⟩]).isSome = true := by
  decide

/-- Subnet `s/one`: a transition `t1` from `a` to the shared place `pipe`. -/
def buildExOne : SubnetDef String Unit :=
  { name := "s/one", places := ["pipe", "a"],
    defs := [buildExDef "t1" [⟨"a", .one⟩] (some (.place "pipe"))], ports := [], chans := [] }

/-- Subnet `two`: a transition `t2` from the shared place `pipe` to `b`. -/
def buildExTwo : SubnetDef String Unit :=
  { name := "two", places := ["pipe", "b"],
    defs := [buildExDef "t2" [⟨"pipe", .one⟩] (some (.place "b"))], ports := [], chans := [] }

/-- **Membership from direct composition** ([MOD-026]): composing `s/one` and `two` directly, the
shared place `pipe` has no entry, `a` and `t1` belong to `s_one` (the `/` written `_`), `t2` to
`two`; the other order gives the same map. -/
theorem buildEx_membership :
    (buildExScript [.composeDirect buildExOne, .composeDirect buildExTwo]).toOption.map
        (fun c => ["pipe", "a", "t1", "t2"].map c.member) =
      some [none, some "s_one", some "s_one", some "two"] ∧
    (buildExScript [.composeDirect buildExTwo, .composeDirect buildExOne]).toOption.map
        (fun c => ["pipe", "a", "t1", "t2"].map c.member) =
      some [none, some "s_one", some "s_one", some "two"] := by
  decide

/-- **A hand-written net builds as the net builder builds it** ([CORE-040]): declaring `p`, adding
`t` from `p` to `q` and declaring `q` terminal gives the transition `t`, the terminal place `q`
and the places `p`, `q`. -/
theorem buildEx_core :
    (buildExScript [.place "p", .trans (buildExDef "t" [⟨"p", .one⟩] (some (.place "q"))),
      .terminal "q"]).toOption.map
        (fun c => (c.trans.map (·.core.name), c.terminals, c.places.length)) =
      some (["t"], ["q"], 2) := by
  decide

/-- **A terminal place a transition consumes from fails the build** ([EXEC-042] AC5). -/
theorem buildEx_terminal :
    buildExErr [.trans (buildExDef "t" [⟨"p", .one⟩] (some (.place "q"))), .terminal "p"] =
      some "EXEC-042" := by
  decide

/-- **A transition the transition builder rejects is never added** ([MOD-023]): two input arcs on
one place fail the transition builder's check ([CORE-030]), and so the script. -/
theorem buildEx_unbuilt :
    (buildExErr [.trans (buildExDef "t" [⟨"p", .one⟩, ⟨"p", .one⟩] none)]).isSome = true := by
  decide

end Examples

end Libpetri.Reference
