import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeBuild
import Libpetri.Spec.Text.MOD_023

set_option linter.missingDocs true

/-!
# MOD-023: Composition produces a flat net (`spec/11-modular-composition.md`)

MOD-023 is a builder requirement (kind B) over an abstract build-script function
`S : ScriptFn N A` (a script of builder calls, from a new builder, gives the net `build()`
returns or a rejection with a message), the transition builder's check
`Build : Trans N → Option String` and a naming model `Nm : Naming N`. A script is a list of
`Op` calls: declare a place, add a transition, declare a terminal place, declare a fusion set,
compose an instance (explicitly or by auto-binding) or a subnet definition directly. The result
is a `ComposedNet`: core's built net (places, transition definitions in declaration order,
terminal places) and, beside it, the [MOD-031] correspondence of each transition and the
[MOD-026] membership map.

The block has three lines. Line 1: every transition of a net that builds passes `Build`,
whichever calls produced it (composition, channel merge, fusion), which is what the "every
construction path" notes of [EXEC-012], [IO-011] and [IO-012] lean on. Line 2: writing a built
net by hand (declare its places, add its transitions in order with no correspondence, declare its
terminal places) builds a net with the same transitions in the same order, the same places up to
order and the same terminal places. Line 3: on a script that binds no channel ([MOD-021]), the
built net's transitions are, in order, the transitions the calls added (by hand, from a composed
instance, from a directly composed subnet), each with the name, timing, priority and action it was
added with. Line 2 alone compares a built net with what its own hand-written copy builds, so a
loss that the second build repeats would pass it; line 3 ties the build to the calls. Every
consumer that reads only a built net's structure (the firing relations through `BuiltNet.toNet`
and `BuiltNet.toTimed`, the verifier through [MOD-050]) then sees the composed net and its
hand-written equivalent alike (`mod023_sameView`).

The witness is the reference build script `buildScript` (`Reference/ComposeBuild.lean`); the
block holds for every naming model, every transition-builder check and every channel merge that
returns only definitions the check accepts (`mod023_buildScript`). Each line has a mutant: a
builder that never runs the transition builder's checks (it meets lines 2 and 3, not line 1), a
builder that lists a declared place twice when an arc also names it (it meets lines 1 and 3, not
line 2), and a composition that rebuilds every rewritten transition at the default priority (it
meets lines 1 and 2, not line 3). Forbidden as well: a builder that checks only the transitions
added by hand, one that stores a hand-added timing in canonical form, and a fusion that returns
the transitions in name order.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Vocabulary -/

section Vocab

variable {N A : Type}

/-- **A built net written by hand**: the builder calls that declare its places, add its
transitions in order as hand-written definitions (no correspondence, [MOD-031]) and declare its
terminal places ([EXEC-042]). No compose or fusion call is made. -/
def mod023_handScript (b : BuiltNet N A) : List (Op N A) :=
  b.places.map Op.place ++ b.trans.map (fun d => Op.trans { toTransDef := d, corr := none }) ++
    b.terminals.map Op.terminal

/-- **The transitions a call adds**, as the call names them: the transition added by hand, the
definitions of a composed instance in the instance's order ([MOD-020], [MOD-024]), the
definitions of a directly composed subnet in its order ([MOD-025]); none for a place, a terminal
place or a fusion set. -/
def mod023_added : Op N A → List (TransDef N A)
  | .trans d => [d.toTransDef]
  | .compose I _ _ => I.defs.map (·.toTransDef)
  | .composeAuto I _ => I.defs.map (·.toTransDef)
  | .composeDirect S => S.defs.map (·.toTransDef)
  | _ => []

/-- The channel bindings of a call: those of a `compose` call ([MOD-021]), none for any other. -/
def mod023_chans : Op N A → List (String × CDef N A)
  | .compose _ _ chans => chans
  | _ => []

/-- **The definitions of a composed instance**: those of the instance a `compose` or an
auto-compose call composes ([MOD-020], [MOD-024]); none for any other call. -/
def mod023_composed : Op N A → List (CDef N A)
  | .compose I _ _ => I.defs
  | .composeAuto I _ => I.defs
  | _ => []

/-- **What composition and fusion keep of a transition**: its name, timing, priority and action
(the arcs and the output specification are what they rewrite). -/
def mod023_kept (d : TransDef N A) : String × Novel.TimedScg.Timing × Int × Act A :=
  (d.core.name, d.timing, d.priority, d.action)

end Vocab

/-! ## MOD-023: Composition Produces Flat Net -/

requirement MOD_023
  id "MOD-023"
  title "Composition Produces Flat Net"
  kind B
  scope "build() of every enclosing builder, whatever compose(...), fuse(...) and other builder calls were made on it (Java, TypeScript, Rust, Python)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_023.s1, MOD_023.s2, MOD_023.s3
  reading "For every naming model Nm, every transition-builder check Build and every build-script function S (a script of builder calls gives the composed net build() returns, or a rejection):"
          "line 1: if S ops builds the net c, every transition definition d of c passes Build (Build d.toTrans = none);"
          "line 2: if S ops builds the net c, then the hand-written script of c (declare c's places, add c's transitions in order with no correspondence, declare c's terminal places) builds some net c' whose transitions are c's, as a list (so in the same order, each with the same name, arcs, output specification, timing, priority and action), whose places are c's in some order (List.Perm, so each as often), and whose terminal places are c's as a set;"
          "line 3: if no call of ops binds a channel (mod023_chans op = [] for every call), the definitions of the instance of every compose and auto-compose call have pairwise distinct names (mod023_composed), and S ops builds the net c, then the name, timing, priority and action of c's transitions, in order, are those of the transitions the calls of ops add (mod023_added: the hand-added transition, the instance's definitions, the subnet's definitions), in the order of the calls."
  assumes "Model scope. A build-script function (ScriptFn, Reference/ComposeBuild.lean) is one implementation's enclosing builder read as a function of the calls made on it, from a new builder, up to build(): Rust's PetriNet builder and its build (rust/libpetri-core/src/petri_net.rs), Java's PetriNet.Builder (java/src/main/java/org/libpetri/core/PetriNet.java) and TypeScript's builder (typescript/src/core/petri-net.ts); Python rides on Rust. A panic or exception, at a call or at build(), is a rejection (.error msg). The calls are Op: place, transition (a Transition exists only once built, so a hand-added definition has passed Build), terminal place, fusion set (MOD-060), compose with bindings (MOD-020), auto-compose (MOD-024) and direct composition (MOD-025). Each transition call adds one built transition: adding one Transition object twice, which Java and TypeScript keep once in an identity-keyed set (CORE-021), is not a script this block reads. The witness buildScript folds those calls over the builder record of the reference net builder (CORE-040: buildScript_core) and finishes with fusion (MOD-061), the terminal check of EXEC-042 and the retired-port check of MOD-027. The naming model Nm is the place naming the composition calls rename under, a model parameter of every composition block (MOD-010, MOD-024, MOD-025). No line reads it; the block keeps it because the holds theorem may bind only the model parameters it passes to the block, and the witness buildScript renames auto- and direct composition through a naming model, which exists at no type uniformly (Unit has none: two valid prefixes must rename its one place apart). So MOD_023_reference passes its Nm through this binder, and all three lines hold for every naming."
          "Line 1 holds for every Build: the specific rejection messages belong to CORE-030, IO-002, IO-004, EXEC-012 and IO-011 to IO-014 (the list of CORE-022's note), and line 1 is what lets their 'every construction path' notes reach a composed net. Build reads the firing view of a definition only (TransDef.toTrans: arcs, output specification and the reapable bit of the timing), so the checks line 1 reaches are the arc and output-specification checks. A check that reads timing values (the timing check of TIME-001 that EXEC-012's note places in the transition builder, the maximum-duration rejection of 03-timing.md) is not in Build and is out of line 1: every transition was built when it was added, so its timing passed that check then, and line 3 says that composition and fusion keep the timing a transition was added with; the timing of a channel merge is MOD-021's (line 5) and its result is a built transition (MOD-021 line 7). Line 1 is met by construction in the runtimes: a hand-added transition is built, composition rebuilds every rewritten transition through the transition builder (MOD-020), a channel merge returns a built transition (MOD-021), fusion rebuilds every rewritten transition (MOD-061 line 2), and direct composition adds a body's built transitions unchanged (MOD-025). The mutant mod023_noCheckScript, which never runs the checks, builds a fused transition that consumes from and reads one place, which EXEC-012 rejects; mod023_handCheckScript, which checks hand-added transitions and never a rewritten one, does the same and is forbidden."
          "Line 2 compares the structure only. Transitions are compared as a list of TransDef, so name, arcs, output specification, timing, priority, action and declaration order are equal (declaration order is the last tie-break of the ready order, EXEC-002, ruling D32). Places are compared up to order (List.Perm, each place as often) and terminal places as a set: the order of places is not normative (ruling D32), and the reference net builder lists a place once, at its last occurrence. The two records a composed net may carry beside that structure are not compared: the MOD-031 correspondence (a hand-written definition has none, and an action of a composed transition resolves its subnet's declared places through it, where a hand-written action names the actual places) and the MOD-026 membership map (only direct composition records one; the hand-written net has none). That is the sentence of the markdown's first paragraph that the two records 'sit beside that structure and are not part of it', and the reading of 'indistinguishable' and 'same actions' the block takes. The mutant mod023_dupScript, which lists a declared place a second time when an arc also names it (a slip from the set the builders keep their places in to a plain list), meets lines 1 and 3 and breaks line 2: the hand-written copy of a composed net declares every place, so A_IN, answer/OUT and go come out twice. mod023_canonScript, which stores the timing of a hand-added transition in canonical form (Window(0, d) as Deadline(d)) and keeps a composed transition's timing as it comes, breaks lines 2 and 3 and is forbidden: a composed Window(0, 5) transition, written by hand, builds as Deadline(5)."
          "Line 3 ties the build to the calls, which line 2 cannot do: line 2 compares a built net with the net its own hand-written copy builds, so a loss that a second build repeats passes it. Line 3 compares the built transitions with the transitions the calls added: the hand-added one, the instance's transitions in the instance's order for compose and auto-compose (MOD-020 line 1, MOD-024), the body's transitions in the body's order for direct composition (MOD-025 line 1), in the order of the calls; fusion rewrites each transition in place and keeps the order (MOD-061 line 1). It compares name, timing, priority and action only: the arcs and the output specification are rewritten by the bindings (MOD-020) and by fusion (MOD-061), whose blocks state the rewrite. Line 3 is premised on distinct names within each composed instance (rulings D10 and D23, the unique-names assumption), because no builder rejects a subnet body with two transitions of one name and every runtime then stages the instance's rewritten transitions in a map keyed by name, so only one of the two reaches the built net (Rust staged.insert and order in apply_composition, rust/libpetri-core/src/petri_net.rs; Java rewrittenByName in applyComposition, java/src/main/java/org/libpetri/core/PetriNet.java; TypeScript rewrittenByName in applyComposition, typescript/src/core/petri-net.ts), where the reference keeps both. MOD-020 (mod020_fresh) and MOD-024 take the same premise. Direct composition adds a body's transitions one by one (MOD-025) and needs no such premise. A script with a channel binding is out of line 3, since a merged transition takes its name, priority, timing and action from the MOD-021 merge (MOD-021 lines 1, 5 and 6). In the runtimes, Java's SubnetRewriter.rebuildWithName copies timing, priority and action onto every rewritten transition (java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java) and applyFusion collects the rewritten transitions in an insertion-ordered set (SubnetRewriter.java). The mutant mod023_dropPriScript, a composition that rebuilds every rewritten transition at the default priority 0 (CORE-020), meets lines 1 and 2 and breaks line 3: composing a subnet whose transition has priority 5 builds it at priority 0, and the hand-written copy of that net, written from the built net, builds it at 0 too. mod023_nameOrderScript, a fusion that returns the transitions in name order (a slip from an insertion-ordered set to a hash set in applyFusion, or to a name-keyed map in Rust's build_with_fusion), is forbidden by line 3 for the same reason."
          "The paragraph on downstream consumers, reworded under ruling D20 (clash mod-b#11, recommendation MB-6 of the composition map): the executor and the event subsystem run the firing relations, which read a built net through BuiltNet.toNet and BuiltNet.toTimed only, and mod023_sameView shows that for every model of line 2 a net and its hand-written equivalent have the same transitions in the untimed view, the same timing of every transition in the timed view and the same places up to order. The verifier reads the same structure (MOD-050, whose block carries AC4). The exporter MAY read the MOD-026 membership to draw subnet clusters (MOD-040); that is the one stated exception, since every exporter reads it (map_to_graph in rust/libpetri-export/src/mapper.rs, PetriNetGraphMapper.map in java/src/main/java/org/libpetri/export/PetriNetGraphMapper.java, mapToGraph in typescript/src/export/petri-net-mapper.ts). The sentence that compiled representations (CONC-007, CONC-020) are constructed identically, provided the hand-written net declares its places in the order the composed net holds them, follows from line 2 because a compiled net is computed from the built net alone; it is not restated here, as no compiled-net model is in scope. The first paragraph's MUST and the two MUST sentences of the consumer paragraph stay in the markdown as prose; lines 2 and 3, mod023_sameView and the blocks named here are what state them."
          "AC1 (identical place index, transition count, arc topology, bitmap masks and timing arrays of the compiled representations, for a hand-written net that declares its places in the composed net's order) follows from line 2 for the transitions, their arcs and their timing; the place index also depends on place order, which line 2 leaves free: Rust sorts the place names before indexing (CompiledNet::compile in rust/libpetri-runtime/src/compiled_net.rs), Java and TypeScript index the places arcs name in transition order and then the declared ones (the CompiledNet constructors in java/src/main/java/org/libpetri/runtime/CompiledNet.java and typescript/src/runtime/compiled-net.ts), so a hand-written net that declares its places in the composed net's order gets the same index, which is the premise AC1 now states. That part is tested, not proven. AC2 (identical event sequences and final markings, with the hand-written actions naming the actual places) follows from line 2 for every firing semantics that reads only the structure (mod023_sameView); the net of line 2 keeps the composed actions with no correspondence, so it is the structure AC2 compares, not the hand-written net AC2 runs; equality of a run's event sequence, timestamps included, is tested, not proven. AC3 is reworded under ruling D20 (clash mod-b#11): byte-equal DOT when the composed net carries no membership, and the subnet clusters drawn from membership as the allowed difference of a directly composed net; DOT bytes are EXP's and MOD-040's, not this block's. AC4 (identical verification results) is MOD-050's line, which takes MOD-023 line 2 as its premise."
          "No acceptance line. The block is three safety lines on a successful build: a builder that rejects every script meets it. When a script builds is stated by the blocks that own each call: CORE-040 for a hand-written script (buildScript_core), MOD-020 line 9, MOD-021, MOD-024 line 4, MOD-025 line 5 and MOD-061 line 6; that the builder offers build() at all is an existence clause for a coverage theorem, not a line of this block. The test derivation (a composed net N1 and a hand-written equivalent N2 run alike) is MOD_023_nonvacuous on the reference for the structure, and a test for the runs."
  signoff "2026-11-13 27c95050b685c890 ai"
  statement : ∀ {N A : Type}, Naming N → (Trans N → Option String) → ScriptFn N A → Prop :=
    fun {N A} _Nm Build S =>
      (∀ (ops : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
        ∀ d ∈ c.trans, Build d.toTrans = none) ∧
      (∀ (ops : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
        ∃ c' : ComposedNet N A, S (mod023_handScript c.toBuiltNet) = .ok c' ∧
          c'.trans = c.trans ∧ c'.places.Perm c.places ∧ ∀ p, p ∈ c'.terminals ↔ p ∈ c.terminals) ∧
      (∀ (ops : List (Op N A)) (c : ComposedNet N A), (∀ op ∈ ops, mod023_chans op = []) →
        (∀ op ∈ ops, ((mod023_composed op).map (·.core.name)).Nodup) →
        S ops = .ok c → c.trans.map mod023_kept = (ops.flatMap mod023_added).map mod023_kept)

/- The pinned readable form of MOD-023: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_023 : {N A : Type} → Naming N → (Reference.Trans N → Option String) → ScriptFn N A → Prop :=
fun {N A} _Nm Build S =>
  (∀ (ops : List (Op N A)) (c : ComposedNet N A), S ops = Except.ok c → ∀ d ∈ c.trans, Build d.toTrans = none) ∧
    (∀ (ops : List (Op N A)) (c : ComposedNet N A),
        S ops = Except.ok c →
          ∃ c',
            S (mod023_handScript c.toBuiltNet) = Except.ok c' ∧
              c'.trans = c.trans ∧ c'.places.Perm c.places ∧ ∀ (p : N), p ∈ c'.terminals ↔ p ∈ c.terminals) ∧
      ∀ (ops : List (Op N A)) (c : ComposedNet N A),
        (∀ op ∈ ops, mod023_chans op = []) →
          (∀ op ∈ ops, (List.map (fun x => x.core.name) (mod023_composed op)).Nodup) →
            S ops = Except.ok c → List.map mod023_kept c.trans = List.map mod023_kept (List.flatMap mod023_added ops)
-/
#guard_msgs in #print MOD_023

/-! ## The three lines, named -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-023: every transition of a built net passes the transition builder's check. -/
def mod023_line1 (Build : Trans N → Option String) (S : ScriptFn N A) : Prop :=
  ∀ (ops : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
    ∀ d ∈ c.trans, Build d.toTrans = none

/-- Line 2 of MOD-023: a built net written by hand builds the same structure. -/
def mod023_line2 (S : ScriptFn N A) : Prop :=
  ∀ (ops : List (Op N A)) (c : ComposedNet N A), S ops = .ok c →
    ∃ c' : ComposedNet N A, S (mod023_handScript c.toBuiltNet) = .ok c' ∧
      c'.trans = c.trans ∧ c'.places.Perm c.places ∧ ∀ p, p ∈ c'.terminals ↔ p ∈ c.terminals

/-- Line 3 of MOD-023: on a script that binds no channel, the built transitions keep, in order,
the name, timing, priority and action of the transitions the calls added. -/
def mod023_line3 (S : ScriptFn N A) : Prop :=
  ∀ (ops : List (Op N A)) (c : ComposedNet N A), (∀ op ∈ ops, mod023_chans op = []) →
    (∀ op ∈ ops, ((mod023_composed op).map (·.core.name)).Nodup) →
    S ops = .ok c → c.trans.map mod023_kept = (ops.flatMap mod023_added).map mod023_kept

/-- MOD-023 is its three lines. -/
theorem mod023_iff {Nm : Naming N} {Build : Trans N → Option String} {S : ScriptFn N A} :
    MOD_023 Nm Build S ↔ mod023_line1 Build S ∧ mod023_line2 S ∧ mod023_line3 S := Iff.rfl

end Lines

/-! ## The reference -/

section Ref

variable {N A : Type} [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

omit [DecidableEq N] [ToString N] in
/-- The hand-written script of a built net is the re-declaration script of the composition model
(`redeclareOps`), each definition added with no correspondence. -/
theorem mod023_handScript_eq (c : ComposedNet N A) :
    mod023_handScript c.toBuiltNet = (redeclareOps c).map Op.ofBOp := by
  simp only [mod023_handScript, redeclareOps, List.map_append, List.map_map]
  rfl

/-- What a builder's definitions keep, in order. -/
def mod023_keptB (b : Bld N A) : List (String × Novel.TimedScg.Timing × Int × Act A) :=
  b.defs.map fun d => mod023_kept d.toTransDef

omit [ToString N] in
/-- Rewriting an instance's definitions through a binding keeps what line 3 compares. -/
theorem mod023_bind_kept (I : Instance N A) (bm : List (BindEntry N)) :
    (I.defs.map (rewriteDef bm)).map (fun d => mod023_kept d.toTransDef) =
      (I.defs.map (·.toTransDef)).map mod023_kept := by
  simp only [List.map_map]
  rfl

omit [DecidableEq N] [ToString N] in
/-- With no channel binding, the channel-merge pass of a compose call changes nothing. -/
theorem mod023_merge_nil {Mg : MergeFn N A} (I : Instance N A) (l : List (CDef N A)) :
    l.mapM (mergeStep Mg I []) = .ok l := by
  have := mapM_except_pure (mergeStep Mg I []) id l (fun _ _ => rfl)
  simpa using this

/-- **One call keeps what line 3 compares**: a successful call that binds no channel appends to
the builder's definitions exactly the transitions the call adds, up to arcs and output
specification. -/
theorem mod023_step_kept {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String}
    {Mg : MergeFn N A} {b b' : Bld N A} {op : Op N A} (hc : mod023_chans op = [])
    (h : scriptStep Nm tyOf Build Mg b op = .ok b') :
    mod023_keptB b' = mod023_keptB b ++ (mod023_added op).map mod023_kept := by
  cases op with
  | place p => cases h; simp [mod023_keptB, mod023_added]
  | trans d =>
    cases hb : Build d.toTrans with
    | some m => rw [step_trans_error hb] at h; cases h
    | none => rw [step_trans hb] at h; cases h; simp [mod023_keptB, mod023_added]
  | terminal p => cases h; simp [mod023_keptB, mod023_added]
  | fuse s =>
    obtain ⟨s', -, rfl⟩ := except_map_ok_iff.1 h
    simp [mod023_keptB, mod023_added]
  | compose I ports chans =>
    cases hc
    rw [step_compose] at h
    obtain ⟨-, -, -, -, -, ms, hms, rfl⟩ := refCompose_ok_iff.1 h
    rw [mod023_merge_nil] at hms
    cases hms
    simp only [mod023_keptB, mod023_added, retire, bindAssemble_defs, List.map_append]
    rw [mod023_bind_kept]
  | composeAuto I cs =>
    change refAuto Nm tyOf Build Mg b I cs = .ok b' at h
    unfold refAuto at h
    split at h
    · split at h
      · obtain ⟨-, ms, hms, rfl⟩ := applyBind_ok_iff.1 h
        rw [mod023_merge_nil] at hms
        cases hms
        simp only [mod023_keptB, mod023_added, bindAssemble_defs, List.map_append]
        rw [mod023_bind_kept]
      · obtain ⟨-, -, -, -, -, ms, hms, rfl⟩ := refCompose_ok_iff.1 h
        rw [mod023_merge_nil] at hms
        cases hms
        simp only [mod023_keptB, mod023_added, retire, bindAssemble_defs, List.map_append]
        rw [mod023_bind_kept]
    · cases h
  | composeDirect S =>
    cases hf : S.defs.findSome? (fun d => Build d.toTrans) with
    | some m => simp only [scriptStep, hf] at h; cases h
    | none =>
      rw [step_composeDirect (List.findSome?_eq_none_iff.1 hf)] at h
      obtain ⟨-, -, -, -, rfl⟩ := refDirect_ok_iff.1 h
      simp [mod023_keptB, mod023_added, directAssemble, List.map_map]

/-- A script that binds no channel appends, call by call, the transitions its calls add. -/
theorem mod023_script_kept {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String}
    {Mg : MergeFn N A} : ∀ (ops : List (Op N A)) (b₀ b : Bld N A),
    (∀ op ∈ ops, mod023_chans op = []) → ops.foldlM (scriptStep Nm tyOf Build Mg) b₀ = .ok b →
    mod023_keptB b = mod023_keptB b₀ ++ (ops.flatMap mod023_added).map mod023_kept
  | [], b₀, b, _, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | op :: ops, b₀, b, hc, h => by
    rw [foldlM_except_cons] at h
    cases hs : scriptStep Nm tyOf Build Mg b₀ op with
    | error m => rw [hs] at h; cases h
    | ok b₁ =>
      rw [hs] at h
      rw [mod023_script_kept ops b₁ b (fun o ho => hc o (List.mem_cons_of_mem _ ho)) h,
        mod023_step_kept (hc op List.mem_cons_self) hs]
      simp [List.flatMap_cons, List.map_append]

omit [ToString N] in
/-- Fusion keeps the order and what line 3 compares ([MOD-061] line 1, `fuseDef_kept`). -/
theorem mod023_fuse_kept {σ : N → N} : ∀ {l l' : List (CDef N A)},
    List.Forall₂ (fun x y => fuseDef σ x = .ok y) l l' →
    l'.map (fun d => mod023_kept d.toTransDef) = l.map (fun d => mod023_kept d.toTransDef)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons hxy hr => by
    obtain ⟨hn, -, -, -, -, ht, hp, ha, -⟩ := fuseDef_kept hxy
    rw [List.map_cons, List.map_cons, mod023_fuse_kept hr]
    simp only [mod023_kept, hn, ht, hp, ha]

/-- The fusion stage of `build()` keeps what line 3 compares. -/
theorem mod023_fuseStage_kept {Build : Trans N → Option String} {b : Bld N A} {X : FuseNet N A}
    (h : fuseStage Build b = .ok X) :
    X.defs.map (fun d => mod023_kept d.toTransDef) = mod023_keptB b := by
  unfold fuseStage at h
  split at h
  · cases h; rfl
  · obtain ⟨-, hm, -, -⟩ := refFuse_ok_iff.1 h
    exact mod023_fuse_kept ((mapM_except_ok_iff _ _ _).1 hm)

/-- **The reference meets line 3** for every naming model, token-type map, transition-builder
check and channel merge. -/
theorem mod023_buildScript_kept (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) : mod023_line3 (buildScript Nm tyOf Build Mg) := by
  intro ops c hc _ h
  unfold buildScript at h
  split at h
  · cases h
  · rename_i b hb
    obtain ⟨X, hX, ht, -⟩ := finish_trans h
    rw [ht, List.map_map]
    exact (mod023_fuseStage_kept hX).trans (mod023_script_kept ops _ _ hc hb)

/-- **The reference build script meets MOD-023** for every naming model, every token-type map,
every transition-builder check and every channel merge that returns only definitions the check
accepts ([MOD-021]). -/
theorem mod023_buildScript (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : MergeFn N A) (hM : MergeBuilds Build Mg) :
    MOD_023 Nm Build (buildScript Nm tyOf Build Mg) :=
  ⟨fun _ _ h => buildScript_builds hM h,
    fun _ c h => by rw [mod023_handScript_eq]; exact buildScript_redeclare hM h,
    mod023_buildScript_kept Nm tyOf Build Mg⟩

end Ref

/-- ✓ The reference build script satisfies MOD-023 for every naming model and every
transition-builder check. Compose the instance `answer` into a builder that already has a hand
added transition, and build: every transition of the net passes the transition builder's checks.
Write the built net out by hand (its places, its transitions in the same order, its terminal
places) and build that: the same transitions come out in the same order, with the same places and
terminal places. With no channel bound, the transitions are the hand added one and then the
instance's, each with the name, timing, priority and action it was added with. -/
@[evidence holds MOD_023]
theorem MOD_023_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N)
    (Build : Trans N → Option String) :
    MOD_023 Nm Build (buildScript Nm (fun _ : N => ()) Build
      (refMerge (A := A) Build (seqAct fun a _ => a) (fun _ _ => .ok none))) :=
  mod023_buildScript Nm _ Build _ (refMerge_builds _ _)

/-! ## A consequence for every model of line 2 -/

section Consequences

variable {N A : Type}

/-- **Composed and hand-written nets look alike to every structural consumer**: for every model
of line 2, a net that builds and its hand-written equivalent have the same transitions in the
untimed firing view (`BuiltNet.toNet`), the same places up to order, and, at every deadline
tolerance, the same timing of every transition in the timed view (`BuiltNet.toTimed`). A
composed pipeline `a/work`, `b/work` and the same two transitions written by hand fire alike under
every firing relation that reads the net only. -/
theorem mod023_sameView {S : ScriptFn N A} (h2 : mod023_line2 S) {ops : List (Op N A)}
    {c : ComposedNet N A} (hc : S ops = .ok c) :
    ∃ c' : ComposedNet N A, S (mod023_handScript c.toBuiltNet) = .ok c' ∧
      c'.toNet.transitions = c.toNet.transitions ∧ c'.toNet.places.Perm c.toNet.places ∧
      ∀ tol, (c'.toTimed tol).timing = (c.toTimed tol).timing := by
  obtain ⟨c', hc', ht, hp, -⟩ := h2 ops c hc
  refine ⟨c', hc', ?_, hp, fun tol => ?_⟩
  · show c'.trans.map TransDef.toTrans = c.trans.map TransDef.toTrans
    rw [ht]
  · show (fun t : Trans N => ((c'.trans.find? (·.core.name == t.core.name)).map (·.timing)).getD
        .immediate) =
      (fun t : Trans N => ((c.trans.find? (·.core.name == t.core.name)).map (·.timing)).getD
        .immediate)
    rw [ht]

end Consequences

/-! ## Worked examples on the reference -/

/- `mod023_ref`: the reference build script at places keyed by name, with the reference transition
check and the reference channel merge. -/
set_option quotPrecheck false in
local notation "mod023_ref" =>
  buildScript strNaming (fun _ : String => ()) refBuild
    (refMerge (A := Unit) refBuild (seqAct fun a _ => a) (fun _ _ => Except.ok none))

/-- The composed script of the examples: instance `answer` of the subnet whose transition `work`
takes from its input port `in`, composed with `in` bound to the caller place `A_IN`, then a
hand-written transition `hub_kill` that takes from `go` and clears `A_IN`. -/
def mod023_exOps : List (Op String Unit) :=
  [.compose buildExInst [("in", "A_IN")] [], .trans (buildExKill "A_IN")]

/-- A script whose fusion would make a transition consume from and read one place: transition `t`
takes from `a` and reads `b`, then `a` and `b` are fused. -/
def mod023_exFuse : List (Op String Unit) :=
  [.trans (fuseExDef "t" [⟨"a", .one⟩] none ["b"]), .fuse ⟨"ab", ["a", "b"]⟩]

/-- A fused script whose declaration order is not name order: `t2` takes from `a` into `x`, `t1`
takes from `b` into `y`, then `a` and `b` are fused into set `ab` (canonical member `a`). -/
def mod023_exOrder : List (Op String Unit) :=
  [.trans (fuseExDef "t2" [⟨"a", .one⟩] (some (.place "x"))),
   .trans (fuseExDef "t1" [⟨"b", .one⟩] (some (.place "y"))),
   .fuse ⟨"ab", ["a", "b"]⟩]

/-- Subnet `pri`: input port `in` over `IN`, transition `work` from `IN` to `OUT` at priority 5. -/
def mod023_exPriSub : SubnetDef String Unit :=
  { name := "pri", places := ["IN", "OUT"],
    defs := [{ buildExDef "work" [⟨"IN", .one⟩] (some (.place "OUT")) with priority := 5 }],
    ports := [⟨"in", .input, "IN"⟩], chans := [] }

/-- A composed script with a non-default priority: instance `answer` of `pri`, `in` bound to
`A_IN`. -/
def mod023_exPri : List (Op String Unit) :=
  [.compose (renamedInstance strNaming mod023_exPriSub "answer") [("in", "A_IN")] []]

/-- What the examples compare of a transition: its name, the places of its input arcs and its
priority. -/
def mod023_view (d : TransDef String Unit) : String × List String × Int :=
  (d.core.name, d.core.inputs.map (·.place), d.priority)

/-- What the line 3 examples compare of a transition: its name and its priority. -/
def mod023_namePri (d : TransDef String Unit) : String × Int :=
  (d.core.name, d.priority)

set_option maxRecDepth 20000 in
/-- ✓ All three lines of MOD-023 are exercised by the reference. Composing instance `answer` with
its input port bound to `A_IN` and then adding `hub_kill` builds a net whose transitions are
`answer/work`, now taking from `A_IN`, and `hub_kill`, both accepted by the transition builder
(line 1). Writing that net by hand, its places, then `answer/work` and `hub_kill` as plain
transitions, builds the same two transitions in the same order with the same arcs and priorities
(line 2). A transition that takes from `a` and reads `b` builds, but fusing `a` and `b` makes it
take from and read `a`, which the transition builder rejects ([EXEC-012]), so the reference
refuses to build that script. Adding `t2` and then `t1` and fusing their input places keeps the
order `t2`, `t1`; composing a subnet whose transition `work` has priority 5 builds `answer/work`
at priority 5 (line 3). -/
@[evidence nonvacuous MOD_023]
theorem MOD_023_nonvacuous :
    (mod023_ref mod023_exOps).toOption.map
        (fun c => c.trans.map fun d => (mod023_view d, (refBuild d.toTrans).isNone)) =
      some [(("answer/work", ["A_IN"], 0), true), (("hub_kill", ["go"], 0), true)] ∧
    (match mod023_ref mod023_exOps with
      | .ok c => (mod023_ref (mod023_handScript c.toBuiltNet)).toOption.map
          (fun c' => decide (c'.trans.map mod023_view = c.trans.map mod023_view))
      | .error _ => none) = some true ∧
    (mod023_ref mod023_exFuse).toOption.isNone = true ∧
    (mod023_ref mod023_exOrder).toOption.map (fun c => c.trans.map mod023_view) =
      some [("t2", ["a"], 0), ("t1", ["a"], 0)] ∧
    (mod023_ref mod023_exPri).toOption.map (fun c => c.trans.map mod023_namePri) =
      some [("answer/work", 5)] := by
  decide

/-! ## Wrong builders -/

section Mutants

variable {N A : Type}

/-- Mutant reading: MOD-023 without line 1 (a built net may hold a transition the transition
builder rejects). -/
def MOD_023_mutant_noCheck (_ : Naming N) (_ : Trans N → Option String) (S : ScriptFn N A) :
    Prop :=
  mod023_line2 S ∧ mod023_line3 S

/-- Mutant reading: MOD-023 without line 2 (a composed net need not build as its hand-written
equivalent does). -/
def MOD_023_mutant_noRedeclare (_ : Naming N) (Build : Trans N → Option String)
    (S : ScriptFn N A) : Prop :=
  mod023_line1 Build S ∧ mod023_line3 S

/-- Mutant reading: MOD-023 without line 3 (the build need not keep the order, name, timing,
priority and action of the transitions the calls added). -/
def MOD_023_mutant_noKept (_ : Naming N) (Build : Trans N → Option String)
    (S : ScriptFn N A) : Prop :=
  mod023_line1 Build S ∧ mod023_line2 S

end Mutants

/-! ### Line 1 -/

/-- The builder that never runs the transition builder's checks: the reference build script with
a check that accepts everything, at every call, in every channel merge and in fusion. -/
def mod023_noCheckScript : ScriptFn String Unit :=
  buildScript strNaming (fun _ => ()) (fun _ => none)
    (refMerge (fun _ => none) (seqAct fun a _ => a) (fun _ _ => .ok none))

/-- The builder that checks every transition added by hand and never again: a hand-added
transition the reference check rejects fails the script, and otherwise nothing is checked, so a
transition that fusion or composition rewrote is never rebuilt. -/
def mod023_handCheckScript : ScriptFn String Unit := fun ops =>
  match ops.findSome? (fun op => match op with
      | .trans d => refBuild d.toTrans
      | _ => none) with
  | some m => .error m
  | none => mod023_noCheckScript ops

set_option maxRecDepth 20000 in
/-- A transition that takes from `a` and reads `b`, with `a` and `b` fused, builds under the
builder that never checks, and the built transition takes from and reads `a`. -/
theorem mod023_noCheck_fused :
    (mod023_noCheckScript mod023_exFuse).toOption.map
        (fun c => c.trans.all fun d => (refBuild d.toTrans).isNone) = some false := by
  decide

/-- A builder that holds a built net with a transition the reference check rejects breaks
line 1. -/
theorem mod023_not_line1 {S : ScriptFn String Unit} {ops : List (Op String Unit)}
    (hS : (S ops).toOption.map (fun c => c.trans.all fun d => (refBuild d.toTrans).isNone) =
      some false) : ¬ mod023_line1 refBuild S := by
  intro h
  cases hs : S ops with
  | error m => rw [hs] at hS; cases hS
  | ok c =>
    rw [hs] at hS
    have hall : (c.trans.all fun d => (refBuild d.toTrans).isNone) = true :=
      List.all_eq_true.2 fun d hd => by rw [h ops c hs d hd]; rfl
    simp only [Except.toOption, Option.map_some, hall, Option.some.injEq] at hS
    cases hS

/-- ✗ The builder that never runs the transition builder's checks kills the mutant: it meets
lines 2 and 3 (written by hand, a net it built builds again the same way, and its transitions are
the ones the calls added), but it builds the script that adds a transition taking from `a` and
reading `b` and then fuses `a` and `b`, and the built transition takes from and reads `a`, which
the reference transition builder rejects ([EXEC-012]). -/
@[evidence mutant MOD_023]
theorem MOD_023_mutant_noCheck_killed :
    MOD_023_mutant_noCheck strNaming refBuild mod023_noCheckScript ∧
      ¬ MOD_023 strNaming refBuild mod023_noCheckScript :=
  ⟨(mod023_buildScript strNaming _ _ _ (refMerge_builds _ _)).2,
    fun h => mod023_not_line1 mod023_noCheck_fused h.1⟩

set_option maxRecDepth 20000 in
/-- ✗ The builder that checks only the transitions added by hand is forbidden: the transition `t`
that takes from `a` and reads `b` passes the check when it is added, but after `a` and `b` are
fused it takes from and reads `a`, the builder never checks it again, and the built net holds a
transition the reference transition builder rejects ([EXEC-012]). -/
@[evidence forbids MOD_023]
theorem MOD_023_forbids_handCheckOnly : ¬ MOD_023 strNaming refBuild mod023_handCheckScript :=
  fun h => mod023_not_line1 (ops := mod023_exFuse) (by decide) h.1

/-! ### Line 2 -/

/-- The places a script declares with a `place` call. -/
def mod023_declared (ops : List (Op String Unit)) : List String :=
  ops.filterMap fun o => match o with
    | .place p => some p
    | _ => none

/-- The builder that lists a declared place a second time when an arc also names it: the
reference build script, then every place declared by a `place` call that some transition of the
built net names is listed again (a slip from the set the builders keep their places in to a plain
list). A composed net whose places were never declared by hand has no duplicate. -/
def mod023_dupScript : ScriptFn String Unit := fun ops =>
  (buildExScript ops).map fun c =>
    { c with places := c.places ++ (mod023_declared ops).filter fun p =>
        c.trans.any fun d => decide (p ∈ d.namedPlaces) }

/-- The duplicating builder meets line 1: its transitions are the reference's. -/
theorem mod023_dup_line1 : mod023_line1 refBuild mod023_dupScript := by
  intro ops c h d hd
  cases hs : buildExScript ops with
  | error m => simp [mod023_dupScript, hs, Except.map] at h
  | ok c₀ =>
    simp only [mod023_dupScript, hs, Except.map, Except.ok.injEq] at h
    subst h
    exact buildScript_builds (refMerge_builds _ _) hs d hd

/-- The duplicating builder meets line 3: its transitions are the reference's. -/
theorem mod023_dup_line3 : mod023_line3 mod023_dupScript := by
  intro ops c hc hn h
  cases hs : buildExScript ops with
  | error m => simp [mod023_dupScript, hs, Except.map] at h
  | ok c₀ =>
    simp only [mod023_dupScript, hs, Except.map, Except.ok.injEq] at h
    subst h
    exact mod023_buildScript_kept _ _ _ _ ops c₀ hc hn hs

set_option maxRecDepth 20000 in
/-- The composed net of `mod023_exOps` and its hand-written copy, under the duplicating builder,
do not have the same places up to order. -/
theorem mod023_dup_differs :
    (match mod023_dupScript mod023_exOps with
      | .ok c => (mod023_dupScript (mod023_handScript c.toBuiltNet)).toOption.map
          (fun c' => c'.places.isPerm c.places)
      | .error _ => none) = some false := by
  decide

/-- ✗ The builder that lists a declared place twice when an arc also names it kills the mutant:
it meets lines 1 and 3 (its transitions are the reference's), but composing instance `answer`
and adding `hub_kill` builds a net that declares no place by hand, while its hand-written copy
declares every place, and `A_IN`, `answer/OUT` and `go`, which arcs name, come out twice, so the
two nets do not have the same places. -/
@[evidence mutant MOD_023]
theorem MOD_023_mutant_noRedeclare_killed :
    MOD_023_mutant_noRedeclare strNaming refBuild mod023_dupScript ∧
      ¬ MOD_023 strNaming refBuild mod023_dupScript := by
  refine ⟨⟨mod023_dup_line1, mod023_dup_line3⟩, fun h => ?_⟩
  have e := mod023_dup_differs
  cases hs : mod023_dupScript mod023_exOps with
  | error m => rw [hs] at e; cases e
  | ok c =>
    obtain ⟨c', hc', -, hp, -⟩ := h.2.1 _ c hs
    rw [hs] at e
    simp only [hc', Except.toOption, Option.map_some, Option.some.injEq] at e
    rw [List.isPerm_iff.2 hp] at e
    cases e

/-- A timing in canonical form: `Window(0, d)`, the interval `[0, d]`, is written `Deadline(d)`
([MOD-021]'s shape table); every other timing is kept. -/
def mod023_canon : Novel.TimedScg.Timing → Novel.TimedScg.Timing
  | .window e d => if e = 0 then .deadline d else .window e d
  | t => t

/-- A call with the timing of a hand-added transition put in canonical form. -/
def mod023_canonOp : Op String Unit → Op String Unit
  | .trans d => .trans { d with timing := mod023_canon d.timing }
  | op => op

/-- The builder that stores the timing of a transition added by hand in canonical form and keeps
the timing a composed transition brings in as it is: the reference build script on the calls
with every hand-added timing put in canonical form. -/
def mod023_canonScript : ScriptFn String Unit := fun ops => buildExScript (ops.map mod023_canonOp)

/-- Subnet `win`: input port `in` over place `IN`, a transition `work` from `IN` to `OUT` that may
fire from 0 to 5 ms after it is enabled, written `Window(0, 5)`. -/
def mod023_exWin : SubnetDef String Unit :=
  { name := "win", places := ["IN", "OUT"],
    defs := [{ buildExDef "work" [⟨"IN", .one⟩] (some (.place "OUT")) with
      timing := Novel.TimedScg.Timing.window 0 5 }],
    ports := [⟨"in", .input, "IN"⟩], chans := [] }

/-- The composed script of the canonicalising builder: instance `answer` of `win`, with `in` bound
to `A_IN`. -/
def mod023_exCompose : List (Op String Unit) :=
  [.compose (renamedInstance strNaming mod023_exWin "answer") [("in", "A_IN")] []]

set_option maxRecDepth 20000 in
/-- Composed with the canonicalising builder, `answer/work` keeps `Window(0, 5)`; written by hand,
the same transition is stored as `Deadline(5)`. -/
theorem mod023_canon_differs :
    (match mod023_canonScript mod023_exCompose with
      | .ok c => (mod023_canonScript (mod023_handScript c.toBuiltNet)).toOption.map
          (fun c' => (c.trans.map TransDef.timing, c'.trans.map TransDef.timing))
      | .error _ => none) = some ([.window 0 5], [.deadline 5]) := by
  decide

/-- ✗ The builder that stores a hand-added timing in canonical form, and a composed one as it
comes, is forbidden: composing instance `answer` of a subnet whose transition `work` has timing
`Window(0, 5)` builds `answer/work` with `Window(0, 5)`, while writing the same net by hand builds
it with `Deadline(5)`, so the composed net is not the net its hand-written equivalent builds. -/
@[evidence forbids MOD_023]
theorem MOD_023_forbids_canonTiming : ¬ MOD_023 strNaming refBuild mod023_canonScript := by
  intro h
  have e := mod023_canon_differs
  cases hs : mod023_canonScript mod023_exCompose with
  | error m => rw [hs] at e; cases e
  | ok c =>
    obtain ⟨c', hc', ht, -⟩ := h.2.1 _ c hs
    simp only [hs, hc', Except.toOption, Option.map_some, ht, Option.some.injEq,
      Prod.mk.injEq] at e
    rw [e.1] at e
    cases e.2

/-! ### Line 3 -/

/-- A builder whose built net, on a script that binds no channel, differs from the transitions the
calls added in a name, in the order or in a priority breaks line 3. -/
theorem mod023_not_line3 {S : ScriptFn String Unit} {ops : List (Op String Unit)}
    (hc : ∀ op ∈ ops, mod023_chans op = [])
    (hn : ∀ op ∈ ops, ((mod023_composed op).map (·.core.name)).Nodup)
    (hS : (S ops).toOption.map (fun c => decide (c.trans.map mod023_namePri =
      (ops.flatMap mod023_added).map mod023_namePri)) = some false) : ¬ mod023_line3 S := by
  intro h
  cases hs : S ops with
  | error m => rw [hs] at hS; cases hS
  | ok c =>
    have e := congrArg (List.map fun k : String × Novel.TimedScg.Timing × Int × Act Unit =>
      (k.1, k.2.2.1)) (h ops c hc hn hs)
    simp only [List.map_map] at e
    have e' : c.trans.map mod023_namePri = (ops.flatMap mod023_added).map mod023_namePri := e
    rw [hs] at hS
    simp [Except.toOption, e'] at hS

/-- The instance with every definition's priority reset to the default 0 ([CORE-020]). -/
def mod023_dropPriInst (I : Instance String Unit) : Instance String Unit :=
  { I with defs := I.defs.map fun d => { d with priority := 0 } }

/-- One call as the priority-dropping builder sees it: a composed instance loses its priorities. -/
def mod023_dropPriOp : Op String Unit → Op String Unit
  | .compose I ports chans => .compose (mod023_dropPriInst I) ports chans
  | .composeAuto I cs => .composeAuto (mod023_dropPriInst I) cs
  | op => op

/-- The builder whose composition rebuilds every rewritten transition at the default priority 0
(Java's `SubnetRewriter.rebuildWithName` without `.priority(t.priority())`); transitions added by
hand keep their priority. -/
def mod023_dropPriScript : ScriptFn String Unit := fun ops =>
  buildExScript (ops.map mod023_dropPriOp)

/-- The priority-dropping builder leaves a hand-written script alone. -/
theorem mod023_dropPri_hand (b : BuiltNet String Unit) :
    (mod023_handScript b).map mod023_dropPriOp = mod023_handScript b := by
  simp only [mod023_handScript, List.map_append, List.map_map]
  rfl

/-- The priority-dropping builder meets lines 1 and 2. -/
theorem mod023_dropPri_lines12 :
    mod023_line1 refBuild mod023_dropPriScript ∧ mod023_line2 mod023_dropPriScript := by
  refine ⟨fun _ _ h => buildScript_builds (refMerge_builds _ _) h, fun ops c h => ?_⟩
  show ∃ c', buildExScript ((mod023_handScript c.toBuiltNet).map mod023_dropPriOp) = .ok c' ∧ _
  rw [mod023_dropPri_hand, mod023_handScript_eq]
  exact buildScript_redeclare (refMerge_builds _ _) h

/-- The script `mod023_exPri` binds no channel. -/
theorem mod023_exPri_chans : ∀ op ∈ mod023_exPri, mod023_chans op = [] := by
  intro op hop
  simp only [mod023_exPri, List.mem_singleton] at hop
  subst hop; rfl

set_option maxRecDepth 20000 in
/-- ✗ The builder whose composition drops the priority kills the mutant: it meets lines 1 and 2
(the composed net already holds priority 0, and its hand-written copy adds priority 0 by hand),
but composing instance `answer` of a subnet whose transition `work` has priority 5 builds
`answer/work` at priority 0, not at the priority 5 it was added with. -/
@[evidence mutant MOD_023]
theorem MOD_023_mutant_noKept_killed :
    MOD_023_mutant_noKept strNaming refBuild mod023_dropPriScript ∧
      ¬ MOD_023 strNaming refBuild mod023_dropPriScript :=
  ⟨mod023_dropPri_lines12, fun h => mod023_not_line3 mod023_exPri_chans (by decide) (by decide) h.2.2⟩

/-- The call declares a fusion set. -/
def mod023_isFuse : Op String Unit → Bool
  | .fuse _ => true
  | _ => false

/-- The call adds a transition by hand. -/
def mod023_isTrans : Op String Unit → Bool
  | .trans _ => true
  | _ => false

/-- The name a call sorts under (the transition's name; only `trans` calls are sorted). -/
def mod023_sortKey : Op String Unit → String
  | .trans d => d.core.name
  | _ => ""

/-- Insert into a list kept in name order. -/
def mod023_insByName (o : Op String Unit) : List (Op String Unit) → List (Op String Unit)
  | [] => [o]
  | x :: xs =>
    if decide (mod023_sortKey x < mod023_sortKey o) then x :: mod023_insByName o xs
    else o :: x :: xs

/-- Insertion sort on the name. -/
def mod023_sortByName : List (Op String Unit) → List (Op String Unit)
  | [] => []
  | o :: os => mod023_insByName o (mod023_sortByName os)

/-- The builder whose fusion returns the transitions in name order (a hash set where Java's
`applyFusion` keeps an insertion-ordered one): on a script that declares a fusion set, the other
calls in order, then the hand-added transitions in name order; without a fusion set, the reference
on the calls as written (every runtime skips fusion then). -/
def mod023_nameOrderScript : ScriptFn String Unit := fun ops =>
  buildExScript (if ops.any mod023_isFuse then
    ops.filter (fun o => !mod023_isTrans o) ++ mod023_sortByName (ops.filter mod023_isTrans)
  else ops)

/-- The script `mod023_exOrder` binds no channel. -/
theorem mod023_exOrder_chans : ∀ op ∈ mod023_exOrder, mod023_chans op = [] := by
  intro op hop
  simp only [mod023_exOrder, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> rfl

set_option maxRecDepth 20000 in
/-- ✗ The builder whose fusion returns the transitions in name order is forbidden: adding `t2` and
then `t1` and fusing their input places builds `t1` before `t2`, so the built transitions are not
in the order the calls added them, and the ready order, whose last tie-break is declaration order
([EXEC-002]), changes. -/
@[evidence forbids MOD_023]
theorem MOD_023_forbids_fuseNameOrder : ¬ MOD_023 strNaming refBuild mod023_nameOrderScript :=
  fun h => mod023_not_line3 mod023_exOrder_chans (by decide) (by decide) h.2.2

end Libpetri.Spec
