import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.Fuse

set_option linter.missingDocs true

/-!
# MOD-061: Fusion resolution at build() (`spec/11-modular-composition.md`)

MOD-061 is a pure-function requirement (kind F) over an abstract fusion function
`F : FuseFn N A` (the declared fusion sets and what a builder holds after every `compose(...)`
call give the fused content, or a rejection with a message) and the transition builder's check
`Build : Trans N → Option String` (a rejection message, or `none`).

On fusion sets of which no two share a member, every member goes to the first declared member of
its set (`SubstSpec`, which has exactly one solution, `substSpec_unique`). The block says what a
successful fusion returns (the builder's transitions, in order, each rewritten through that
substitution and, when an input arc was on a removed member, its input arcs merged by the
[MOD-021] table; every rewritten transition passes `Build`; the set of places and the set of
terminal places), that the outcome does not depend on the order of the sets, when fusion
succeeds, and when and with which message it fails (two different sets that share a member; an
off-table input pair, named after its fusion set or, off every set, after its place).

The witness is the reference fusion `refFuse Build` (`Reference/Fuse.lean`); the block holds for
every `Build`. Four consequences hold for every model: an off-table pair rejects
(`mod061_offTable`), a rewrite that `Build` rejects rejects (`mod061_buildFails`), no member
other than the first declared one of its set is a place of the result (`mod061_removed`, AC3),
and two sets sharing one place are reported in declaration order (`mod061_twoSets_msg`).
Every line has a mutant: a wrong fusion that meets every other line and breaks that one.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The messages -/

section Messages

variable {N : Type}

/-- The seam of a fusion diagnostic: `Fusion set '<name>'`. -/
def mod061_seam (s : FusionSet N) : String := "Fusion set '" ++ s.name ++ "'"

variable [ToString N]

/-- The seam of a fusion diagnostic on a place no fusion set lists: `Fusion set '<place>'`, the
fallback of all three runtimes. -/
def mod061_placeSeam (p : N) : String := "Fusion set '" ++ toString p ++ "'"

/-- The [MOD-021] rule (c) diagnostic as Java and TypeScript spell it (`atLeast(n)`). -/
def mod061_collisionMsg (seam : String) (c : Collision N) : String :=
  s!"{seam}: input arcs {cardStr c.left} and {cardStr c.right} collide on place '{c.place}' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)."

/-- A cardinality as Rust and Python spell it in a diagnostic: `at_least(n)` for `atLeast`. -/
def mod061_cardStrSnake : Card → String
  | .one => "one()"
  | .exactly n => s!"exactly({n})"
  | .all => "all()"
  | .atLeast n => s!"at_least({n})"

/-- The [MOD-021] rule (c) diagnostic as Rust and Python spell it (`at_least(n)`, rust
`rewriter.rs` `apply_fusion`). -/
def mod061_collisionMsgSnake (seam : String) (c : Collision N) : String :=
  s!"{seam}: input arcs {mod061_cardStrSnake c.left} and {mod061_cardStrSnake c.right} collide on place '{c.place}' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / at_least(n)."

/-- The overlap rejection of all three runtimes: the shared place and both sets. -/
def mod061_overlapMsg (p : N) (a b : String) : String :=
  s!"Fusion overlap: place '{p}' appears in two fusion sets ('{a}' and '{b}'). A place may appear in at most one fusion set (MOD-060)."

end Messages

/-! ## MOD-061: Fusion Resolution at build() -/

requirement MOD_061
  id "MOD-061"
  title "Fusion Resolution at build()"
  kind F
  scope "fusion at build() of every builder that declares fusion sets"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the transitions of the result *shall* be the builder's transitions, in the same order and number, each with every member of a fusion set replaced by the first declared member of that set in every input, inhibitor, read and reset arc and in the output specification, with its name, timing, priority and action unchanged and, where at least one of its declared input arcs is on a member that is not the first declared member of its set, with its input arcs merged by the canonical merge table of [MOD-021] into one arc per place at the position of the first arc on that place."
        "*When* fusion at `build()` succeeds, every transition of the result *shall* pass the checks of the transition builder ([CORE-030], [IO-011], [IO-012], [EXEC-012])."
        "*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of places of the result *shall* be the builder's places other than the members that are not the first declared member of their fusion set, together with the places a transition of the result names and the terminal places of the result."
        "*When* fusion at `build()` succeeds on fusion sets of which no two share a member, the set of terminal places ([EXEC-042]) of the result *shall* be the declared terminal places with every member of a fusion set replaced by the first declared member of that set."
        "*Where* no two declared fusion sets share a member, the outcome of fusion at `build()` *shall* be the same for every order in which the fusion sets are declared: the same failure with the same message, or a fused net with the same transitions in the same order, the same set of places and the same set of terminal places."
        "*When* no two declared fusion sets share a member and the rewrite of every transition meets no pair of input arcs that the canonical merge table of [MOD-021] does not list and passes the checks of the transition builder, fusion at `build()` *shall* succeed."
        "*If* no two declared fusion sets share a member and merging the input arcs of a rewritten transition meets two arcs on one place whose pair the canonical merge table of [MOD-021] does not list, *then* fusion at `build()` *shall* fail."
        "*If* no two declared fusion sets share a member and the transition builder rejects the rewrite of a transition, *then* fusion at `build()` *shall* fail."
        "*If* two declared fusion sets that differ in name or in members share a member, *then* fusion at `build()` *shall* fail with the message `Fusion overlap: place '<p>' appears in two fusion sets ('<first>' and '<second>'). A place may appear in at most one fusion set (MOD-060).`, where `<p>` is a member that two declared fusion sets both list and `<first>` and `<second>` are the names of those two sets, the one declared first named first."
        "*If* exactly two fusion sets that differ in name or in members are declared and they share exactly one member `p`, *then* the message of that failure *shall* name `p`, then the set declared first, then the set declared second."
        "*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a member of a fusion set, *then* fusion at `build()` *shall* fail with the [MOD-021] rule (c) diagnostic for that pair, whose earlier side is the merge of the arcs before it on that place, whose seam is `Fusion set '<name>'` with the name of that set, and whose method spelling is one of the two that [MOD-021] allows."
        "*If* every transition before a transition `t` rewrites and passes the checks of the transition builder, no two declared fusion sets share a member, and the first off-table pair met while merging the input arcs of `t` lies on a place that no fusion set lists, *then* fusion at `build()` *shall* fail with the same diagnostic, the name of that place standing in the seam for the name of a set."
  reading "For every transition-builder check Build and every fusion function F (fusion sets and a builder's places, transition definitions and terminal places give the fused content or a rejection message), where 'disjoint' means FusionDisjoint (no place is a member of two sets at two list positions) and σ is the substitution SubstSpec asks for (a member goes to the first member of its set, every other place stays):"
          "line 1: on disjoint sets, if F succeeds with Y, then rewriting the builder's definitions in order with fuseDef σ succeeds, and the rewritten definitions are Y's definitions, compared as a list of TransDef, so in the same order and number (every arc place and output place through σ; name, timing, priority, action kept; when some input arc is on a place σ moves, the input arcs merged by the MOD-021 table at the first-seen position; read, inhibitor and reset arcs kept as they are);"
          "line 2: if F succeeds with Y, every definition of Y passes Build;"
          "line 3: on disjoint sets, if F succeeds with Y, a place is a place of Y exactly when it is a builder place that σ fixes, or σ of a declared terminal place, or a place some definition of Y names;"
          "line 4: on disjoint sets, if F succeeds with Y, a place is a terminal place of Y exactly when it is σ of a declared terminal place;"
          "line 5: on disjoint sets, for any permutation sets' of the sets, a rejection of F on sets with message m is a rejection of F on sets' with message m, and a success Y on sets has a success Y' on sets' with the same definitions as a list of TransDef, the same places as a set and the same terminal places as a set;"
          "line 6: on disjoint sets, if every definition rewrites with fuseDef σ to a definition that Build accepts, F succeeds;"
          "line 7: if two different sets of the declaration list share a member, F fails with mod061_overlapMsg p r.name s.name for some place p and some sets r and s that both list p, r declared before s (sets = l₁ ++ r :: (l₂ ++ s :: l₃));"
          "line 8: on disjoint sets, if every definition before d rewrites and passes Build and the rewrite of d meets the off-table collision c on a member of set s, F fails with the MOD-021 rule (c) diagnostic for c with seam Fusion set '<name of s>', spelled either as Java and TypeScript do (atLeast(n)) or as Rust and Python do (at_least(n));"
          "line 9: as line 8, when no set lists the place of c: the seam is Fusion set '<name of the place>'."
  assumes "Ruling D54 (a) (clash mod-c#2, R-MC6): the canonical member is the first declared member of a set and keeps its own name; the set's name is used in diagnostics only, as every runtime does (the 'Canonical member' section of the FusionSet documentation in rust/libpetri-core/src/fusion.rs, java/src/main/java/org/libpetri/core/FusionSet.java and typescript/src/core/fusion-set.ts). That fixed choice is what makes the fused structure a function of the declaration (substSpec_unique). One-member sets and the declaration check (empty set, token types) are MOD-060's; a one-member set fuses nothing (refFuse_short). MOD-060 states the same choice (item 1, item 2 and AC4); step 1 of MOD-061 does not cite it."
          "Model scope. A fusion function works on what the builder holds after every compose call (FuseNet: places, CDef definitions in declaration order per ruling D32 (a), terminal places), as Rust build_with_fusion (rust/libpetri-core/src/petri_net.rs), Java buildWithFusion (java/src/main/java/org/libpetri/core/PetriNet.java) and TypeScript buildWithFusion (typescript/src/core/petri-net.ts) do; Python rides on Rust. FuseNet has no field for fusion sets, so the sentence 'the built net keeps no record of the fusion sets' holds by construction. That fusion runs after every compose call and before CORE-040 returns the net (item 'Fusion MUST be applied after all compose(...) calls' and AC4's 'composing then fusing is observationally equivalent to a hand-written net'), that the retired-port check of MOD-027 and the terminal check of EXEC-042 run on the fused net, and that removed members lose their subnet membership entry (MOD-026) are ComposeBuild's finish (composition wave W8, MOD-023, MOD-026, MOD-027). Line 6 says that fusion itself succeeds; those later checks may still fail build()."
          "Line 1 compares definitions as TransDef, not as CDef: the declared-to-actual correspondence a rewrite records is MOD-031's (Rust keeps none when every entry is the identity, the MAY of MOD-031). The list equality fixes order and number: a result that drops or reorders a transition breaks it. 'An input arc on a member that is not the first declared member of its set' is an input arc on a place σ moves (fuseTouches): the merge runs on exactly those transitions (Rust apply_fusion inputs_touched, rust/libpetri-core/src/rewriter.rs; Java and TypeScript applyFusion), and then over all its input arcs; a transition whose input arcs are all on places σ fixes, two of them on the first member of a set for example, is not merged and keeps the duplicate, which Build rejects (CORE-030). Read, inhibitor and reset arcs that land on one place are kept as they are in every runtime (rebuild_with_name in rust/libpetri-core/src/rewriter.rs, rebuildWithName in java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java and typescript/src/core/internal/subnet-rewriter.ts), unlike a channel merge (MOD-021 rule (a))."
          "Every rewritten transition passes through the transition builder again (line 2; IO-011, IO-012, EXEC-012 and CORE-030 name fusion as a construction path). The sentence that a rewrite the builder rejects fails fusion is mod061_buildFails, a consequence of lines 1 and 2, and the sentence that an off-table pair fails fusion is mod061_offTable, a consequence of line 1. The message of a builder rejection is owned by CORE-030, IO-011, IO-012 and EXEC-012 and is not stated here (skeptic correction S6 of the composition design: the block holds for every Build)."
          "Line 3 and line 4 compare places and terminal places as sets: the order of places is not normative (ruling D32), Java collects places in a HashSet, and terminals are deduplicated in declaration order by every runtime. Under line 3 a canonical member that is neither declared, nor named by an arc, nor terminal is not a place of the result, as in every runtime (a member is never checked to be a builder place). Line 4 is the sentence of ruling D20 (R-MC8 (a)) that a terminal on a removed member names the canonical member (the terminal remap at the end of build_with_fusion in petri_net.rs, buildWithFusion in PetriNet.java and petri-net.ts)."
          "A fusion set may list its first member again later (members [a, b, a]). Every runtime skips a later member equal to the canonical member when it builds the fusion map and the removed names (the fusion-map loop of build_with_fusion in rust/libpetri-core/src/petri_net.rs and of buildWithFusion in java/src/main/java/org/libpetri/core/PetriNet.java and typescript/src/core/petri-net.ts), so the declared place a remains, as lines 1 and 3 say with the spec's 'the canonical member remains' (step 3): σ fixes a, and the reference keeps a (mod061_dupCanonical_kept)."
          "Line 5 is the MUST 'the final flat net MUST be independent of that order' and AC6, read as the markdown asks: 'observationally identical', AC6's 'identical place set, transition set, arc topology'. A rejection keeps its message; a success keeps its transitions in order and its places and terminal places as sets, so the order in which the built net lists places is free, as in lines 3 and 4 (mod061_setOrder_meets: a fusion that lists the first members of the sets first, in declaration order, meets MOD-061). The application order inside build() cannot be observed through F; independence from the declaration order covers it, and AC6 is reworded to 'declared in opposite orders'. AC6's 'identical executor behavior' follows, since equal nets run alike. Without disjointness nothing is claimed: overlapping sets are rejected (line 7), and the substitution would not exist (substSpec_overlap)."
          "Line 7 is the overlap sentence, raised from SHOULD to MUST under ruling D20 (R-MC8 (a)), since every runtime rejects (the overlap check at the start of build_with_fusion in petri_net.rs, buildWithFusion in PetriNet.java and petri-net.ts) with this message. 'Different' is structural: the two sets differ in name or in members. Declaring the same set (same name, same members) twice is implementation-defined and not covered: Rust rejects it by list position, Java and TypeScript compare set objects with != and fuse one object declared twice once (two separately built equal sets count as different there, which line 7 neither requires nor forbids). Two sets with the same members and different names are different and rejected. Which shared place and which pair the message names when several sets or places overlap is not fixed: the runtimes walk the sets in declaration order and report the first member an earlier set lists, Rust and Java with the first earlier set listing it, TypeScript with the latest; line 7 claims only some shared place and some pair that lists it, earlier set first. With exactly two sets sharing exactly one place the message is determined (mod061_twoSets_msg, a consequence of line 7, and the sentence that states it)."
          "Lines 8 and 9 state the message of a first offender only (skeptic correction S3): with an earlier transition that fails Build, that failure is reported. The collision is the first off-table pair met while merging left to right, its earlier side the merge of the arcs before it on that place (insertInE; Rust merge_input_arcs, Java mergeInputArcs, TypeScript normalizeInputArcs): one(), one(), then atLeast(1) on one place reports exactly(2) and atLeast(1). Line 8 is a pair on a member of a set (after the substitution, its first member); line 9 is a pair on a place no set lists, for example a duplicate input arc on an unfused place of a transition that also has a moved arc, where every runtime puts the place's own name in the seam (the set-name fallback in apply_fusion in rewriter.rs, and the seam function buildWithFusion passes to applyFusion in PetriNet.java and petri-net.ts; a pair on a member lies on the first member after the substitution, the key Rust and Java look up). MOD-021 binds the method spelling of atLeast to the host language, which Rust and Python spell at_least(n) in the cardinality and in the closing hint (the panic message of apply_fusion and describe_in in rewriter.rs); F carries no host language, so lines 8 and 9 accept both spellings and the binding stays MOD-021's."
          "AC1 (three leaky-bucket instances share one limiter) is MOD_061_nonvacuous on the reference (every take transition draws from b1/limit). AC2 is reworded under ruling D54 (a) (R-MC7, clash mod-c#1): a token put on a non-canonical member at initial-marking time stays on that undeclared name, retained and inert, which is CORE-072's line; no executor knows a fusion set (the CORE-072 diagnostic warn_unknown_places in rust/libpetri-runtime/src/executor_core/executor.rs). AC3 (non-canonical members are not places of the built net) is mod061_removed, a consequence of lines 1 and 3 for every model. AC4's merge and rejection are lines 1, 8 and 9 and mod061_offTable; its 'after composition' is ComposeBuild's. AC5 (export and verification need no awareness of fusion) is MOD-023's and MOD-050's. AC6 is line 5. AC7 is line 7."
          "The test derivation's 'fuse two places each consumed via one() by the same transition; verify the built net consumes 2 from the canonical place' is fuseEx_both_merged on the reference, 'fuse places whose colliding input arcs cannot merge; verify build rejection names the fusion set' is fuseEx_mix_rejected, and 'declare b terminal and fuse {a, b}; verify a is terminal in the built net' is fuseEx_terminal_moved (the first two in MOD_061_nonvacuous)."
  signoff "2026-11-13 5c60993d359bc7b0 ai"
  statement : ∀ {N A : Type} [DecidableEq N] [ToString N], (Trans N → Option String) →
      FuseFn N A → Prop :=
    fun Build F =>
      (∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
        (X.defs.mapM (fuseDef σ)).map (·.map CDef.toTransDef) = .ok (Y.defs.map CDef.toTransDef)) ∧
      (∀ sets X Y, F sets X = .ok Y → ∀ d ∈ Y.defs, Build d.toTrans = none) ∧
      (∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
        ∀ p, p ∈ Y.places ↔ (p ∈ X.places ∧ σ p = p) ∨ p ∈ X.terminals.map σ ∨
          ∃ d ∈ Y.defs, p ∈ d.namedPlaces) ∧
      (∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
        ∀ p, p ∈ Y.terminals ↔ p ∈ X.terminals.map σ) ∧
      (∀ sets sets' X, FusionDisjoint sets → sets.Perm sets' →
        (∀ m, F sets X = .error m → F sets' X = .error m) ∧
        ∀ Y, F sets X = .ok Y → ∃ Y', F sets' X = .ok Y' ∧
          Y.defs.map CDef.toTransDef = Y'.defs.map CDef.toTransDef ∧
          (∀ p, p ∈ Y.places ↔ p ∈ Y'.places) ∧ (∀ p, p ∈ Y.terminals ↔ p ∈ Y'.terminals)) ∧
      (∀ sets X σ, FusionDisjoint sets → SubstSpec sets σ →
        (∀ d ∈ X.defs, ∃ d', fuseDef σ d = .ok d' ∧ Build d'.toTrans = none) →
        ∃ Y, F sets X = .ok Y) ∧
      (∀ sets X a b, a ∈ sets → b ∈ sets → a ≠ b → (∃ p, p ∈ a.members ∧ p ∈ b.members) →
        ∃ (p : _) (r s : FusionSet _), [r, s].Sublist sets ∧ p ∈ r.members ∧ p ∈ s.members ∧
          F sets X = .error (mod061_overlapMsg p r.name s.name)) ∧
      (∀ sets X σ pre d post c s, FusionDisjoint sets → SubstSpec sets σ →
        X.defs = pre ++ d :: post →
        (∀ e ∈ pre, ∃ e', fuseDef σ e = .ok e' ∧ Build e'.toTrans = none) →
        fuseDef σ d = .error c → s ∈ sets → c.place ∈ s.members →
        F sets X = .error (mod061_collisionMsg (mod061_seam s) c) ∨
          F sets X = .error (mod061_collisionMsgSnake (mod061_seam s) c)) ∧
      (∀ sets X σ pre d post c, FusionDisjoint sets → SubstSpec sets σ →
        X.defs = pre ++ d :: post →
        (∀ e ∈ pre, ∃ e', fuseDef σ e = .ok e' ∧ Build e'.toTrans = none) →
        fuseDef σ d = .error c → (∀ s ∈ sets, c.place ∉ s.members) →
        F sets X = .error (mod061_collisionMsg (mod061_placeSeam c.place) c) ∨
          F sets X = .error (mod061_collisionMsgSnake (mod061_placeSeam c.place) c))

/- The pinned readable form of MOD-061: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_061 : {N A : Type} →
  [DecidableEq N] → [ToString N] → (Reference.Trans N → Option String) → FuseFn N A → Prop :=
fun {N A} [DecidableEq N] [ToString N] Build F =>
  (∀ (sets : List (FusionSet N)) (X Y : FuseNet N A) (σ : N → N),
      FusionDisjoint sets →
        SubstSpec sets σ →
          F sets X = Except.ok Y →
            Except.map (fun x => List.map CDef.toTransDef x) (List.mapM (fuseDef σ) X.defs) =
              Except.ok (List.map CDef.toTransDef Y.defs)) ∧
    (∀ (sets : List (FusionSet N)) (X Y : FuseNet N A), F sets X = Except.ok Y → ∀ d ∈ Y.defs, Build d.toTrans = none) ∧
      (∀ (sets : List (FusionSet N)) (X Y : FuseNet N A) (σ : N → N),
          FusionDisjoint sets →
            SubstSpec sets σ →
              F sets X = Except.ok Y →
                ∀ (p : N),
                  p ∈ Y.places ↔
                    p ∈ X.places ∧ σ p = p ∨ p ∈ List.map σ X.terminals ∨ ∃ d ∈ Y.defs, p ∈ d.namedPlaces) ∧
        (∀ (sets : List (FusionSet N)) (X Y : FuseNet N A) (σ : N → N),
            FusionDisjoint sets →
              SubstSpec sets σ → F sets X = Except.ok Y → ∀ (p : N), p ∈ Y.terminals ↔ p ∈ List.map σ X.terminals) ∧
          (∀ (sets sets' : List (FusionSet N)) (X : FuseNet N A),
              FusionDisjoint sets →
                sets.Perm sets' →
                  (∀ (m : String), F sets X = Except.error m → F sets' X = Except.error m) ∧
                    ∀ (Y : FuseNet N A),
                      F sets X = Except.ok Y →
                        ∃ Y',
                          F sets' X = Except.ok Y' ∧
                            List.map CDef.toTransDef Y.defs = List.map CDef.toTransDef Y'.defs ∧
                              (∀ (p : N), p ∈ Y.places ↔ p ∈ Y'.places) ∧
                                ∀ (p : N), p ∈ Y.terminals ↔ p ∈ Y'.terminals) ∧
            (∀ (sets : List (FusionSet N)) (X : FuseNet N A) (σ : N → N),
                FusionDisjoint sets →
                  SubstSpec sets σ →
                    (∀ d ∈ X.defs, ∃ d', fuseDef σ d = Except.ok d' ∧ Build d'.toTrans = none) →
                      ∃ Y, F sets X = Except.ok Y) ∧
              (∀ (sets : List (FusionSet N)) (X : FuseNet N A) (a b : FusionSet N),
                  a ∈ sets →
                    b ∈ sets →
                      a ≠ b →
                        (∃ p ∈ a.members, p ∈ b.members) →
                          ∃ p r s,
                            [r, s].Sublist sets ∧
                              p ∈ r.members ∧
                                p ∈ s.members ∧ F sets X = Except.error (mod061_overlapMsg p r.name s.name)) ∧
                (∀ (sets : List (FusionSet N)) (X : FuseNet N A) (σ : N → N) (pre : List (CDef N A)) (d : CDef N A)
                    (post : List (CDef N A)) (c : Collision N) (s : FusionSet N),
                    FusionDisjoint sets →
                      SubstSpec sets σ →
                        X.defs = pre ++ d :: post →
                          (∀ e ∈ pre, ∃ e', fuseDef σ e = Except.ok e' ∧ Build e'.toTrans = none) →
                            fuseDef σ d = Except.error c →
                              s ∈ sets →
                                c.place ∈ s.members →
                                  F sets X = Except.error (mod061_collisionMsg (mod061_seam s) c) ∨
                                    F sets X = Except.error (mod061_collisionMsgSnake (mod061_seam s) c)) ∧
                  ∀ (sets : List (FusionSet N)) (X : FuseNet N A) (σ : N → N) (pre : List (CDef N A)) (d : CDef N A)
                    (post : List (CDef N A)) (c : Collision N),
                    FusionDisjoint sets →
                      SubstSpec sets σ →
                        X.defs = pre ++ d :: post →
                          (∀ e ∈ pre, ∃ e', fuseDef σ e = Except.ok e' ∧ Build e'.toTrans = none) →
                            fuseDef σ d = Except.error c →
                              (∀ s ∈ sets, c.place ∉ s.members) →
                                F sets X = Except.error (mod061_collisionMsg (mod061_placeSeam c.place) c) ∨
                                  F sets X = Except.error (mod061_collisionMsgSnake (mod061_placeSeam c.place) c)
-/
#guard_msgs in #print MOD_061

/-! ### The nine lines, named (for the mutants) -/

section Lines

variable {N A : Type} [DecidableEq N] [ToString N]

/-- Line 1 of MOD-061: a success holds the rewritten definitions, in order. -/
def mod061_line1 (F : FuseFn N A) : Prop :=
  ∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
    (X.defs.mapM (fuseDef σ)).map (·.map CDef.toTransDef) = .ok (Y.defs.map CDef.toTransDef)

/-- Line 2 of MOD-061: every definition of a success passes the transition builder's check. -/
def mod061_line2 (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  ∀ sets X Y, F sets X = .ok Y → ∀ d ∈ Y.defs, Build d.toTrans = none

/-- Line 3 of MOD-061: the places of a success. -/
def mod061_line3 (F : FuseFn N A) : Prop :=
  ∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
    ∀ p, p ∈ Y.places ↔ (p ∈ X.places ∧ σ p = p) ∨ p ∈ X.terminals.map σ ∨
      ∃ d ∈ Y.defs, p ∈ d.namedPlaces

/-- Line 4 of MOD-061: the terminal places of a success. -/
def mod061_line4 (F : FuseFn N A) : Prop :=
  ∀ sets X Y σ, FusionDisjoint sets → SubstSpec sets σ → F sets X = .ok Y →
    ∀ p, p ∈ Y.terminals ↔ p ∈ X.terminals.map σ

/-- Line 5 of MOD-061: on disjoint sets the outcome does not depend on their order. -/
def mod061_line5 (F : FuseFn N A) : Prop :=
  ∀ sets sets' X, FusionDisjoint sets → sets.Perm sets' →
    (∀ m, F sets X = .error m → F sets' X = .error m) ∧
    ∀ Y, F sets X = .ok Y → ∃ Y', F sets' X = .ok Y' ∧
      Y.defs.map CDef.toTransDef = Y'.defs.map CDef.toTransDef ∧
      (∀ p, p ∈ Y.places ↔ p ∈ Y'.places) ∧ (∀ p, p ∈ Y.terminals ↔ p ∈ Y'.terminals)

/-- Line 6 of MOD-061: acceptance. -/
def mod061_line6 (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  ∀ sets X σ, FusionDisjoint sets → SubstSpec sets σ →
    (∀ d ∈ X.defs, ∃ d', fuseDef σ d = .ok d' ∧ Build d'.toTrans = none) → ∃ Y, F sets X = .ok Y

/-- Line 7 of MOD-061: two different sets that share a member reject, naming a shared place and
two sets that list it, the earlier first. -/
def mod061_line7 (F : FuseFn N A) : Prop :=
  ∀ sets X a b, a ∈ sets → b ∈ sets → a ≠ b → (∃ p, p ∈ a.members ∧ p ∈ b.members) →
    ∃ (p : N) (r s : FusionSet N), [r, s].Sublist sets ∧ p ∈ r.members ∧ p ∈ s.members ∧
      F sets X = .error (mod061_overlapMsg p r.name s.name)

/-- Line 8 of MOD-061: the message of a first off-table pair on a member names its fusion set. -/
def mod061_line8 (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  ∀ sets X σ pre d post c s, FusionDisjoint sets → SubstSpec sets σ →
    X.defs = pre ++ d :: post →
    (∀ e ∈ pre, ∃ e', fuseDef σ e = .ok e' ∧ Build e'.toTrans = none) →
    fuseDef σ d = .error c → s ∈ sets → c.place ∈ s.members →
    F sets X = .error (mod061_collisionMsg (mod061_seam s) c) ∨
      F sets X = .error (mod061_collisionMsgSnake (mod061_seam s) c)

/-- Line 9 of MOD-061: the message of a first off-table pair on a place no set lists names the
place. -/
def mod061_line9 (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  ∀ sets X σ pre d post c, FusionDisjoint sets → SubstSpec sets σ →
    X.defs = pre ++ d :: post →
    (∀ e ∈ pre, ∃ e', fuseDef σ e = .ok e' ∧ Build e'.toTrans = none) →
    fuseDef σ d = .error c → (∀ s ∈ sets, c.place ∉ s.members) →
    F sets X = .error (mod061_collisionMsg (mod061_placeSeam c.place) c) ∨
      F sets X = .error (mod061_collisionMsgSnake (mod061_placeSeam c.place) c)

/-- MOD-061 is its nine lines. -/
theorem mod061_iff (Build : Trans N → Option String) (F : FuseFn N A) :
    MOD_061 Build F ↔ mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
      mod061_line5 F ∧ mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧
      mod061_line9 Build F :=
  Iff.rfl

end Lines

/-! ### Shared proof steps -/

section Steps

variable {N A : Type} [DecidableEq N] [ToString N]

omit [ToString N] in
/-- Overlap detection reports a place and two sets that both list it, the earlier one first. -/
theorem mod061_overlapAux_split : ∀ (seen l : List (FusionSet N)) {p : N} {x y : String},
    overlapAux seen l = some (p, x, y) →
    ∃ r s, [r, s].Sublist (seen ++ l) ∧ p ∈ r.members ∧ p ∈ s.members ∧ x = r.name ∧ y = s.name
  | _, [], _, _, _, h => by simp [overlapAux] at h
  | seen, s :: rest, p, x, y, h => by
    unfold overlapAux at h
    split at h
    · rename_i q hf
      have hq := List.mem_of_find?_eq_some hf
      have hq' := List.find?_some hf
      simp only [List.any_eq_true, decide_eq_true_eq] at hq'
      obtain ⟨r0, hr0, hqr0⟩ := hq'
      cases ho : fusionOwner seen q with
      | none => exact absurd hqr0 (fusionOwner_eq_none_iff.1 ho r0 hr0)
      | some r =>
        obtain ⟨hr, hqr⟩ := fusionOwner_some ho
        rw [ho] at h
        simp only [Option.map_some, Option.getD_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨r, s, (List.singleton_sublist.2 hr).append
          (List.singleton_sublist.2 List.mem_cons_self), hqr, hq, rfl, rfl⟩
    · obtain ⟨r, s', he, h1, h2, h3, h4⟩ := mod061_overlapAux_split (seen ++ [s]) rest h
      exact ⟨r, s', by simpa using he, h1, h2, h3, h4⟩

omit [DecidableEq N] in
/-- The overlap message of the reference is the one the block states. -/
theorem mod061_overlapMsg_eq (p : N) (a b : String) : overlapMsg p a b = mod061_overlapMsg p a b :=
  rfl

/-- A fusion that rejects whatever overlap detection finds with the runtimes' message meets
line 7. -/
theorem mod061_line7_of {F : FuseFn N A}
    (h : ∀ sets X p a b, findOverlap sets = some (p, a, b) → F sets X = .error (overlapMsg p a b)) :
    mod061_line7 F := by
  rintro sets X a b ha hb hne ⟨p, hpa, hpb⟩
  cases ho : findOverlap sets with
  | none => exact absurd (((findOverlap_eq_none_iff sets).1 ho).unique ha hb hpa hpb) hne
  | some t =>
    obtain ⟨q, x, y⟩ := t
    obtain ⟨r, s, he, h1, h2, rfl, rfl⟩ := mod061_overlapAux_split [] sets ho
    exact ⟨q, r, s, by simpa using he, h1, h2, h sets X q _ _ ho⟩

omit [DecidableEq N] [ToString N] in
/-- A fusion whose outcome does not depend on the order of disjoint sets meets line 5. -/
theorem mod061_line5_of_eq {F : FuseFn N A}
    (h : ∀ sets sets' X, FusionDisjoint sets → sets.Perm sets' → F sets X = F sets' X) :
    mod061_line5 F := by
  intro sets sets' X hd hp
  rw [h sets sets' X hd hp]
  exact ⟨fun _ h => h, fun Y hY => ⟨Y, hY, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩⟩

/-- The reference fusion with the seam of a collision given by `seam`: the shape of the reference
(`seam := seamOf`) and of two wrong fusions below. -/
def mod061_seamFuse (Build : Trans N → Option String) (seam : List (FusionSet N) → N → String) :
    FuseFn N A := fun sets X =>
  match findOverlap sets with
  | some (p, a, b) => .error (overlapMsg p a b)
  | none => (X.defs.mapM (fuseStep Build (refSubst sets) (seam sets))).map
      (fuseAssemble (refSubst sets) X)

/-- The reference fusion is the seam fusion with the reference seam. -/
theorem mod061_seamFuse_ref (Build : Trans N → Option String) :
    mod061_seamFuse (A := A) Build seamOf = refFuse Build :=
  rfl

/-- A seam fusion succeeds exactly when the reference does. -/
theorem mod061_seamFuse_ok (Build : Trans N → Option String)
    (seam : List (FusionSet N) → N → String) (sets : List (FusionSet N)) (X Y : FuseNet N A) :
    mod061_seamFuse Build seam sets X = .ok Y ↔ refFuse Build sets X = .ok Y := by
  unfold mod061_seamFuse refFuse
  cases findOverlap sets with
  | some t => obtain ⟨p, a, b⟩ := t; simp
  | none =>
    simp only
    rw [except_map_ok_iff, except_map_ok_iff]
    constructor
    · rintro ⟨ds, hds, rfl⟩; exact ⟨ds, mapM_fuseStep_ok_iff.2 (mapM_fuseStep_ok_iff.1 hds), rfl⟩
    · rintro ⟨ds, hds, rfl⟩; exact ⟨ds, mapM_fuseStep_ok_iff.2 (mapM_fuseStep_ok_iff.1 hds), rfl⟩

/-- A seam fusion rejects an overlap as the reference does. -/
theorem mod061_seamFuse_line7 (Build : Trans N → Option String)
    (seam : List (FusionSet N) → N → String) : mod061_line7 (mod061_seamFuse (A := A) Build seam) :=
  mod061_line7_of fun sets X p a b ho => by simp only [mod061_seamFuse, ho]

/-- A seam fusion whose seam does not read the order of disjoint sets meets line 5. -/
theorem mod061_seamFuse_line5 (Build : Trans N → Option String)
    (seam : List (FusionSet N) → N → String)
    (hs : ∀ sets sets', FusionDisjoint sets → sets.Perm sets' → seam sets = seam sets') :
    mod061_line5 (mod061_seamFuse (A := A) Build seam) :=
  mod061_line5_of_eq fun sets sets' X hd hp => by
    unfold mod061_seamFuse
    rw [(findOverlap_eq_none_iff sets).2 hd, (findOverlap_eq_none_iff sets').2 (hd.perm hp),
      refSubst_perm hp hd, hs sets sets' hd hp]

/-- **The first offender's message** of a seam fusion: when every definition before `d` passes,
a collision at `d` rejects with the [MOD-021] diagnostic and the seam of its place. -/
theorem mod061_seamFuse_first {Build : Trans N → Option String}
    {seam : List (FusionSet N) → N → String} {sets : List (FusionSet N)} {X : FuseNet N A}
    (hd : FusionDisjoint sets) {pre post : List (CDef N A)} {d : CDef N A} {c : Collision N}
    (hX : X.defs = pre ++ d :: post)
    (hpre : ∀ e ∈ pre, ∃ e', fuseDef (refSubst sets) e = .ok e' ∧ Build e'.toTrans = none)
    (hc : fuseDef (refSubst sets) d = .error c) :
    mod061_seamFuse Build seam sets X = .error (mod061_collisionMsg (seam sets c.place) c) := by
  simp only [mod061_seamFuse, (findOverlap_eq_none_iff sets).2 hd, hX]
  rw [mapM_except_error_first _ d (fuseMsg (seam sets) c) post (by simp [fuseStep, hc]) pre
    (fun e he => by obtain ⟨e', h⟩ := hpre e he; exact ⟨e', fuseStep_ok_iff.2 h⟩)]
  rfl

/-- A seam fusion running `B` whose seam names the set of a member meets line 8 for every check
`Build` that `B` accepts at least whatever `Build` accepts. -/
theorem mod061_seamFuse_line8 (Build B : Trans N → Option String)
    (hB : ∀ t, Build t = none → B t = none) (seam : List (FusionSet N) → N → String)
    (hs : ∀ sets s p, FusionDisjoint sets → s ∈ sets → p ∈ s.members → seam sets p = mod061_seam s) :
    mod061_line8 Build (mod061_seamFuse (A := A) B seam) := by
  intro sets X σ pre d post c s hd hσ hX hpre hc hsm hp
  rw [(substSpec_iff hd).1 hσ] at hpre hc
  left
  rw [mod061_seamFuse_first hd hX (fun e he => by
    obtain ⟨e', h1, h2⟩ := hpre e he
    exact ⟨e', h1, hB _ h2⟩) hc, hs sets s c.place hd hsm hp]

/-- A seam fusion running `B` whose seam names a place no set lists meets line 9 for every check
`Build` that `B` accepts at least whatever `Build` accepts. -/
theorem mod061_seamFuse_line9 (Build B : Trans N → Option String)
    (hB : ∀ t, Build t = none → B t = none) (seam : List (FusionSet N) → N → String)
    (hs : ∀ sets p, (∀ s ∈ sets, p ∉ s.members) → seam sets p = mod061_placeSeam p) :
    mod061_line9 Build (mod061_seamFuse (A := A) B seam) := by
  intro sets X σ pre d post c hd hσ hX hpre hc hp
  rw [(substSpec_iff hd).1 hσ] at hpre hc
  left
  rw [mod061_seamFuse_first hd hX (fun e he => by
    obtain ⟨e', h1, h2⟩ := hpre e he
    exact ⟨e', h1, hB _ h2⟩) hc, hs sets c.place hp]

/-- The reference seam names the set of a member. -/
theorem mod061_seamOf_member (sets : List (FusionSet N)) (s : FusionSet N) (p : N)
    (hd : FusionDisjoint sets) (hs : s ∈ sets) (hp : p ∈ s.members) :
    seamOf sets p = mod061_seam s :=
  seamOf_member hd hs hp

/-- The reference seam names a place no set lists. -/
theorem mod061_seamOf_none (sets : List (FusionSet N)) (p : N) (h : ∀ s ∈ sets, p ∉ s.members) :
    seamOf sets p = mod061_placeSeam p := by
  simp only [seamOf, fusionOwner_eq_none_iff.2 h, Option.map_none, Option.getD_none,
    mod061_placeSeam]

end Steps

/-! ### The reference -/

section Ref

variable {N A : Type} [DecidableEq N] [ToString N]

/-- The reference meets line 1 for every check it runs. -/
theorem mod061_ref_line1 (B : Trans N → Option String) : mod061_line1 (refFuse (A := A) B) := by
  intro sets X Y σ hd hσ h
  rw [(substSpec_iff hd).1 hσ, (refFuse_ok_iff.1 h).2.1]
  rfl

/-- The reference meets line 2 for the check it runs. -/
theorem mod061_ref_line2 (B : Trans N → Option String) : mod061_line2 B (refFuse (A := A) B) :=
  fun _ _ _ h => (refFuse_ok_iff.1 h).2.2.1

/-- The reference meets line 3 for every check it runs. -/
theorem mod061_ref_line3 (B : Trans N → Option String) : mod061_line3 (refFuse (A := A) B) := by
  intro sets X Y σ hd hσ h p
  rw [(substSpec_iff hd).1 hσ]
  exact refFuse_mem_places h p

/-- The reference meets line 4 for every check it runs. -/
theorem mod061_ref_line4 (B : Trans N → Option String) : mod061_line4 (refFuse (A := A) B) := by
  intro sets X Y σ hd hσ h p
  rw [(substSpec_iff hd).1 hσ, refFuse_terminals h]
  exact List.mem_eraseDups

/-- The reference meets line 5 for every check it runs. -/
theorem mod061_ref_line5 (B : Trans N → Option String) : mod061_line5 (refFuse (A := A) B) :=
  mod061_line5_of_eq fun _ _ X hd hp => refFuse_perm hp hd X

/-- The reference running `B` meets line 6 for every check `Build` that `B` accepts at least
whatever `Build` accepts. -/
theorem mod061_ref_line6 (Build B : Trans N → Option String)
    (hB : ∀ t, Build t = none → B t = none) : mod061_line6 Build (refFuse (A := A) B) := by
  intro sets X σ hd hσ h
  rw [(substSpec_iff hd).1 hσ] at h
  exact refFuse_accepts' hd fun d hd' => by
    obtain ⟨d', h1, h2⟩ := h d hd'
    exact ⟨d', h1, hB _ h2⟩

/-- The reference meets line 7 for every check it runs. -/
theorem mod061_ref_line7 (B : Trans N → Option String) : mod061_line7 (refFuse (A := A) B) :=
  mod061_line7_of fun _ X _ _ _ ho => refFuse_overlap_msg X ho

/-- The reference running `B` meets line 8 for every check `Build` that `B` accepts at least
whatever `Build` accepts. -/
theorem mod061_ref_line8 (Build B : Trans N → Option String)
    (hB : ∀ t, Build t = none → B t = none) : mod061_line8 Build (refFuse (A := A) B) :=
  mod061_seamFuse_line8 Build B hB seamOf mod061_seamOf_member

/-- The reference running `B` meets line 9 for every check `Build` that `B` accepts at least
whatever `Build` accepts. -/
theorem mod061_ref_line9 (Build B : Trans N → Option String)
    (hB : ∀ t, Build t = none → B t = none) : mod061_line9 Build (refFuse (A := A) B) :=
  mod061_seamFuse_line9 Build B hB seamOf mod061_seamOf_none

end Ref

/-- ✓ The reference fusion satisfies MOD-061 for every transition-builder check: it rejects two
sets that share a place with the runtimes' overlap message, rewrites every definition through the
first-member substitution, merging the input arcs of a transition with a moved input arc by the
[MOD-021] table, re-runs the check on each, names the fusion set (or, off every set, the place)
when a pair does not merge, keeps the places the substitution fixes and does not depend on the
order of disjoint sets. -/
@[evidence holds MOD_061]
theorem MOD_061_reference {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) : MOD_061 Build (refFuse (A := A) Build) :=
  ⟨mod061_ref_line1 Build, mod061_ref_line2 Build, mod061_ref_line3 Build,
    mod061_ref_line4 Build, mod061_ref_line5 Build, mod061_ref_line6 Build Build (fun _ h => h),
    mod061_ref_line7 Build, mod061_ref_line8 Build Build (fun _ h => h),
    mod061_ref_line9 Build Build (fun _ h => h)⟩

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A : Type} [DecidableEq N] [ToString N]

omit [DecidableEq N] [ToString N] in
/-- The substitution fusion asks for leaves a place it produced where it is. -/
theorem mod061_subst_idem {sets : List (FusionSet N)} {σ : N → N} (hσ : SubstSpec sets σ)
    (q : N) : σ (σ q) = σ q := by
  by_cases h : ∃ s ∈ sets, q ∈ s.members
  · obtain ⟨s, hs, hq⟩ := h
    have hne : s.members ≠ [] := List.ne_nil_of_mem hq
    rw [hσ.1 s hs q hq, hσ.1 s hs _ (s.canonical_mem hne q)]
    obtain ⟨n, ms⟩ := s
    cases ms with
    | nil => exact absurd rfl hne
    | cons a l => rfl
  · have h' : ∀ s ∈ sets, q ∉ s.members := fun s hs hq => h ⟨s, hs, hq⟩
    rw [hσ.2 q h', hσ.2 q h']

omit [ToString N] in
/-- **An off-table pair rejects** (AC4): in every model of line 1, on disjoint sets, a definition
whose rewrite meets an input pair the [MOD-021] table does not list fails the fusion. Fusing `a`
and `b` under a transition that takes `one()` from `a` and `all()` from `b` cannot succeed. -/
theorem mod061_offTable {F : FuseFn N A} (h1 : mod061_line1 F) {sets : List (FusionSet N)}
    {X : FuseNet N A} {σ : N → N} {d : CDef N A} {c : Collision N} (hd : FusionDisjoint sets)
    (hσ : SubstSpec sets σ) (hm : d ∈ X.defs) (hc : fuseDef σ d = .error c) :
    ∀ Y, F sets X ≠ .ok Y := by
  intro Y hY
  obtain ⟨ds, hds, -⟩ := except_map_ok_iff.1 (h1 sets X Y σ hd hσ hY)
  obtain ⟨y, -, hy⟩ := forall₂_mem_left ((mapM_except_ok_iff _ _ _).1 hds) d hm
  rw [hc] at hy
  cases hy

omit [ToString N] in
/-- **A rewrite the transition builder rejects rejects the fusion**: in every model of lines 1
and 2, on disjoint sets, a definition whose rewrite fails the check `Build` fails the fusion.
Fusing `a` and `b` under a transition that consumes from `a` and reads `b` gives a transition
that consumes from and reads `a`, which [EXEC-012] rejects, so the fusion fails. -/
theorem mod061_buildFails {Build : Trans N → Option String} {F : FuseFn N A}
    (h1 : mod061_line1 F) (h2 : mod061_line2 Build F) {sets : List (FusionSet N)}
    {X : FuseNet N A} {σ : N → N} {d d' : CDef N A} {m : String} (hd : FusionDisjoint sets)
    (hσ : SubstSpec sets σ) (hm : d ∈ X.defs) (hf : fuseDef σ d = .ok d')
    (hb : Build d'.toTrans = some m) : ∀ Y, F sets X ≠ .ok Y := by
  intro Y hY
  obtain ⟨ds, hds, hmap⟩ := except_map_ok_iff.1 (h1 sets X Y σ hd hσ hY)
  obtain ⟨y, hy, hfy⟩ := forall₂_mem_left ((mapM_except_ok_iff _ _ _).1 hds) d hm
  rw [hf] at hfy
  cases hfy
  have : d'.toTransDef ∈ Y.defs.map CDef.toTransDef := by
    rw [← hmap]; exact List.mem_map_of_mem hy
  obtain ⟨z, hz, hze⟩ := List.mem_map.1 this
  have hzb := h2 sets X Y hY z hz
  have hzt : z.toTrans = d'.toTrans := by
    show z.toTransDef.toTrans = d'.toTransDef.toTrans
    rw [hze]
  rw [hzt, hb] at hzb
  cases hzb

omit [ToString N] in
/-- **No removed member is a place of the result** (AC3): in every model of lines 1 and 3, on
disjoint sets, a member that is not the first declared member of its set is not a place of a
successful fusion. Fusing the limiter places `b1/limit`, `b2/limit` and `b3/limit` of three
leaky-bucket instances leaves `b1/limit` and removes the other two. -/
theorem mod061_removed {F : FuseFn N A} (h1 : mod061_line1 F) (h3 : mod061_line3 F)
    {sets : List (FusionSet N)} {X Y : FuseNet N A} {σ : N → N} (hd : FusionDisjoint sets)
    (hσ : SubstSpec sets σ) (hY : F sets X = .ok Y) {s : FusionSet N} (hs : s ∈ sets) {p : N}
    (hp : p ∈ s.members) (hne : p ≠ s.canonical p) : p ∉ Y.places := by
  intro hpY
  have hσp : σ p = s.canonical p := hσ.1 s hs p hp
  suffices h : σ p = p by rw [hσp] at h; exact hne h.symm
  rcases (h3 sets X Y σ hd hσ hY p).1 hpY with ⟨-, h⟩ | h | ⟨d, hdY, hpd⟩
  · exact h
  · obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
    exact mod061_subst_idem hσ q
  · obtain ⟨ds, hds, hmap⟩ := except_map_ok_iff.1 (h1 sets X Y σ hd hσ hY)
    have : d.toTransDef ∈ ds.map CDef.toTransDef := by
      rw [hmap]; exact List.mem_map_of_mem hdY
    obtain ⟨e, he, hee⟩ := List.mem_map.1 this
    obtain ⟨d0, -, hf⟩ := forall₂_mem_right ((mapM_except_ok_iff _ _ _).1 hds) e he
    have hpe : p ∈ e.namedPlaces := by
      show p ∈ e.toTransDef.namedPlaces
      rw [hee]; exact hpd
    obtain ⟨q, -, rfl⟩ := fuseDef_namedPlaces hf p hpe
    exact mod061_subst_idem hσ q

omit [DecidableEq N] in
/-- **Two sets sharing one place are reported in declaration order**: in every model of line 7,
two different sets `a` and `b` declared in that order that share exactly the place `p` reject
with the overlap message naming `p`, then `a`, then `b`. Declaring `x = {p}` and then `y = {p}`
gives `Fusion overlap: place 'p' appears in two fusion sets ('x' and 'y'). ...`. -/
theorem mod061_twoSets_msg {F : FuseFn N A} (h7 : mod061_line7 F) {a b : FusionSet N}
    (X : FuseNet N A) {p : N} (hne : a ≠ b) (hpa : p ∈ a.members) (hpb : p ∈ b.members)
    (hu : ∀ q ∈ b.members, q ∈ a.members → q = p) :
    F [a, b] X = .error (mod061_overlapMsg p a.name b.name) := by
  obtain ⟨q, r, s, he, hqr, hqs, hF⟩ :=
    h7 [a, b] X a b List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hne ⟨p, hpa, hpb⟩
  have hrs : r = a ∧ s = b := by
    have := he.eq_of_length rfl
    simp only [List.cons.injEq, and_true] at this
    exact this
  obtain ⟨rfl, rfl⟩ := hrs
  rw [hF, hu q hqs hqr]

end Consequences

/-! ### Example -/

/-- A builder whose transition `t` takes `one()` from `b`, then `one()` and `all()` from the
unfused place `q`. -/
def mod061_exFallback : FuseNet String Unit :=
  { places := ["a", "b", "q"],
    defs := [fuseExDef "t" [⟨"b", .one⟩, ⟨"q", .one⟩, ⟨"q", .all⟩] none] }

set_option maxRecDepth 20000 in
/-- ✓ Every line of MOD-061 is exercised by the reference on the worked examples of
`Reference/Fuse.lean`. Three leaky-bucket instances whose limiter places are fused all draw their
permit from `b1/limit`, the first declared member (AC1); `b1/limit` stays a place and `b2/limit`
and `b3/limit` are gone (AC3); a transition that takes `one()` from `a` and `one()` from `b`
takes `exactly(2)` from `a` once `a` and `b` are fused; `one()` with `all()` is rejected with
the [MOD-021] diagnostic naming the fusion set `ab` (AC4); when the pair that does not merge sits
on the unfused place `q`, the diagnostic names `q`; and two sets `x` and `y` that both list `p`
are rejected naming `p`, then `x`, then `y` (AC7). -/
@[evidence nonvacuous MOD_061]
theorem MOD_061_nonvacuous :
    (refFuse refBuild [fuseExLimiter] fuseExBuckets).toOption.map
        (fun Y => Y.defs.map fun d => d.core.inputs.map (·.place)) =
      some [["b1/req", "b1/limit"], ["b2/req", "b1/limit"], ["b3/req", "b1/limit"]] ∧
    (refFuse refBuild [fuseExLimiter] fuseExBuckets).toOption.map
        (fun Y => ["b1/limit", "b2/limit", "b3/limit"].map Y.places.contains) =
      some [true, false, false] ∧
    (refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExBoth).toOption.map
        (fun Y => Y.defs.map fun d => d.core.inputs.map fun s => (s.place, s.card)) =
      some [[("a", Card.exactly 2)]] ∧
    (match refFuse refBuild [⟨"ab", ["a", "b"]⟩] fuseExMix with
      | .error m => some m | .ok _ => none) =
      some "Fusion set 'ab': input arcs one() and all() collide on place 'a' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)." ∧
    (match refFuse refBuild [⟨"ab", ["a", "b"]⟩] mod061_exFallback with
      | .error m => some m | .ok _ => none) =
      some "Fusion set 'q': input arcs one() and all() collide on place 'q' and have no additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n)." ∧
    (match refFuse refBuild [⟨"x", ["p"]⟩, ⟨"y", ["p"]⟩] (⟨[], [], []⟩ : FuseNet String Unit) with
      | .error m => some m | .ok _ => none) =
      some "Fusion overlap: place 'p' appears in two fusion sets ('x' and 'y'). A place may appear in at most one fusion set (MOD-060)." :=
  ⟨fuseEx_buckets_inputs, fuseEx_buckets_places, fuseEx_both_merged, fuseEx_mix_rejected,
    by decide, by decide⟩

/-- **A set that lists its first member again keeps it** (step 3, "the canonical member remains"):
fusing the set `aba` with members `a, b, a` in a builder that declares `a` and `b` and has no
transition leaves `a` as the only place. A wrong fusion that treats every later position as
non-canonical (the behaviour RD-25 recorded) drops `a` here. -/
theorem mod061_dupCanonical_kept :
    (refFuse refBuild [⟨"aba", ["a", "b", "a"]⟩] (⟨["a", "b"], [], []⟩ : FuseNet String Unit)).toOption.map
      (·.places) = some ["a"] := by
  decide

/-! ### Wrong fusions -/

section Wrong

variable {N A : Type} [DecidableEq N] [ToString N]

omit [DecidableEq N] [ToString N] in
/-- A projection of a successful result. -/
theorem mod061_proj {ε α β : Type} {e : Except ε α} {y : α} (g : α → β) (h : e = .ok y) :
    e.toOption.map g = some (g y) := by
  rw [h]; rfl

omit [DecidableEq N] [ToString N] in
/-- A result whose `toOption` is `some` is a success. -/
theorem mod061_ok_of_isSome {ε α : Type} {e : Except ε α} (h : e.toOption.isSome = true) :
    ∃ y, e = .ok y := by
  cases e with
  | error _ => cases h
  | ok y => exact ⟨y, rfl⟩

omit [DecidableEq N] [ToString N] in
/-- The rejection message of a result, if any. -/
def mod061_err {α : Type} : Except String α → Option String
  | .error m => some m
  | .ok _ => none

/-- A fusion that post-processes the reference's success with `pp`; rejections are the
reference's. The shape of four wrong fusions below. -/
def mod061_ppFuse (Build : Trans N → Option String)
    (pp : List (FusionSet N) → FuseNet N A → FuseNet N A → FuseNet N A) : FuseFn N A :=
  fun sets X => (refFuse Build sets X).map (pp sets X)

theorem mod061_ppFuse_ok {Build : Trans N → Option String}
    {pp : List (FusionSet N) → FuseNet N A → FuseNet N A → FuseNet N A}
    {sets : List (FusionSet N)} {X Y : FuseNet N A} :
    mod061_ppFuse Build pp sets X = .ok Y ↔ ∃ Z, refFuse Build sets X = .ok Z ∧ pp sets X Z = Y :=
  except_map_ok_iff

theorem mod061_ppFuse_error {Build : Trans N → Option String}
    {pp : List (FusionSet N) → FuseNet N A → FuseNet N A → FuseNet N A}
    {sets : List (FusionSet N)} {X : FuseNet N A} {m : String}
    (h : refFuse Build sets X = .error m) : mod061_ppFuse Build pp sets X = .error m := by
  show (refFuse Build sets X).map (pp sets X) = _
  rw [h]; rfl

/-- A post-processing fusion meets lines 6 to 9: its rejections are the reference's. -/
theorem mod061_ppFuse_6to9 (Build : Trans N → Option String)
    (pp : List (FusionSet N) → FuseNet N A → FuseNet N A → FuseNet N A) :
    mod061_line6 Build (mod061_ppFuse Build pp) ∧ mod061_line7 (mod061_ppFuse Build pp) ∧
      mod061_line8 Build (mod061_ppFuse Build pp) ∧ mod061_line9 Build (mod061_ppFuse Build pp) := by
  refine ⟨fun sets X σ hd hσ h => ?_,
    mod061_line7_of fun _ X _ _ _ ho => mod061_ppFuse_error (refFuse_overlap_msg X ho),
    fun sets X σ pre d post c s hd hσ hX hpre hc hs hp => ?_,
    fun sets X σ pre d post c hd hσ hX hpre hc hp => ?_⟩
  · obtain ⟨Z, hZ⟩ := mod061_ref_line6 Build Build (fun _ h => h) sets X σ hd hσ h
    exact ⟨pp sets X Z, mod061_ppFuse_ok.2 ⟨Z, hZ, rfl⟩⟩
  · rcases mod061_ref_line8 Build Build (fun _ h => h) sets X σ pre d post c s hd hσ hX hpre hc hs hp
      with h | h
    · exact Or.inl (mod061_ppFuse_error h)
    · exact Or.inr (mod061_ppFuse_error h)
  · rcases mod061_ref_line9 Build Build (fun _ h => h) sets X σ pre d post c hd hσ hX hpre hc hp
      with h | h
    · exact Or.inl (mod061_ppFuse_error h)
    · exact Or.inr (mod061_ppFuse_error h)

/-- A post-processing fusion whose post-processing does not read the order of disjoint sets meets
line 5. -/
theorem mod061_ppFuse_5 (Build : Trans N → Option String)
    (pp : List (FusionSet N) → FuseNet N A → FuseNet N A → FuseNet N A)
    (hpp : ∀ sets sets', FusionDisjoint sets → sets.Perm sets' → pp sets = pp sets') :
    mod061_line5 (mod061_ppFuse Build pp) :=
  mod061_line5_of_eq fun sets sets' X hd hp => by
    show (refFuse Build sets X).map (pp sets X) = (refFuse Build sets' X).map (pp sets' X)
    rw [refFuse_perm hp hd X, hpp sets sets' hd hp]

/-- A fusion whose successes are the reference's meets lines 1 to 4 and 6. -/
theorem mod061_okIff {Build : Trans N → Option String} {F : FuseFn N A}
    (h : ∀ sets X Y, F sets X = .ok Y ↔ refFuse Build sets X = .ok Y) :
    mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
      mod061_line6 Build F :=
  ⟨fun sets X Y σ hd hσ hY => mod061_ref_line1 Build sets X Y σ hd hσ ((h _ _ _).1 hY),
    fun sets X Y hY => mod061_ref_line2 Build sets X Y ((h _ _ _).1 hY),
    fun sets X Y σ hd hσ hY => mod061_ref_line3 Build sets X Y σ hd hσ ((h _ _ _).1 hY),
    fun sets X Y σ hd hσ hY => mod061_ref_line4 Build sets X Y σ hd hσ ((h _ _ _).1 hY),
    fun sets X σ hd hσ hb => by
      obtain ⟨Y, hY⟩ := mod061_ref_line6 Build Build (fun _ h => h) sets X σ hd hσ hb
      exact ⟨Y, (h _ _ _).2 hY⟩⟩

/-- A fusion that rebuilds every transition with the default priority 0. -/
def mod061_prioFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_ppFuse Build fun _ _ Z => { Z with defs := Z.defs.map fun d => { d with priority := 0 } }

/-- A fusion that keeps the builder's declared places, removed members included. -/
def mod061_keepPlacesFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_ppFuse Build fun _ X Z => { Z with places := Z.places ++ X.places }

/-- A fusion that keeps the declared terminal places as they were declared. -/
def mod061_keepTerminalsFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_ppFuse Build fun _ X Z => { Z with terminals := X.terminals }

/-- A fusion that lists the first members of the sets first, in the order the sets are
declared. Its places depend on the order of the sets, but only as a list: it meets MOD-061. -/
def mod061_setOrderFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_ppFuse Build fun sets _ Z =>
    { Z with places := (sets.filterMap (·.members.head?)).filter (fun p => decide (p ∈ Z.places)) ++
        Z.places }

/-- The transition builder's check `Build` with the name of the first declared set appended to
every rejection message. -/
def mod061_tagBuild (sets : List (FusionSet N)) (Build : Trans N → Option String) :
    Trans N → Option String :=
  fun t => (Build t).map (· ++ ((sets.head?.map (·.name)).getD ""))

/-- A fusion whose rejections by the transition builder name the first declared set. -/
def mod061_orderMsgFuse (Build : Trans N → Option String) : FuseFn N A := fun sets X =>
  refFuse (mod061_tagBuild sets Build) sets X

/-- A fusion that never runs the transition builder's check. -/
def mod061_noCheckFuse : FuseFn N A := refFuse fun _ => none

/-- A fusion that rejects whatever the reference accepts. -/
def mod061_rejectOkFuse (Build : Trans N → Option String) : FuseFn N A :=
  fun sets X => (refFuse Build sets X).bind fun _ => .error "rejected"

/-- A fusion that rejects an overlap of two sets only, and accepts an overlap among three or more
sets with an empty result. -/
def mod061_pairOverlapFuse (Build : Trans N → Option String) : FuseFn N A := fun sets X =>
  if 3 ≤ sets.length ∧ (findOverlap sets).isSome = true then .ok ⟨[], [], []⟩
  else refFuse Build sets X

/-- A fusion whose overlap message names the two sets in reverse order. -/
def mod061_swapOverlapFuse (Build : Trans N → Option String) : FuseFn N A := fun sets X =>
  match findOverlap sets with
  | some (p, a, b) => .error (overlapMsg p b a)
  | none => refFuse Build sets X

/-- A fusion whose collision message names the place instead of its fusion set. -/
def mod061_placeSeamFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_seamFuse Build fun _ p => mod061_placeSeam p

/-- A seam that names the set of a member and leaves the name empty on a place no set lists. -/
def mod061_blankSeam (sets : List (FusionSet N)) (p : N) : String :=
  match fusionOwner sets p with
  | some s => mod061_seam s
  | none => "Fusion set ''"

/-- A fusion whose collision message on a place no set lists leaves the seam's name empty. -/
def mod061_blankSeamFuse (Build : Trans N → Option String) : FuseFn N A :=
  mod061_seamFuse Build mod061_blankSeam

end Wrong

/-! ### Mutants, one per line -/

section Mutants

variable {N A : Type} [DecidableEq N] [ToString N]

/-- Mutant reading: MOD-061 without line 1 (a success need not hold the rewritten
definitions). -/
def MOD_061_mutant_noRewrite (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧ mod061_line5 F ∧
    mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 2 (the transition builder's check need not pass). -/
def MOD_061_mutant_noCheck (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line3 F ∧ mod061_line4 F ∧ mod061_line5 F ∧
    mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 3 (removed members may stay places). -/
def MOD_061_mutant_noPlaces (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line4 F ∧ mod061_line5 F ∧
    mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 4 (terminal places need not follow the fusion). -/
def MOD_061_mutant_noTerminals (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line5 F ∧
    mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 5 (the outcome may depend on the order of the sets). -/
def MOD_061_mutant_orderDependent (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
    mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 6, the rejections and the shape of a success only
(skeptic correction S2 of the composition design: a partial function needs an acceptance
line). -/
def MOD_061_mutant_noAcceptance (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
    mod061_line5 F ∧ mod061_line7 F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 7 (overlap rejection read as a SHOULD). -/
def MOD_061_mutant_overlapOptional (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
    mod061_line5 F ∧ mod061_line6 Build F ∧ mod061_line8 Build F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 8 (any collision message on a member). -/
def MOD_061_mutant_anySeam (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
    mod061_line5 F ∧ mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line9 Build F

/-- Mutant reading: MOD-061 without line 9 (any collision message on a place no set lists). -/
def MOD_061_mutant_anyFallbackSeam (Build : Trans N → Option String) (F : FuseFn N A) : Prop :=
  mod061_line1 F ∧ mod061_line2 Build F ∧ mod061_line3 F ∧ mod061_line4 F ∧
    mod061_line5 F ∧ mod061_line6 Build F ∧ mod061_line7 F ∧ mod061_line8 Build F

end Mutants

/-! #### Line 1: a fusion that drops the priority -/

/-- An example builder: one transition `t` of priority 3 taking one token from `a`. -/
def mod061_exPrio : FuseNet String Unit :=
  { places := ["a"], defs := [{ fuseExDef "t" [⟨"a", .one⟩] none with priority := 3 }] }

/-- The fusion that rebuilds every transition with priority 0 kills the mutant: it meets every
line but line 1, and fusing no set over a transition of priority 3 returns one of priority 0. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_noRewrite_killed :
    MOD_061_mutant_noRewrite refBuild (mod061_prioFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_prioFuse (N := String) (A := Unit) refBuild) := by
  have h69 := mod061_ppFuse_6to9 (N := String) (A := Unit) refBuild
    (fun _ _ Z => { Z with defs := Z.defs.map fun d => { d with priority := 0 } })
  refine ⟨⟨fun sets X Y hY d hd => ?_, fun sets X Y σ hd hσ hY p => ?_,
    fun sets X Y σ hd hσ hY p => ?_,
    mod061_ppFuse_5 refBuild _ (fun _ _ _ _ => rfl), h69⟩, fun h => ?_⟩
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd
    exact mod061_ref_line2 refBuild sets X Z hZ d0 hd0
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    rw [mod061_ref_line3 refBuild sets X Z σ hd hσ hZ p]
    simp only [List.mem_map]
    constructor
    · rintro (h | h | ⟨d, hd, hp⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨_, ⟨d, hd, rfl⟩, hp⟩)
    · rintro (h | h | ⟨_, ⟨d, hd, rfl⟩, hp⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨d, hd, hp⟩)
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line4 refBuild sets X Z σ hd hσ hZ p
  · have hd : FusionDisjoint ([] : List (FusionSet String)) := List.Pairwise.nil
    obtain ⟨Y, hY⟩ := mod061_ok_of_isSome (e := mod061_prioFuse refBuild [] mod061_exPrio)
      (by decide)
    have e1 := mod061_proj (List.map (·.priority)) (h.1 [] mod061_exPrio Y _ hd (refSubst_spec hd) hY)
    have e2 := mod061_proj (fun Y : FuseNet String Unit => Y.defs.map (·.priority)) hY
    have c1 : ((mod061_exPrio.defs.mapM (fuseDef (refSubst []))).map
        (·.map CDef.toTransDef)).toOption.map (List.map (·.priority)) = some [3] := by decide
    have c2 : (mod061_prioFuse refBuild [] mod061_exPrio).toOption.map
        (fun Y : FuseNet String Unit => Y.defs.map (·.priority)) = some [0] := by decide
    rw [c1] at e1
    rw [c2] at e2
    simp only [Option.some.injEq, List.map_map] at e1 e2
    have : ([3] : List Int) = [0] := e1.trans e2.symm
    exact absurd this (by decide)

/-! #### Line 2: a fusion that never runs the check -/

/-- The fusion that never runs the transition builder's check kills the mutant: it meets every
line but line 2, and fusing `a` and `b` under a transition that consumes from `a` and reads `b`
returns a transition that consumes from and reads `a`, which the reference builder rejects
([EXEC-012]). -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_noCheck_killed :
    MOD_061_mutant_noCheck refBuild (mod061_noCheckFuse (N := String) (A := Unit)) ∧
      ¬ MOD_061 refBuild (mod061_noCheckFuse (N := String) (A := Unit)) := by
  have hB : ∀ t : Trans String, refBuild t = none → (fun _ => none : Trans String → Option String) t = none :=
    fun _ _ => rfl
  refine ⟨⟨mod061_ref_line1 _, mod061_ref_line3 _, mod061_ref_line4 _, mod061_ref_line5 _,
    mod061_ref_line6 refBuild _ hB, mod061_ref_line7 _, mod061_ref_line8 refBuild _ hB,
    mod061_ref_line9 refBuild _ hB⟩, fun h => ?_⟩
  obtain ⟨Y, hY⟩ := mod061_ok_of_isSome
    (e := mod061_noCheckFuse (N := String) (A := Unit) [⟨"ab", ["a", "b"]⟩] fuseExInRead)
    (by decide)
  have e1 := mod061_proj (fun Y : FuseNet String Unit => Y.defs.all fun d => (refBuild d.toTrans).isNone) hY
  have c1 : (mod061_noCheckFuse (N := String) (A := Unit) [⟨"ab", ["a", "b"]⟩] fuseExInRead).toOption.map
      (fun Y : FuseNet String Unit => Y.defs.all fun d => (refBuild d.toTrans).isNone) = some false := by
    decide
  rw [c1] at e1
  have hall : (Y.defs.all fun d => (refBuild d.toTrans).isNone) = true := by
    rw [List.all_eq_true]
    intro d hd
    rw [h.2.1 _ _ Y hY d hd]; rfl
  simp only [Option.some.injEq] at e1
  rw [hall] at e1
  cases e1

/-! #### Line 3: a fusion that keeps the removed members -/

/-- The fusion that keeps the builder's declared places kills the mutant: it meets every line but
line 3, and fusing `a` and `b` in a builder declaring both keeps `b`. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_noPlaces_killed :
    MOD_061_mutant_noPlaces refBuild (mod061_keepPlacesFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_keepPlacesFuse (N := String) (A := Unit) refBuild) := by
  have h69 := mod061_ppFuse_6to9 (N := String) (A := Unit) refBuild
    (fun _ X Z => { Z with places := Z.places ++ X.places })
  refine ⟨⟨fun sets X Y σ hd hσ hY => ?_, fun sets X Y hY => ?_, fun sets X Y σ hd hσ hY => ?_,
    mod061_ppFuse_5 refBuild _ (fun _ _ _ _ => rfl), h69⟩, fun h => ?_⟩
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line1 refBuild sets X Z σ hd hσ hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line2 refBuild sets X Z hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line4 refBuild sets X Z σ hd hσ hZ
  · let sets : List (FusionSet String) := [⟨"ab", ["a", "b"]⟩]
    let X : FuseNet String Unit := ⟨["a", "b"], [], []⟩
    have hd : FusionDisjoint sets := (findOverlap_eq_none_iff sets).1 (by decide)
    obtain ⟨Y, hY⟩ := mod061_ok_of_isSome (e := mod061_keepPlacesFuse refBuild sets X) (by decide)
    have e1 := mod061_proj (fun Y : FuseNet String Unit => (Y.places.contains "b", Y.defs.length)) hY
    have c1 : (mod061_keepPlacesFuse refBuild sets X).toOption.map
        (fun Y : FuseNet String Unit => (Y.places.contains "b", Y.defs.length)) = some (true, 0) := by
      decide
    rw [c1] at e1
    simp only [Option.some.injEq, Prod.mk.injEq] at e1
    have hb : "b" ∈ Y.places := List.contains_iff_mem.1 e1.1.symm
    have hnil : Y.defs = [] := List.eq_nil_of_length_eq_zero e1.2.symm
    rcases (h.2.2.1 sets X Y _ hd (refSubst_spec hd) hY "b").1 hb with ⟨-, h⟩ | h | ⟨d, hd', -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [hnil] at hd'; cases hd'

/-! #### Line 4: a fusion that keeps the declared terminal places -/

/-- The fusion that keeps the declared terminal places kills the mutant: it meets every line but
line 4, and fusing `a` and `b` with `b` declared terminal leaves `b` terminal instead of `a`. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_noTerminals_killed :
    MOD_061_mutant_noTerminals refBuild (mod061_keepTerminalsFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_keepTerminalsFuse (N := String) (A := Unit) refBuild) := by
  have h69 := mod061_ppFuse_6to9 (N := String) (A := Unit) refBuild
    (fun _ X Z => { Z with terminals := X.terminals })
  refine ⟨⟨fun sets X Y σ hd hσ hY => ?_, fun sets X Y hY => ?_, fun sets X Y σ hd hσ hY => ?_,
    mod061_ppFuse_5 refBuild _ (fun _ _ _ _ => rfl), h69⟩, fun h => ?_⟩
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line1 refBuild sets X Z σ hd hσ hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line2 refBuild sets X Z hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line3 refBuild sets X Z σ hd hσ hZ
  · let sets : List (FusionSet String) := [⟨"ab", ["a", "b"]⟩]
    have hd : FusionDisjoint sets := (findOverlap_eq_none_iff sets).1 (by decide)
    obtain ⟨Y, hY⟩ := mod061_ok_of_isSome (e := mod061_keepTerminalsFuse refBuild sets fuseExTerm)
      (by decide)
    have e1 := mod061_proj (fun Y : FuseNet String Unit => Y.terminals) hY
    have c1 : (mod061_keepTerminalsFuse refBuild sets fuseExTerm).toOption.map
        (fun Y : FuseNet String Unit => Y.terminals) = some ["b"] := by decide
    rw [c1] at e1
    simp only [Option.some.injEq] at e1
    have hb : "b" ∈ Y.terminals := by rw [← e1]; exact List.mem_cons_self
    have := (h.2.2.2.1 sets fuseExTerm Y _ hd (refSubst_spec hd) hY "b").1 hb
    exact absurd this (by decide)

/-! #### Line 5: a fusion whose builder rejections name the first declared set -/

/-- Two disjoint sets `A = {a, a2}` and `B = {b, b2}`. -/
def mod061_exSetsAB : List (FusionSet String) := [⟨"A", ["a", "a2"]⟩, ⟨"B", ["b", "b2"]⟩]

/-- The same two sets declared the other way round. -/
def mod061_exSetsBA : List (FusionSet String) := [⟨"B", ["b", "b2"]⟩, ⟨"A", ["a", "a2"]⟩]

/-- A builder whose transition `t` consumes from `a` and reads `a2`: once `a` and `a2` are fused
it consumes from and reads `a`, which the reference builder rejects ([EXEC-012]). -/
def mod061_exOrder : FuseNet String Unit :=
  { places := ["a", "a2", "b", "b2"], defs := [fuseExDef "t" [⟨"a", .one⟩] none ["a2"]] }

/-- The tagged check rejects exactly what the check rejects. -/
theorem mod061_tagBuild_none {N : Type} (sets : List (FusionSet N)) (Build : Trans N → Option String)
    (t : Trans N) : mod061_tagBuild sets Build t = none ↔ Build t = none :=
  Option.map_eq_none_iff

/-- The fusion with tagged rejections succeeds exactly when the reference does. -/
theorem mod061_orderMsg_ok {N A : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (sets : List (FusionSet N)) (X Y : FuseNet N A) :
    mod061_orderMsgFuse Build sets X = .ok Y ↔ refFuse Build sets X = .ok Y := by
  simp only [mod061_orderMsgFuse, refFuse_ok_iff, mod061_tagBuild_none]

set_option maxRecDepth 20000 in
/-- The fusion whose builder rejections carry the name of the first declared set kills the
mutant: it meets every line but line 5, and over a transition that consumes from `a` and reads
`a2`, fusing `{a, a2}` and `{b, b2}` gives one message when `A` is declared first and another
when `B` is. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_orderDependent_killed :
    MOD_061_mutant_orderDependent refBuild (mod061_orderMsgFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_orderMsgFuse (N := String) (A := Unit) refBuild) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := mod061_okIff (mod061_orderMsg_ok (N := String) (A := Unit) refBuild)
  have hB : ∀ sets (t : Trans String), refBuild t = none → mod061_tagBuild sets refBuild t = none :=
    fun sets t h => (mod061_tagBuild_none sets refBuild t).2 h
  refine ⟨⟨h1, h2, h3, h4, h6,
    mod061_line7_of fun sets X _ _ _ ho => refFuse_overlap_msg (Build := mod061_tagBuild sets refBuild) X ho,
    fun sets X σ pre d post c s hd hσ hX hpre hc hs hp =>
      mod061_ref_line8 refBuild (mod061_tagBuild sets refBuild) (hB sets) sets X σ pre d post c s hd
        hσ hX hpre hc hs hp,
    fun sets X σ pre d post c hd hσ hX hpre hc hp =>
      mod061_ref_line9 refBuild (mod061_tagBuild sets refBuild) (hB sets) sets X σ pre d post c hd
        hσ hX hpre hc hp⟩, fun h => ?_⟩
  have hd : FusionDisjoint mod061_exSetsAB := (findOverlap_eq_none_iff _).1 (by decide)
  have hne : mod061_err (mod061_orderMsgFuse refBuild mod061_exSetsAB mod061_exOrder) ≠
      mod061_err (mod061_orderMsgFuse refBuild mod061_exSetsBA mod061_exOrder) := by decide
  have hsome : (mod061_err (mod061_orderMsgFuse refBuild mod061_exSetsAB mod061_exOrder)).isSome =
      true := by decide
  cases hF : mod061_orderMsgFuse refBuild mod061_exSetsAB mod061_exOrder with
  | ok Y => rw [hF] at hsome; cases hsome
  | error m =>
    have h' := (h.2.2.2.2.1 mod061_exSetsAB mod061_exSetsBA mod061_exOrder hd
      (List.Perm.swap _ _ [])).1 m hF
    rw [hF, h'] at hne
    exact hne rfl

/-- **Place order is not normative**: the fusion that lists the first members of the sets first,
in declaration order, meets MOD-061. Declaring `A = {a, a2}` before `B = {b, b2}` lists the
places `a, b, a, b`, declaring `B` first lists `b, a, a, b`; both are the places `a` and `b`. -/
theorem mod061_setOrder_meets :
    MOD_061 refBuild (mod061_setOrderFuse (N := String) (A := Unit) refBuild) := by
  have h69 := mod061_ppFuse_6to9 (N := String) (A := Unit) refBuild
    (fun sets _ Z => { Z with places :=
      (sets.filterMap (·.members.head?)).filter (fun p => decide (p ∈ Z.places)) ++ Z.places })
  have hmem : ∀ (sets : List (FusionSet String)) (Z : FuseNet String Unit) p,
      p ∈ (sets.filterMap (·.members.head?)).filter (fun p => decide (p ∈ Z.places)) ++ Z.places ↔
        p ∈ Z.places := by
    intro sets Z p
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.elim (·.2) id, Or.inr⟩
  refine ⟨fun sets X Y σ hd hσ hY => ?_, fun sets X Y hY => ?_, fun sets X Y σ hd hσ hY p => ?_,
    fun sets X Y σ hd hσ hY => ?_, fun sets sets' X hd hp => ⟨fun m hm => ?_, fun Y hY => ?_⟩, h69⟩
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line1 refBuild sets X Z σ hd hσ hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line2 refBuild sets X Z hZ
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    rw [← mod061_ref_line3 refBuild sets X Z σ hd hσ hZ p]
    exact hmem sets Z p
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    exact mod061_ref_line4 refBuild sets X Z σ hd hσ hZ
  · cases hr : refFuse refBuild sets X with
    | ok Z =>
      have : mod061_setOrderFuse refBuild sets X = .ok _ := mod061_ppFuse_ok.2 ⟨Z, hr, rfl⟩
      rw [this] at hm; cases hm
    | error m' =>
      have e1 : mod061_setOrderFuse refBuild sets X = .error m' := mod061_ppFuse_error hr
      rw [e1] at hm
      cases hm
      exact mod061_ppFuse_error (by rw [← refFuse_perm hp hd X]; exact hr)
  · obtain ⟨Z, hZ, rfl⟩ := mod061_ppFuse_ok.1 hY
    have hZ' : refFuse refBuild sets' X = .ok Z := by rw [← refFuse_perm hp hd X]; exact hZ
    refine ⟨_, mod061_ppFuse_ok.2 ⟨Z, hZ', rfl⟩, rfl, fun p => ?_, fun _ => Iff.rfl⟩
    exact (hmem sets Z p).trans (hmem sets' Z p).symm

/-! #### Line 6: a fusion that rejects every success -/

/-- The fusion that rejects whatever the reference accepts kills the mutant: it meets every line
but line 6 (it never succeeds, and its rejections otherwise are the reference's), and rejects a
builder with no transition and no fusion set. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_noAcceptance_killed :
    MOD_061_mutant_noAcceptance refBuild (mod061_rejectOkFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_rejectOkFuse (N := String) (A := Unit) refBuild) := by
  have hNever : ∀ sets X Y, mod061_rejectOkFuse (N := String) (A := Unit) refBuild sets X ≠ .ok Y := by
    intro sets X Y h
    unfold mod061_rejectOkFuse at h
    cases hr : refFuse refBuild sets X with
    | error m => rw [hr] at h; cases h
    | ok Z => rw [hr] at h; cases h
  have keep : ∀ sets X m, refFuse (N := String) (A := Unit) refBuild sets X = .error m →
      mod061_rejectOkFuse refBuild sets X = .error m := by
    intro sets X m hr
    show (refFuse refBuild sets X).bind _ = _
    rw [hr]; rfl
  refine ⟨⟨fun _ _ Y _ _ _ hY => absurd hY (hNever _ _ Y), fun _ _ Y hY => absurd hY (hNever _ _ Y),
    fun _ _ Y _ _ _ hY => absurd hY (hNever _ _ Y), fun _ _ Y _ _ _ hY => absurd hY (hNever _ _ Y),
    mod061_line5_of_eq fun sets sets' X hd hp => ?_,
    mod061_line7_of fun _ X _ _ _ ho => keep _ _ _ (refFuse_overlap_msg X ho),
    fun sets X σ pre d post c s hd hσ hX hpre hc hs hp => ?_,
    fun sets X σ pre d post c hd hσ hX hpre hc hp => ?_⟩, fun h => ?_⟩
  · show (refFuse refBuild sets X).bind _ = (refFuse refBuild sets' X).bind _
    rw [refFuse_perm hp hd X]
  · rcases mod061_ref_line8 refBuild refBuild (fun _ h => h) sets X σ pre d post c s hd hσ hX hpre
      hc hs hp with h | h
    · exact Or.inl (keep _ _ _ h)
    · exact Or.inr (keep _ _ _ h)
  · rcases mod061_ref_line9 refBuild refBuild (fun _ h => h) sets X σ pre d post c hd hσ hX hpre
      hc hp with h | h
    · exact Or.inl (keep _ _ _ h)
    · exact Or.inr (keep _ _ _ h)
  · have hd : FusionDisjoint ([] : List (FusionSet String)) := List.Pairwise.nil
    obtain ⟨Y, hY⟩ := h.2.2.2.2.2.1 [] ⟨[], [], []⟩ _ hd (refSubst_spec hd) (fun _ h => nomatch h)
    exact hNever _ _ _ hY

/-! #### Line 7: a fusion that tolerates an overlap among three sets -/

/-- Three sets: `ab` and `cb` share `b`, and `d` shares nothing. -/
def mod061_exSets3 : List (FusionSet String) := [⟨"ab", ["a", "b"]⟩, ⟨"cb", ["c", "b"]⟩, ⟨"d", ["d"]⟩]

/-- The fusion that rejects an overlap only between two sets kills the mutant: it meets every line
but line 7 (every other line is about disjoint sets), and accepts the three sets `ab`, `cb`, `d`,
although `ab` and `cb` share `b`. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_overlapOptional_killed :
    MOD_061_mutant_overlapOptional refBuild (mod061_pairOverlapFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_pairOverlapFuse (N := String) (A := Unit) refBuild) := by
  have eq : ∀ sets X, FusionDisjoint sets →
      mod061_pairOverlapFuse (N := String) (A := Unit) refBuild sets X = refFuse refBuild sets X := by
    intro sets X hd
    unfold mod061_pairOverlapFuse
    rw [if_neg (by rw [(findOverlap_eq_none_iff sets).2 hd]; simp)]
  refine ⟨⟨fun sets X Y σ hd hσ hY => mod061_ref_line1 refBuild sets X Y σ hd hσ (eq sets X hd ▸ hY),
    fun sets X Y hY => ?_,
    fun sets X Y σ hd hσ hY => mod061_ref_line3 refBuild sets X Y σ hd hσ (eq sets X hd ▸ hY),
    fun sets X Y σ hd hσ hY => mod061_ref_line4 refBuild sets X Y σ hd hσ (eq sets X hd ▸ hY),
    mod061_line5_of_eq fun sets sets' X hd hp => by
      rw [eq sets X hd, eq sets' X (hd.perm hp), refFuse_perm hp hd X],
    fun sets X σ hd hσ hb => by
      rw [eq sets X hd]; exact mod061_ref_line6 refBuild refBuild (fun _ h => h) sets X σ hd hσ hb,
    fun sets X σ pre d post c s hd hσ hX hpre hc hs hp => by
      rw [eq sets X hd]
      exact mod061_ref_line8 refBuild refBuild (fun _ h => h) sets X σ pre d post c s hd hσ hX hpre
        hc hs hp,
    fun sets X σ pre d post c hd hσ hX hpre hc hp => by
      rw [eq sets X hd]
      exact mod061_ref_line9 refBuild refBuild (fun _ h => h) sets X σ pre d post c hd hσ hX hpre
        hc hp⟩, fun h => ?_⟩
  · unfold mod061_pairOverlapFuse at hY
    split at hY
    · cases hY; intro d hd; cases hd
    · exact mod061_ref_line2 refBuild sets X Y hY
  · have hne : (⟨"ab", ["a", "b"]⟩ : FusionSet String) ≠ ⟨"cb", ["c", "b"]⟩ := fun e =>
      absurd (congrArg FusionSet.name e) (by decide)
    obtain ⟨_, _, _, -, -, -, hF⟩ := h.2.2.2.2.2.2.1 mod061_exSets3 ⟨[], [], []⟩ _ _
      List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hne ⟨"b", by decide, by decide⟩
    have hok : mod061_pairOverlapFuse (N := String) (A := Unit) refBuild mod061_exSets3 ⟨[], [], []⟩ =
        .ok ⟨[], [], []⟩ := by
      unfold mod061_pairOverlapFuse
      rw [if_pos (by decide)]
    rw [hok] at hF
    cases hF

/-- ✗ A fusion that names the two overlapping sets in reverse order violates MOD-061 (line 7):
declaring `x = {p}` and then `y = {p}` reports `('y' and 'x')`. -/
@[evidence forbids MOD_061]
theorem MOD_061_forbids_swapOverlap :
    ¬ MOD_061 refBuild (mod061_swapOverlapFuse (N := String) (A := Unit) refBuild) := by
  intro h
  have hne : (⟨"x", ["p"]⟩ : FusionSet String) ≠ ⟨"y", ["p"]⟩ := fun e =>
    absurd (congrArg FusionSet.name e) (by decide)
  have e1 := congrArg mod061_err (mod061_twoSets_msg h.2.2.2.2.2.2.1
    (⟨[], [], []⟩ : FuseNet String Unit) hne (p := "p") (by decide) (by decide) (by decide))
  exact absurd e1 (by decide)

/-! #### Line 8: a fusion that names the place instead of its set -/

/-- The collision of the mix example: `one()` met by `all()` on `a`. -/
theorem mod061_mix_collision :
    fuseDef (refSubst [⟨"ab", ["a", "b"]⟩]) (fuseExDef "t" [⟨"a", .one⟩, ⟨"b", .all⟩] none) =
      .error (⟨"a", .one, .all⟩ : Collision String) := by
  rfl

/-- The fusion that names the place instead of its fusion set kills the mutant: it meets every
line but line 8, and reports the `one()` and `all()` pair on `a` under the set `ab` with the seam
`Fusion set 'a'`. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_anySeam_killed :
    MOD_061_mutant_anySeam refBuild (mod061_placeSeamFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_placeSeamFuse (N := String) (A := Unit) refBuild) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := mod061_okIff (F := mod061_placeSeamFuse (N := String) (A := Unit) refBuild)
    (mod061_seamFuse_ok (N := String) (A := Unit) refBuild fun _ p => mod061_placeSeam p)
  refine ⟨⟨h1, h2, h3, h4, mod061_seamFuse_line5 refBuild _ (fun _ _ _ _ => rfl), h6,
    mod061_seamFuse_line7 refBuild _,
    mod061_seamFuse_line9 refBuild refBuild (fun _ h => h) _ (fun _ _ _ => rfl)⟩, fun h => ?_⟩
  let sets : List (FusionSet String) := [⟨"ab", ["a", "b"]⟩]
  have hd : FusionDisjoint sets := (findOverlap_eq_none_iff sets).1 (by decide)
  have := h.2.2.2.2.2.2.2.1 sets fuseExMix _ [] _ [] _ ⟨"ab", ["a", "b"]⟩ hd (refSubst_spec hd) rfl
    (fun _ h => nomatch h) mod061_mix_collision List.mem_cons_self (by decide)
  rcases this with e | e
  · exact absurd (congrArg mod061_err e) (by decide)
  · exact absurd (congrArg mod061_err e) (by decide)

/-! #### Line 9: a fusion that leaves the seam blank off every set -/

/-- The collision of the fallback example: `one()` met by `all()` on the unfused place `q`. -/
theorem mod061_fallback_collision :
    fuseDef (refSubst [⟨"ab", ["a", "b"]⟩])
        (fuseExDef "t" [⟨"b", .one⟩, ⟨"q", .one⟩, ⟨"q", .all⟩] none) =
      .error (⟨"q", .one, .all⟩ : Collision String) := by
  rfl

/-- The fusion that leaves the seam's name blank on a place no set lists kills the mutant: it
meets every line but line 9, and reports the `one()` and `all()` pair on the unfused place `q`
with the seam `Fusion set ''` instead of `Fusion set 'q'`. -/
@[evidence mutant MOD_061]
theorem MOD_061_mutant_anyFallbackSeam_killed :
    MOD_061_mutant_anyFallbackSeam refBuild (mod061_blankSeamFuse (N := String) (A := Unit) refBuild) ∧
      ¬ MOD_061 refBuild (mod061_blankSeamFuse (N := String) (A := Unit) refBuild) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := mod061_okIff (F := mod061_blankSeamFuse (N := String) (A := Unit) refBuild)
    (mod061_seamFuse_ok (N := String) (A := Unit) refBuild mod061_blankSeam)
  refine ⟨⟨h1, h2, h3, h4, mod061_seamFuse_line5 refBuild _ (fun sets sets' hd hp => by
      funext p; simp only [mod061_blankSeam, fusionOwner_perm hp hd]), h6,
    mod061_seamFuse_line7 refBuild _,
    mod061_seamFuse_line8 refBuild refBuild (fun _ h => h) _ (fun sets s p hd hs hp => by
      simp only [mod061_blankSeam, (fusionOwner_eq_some_iff hd).2 ⟨hs, hp⟩])⟩, fun h => ?_⟩
  let sets : List (FusionSet String) := [⟨"ab", ["a", "b"]⟩]
  have hd : FusionDisjoint sets := (findOverlap_eq_none_iff sets).1 (by decide)
  have := h.2.2.2.2.2.2.2.2 sets mod061_exFallback _ [] _ [] _ hd (refSubst_spec hd) rfl
    (fun _ h => nomatch h) mod061_fallback_collision (by decide)
  rcases this with e | e
  · exact absurd (congrArg mod061_err e) (by decide)
  · exact absurd (congrArg mod061_err e) (by decide)

/-! ### Wrong fusions that break several lines -/

/-- A fusion that renames the members and merges nothing: every member goes to its set's first
member, and the input arcs are kept as they are. -/
def mod061_noMergeFuse : FuseFn String Unit := fun sets X =>
  .ok { X with defs := X.defs.map (·.map (refSubst sets) id) }

/-- ✗ A fusion that renames without merging violates MOD-061 (line 2): fusing `a` and `b` under
a transition that takes `one()` from each leaves two `one()` arcs on `a`, which the reference
builder rejects ([CORE-030]), where the table would give a single `exactly(2)` arc. -/
@[evidence forbids MOD_061]
theorem MOD_061_forbids_noMerge : ¬ MOD_061 refBuild mod061_noMergeFuse := by
  intro h
  have := h.2.1 [⟨"ab", ["a", "b"]⟩] fuseExBoth _ rfl _ List.mem_cons_self
  exact absurd this (by decide)

/-- ✗ A fusion that rejects every build violates MOD-061 (line 6): it rejects a builder with no
transition and no fusion set. -/
@[evidence forbids MOD_061]
theorem MOD_061_forbids_rejectAll :
    ¬ MOD_061 refBuild (fun (_ : List (FusionSet String)) (_ : FuseNet String Unit) =>
      (.error "rejected" : Except String (FuseNet String Unit))) := by
  intro h
  have hd : FusionDisjoint ([] : List (FusionSet String)) := List.Pairwise.nil
  obtain ⟨Y, hY⟩ := h.2.2.2.2.2.1 [] ⟨[], [], []⟩ _ hd (refSubst_spec hd) (fun _ h => nomatch h)
  cases hY

end Libpetri.Spec
