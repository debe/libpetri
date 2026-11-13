import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeBind
import Libpetri.Spec.Req.MOD_006
import Libpetri.Spec.Req.MOD_031
import Libpetri.Spec.Text.MOD_024

set_option linter.missingDocs true

/-!
# MOD-024: Identity-default port inference (`spec/11-modular-composition.md`)

MOD-024 is a behaviour requirement (kind B) on the single-argument `compose(instance)` of an
enclosing net's builder, over four abstract parameters: a naming model `Nm : Naming N` (how a
prefix renames a place: by name in TypeScript and Rust, by name and token type in Java), the
transition builder's check `Build`, a composition function `C : ComposeFn N A` (the explicit
`compose(instance, bindings)` of [MOD-020]) and an auto-composition function `Au : AutoFn N A`
(a builder, an instance and the names of the channels its subnet declares give the builder after
the call, or a rejection).

It says four things. With ports and no channel, `compose(instance)` is the explicit form with
every port bound to the place on its own declaration, result and rejection alike. A declared
channel fails the call with a message naming every channel. Without ports (the inference path,
a MAY that Java, TypeScript and Rust all take) and with pairwise distinct transition names, a
successful call rewrites every renamed body place `p/x` whose original `x` the builder holds to
`x`, keeps every other place, adds the places the rewritten transitions name and leaves the
builder's terminal places, retired ports, subnet membership and fusion sets alone; and such a
call succeeds exactly when every rewritten transition passes `Build`.

The witness is the reference auto-composition `refAuto` against the reference composition
`refCompose` (`Reference/ComposeBind.lean`); the block holds for every naming model, transition
builder, token-type map and channel merge (`mod024_ref`). For every model of the block an empty
subnet composes as a no-op on the builder's places and transitions (`mod024_empty`, AC6). One
wrong auto-composition per line is killed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The inferred place map -/

section Infer

variable {N A : Type} [DecidableEq N]

/-- **The inferred place map** of auto-composition without ports ([MOD-024]): a place `q` of the
instance goes to the first builder place `h` whose renamed copy under the instance's prefix is
`q`; every other place stays. Under a valid prefix there is at most one such `h`, the place `q`
renames. -/
def autoPlace (Nm : Naming N) (b : Bld N A) (I : Instance N A) (q : N) : N :=
  (b.places.find? fun h => decide (Nm.pre I.pfx h = q ∧ q ∈ I.places)).getD q

/-- One instance definition rewritten through the inferred place map: every arc and
output-specification place through `autoPlace`, the name, timing, priority and action kept. -/
def autoDef (Nm : Naming N) (b : Bld N A) (I : Instance N A) (d : CDef N A) : CDef N A :=
  d.map (autoPlace Nm b I) id

/-- **An inferred rewrite of one definition**: `m` is `d` rewritten by `autoDef`, or the same
rewrite with an all-identity correspondence dropped as a whole (`corrDropPass`), the MAY of
[MOD-031] that Rust, Java and TypeScript take. -/
def mod024_autoOk (Nm : Naming N) (b : Bld N A) (I : Instance N A) (m d : CDef N A) : Prop :=
  m = autoDef Nm b I d ∨ m = corrDropPass (autoPlace Nm b I) id d

end Infer

/-! ## MOD-024: Identity-Default Port Inference (auto-compose) -/

requirement MOD_024
  id "MOD-024"
  title "Identity-Default Port Inference (auto-compose)"
  kind B
  scope "every enclosing-net builder that offers the single-argument compose(instance) (Java, TypeScript, Rust); lines 3 and 4 for those with the inference path (all three)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_024.s1, MOD_024.s2, MOD_024.s3, MOD_024.s4
  reading "For every naming model Nm, transition builder check Build, composition function C and auto-composition function Au (whose third argument is the names of the channels the instance's subnet declares):"
          "for every builder b and instance I with at least one port, Au b I [] equals C b I ports [], where ports binds each port's name to the place on its declaration (I.iface), in declaration order, and no channel is bound;"
          "for every builder b, instance I and non-empty list cs of declared channel names, Au b I cs fails with a message that contains every name in cs;"
          "for every builder b and instance I without ports whose definitions have pairwise distinct names, if Au b I [] returns b', then the definitions of b' are those of b followed by one definition per definition of I, in order, each I's definition rewritten by autoDef (every place q goes to the first builder place h with Nm.pre (prefix of I) h = q, when q is a place of I, and stays otherwise; name, timing, priority and action kept, the MOD-031 correspondence chained through the same map) or that rewrite with its correspondence dropped as a whole when every entry of it maps a place to itself (mod024_autoOk, corrDropPass of MOD-031), a place is in b' exactly when it is in b or a rewritten definition names it, and the terminal places, retired ports, subnet contributions and fusion sets of b' are those of b;"
          "for every builder b and instance I without ports whose definitions have pairwise distinct names, Au b I [] succeeds exactly when Build accepts every rewritten definition."
  assumes "The single-argument form is a SHOULD. Java (PetriNet.java compose(Instance), java/src/main/java/org/libpetri/core/PetriNet.java), Rust (compose_auto, rust/libpetri-core/src/petri_net.rs) and TypeScript (composeAuto behind compose(instance), typescript/src/core/petri-net.ts) offer it. Python offers only the explicit forms (NetBuilder.compose and compose_instance take a port_bindings mapping, rust/libpetri-py/src/model.rs), which the SHOULD allows; the block's scope leaves it out."
          "The model passes the names of the channels the instance's subnet declares as the argument cs, since Instance holds no channel list; that cs is the declared list is the caller's premise, not a line. Lines 1, 3 and 4 are stated at cs = [], the subnet declaring no channel. Line 2 holds whatever the ports are: Rust and TypeScript check channels first, Java checks for terminal places first, which instantiate already refuses (EXEC-042 AC6), so the check is unreachable from an instance and not stated here."
          "Line 1 is the sentence 'the resulting binding map MUST be processed identically to an explicit compose(instance, map) call per [MOD-020]' as an equation of results: the same builder or the same rejection message. Rust and TypeScript bind a port to the builder's equal-named place object when the builder holds one (compose_auto in petri_net.rs, composeAuto in petri-net.ts); under name-only place equality that object is the declared place, so the binding is the one line 1 names. In TypeScript the explicit form keeps the caller's own Place object in the rewritten arcs (the mergeMap of composeInternal in typescript/src/core/petri-net.ts), and the builder keys its places by name and keeps the first object of a name (the _places map of PetriNetBuilder and its addPlace in petri-net.ts), so both forms leave one place of that name in the builder; the line compares places by name, the TypeScript place equality of CORE-002. Two ports over one body place (ruling D35 (a)) are bound to one declared place, so their bindings agree. AC1 (structurally equal to the explicit form) and AC5 (auto-compose then build() is indistinguishable from the explicit form then build()) are line 1, build() being a function of the builder. AC2 (the declared place P arrives in the net through the rewritten port arcs when the builder lacked it) is line 1 with MOD-020's success shape, which adds every place an arc of an added definition names; MOD_024_nonvacuous shows it on the reference. The result satisfying MOD-023 is MOD-023's line applied to the explicit form."
          "Line 2 is AC4 and the sentence 'If the subnet's interface declares any channel, compose(instance) MUST raise an error naming the channels'. To name a channel is for the message to contain its name as a substring (MsgNames, MOD-006). All three runtimes name every declared channel and point at their explicit overload (compose_with in Rust, compose(instance, Consumer) in Java, compose(instance, bind => ...) in TypeScript); the pointer is API-specific text and is tested, not proven."
          "Lines 3 and 4 are the MAY paragraph on body inference and AC3, scoped to implementations with the inference path: all three runtimes walk the renamed body's places, strip the prefix and probe the builder's place set with the original identity (Java by name and token type, Place.of(originalName, renamed.tokenType()); Rust and TypeScript by name), and bind each match through the same composition step as the explicit form (applyComposition / apply_composition) with no port, so no MOD-020 collision can arise (two different places never rename to one) and no port is retired (MOD-027). The naming model Nm is the implementation's place equality (strNaming or typedNaming, CORE-002), so the probe is Nm.pre (prefix) h = q. The two equalities give different bindings when the builder holds a place of the body place's name and another token type: Java keeps the body place private, the name-only runtimes bind it (mod024_placeEquality_divergence). An implementation without the inference path is out of the scope of lines 3 and 4: line 1's sentence then applies with no bindings. The inference reads the builder's places at the call, so it is order-sensitive by design (MOD-025 contrasts this); MOD_024_nonvacuous shows a builder that does not hold the place at the call keeping the renamed place private."
          "Line 3 states the definitions, the place set and the builder's other records; the order of the places is not normative (ruling D32). An instance place that no arc names is not added, as for the explicit form (ruling D20, mod-b item 9). Line 3's rewrite is CDef.map, so the MOD-031 correspondence is chained through the inferred map; what the correspondence then resolves is MOD-031's line. A rewritten definition may instead carry no correspondence when the chained one maps every place to itself (mod024_autoOk, MOD-031's corrDropPass): that is the MAY of MOD-031 (AC9), and all three runtimes take it on every rewrite pass (Rust wholesale_drop_if_all_identity, rust/libpetri-core/src/rewriter.rs; Java compactIdentityAlias, java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java, by name and token type; TypeScript dropIfAllIdentity, which returns EMPTY_ALIAS, typescript/src/core/internal/subnet-rewriter.ts). On the inference path a body place s/P moved back to P chains the entry (P, P), so a definition whose places the builder all holds ends with an all-identity correspondence, which the runtimes drop and the reference keeps; mod024_dropAu_holds shows that the model that drops it meets the block. The identity test is decided by the naming model's place equality (decide on N), which is the one the correspondence lookup uses (MOD-031). The builder's terminal places, retired ports (MOD-027: body places merged by inference are not ports and are not retired), subnet contributions (MOD-026 item 4: instance composition records no membership) and fusion sets (MOD-060) stay as they were: Rust apply_composition retires only merge entries that are port places (its MOD-027 retire step, rust/libpetri-core/src/petri_net.rs), TypeScript applyComposition walks the instance's port handles and Java composeInternal its interface's ports, which an instance without ports has none of, and none of the three records membership or a fusion set on this path."
          "Line 4 is the acceptance line skeptic correction S2 of the composition design asks for, with its converse: a transition that fails the transition builder's checks after the rewrite fails the call, as in MOD-020, since all three runtimes rebuild every rewritten transition through the transition builder (Rust substitute_places, rust/libpetri-core/src/rewriter.rs). The message is the builder's, as in MOD-020, and line 4 does not state it. With line 3 this is AC5 for a subnet without ports: the explicit form with the inferred wiring succeeds and fails on the same calls and gives the same builder."
          "The sentence that name-only implementations MUST document the more permissive matching contract in their API surface is a documentation duty (Rust compose_auto's doc comment and TypeScript composeAuto's comment state it), reviewed, not proven. The SHOULD that the probe uses the implementation's own Place equality is the parameter Nm. The SHOULD on when callers use the explicit overloads is guidance to callers, not a duty of the builder."
          "AC6 (an empty subnet composes as a no-op on the builder's place and transition sets) follows from lines 3 and 4 for every model of the block (mod024_empty), so it has no mutant of its own."
          "Lines 3 and 4 assume that the instance's transitions have pairwise distinct names, the premise MOD-020 takes (mod020_fresh) under the unique-names assumption of rulings D10 and D23. Transition names are assumed distinct (ruling D23) and no builder rejects a subnet body with two transitions of one name, and Rust's apply_composition stages the rewritten transitions in a map keyed by name (its staged map, rust/libpetri-core/src/petri_net.rs) and drains it through the insertion order (its order vector), so the second transition of a name replaces the first and the builder gains one transition fewer than line 3 says. The block claims nothing about such a call, which leaves a builder free to reject it. Composing one instance twice, or two instances under one prefix, is not excluded: every runtime appends the second instance's transitions after the first (Java and TypeScript hold transitions in sets keyed by object identity, Rust in its builder's transition list), as line 3 says."
  signoff "2026-11-13 056632f9552acc2f ai"
  statement : ∀ {N A : Type} [DecidableEq N], Naming N → (Trans N → Option String) →
      ComposeFn N A → AutoFn N A → Prop :=
    fun {N A} _ Nm Build C Au =>
      (∀ (b : Bld N A) (I : Instance N A), I.iface ≠ [] →
        Au b I [] = C b I (I.iface.map fun pt => (pt.name, pt.place)) []) ∧
      (∀ (b : Bld N A) (I : Instance N A) (cs : List String), cs ≠ [] →
        ∃ msg, Au b I cs = .error msg ∧ ∀ c ∈ cs, MsgNames msg c) ∧
      (∀ (b b' : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
        Au b I [] = .ok b' →
        (∃ ms, b'.defs = b.defs ++ ms ∧ List.Forall₂ (mod024_autoOk Nm b I) ms I.defs) ∧
        (∀ x, x ∈ b'.places ↔ x ∈ b.places ∨ ∃ d ∈ I.defs, x ∈ (autoDef Nm b I d).namedPlaces) ∧
        b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.contrib = b.contrib ∧
        b'.fusions = b.fusions) ∧
      (∀ (b : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
        ((∃ b', Au b I [] = .ok b') ↔ ∀ d ∈ I.defs, Build (autoDef Nm b I d).toTrans = none))

/- The pinned readable form of MOD-024: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_024 : {N A : Type} →
  [DecidableEq N] → Naming N → (Reference.Trans N → Option String) → ComposeFn N A → AutoFn N A → Prop :=
fun {N A} x Nm Build C Au =>
  (∀ (b : Bld N A) (I : Instance N A),
      I.iface ≠ [] → Au b I [] = C b I (List.map (fun pt => (pt.name, pt.place)) I.iface) []) ∧
    (∀ (b : Bld N A) (I : Instance N A) (cs : List String),
        cs ≠ [] → ∃ msg, Au b I cs = Except.error msg ∧ ∀ c ∈ cs, MsgNames msg c) ∧
      (∀ (b b' : Bld N A) (I : Instance N A),
          I.iface = [] →
            (List.map (fun x => x.core.name) I.defs).Nodup →
              Au b I [] = Except.ok b' →
                (∃ ms, b'.defs = b.defs ++ ms ∧ List.Forall₂ (mod024_autoOk Nm b I) ms I.defs) ∧
                  (∀ (x_1 : N), x_1 ∈ b'.places ↔ x_1 ∈ b.places ∨ ∃ d ∈ I.defs, x_1 ∈ (autoDef Nm b I d).namedPlaces) ∧
                    b'.terminals = b.terminals ∧
                      b'.retired = b.retired ∧ b'.contrib = b.contrib ∧ b'.fusions = b.fusions) ∧
        ∀ (b : Bld N A) (I : Instance N A),
          I.iface = [] →
            (List.map (fun x => x.core.name) I.defs).Nodup →
              ((∃ b', Au b I [] = Except.ok b') ↔ ∀ d ∈ I.defs, Build (autoDef Nm b I d).toTrans = none)
-/
#guard_msgs in #print MOD_024

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type} [DecidableEq N]

/-- Line 1 of MOD-024: with ports, auto-composition is the explicit form with every port bound to
its own declared place. -/
def mod024_line1 (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  ∀ (b : Bld N A) (I : Instance N A), I.iface ≠ [] →
    Au b I [] = C b I (I.iface.map fun pt => (pt.name, pt.place)) []

/-- Line 2 of MOD-024: a declared channel fails the call, naming every channel. -/
def mod024_line2 (Au : AutoFn N A) : Prop :=
  ∀ (b : Bld N A) (I : Instance N A) (cs : List String), cs ≠ [] →
    ∃ msg, Au b I cs = .error msg ∧ ∀ c ∈ cs, MsgNames msg c

/-- Line 3 of MOD-024: without ports, a success rewrites through the inferred place map and
leaves the builder's other records alone. -/
def mod024_line3 (Nm : Naming N) (Au : AutoFn N A) : Prop :=
  ∀ (b b' : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
    Au b I [] = .ok b' →
    (∃ ms, b'.defs = b.defs ++ ms ∧ List.Forall₂ (mod024_autoOk Nm b I) ms I.defs) ∧
    (∀ x, x ∈ b'.places ↔ x ∈ b.places ∨ ∃ d ∈ I.defs, x ∈ (autoDef Nm b I d).namedPlaces) ∧
    b'.terminals = b.terminals ∧ b'.retired = b.retired ∧ b'.contrib = b.contrib ∧
    b'.fusions = b.fusions

/-- Line 4 of MOD-024: without ports, the call succeeds exactly when every rewritten definition
passes `Build`. -/
def mod024_line4 (Nm : Naming N) (Build : Trans N → Option String) (Au : AutoFn N A) : Prop :=
  ∀ (b : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
    ((∃ b', Au b I [] = .ok b') ↔ ∀ d ∈ I.defs, Build (autoDef Nm b I d).toTrans = none)

/-- Line 3 without its last part: the definitions and the places only, the builder's other
records free (for the mutants). -/
def mod024_line3_shape (Nm : Naming N) (Au : AutoFn N A) : Prop :=
  ∀ (b b' : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
    Au b I [] = .ok b' →
    (∃ ms, b'.defs = b.defs ++ ms ∧ List.Forall₂ (mod024_autoOk Nm b I) ms I.defs) ∧
    (∀ x, x ∈ b'.places ↔ x ∈ b.places ∨ ∃ d ∈ I.defs, x ∈ (autoDef Nm b I d).namedPlaces)

/-- Line 4 without its converse: every rewritten definition passing `Build` is enough for
success, and a refused one need not fail the call (for the mutants). -/
def mod024_line4_accept (Nm : Naming N) (Build : Trans N → Option String) (Au : AutoFn N A) :
    Prop :=
  ∀ (b : Bld N A) (I : Instance N A), I.iface = [] → (I.defs.map (·.core.name)).Nodup →
    (∀ d ∈ I.defs, Build (autoDef Nm b I d).toTrans = none) → ∃ b', Au b I [] = .ok b'

/-- Line 3 gives its shape. -/
theorem mod024_line3_shape_of {Nm : Naming N} {Au : AutoFn N A} (h : mod024_line3 Nm Au) :
    mod024_line3_shape Nm Au :=
  fun b b' I hi hn hr => ⟨(h b b' I hi hn hr).1, (h b b' I hi hn hr).2.1⟩

/-- Line 4 gives its acceptance half. -/
theorem mod024_line4_accept_of {Nm : Naming N} {Build : Trans N → Option String}
    {Au : AutoFn N A} (h : mod024_line4 Nm Build Au) : mod024_line4_accept Nm Build Au :=
  fun b I hi hn hb => (h b I hi hn).2 hb

/-- MOD-024 is its four lines. -/
theorem mod024_iff (Nm : Naming N) (Build : Trans N → Option String) (C : ComposeFn N A)
    (Au : AutoFn N A) :
    MOD_024 Nm Build C Au ↔
      mod024_line1 C Au ∧ mod024_line2 Au ∧ mod024_line3 Nm Au ∧ mod024_line4 Nm Build Au :=
  Iff.rfl

end Lines

/-! ### The reference -/

section RefLemmas

variable {N A : Type} [DecidableEq N] [ToString N] {T : Type} [DecidableEq T] [ToString T]

/-- The inferred place map is the reference's binding map over the inferred bindings. -/
theorem autoPlace_eq (Nm : Naming N) (b : Bld N A) (I : Instance N A) :
    autoPlace Nm b I = bindSubst (inferEntries Nm b I) := by
  funext q
  unfold autoPlace bindSubst bindLookup inferEntries
  induction b.places with
  | nil => rfl
  | cons h t ih =>
    by_cases hq : Nm.pre I.pfx h ∈ I.places
    · by_cases he : Nm.pre I.pfx h = q
      · subst he
        simp only [List.filterMap_cons, hq, if_true, List.find?_cons, decide_true, and_self,
          Option.map_some, Option.getD_some]
      · simp only [List.filterMap_cons, hq, if_true, List.find?_cons, he, false_and,
          decide_false]
        exact ih
    · have hne : ¬ (Nm.pre I.pfx h = q ∧ q ∈ I.places) := by
        rintro ⟨rfl, h2⟩; exact hq h2
      simp only [List.filterMap_cons, hq, if_false, List.find?_cons, hne, decide_false]
      exact ih

/-- The inferred definition is the reference's rewritten definition. -/
theorem autoDef_eq (Nm : Naming N) (b : Bld N A) (I : Instance N A) :
    autoDef Nm b I = rewriteDef (inferEntries Nm b I) := by
  funext d
  unfold autoDef rewriteDef
  rw [autoPlace_eq]

/-- Inferred bindings never clash: two different places are never bound to one builder place. -/
theorem infer_noClash (Nm : Naming N) (b : Bld N A) (I : Instance N A) (x y : N) :
    ¬ BindClash (inferEntries Nm b I) x y := by
  rintro ⟨hxy, e, e', he, he', hc⟩
  obtain ⟨hem, rfl⟩ := bindLookup_some he
  obtain ⟨hem', rfl⟩ := bindLookup_some he'
  obtain ⟨h, -, -, rfl⟩ := mem_inferEntries.1 hem
  obtain ⟨h', -, -, rfl⟩ := mem_inferEntries.1 hem'
  simp only at hc
  subst hc
  exact hxy rfl

/-- A list's `toString` is a fold whose start stays a prefix. -/
theorem foldl_sep_prefix (xs : List String) (acc : String) :
    ∃ t, (xs.foldl (fun l r => l ++ ", " ++ toString r) acc).toList = acc.toList ++ t := by
  induction xs generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons y ys ih =>
    obtain ⟨t, ht⟩ := ih (acc ++ ", " ++ toString y)
    refine ⟨(", " ++ toString y).toList ++ t, ?_⟩
    simp only [List.foldl_cons, ht, String.toList_append, List.append_assoc]

/-- Every element of the list is a substring of the fold. -/
theorem foldl_sep_infix (xs : List String) (acc : String) :
    ∀ c ∈ xs, c.toList <:+: (xs.foldl (fun l r => l ++ ", " ++ toString r) acc).toList := by
  induction xs generalizing acc with
  | nil => intro c hc; cases hc
  | cons y ys ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨t, ht⟩ := foldl_sep_prefix ys (acc ++ ", " ++ toString c)
      simp only [List.foldl_cons, ht, String.toList_append]
      exact ⟨acc.toList ++ ", ".toList, t, by simp [List.append_assoc]; rfl⟩
    · simpa only [List.foldl_cons] using ih (acc ++ ", " ++ toString y) c hc

/-- Every element of a list of strings is a substring of the list's `toString`. -/
theorem mem_toString_infix {cs : List String} {c : String} (hc : c ∈ cs) :
    c.toList <:+: (toString cs).toList := by
  show c.toList <:+: (List.toString cs).toList
  match cs, hc with
  | [x], hc =>
    rcases List.mem_singleton.1 hc with rfl
    exact ⟨"[".toList, "]".toList, by simp [List.toString, String.toList_append]; rfl⟩
  | x :: y :: ys, hc =>
    have hpush : ∀ s : String, (s.push ']').toList = s.toList ++ [']'] := by simp
    unfold List.toString
    rw [hpush]
    rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨t, ht⟩ := foldl_sep_prefix (y :: ys) ("[" ++ toString c)
      rw [ht]
      exact ⟨"[".toList, t ++ [']'], by simp [String.toList_append, List.append_assoc]; rfl⟩
    · exact (foldl_sep_infix (y :: ys) ("[" ++ toString x) c hc).trans (List.infix_append [] _ _)

/-- The reference's channel message names every declared channel. -/
theorem autoChanMsg_names (pfx : String) {cs : List String} {c : String} (hc : c ∈ cs) :
    MsgNames (autoChanMsg pfx cs) c := by
  unfold MsgNames autoChanMsg
  refine (mem_toString_infix hc).trans ?_
  simp only [String.toList_append, List.append_assoc]
  exact (((List.prefix_append _ _).isInfix.trans (List.suffix_append _ _).isInfix).trans
    (List.suffix_append _ _).isInfix).trans (List.suffix_append _ _).isInfix

variable {Nm : Naming N} {tyOf : N → T} {Build : Trans N → Option String}
  {Mg : CDef N A → CDef N A → Except String (CDef N A)}

/-- Line 1 of the reference: `refAuto_ports`. -/
theorem mod024_ref_line1 : mod024_line1 (refCompose tyOf Build Mg) (refAuto Nm tyOf Build Mg) :=
  fun _ _ h => refAuto_ports h

/-- Line 2 of the reference: the channel message names every channel. -/
theorem mod024_ref_line2 : mod024_line2 (refAuto Nm tyOf Build Mg) :=
  fun _ I _ h => ⟨_, refAuto_chans h, fun _ hc => autoChanMsg_names I.pfx hc⟩

/-- Line 3 of the reference: a success without ports is the inferred rewrite, and the builder's
other records are kept. -/
theorem mod024_ref_line3 : mod024_line3 Nm (refAuto Nm tyOf Build Mg) := by
  intro b b' I hi _ h
  rw [refAuto_infer hi, applyBind_ok_iff] at h
  obtain ⟨-, ms, hms, rfl⟩ := h
  have hms' : ms = I.defs.map (rewriteDef (inferEntries Nm b I)) := by
    have hid : ∀ l : List (CDef N A), l.mapM (mergeStep Mg I []) = .ok l := by
      intro l
      induction l with
      | nil => rfl
      | cons d l ih =>
        simp [List.mapM_cons, mergeStep_none (Mg := Mg) (I := I) (chans := []) (d := d)
          (by simp), ih]
        rfl
    rw [hid] at hms
    cases hms; rfl
  subst hms'
  refine ⟨⟨_, bindAssemble_defs _ _, ?_⟩, fun x => ?_, rfl, rfl, rfl, rfl⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_same]
    intro d _
    exact Or.inl (by rw [autoDef_eq])
  rw [autoDef_eq, mem_bindAssemble_places]
  simp [List.mem_map]

/-- Line 4 of the reference: without ports, the call succeeds exactly when every rewritten
definition passes `Build`. -/
theorem mod024_ref_line4 : mod024_line4 Nm Build (refAuto Nm tyOf Build Mg) := by
  intro b I hi _
  rw [refAuto_infer hi]
  constructor
  · rintro ⟨b', h⟩ d hd
    rw [autoDef_eq]
    exact ((applyBind_ok_iff.1 h).1 d hd).2.2
  · intro hb
    have hall : ∀ d ∈ I.defs, ¬ InCollision (inferEntries Nm b I) d ∧
        ¬ OutCollision (inferEntries Nm b I) d ∧
        Build (rewriteDef (inferEntries Nm b I) d).toTrans = none := by
      intro d hd
      refine ⟨?_, ?_, by rw [← autoDef_eq]; exact hb d hd⟩
      · rintro ⟨x, -, y, -, hc⟩; exact infer_noClash Nm b I x y hc
      · rintro ⟨o, -, br, -, x, -, y, -, hc⟩; exact infer_noClash Nm b I x y hc
    refine ⟨bindAssemble b (I.defs.map (rewriteDef (inferEntries Nm b I))),
      applyBind_ok_iff.2 ⟨hall, _, ?_, rfl⟩⟩
    generalize I.defs.map (rewriteDef (inferEntries Nm b I)) = l
    induction l with
    | nil => rfl
    | cons d l ih =>
      simp [List.mapM_cons, mergeStep_none (Mg := Mg) (I := I) (chans := []) (d := d) (by simp),
        ih]
      rfl

/-- The reference auto-composition satisfies MOD-024 against the reference composition, for
every naming model, transition builder, token-type map and channel merge. -/
theorem mod024_ref (Nm : Naming N) (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    MOD_024 Nm Build (refCompose tyOf Build Mg) (refAuto Nm tyOf Build Mg) :=
  ⟨mod024_ref_line1, mod024_ref_line2, mod024_ref_line3, mod024_ref_line4⟩

end RefLemmas

/-- ✓ The reference auto-composition satisfies MOD-024 for every naming model and transition
builder. An instance `w1` with a port `in` on its place `in` is composed exactly as if `in` were
bound by hand to the caller place `in`. An instance whose definition declares the channel `go`
is refused, with a message that names `go`. An instance with no ports moves its place `w1/x` onto
the builder's place `x` when the builder has one, and keeps it as `w1/x` otherwise. -/
@[evidence holds MOD_024]
theorem MOD_024_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N)
    (Build : Trans N → Option String) :
    MOD_024 Nm Build (refCompose (A := A) (fun _ : N => ()) Build (fun c _ => .ok c))
      (refAuto Nm (fun _ : N => ()) Build (fun c _ => .ok c)) :=
  mod024_ref Nm _ Build _

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A : Type} [DecidableEq N]

/-- Both inferred rewrites of a definition are the same transition: they differ in the
correspondence only. -/
theorem mod024_autoOk_trans {Nm : Naming N} {b : Bld N A} {I : Instance N A} {m d : CDef N A}
    (h : mod024_autoOk Nm b I m d) : m.toTransDef = (autoDef Nm b I d).toTransDef := by
  rcases h with rfl | rfl <;> rfl

/-- **Line 3's definitions as transitions**: the builder's definitions followed by the inferred
rewrite of every instance definition, compared as transitions (correspondence aside). -/
theorem mod024_defs_trans {Nm : Naming N} {b b' : Bld N A} {I : Instance N A}
    (h : ∃ ms, b'.defs = b.defs ++ ms ∧ List.Forall₂ (mod024_autoOk Nm b I) ms I.defs) :
    b'.defs.map CDef.toTransDef = (b.defs ++ I.defs.map (autoDef Nm b I)).map CDef.toTransDef := by
  obtain ⟨ms, h1, hF⟩ := h
  rw [h1, List.map_append, List.map_append]
  congr 1
  clear h1
  generalize I.defs = l at hF ⊢
  induction hF with
  | nil => rfl
  | cons hr _ ih => simp only [List.map_cons, mod024_autoOk_trans hr, ih]

/-- **AC6.** In every model of MOD-024, auto-composing an instance with no port, no place and no
transition succeeds and leaves the builder's transitions as they were and its places the same
set. -/
theorem mod024_empty {Nm : Naming N} {Build : Trans N → Option String} {C : ComposeFn N A}
    {Au : AutoFn N A} (h : MOD_024 Nm Build C Au) {b : Bld N A} {I : Instance N A}
    (hi : I.iface = []) (hd : I.defs = []) :
    ∃ b', Au b I [] = .ok b' ∧ b'.defs = b.defs ∧ ∀ x, x ∈ b'.places ↔ x ∈ b.places := by
  have hn : (I.defs.map (·.core.name)).Nodup := by simp [hd]
  obtain ⟨b', hb'⟩ := (h.2.2.2 b I hi hn).2 (by simp [hd])
  obtain ⟨⟨ms, h1, hF⟩, h2, -⟩ := h.2.2.1 b b' I hi hn hb'
  rw [hd, List.forall₂_nil_right_iff] at hF
  exact ⟨b', hb', by simp [h1, hF], fun x => by simp [h2, hd]⟩

end Consequences

/-! ### Examples -/

/-- A producer subnet: transition `emit` puts one token into `P`, exposed as the output port
`out`. -/
def mod024_exProd : SubnetDef String Unit :=
  { name := "Prod", places := ["P"], defs := [bindExDef "emit" [] (some (.place "P"))],
    ports := [⟨"out", .output, "P"⟩], chans := [] }

/-- The same producer without ports: its place `P` is found by inference. -/
def mod024_exBare : SubnetDef String Unit :=
  { name := "Bare", places := ["P", "q"],
    defs := [bindExDef "emit" [⟨"q", .one⟩] (some (.place "P"))], ports := [], chans := [] }

/-- Instantiate `S` under `pfx` (places by name) and auto-compose it into `b`, with the reference
transition builder, no token-type check and a merge that keeps the caller side. -/
def mod024_exAuto (b : Bld String Unit) (S : SubnetDef String Unit) (pfx : String) :
    Except String (Bld String Unit) :=
  refInst strNaming S pfx >>= fun I =>
    refAuto strNaming (fun _ => ()) refBuild (fun c _ => .ok c) b I (S.chans.map (·.name))

/-- The places and the transitions with the places they name, of a successful call. -/
def mod024_exView (r : Except String (Bld String Unit)) :
    Option (List String × List (String × List String)) :=
  r.toOption.map fun b => (b.places, b.defs.map fun d => (d.core.name, d.namedPlaces))

/-- ✓ Every line of MOD-024 is exercised by the reference.
* Auto-composing the producer `Prod` (port `out` on `P`) under `s` into an empty builder gives
  `s/emit` writing to `P`, and `P` arrives in the builder through that arc (AC2): the same as
  binding `out` to `P` explicitly (AC1, line 1).
* Two producers auto-composed under `s` and `t` both write to the one place `P` (the test
  derivation).
* The subnet `C`, which declares the channel `go`, is rejected with a message naming `go`
  (AC4, line 2).
* Without ports, a builder that already holds `P` gets `s/emit` writing to `P` and taking from
  the private `s/q` (AC3, lines 3 and 4); an empty builder, which might declare `P` only later,
  keeps `s/P` private, since inference reads the builder at the call. -/
@[evidence nonvacuous MOD_024]
theorem MOD_024_nonvacuous :
    mod024_exView (mod024_exAuto Bld.empty mod024_exProd "s") =
      some (["P"], [("s/emit", ["P"])]) ∧
    mod024_exView (refInst strNaming mod024_exProd "s" >>= fun I =>
        refCompose (fun _ => ()) refBuild (fun c _ => .ok c) Bld.empty I [("out", "P")] []) =
      some (["P"], [("s/emit", ["P"])]) ∧
    mod024_exView (mod024_exAuto Bld.empty mod024_exProd "s" >>= fun b =>
        mod024_exAuto b mod024_exProd "t") =
      some (["P"], [("s/emit", ["P"]), ("t/emit", ["P"])]) ∧
    (match mod024_exAuto Bld.empty bindExChan "s" with
      | .error m => decide ("go".toList <:+: m.toList)
      | .ok _ => false) = true ∧
    mod024_exView (mod024_exAuto { places := ["P"], defs := [] } mod024_exBare "s") =
      some (["P", "s/q"], [("s/emit", ["s/q", "P"])]) ∧
    mod024_exView (mod024_exAuto Bld.empty mod024_exBare "s") =
      some (["s/q", "s/P"], [("s/emit", ["s/q", "s/P"])]) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Wrong auto-compositions -/

/-- The transition builder that accepts every transition. -/
def mod024_acceptAll : Trans String → Option String := fun _ => none

/-- The reference composition of the wrong models below (places by name, no token-type check,
every transition accepted, a merge that keeps the caller side). -/
def mod024_C : ComposeFn String Unit :=
  refCompose (fun _ => ()) mod024_acceptAll (fun c _ => .ok c)

/-- The reference auto-composition at the same parameters. -/
def mod024_Au : AutoFn String Unit :=
  refAuto strNaming (fun _ => ()) mod024_acceptAll (fun c _ => .ok c)

/-- An auto-composition that is the reference except where `w` holds of the instance and the
channel names, where it answers `alt`. -/
def mod024_patch (w : Instance String Unit → List String → Bool)
    (alt : Bld String Unit → Instance String Unit → List String → Except String (Bld String Unit)) :
    AutoFn String Unit := fun b I cs => if w I cs then alt b I cs else mod024_Au b I cs

/-- Composing with no binding under the transition builder that accepts everything always
succeeds, adding the instance's definitions unchanged. -/
theorem mod024_noBind_ok (b : Bld String Unit) (I : Instance String Unit) :
    applyBind mod024_acceptAll (fun c _ => .ok c) b I [] [] =
      .ok (bindAssemble b (I.defs.map (rewriteDef []))) := by
  have hall : ∀ d ∈ I.defs, ¬ InCollision ([] : List (BindEntry String)) d ∧
      ¬ OutCollision ([] : List (BindEntry String)) d ∧
      mod024_acceptAll (rewriteDef [] d).toTrans = none := by
    intro d _
    refine ⟨?_, ?_, rfl⟩
    · rintro ⟨x, -, y, -, -, e, -, he, -⟩; cases he
    · rintro ⟨o, -, br, -, x, -, y, -, -, e, -, he, -⟩; cases he
  refine applyBind_ok_iff.2 ⟨hall, I.defs.map (rewriteDef []), ?_, rfl⟩
  generalize I.defs.map (rewriteDef []) = l
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp [List.mapM_cons, mergeStep_none (Mg := fun c (_ : CDef String Unit) => Except.ok c)
      (I := I) (chans := []) (d := d) (by simp), ih]
    rfl

/-- An instance with no port, no place, no transition and no channel. -/
def mod024_exEmpty : Instance String Unit :=
  ⟨"s", [], [], fun _ => none, fun _ => none, []⟩

/-! ### Mutant: line 1 dropped -/

/-- Mutant reading: MOD-024 without line 1, so the form with ports need not be the explicit
composition. -/
def MOD_024_mutant_noPortLine {N A : Type} [DecidableEq N] (Nm : Naming N)
    (Build : Trans N → Option String) (_C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line2 Au ∧ mod024_line3 Nm Au ∧ mod024_line4 Nm Build Au

/-- The auto-composition that does nothing when the subnet has ports kills the mutant: it meets
lines 2 to 4, which say nothing about ports, but auto-composing the producer `Prod` leaves the
builder without `s/emit`, while binding `out` to `P` explicitly adds it (line 1). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_noPortLine_killed :
    MOD_024_mutant_noPortLine strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && !I.iface.isEmpty) fun b _ _ => .ok b) ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && !I.iface.isEmpty) fun b _ _ => .ok b) := by
  refine ⟨⟨fun b I cs hc => ?_, fun b b' I hi hn h => ?_, fun b I hi hn => ?_⟩, fun h => ?_⟩
  · have hw : (cs.isEmpty && !I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && !I.iface.isEmpty) = false := by simp [hi]
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false] at h
    exact mod024_ref_line3 b b' I hi hn h
  · have hw : (([] : List String).isEmpty && !I.iface.isEmpty) = false := by simp [hi]
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line4 b I hi hn
  · have h1 := h.1 Bld.empty (renamedInstance strNaming mod024_exProd "s") (by decide)
    have := congrArg (fun r : Except String (Bld String Unit) => r.toOption.map (·.defs.length)) h1
    exact absurd this (by decide)

/-! ### Mutant: line 2 dropped -/

/-- Mutant reading: MOD-024 without line 2, so a declared channel need not fail the call. -/
def MOD_024_mutant_noChanLine {N A : Type} [DecidableEq N] (Nm : Naming N)
    (Build : Trans N → Option String) (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line1 C Au ∧ mod024_line3 Nm Au ∧ mod024_line4 Nm Build Au

/-- The auto-composition that ignores channels kills the mutant: it meets lines 1, 3 and 4,
which are stated for a subnet without channels, but composes an empty instance that declares the
channel `go` instead of failing (line 2). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_noChanLine_killed :
    MOD_024_mutant_noChanLine strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun _ cs => !cs.isEmpty) fun b I _ => mod024_Au b I []) ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun _ cs => !cs.isEmpty) fun b I _ => mod024_Au b I []) := by
  refine ⟨⟨fun b I hi => ?_, fun b b' I hi hn h => ?_, fun b I hi hn => ?_⟩, fun h => ?_⟩
  · exact mod024_ref_line1 b I hi
  · exact mod024_ref_line3 b b' I hi hn h
  · exact mod024_ref_line4 b I hi hn
  · obtain ⟨msg, hm, -⟩ := h.2.1 Bld.empty mod024_exEmpty ["go"] (by simp)
    have he : mod024_Au Bld.empty mod024_exEmpty [] = .ok Bld.empty := refAuto_empty rfl rfl
    simp only [mod024_patch, List.isEmpty_cons, Bool.not_false, if_true, he] at hm
    cases hm

/-! ### Mutant: line 3 dropped -/

/-- Mutant reading: MOD-024 without line 3, so the call without ports need not infer. -/
def MOD_024_mutant_noInferLine {N A : Type} [DecidableEq N] (Nm : Naming N)
    (Build : Trans N → Option String) (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line1 C Au ∧ mod024_line2 Au ∧ mod024_line4 Nm Build Au

/-- The auto-composition that never infers (the explicit form with no binding, which the MAY
allows an implementation outside this line's scope) kills the mutant: under a transition builder
that accepts everything it meets lines 1, 2 and 4, but composing the portless `Bare` into a
builder that holds `P` leaves `s/emit` writing to `s/P` instead of `P` (line 3). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_noInferLine_killed :
    MOD_024_mutant_noInferLine strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
          fun b I _ => applyBind mod024_acceptAll (fun c _ => .ok c) b I [] []) ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
          fun b I _ => applyBind mod024_acceptAll (fun c _ => .ok c) b I [] []) := by
  refine ⟨⟨fun b I hi => ?_, fun b I cs hc => ?_, fun b I hi _ => ?_⟩, fun h => ?_⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = false := by
      cases hI : I.iface with
      | nil => exact absurd hI hi
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line1 b I hi
  · have hw : (cs.isEmpty && I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_patch, hw, if_true]
    exact ⟨fun _ _ _ => rfl, fun _ => ⟨_, mod024_noBind_ok b I⟩⟩
  · have hb : mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
        (fun b I _ => applyBind mod024_acceptAll (fun c _ => .ok c) b I [] [])
        { places := ["P"], defs := [] } (renamedInstance strNaming mod024_exBare "s") [] =
        .ok (bindAssemble { places := ["P"], defs := [] }
          ((renamedInstance strNaming mod024_exBare "s").defs.map (rewriteDef []))) := by
      have hw : (([] : List String).isEmpty &&
          (renamedInstance (A := Unit) strNaming mod024_exBare "s").iface.isEmpty) = true := rfl
      simp only [mod024_patch, hw, if_true]
      exact mod024_noBind_ok _ _
    have := mod024_defs_trans (h.2.2.1 _ _ _ rfl (by decide) hb).1
    have := congrArg (List.map fun d : TransDef String Unit => d.namedPlaces) this
    simp only [List.map_map] at this
    exact absurd this (by decide)

/-! ### Mutant: line 4 dropped -/

/-- Mutant reading: MOD-024 without line 4, the success shape without ports and no acceptance
(skeptic correction S2 of the composition design). -/
def MOD_024_mutant_noAcceptance {N A : Type} [DecidableEq N] (Nm : Naming N)
    (_Build : Trans N → Option String) (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line1 C Au ∧ mod024_line2 Au ∧ mod024_line3 Nm Au

/-- The auto-composition that rejects every subnet without ports kills the mutant: it meets lines
1, 2 and 3 (line 3 speaks of successes only), but rejects the empty instance, whose transitions
all pass the transition builder (line 4). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_noAcceptance_killed :
    MOD_024_mutant_noAcceptance strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty) fun _ _ _ => .error "rejected") ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C
        (mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty) fun _ _ _ => .error "rejected") := by
  refine ⟨⟨fun b I hi => ?_, fun b I cs hc => ?_, fun b b' I hi _ h => ?_⟩, fun h => ?_⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = false := by
      cases hI : I.iface with
      | nil => exact absurd hI hi
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line1 b I hi
  · have hw : (cs.isEmpty && I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_patch, hw, if_true] at h
    cases h
  · obtain ⟨b', hb'⟩ :=
      (h.2.2.2 Bld.empty mod024_exEmpty rfl List.nodup_nil).2 (fun _ hd => nomatch hd)
    cases hb'

/-! ### Mutant: the builder's other records left free -/

/-- Mutant reading: MOD-024 with line 3 cut to the definitions and the places, so a call
without ports may change the builder's terminal places, retired ports, subnet membership or
fusion sets. -/
def MOD_024_mutant_recordsFree {N A : Type} [DecidableEq N] (Nm : Naming N)
    (Build : Trans N → Option String) (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line1 C Au ∧ mod024_line2 Au ∧ mod024_line3_shape Nm Au ∧ mod024_line4 Nm Build Au

/-- The auto-composition that also retires every place it infers: the slip of dropping the
port filter in the MOD-027 retire step of Rust `apply_composition`, so that the no-port branch of
`compose_auto` records a retired port for every merged body place. -/
def mod024_retireAll : AutoFn String Unit :=
  mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
    fun b I _ => (mod024_Au b I []).map (retire I.pfx (inferEntries strNaming b I))

/-- The auto-composition that also records subnet membership for every transition it adds, as
direct composition does ([MOD-026]). -/
def mod024_recordAll : AutoFn String Unit :=
  mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
    fun b I _ => (mod024_Au b I []).map fun b' =>
      { b' with contrib := b'.contrib ++ I.defs.map fun d => (d.core.name, I.pfx) }

/-- A builder holding the place `P`, nothing else. -/
def mod024_bP : Bld String Unit := { places := ["P"], defs := [] }

/-- A model that is the reference on every call but the portless ones, and there the reference
with only some record `f` changed, meets every line but the last part of line 3. -/
theorem mod024_recordsFree_of
    (f : Bld String Unit → Instance String Unit → Bld String Unit → Bld String Unit)
    (hd : ∀ b I b', (f b I b').defs = b'.defs) (hp : ∀ b I b', (f b I b').places = b'.places) :
    MOD_024_mutant_recordsFree strNaming mod024_acceptAll mod024_C
      (mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
        fun b I _ => (mod024_Au b I []).map (f b I)) := by
  refine ⟨fun b I hi => ?_, fun b I cs hc => ?_, fun b b' I hi hn h => ?_, fun b I hi hn => ?_⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = false := by
      cases hI : I.iface with
      | nil => exact absurd hI hi
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line1 b I hi
  · have hw : (cs.isEmpty && I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_patch, hw, if_true] at h
    cases hr : mod024_Au b I [] with
    | error m => rw [hr] at h; cases h
    | ok b0 =>
      rw [hr] at h
      cases h
      obtain ⟨h1, h2, -⟩ := mod024_ref_line3 b b0 I hi hn hr
      exact ⟨by rw [hd]; exact h1, fun x => by rw [hp]; exact h2 x⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_patch, hw, if_true]
    have h4 : mod024_line4 strNaming mod024_acceptAll mod024_Au := mod024_ref_line4
    rw [← h4 b I hi hn]
    cases mod024_Au b I [] with
    | error m => exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun ⟨_, h⟩ => nomatch h)⟩
    | ok b0 => exact ⟨fun _ => ⟨b0, rfl⟩, fun _ => ⟨f b I b0, rfl⟩⟩

/-- A wrong model is refused by line 3 when, on the portless `Bare` under `s` into a builder
holding `P`, it records a retired port or a membership entry. -/
theorem mod024_records_killed (Au : AutoFn String Unit)
    (hv : ((Au mod024_bP (renamedInstance strNaming mod024_exBare "s") []).toOption.map
      fun b => b.retired.length + b.contrib.length) ≠ some 0) :
    ¬ MOD_024 strNaming mod024_acceptAll mod024_C Au := by
  intro h
  cases hr : Au mod024_bP (renamedInstance strNaming mod024_exBare "s") [] with
  | error m =>
    obtain ⟨b', hb'⟩ := (h.2.2.2 mod024_bP (renamedInstance strNaming mod024_exBare "s") rfl
      (by decide)).2 (fun _ _ => rfl)
    rw [hr] at hb'; cases hb'
  | ok b' =>
    obtain ⟨-, -, -, h4, h5, -⟩ := h.2.2.1 mod024_bP b' (renamedInstance strNaming mod024_exBare "s")
      rfl (by decide) hr
    rw [hr] at hv
    exact hv (by simp [Except.toOption, h4, h5, mod024_bP])

/-- The auto-composition that retires every place it infers kills the mutant: composing the
portless `Bare` under `s` into a builder holding `P` moves `s/P` to `P` as the reference does,
so the transitions and places are right, but it also records `s/P` as a retired port, and
[MOD-027] says a body place merged by inference is not a port and is not retired (line 3). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_recordsFree_killed :
    MOD_024_mutant_recordsFree strNaming mod024_acceptAll mod024_C mod024_retireAll ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C mod024_retireAll :=
  ⟨mod024_recordsFree_of (fun b I => retire I.pfx (inferEntries strNaming b I))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    mod024_records_killed _ (by decide)⟩

/-- The auto-composition that records subnet membership on the inference path is refused too:
on the same call it records `s/emit` as a member of `s`, and [MOD-026] says instance composition
records no membership (line 3). -/
theorem mod024_recordAll_killed :
    MOD_024_mutant_recordsFree strNaming mod024_acceptAll mod024_C mod024_recordAll ∧
      ¬ MOD_024 strNaming mod024_acceptAll mod024_C mod024_recordAll :=
  ⟨mod024_recordsFree_of
      (fun _ I b' => { b' with contrib := b'.contrib ++ I.defs.map fun d => (d.core.name, I.pfx) })
      (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    mod024_records_killed _ (by decide)⟩

/-! ### Mutant: a refused transition need not fail the call -/

/-- Mutant reading: MOD-024 with line 4 cut to its acceptance half, so a call without ports may
succeed although the transition builder refuses a rewritten transition. -/
def MOD_024_mutant_noRefusal {N A : Type} [DecidableEq N] (Nm : Naming N)
    (Build : Trans N → Option String) (C : ComposeFn N A) (Au : AutoFn N A) : Prop :=
  mod024_line1 C Au ∧ mod024_line2 Au ∧ mod024_line3 Nm Au ∧ mod024_line4_accept Nm Build Au

/-- A transition builder that refuses the transition named `s/emit`. -/
def mod024_refuseEmit : Trans String → Option String := fun t =>
  if t.core.name = "s/emit" then some "refused" else none

/-- The reference composition under that builder. -/
def mod024_refuseC : ComposeFn String Unit :=
  refCompose (fun _ => ()) mod024_refuseEmit (fun c _ => .ok c)

/-- The auto-composition that skips the transition builder's checks on the inference path (a
fast path that pushes the rewritten transitions straight into the builder): the reference under
`mod024_refuseEmit`, except that a call without ports runs the reference that accepts every
transition. -/
def mod024_skipCheck : AutoFn String Unit := fun b I cs =>
  if cs.isEmpty && I.iface.isEmpty then mod024_Au b I []
  else refAuto strNaming (fun _ => ()) mod024_refuseEmit (fun c _ => .ok c) b I cs

/-- The auto-composition that skips the check kills the mutant: composing the portless `Bare`
under `s` into a builder holding `P` succeeds, although the transition builder refuses the
rewritten `s/emit` and the reference, like the explicit form with the same wiring, fails the
call (line 4). -/
@[evidence mutant MOD_024]
theorem MOD_024_mutant_noRefusal_killed :
    MOD_024_mutant_noRefusal strNaming mod024_refuseEmit mod024_refuseC mod024_skipCheck ∧
      ¬ MOD_024 strNaming mod024_refuseEmit mod024_refuseC mod024_skipCheck := by
  refine ⟨⟨fun b I hi => ?_, fun b I cs hc => ?_, fun b b' I hi hn h => ?_,
    fun b I hi hn _ => ?_⟩, fun h => ?_⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = false := by
      cases hI : I.iface with
      | nil => exact absurd hI hi
      | cons _ _ => rfl
    simp only [mod024_skipCheck, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line1 b I hi
  · have hw : (cs.isEmpty && I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_skipCheck, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_skipCheck, hw, if_true] at h
    exact mod024_ref_line3 b b' I hi hn h
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_skipCheck, hw, if_true]
    exact (mod024_ref_line4 (Nm := strNaming) (tyOf := fun _ : String => ())
      (Mg := fun c (_ : CDef String Unit) => .ok c) b I hi hn).2 fun _ _ => rfl
  · have h4 : mod024_line4 strNaming mod024_acceptAll mod024_Au := mod024_ref_line4
    have hok : ∃ b', mod024_skipCheck mod024_bP (renamedInstance strNaming mod024_exBare "s") []
        = .ok b' :=
      (h4 mod024_bP (renamedInstance strNaming mod024_exBare "s") rfl (by decide)).2
        fun _ _ => rfl
    have hall := (h.2.2.2 _ _ rfl (by decide)).1 hok
    have hb : ((renamedInstance strNaming mod024_exBare "s").defs.all fun d =>
        mod024_refuseEmit (autoDef strNaming mod024_bP
          (renamedInstance strNaming mod024_exBare "s") d).toTrans == none) = true :=
      List.all_eq_true.2 fun d hd => by simp [hall d hd]
    exact absurd hb (by decide)

/-! ### Place equality across languages -/

/-- The transition `emit` of the place-equality example over typed places: it puts a token into
the place `P` of token type `false`. -/
def mod024_emitT : CDef (String × Bool) Unit :=
  { core := ⟨"emit", [], [], [], []⟩, out := some (.place ("P", false)),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The same transition over places identified by name. -/
def mod024_emitS : CDef String Unit :=
  { core := ⟨"emit", [], [], [], []⟩, out := some (.place "P"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- **The two place equalities give different inferred bindings** (the Place equality note of
the MOD-024 body). A portless subnet writes into its place `P`; the builder already holds a
place named `P` of another token type. With places compared by name and token type (Java,
`typedNaming`), the two places differ, so `P` stays private as `s/P` and the builder keeps both.
With places compared by name only (TypeScript, Rust, Python, `strNaming`), the body's `P` is the
builder's `P` and `s/emit` writes into it. Both are models of MOD-024, whose probe is the
implementation's own place equality. -/
theorem mod024_placeEquality_divergence :
    ((refInst (typedNaming Bool)
        { name := "Bare", places := [("P", false)], defs := [mod024_emitT], ports := [],
          chans := [] } "s" >>= fun I =>
        refAuto (typedNaming Bool) (fun _ => ()) refBuild (fun c _ => .ok c)
          { places := [("P", true)], defs := [] } I []).toOption.map
        fun b => (b.places, b.defs.map (·.namedPlaces))) =
      some ([("P", true), ("s/P", false)], [[("s/P", false)]]) ∧
    ((refInst strNaming
        { name := "Bare", places := ["P"], defs := [mod024_emitS], ports := [], chans := [] } "s"
        >>= fun I =>
        refAuto strNaming (fun _ => ()) refBuild (fun c _ => .ok c)
          { places := ["P"], defs := [] } I []).toOption.map
        fun b => (b.places, b.defs.map (·.namedPlaces))) =
      some (["P"], [["P"]]) := by
  decide

/-! ### The runtimes' correspondence: an all-identity one dropped -/

/-- A definition with an all-identity correspondence dropped as a whole, as Rust
(`wholesale_drop_if_all_identity`, `rust/libpetri-core/src/rewriter.rs`), Java
(`compactIdentityAlias`, `java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java`)
and TypeScript (`dropIfAllIdentity`, `typescript/src/core/internal/subnet-rewriter.ts`) do on
every rewrite pass. -/
def mod024_dropId (d : CDef String Unit) : CDef String Unit :=
  { d with corr := d.corr.bind corrDropAllId }

/-- The reference auto-composition with the runtimes' correspondence: on the inference path every
added definition's all-identity correspondence is dropped. -/
def mod024_dropAu : AutoFn String Unit :=
  mod024_patch (fun I cs => cs.isEmpty && I.iface.isEmpty)
    fun b I _ => (mod024_Au b I []).map fun b' =>
      { b' with defs := b.defs ++ (b'.defs.drop b.defs.length).map mod024_dropId }

/-- Dropping twice is dropping once. -/
theorem mod024_dropId_idem (d : CDef String Unit) :
    mod024_dropId (mod024_dropId d) = mod024_dropId d := by
  cases d with
  | mk td corr =>
    cases corr with
    | none => rfl
    | some al =>
      simp only [mod024_dropId, Option.bind_some]
      unfold corrDropAllId
      split <;> simp_all

/-- The dropped form of an inferred rewrite is an inferred rewrite. -/
theorem mod024_autoOk_dropId {b : Bld String Unit} {I : Instance String Unit}
    {m d : CDef String Unit} (h : mod024_autoOk strNaming b I m d) :
    mod024_autoOk strNaming b I (mod024_dropId m) d := by
  have hd : mod024_dropId (autoDef strNaming b I d) =
      corrDropPass (autoPlace strNaming b I) id d := rfl
  rcases h with rfl | rfl
  · exact Or.inr hd
  · rw [← hd, mod024_dropId_idem]
    exact Or.inr rfl

/-- **The runtimes' choice meets the block.** The auto-composition that drops an all-identity
correspondence, as all three runtimes do and as [MOD-031] allows, satisfies MOD-024: on the
portless `OnlyP` (`emit` writes into `P`) under `s` into a builder holding `P`, it adds `s/emit`
writing into `P` with no correspondence, where the reference keeps `[(P, P)]`. -/
theorem mod024_dropAu_holds :
    MOD_024 strNaming mod024_acceptAll mod024_C mod024_dropAu := by
  refine ⟨fun b I hi => ?_, fun b I cs hc => ?_, fun b b' I hi hn h => ?_, fun b I hi hn => ?_⟩
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = false := by
      cases hI : I.iface with
      | nil => exact absurd hI hi
      | cons _ _ => rfl
    simp only [mod024_dropAu, mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line1 b I hi
  · have hw : (cs.isEmpty && I.iface.isEmpty) = false := by
      cases cs with
      | nil => exact absurd rfl hc
      | cons _ _ => rfl
    simp only [mod024_dropAu, mod024_patch, hw, Bool.false_eq_true, if_false]
    exact mod024_ref_line2 b I cs hc
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_dropAu, mod024_patch, hw, if_true] at h
    cases hr : mod024_Au b I [] with
    | error m => rw [hr] at h; cases h
    | ok b0 =>
      rw [hr] at h
      cases h
      obtain ⟨⟨ms, h1, hF⟩, h2, h3, h4, h5, h6⟩ := mod024_ref_line3 b b0 I hi hn hr
      refine ⟨⟨ms.map mod024_dropId, by show b.defs ++ _ = _; rw [h1, List.drop_left], ?_⟩, h2, h3, h4, h5, h6⟩
      rw [List.forall₂_map_left_iff]
      exact hF.imp fun _ _ => mod024_autoOk_dropId
  · have hw : (([] : List String).isEmpty && I.iface.isEmpty) = true := by simp [hi]
    simp only [mod024_dropAu, mod024_patch, hw, if_true]
    have h4 : mod024_line4 strNaming mod024_acceptAll mod024_Au := mod024_ref_line4
    rw [← h4 b I hi hn]
    cases mod024_Au b I [] with
    | error m => exact ⟨(fun ⟨_, h⟩ => nomatch h), (fun ⟨_, h⟩ => nomatch h)⟩
    | ok b0 => exact ⟨fun _ => ⟨b0, rfl⟩, fun _ => ⟨_, rfl⟩⟩

end Libpetri.Spec
