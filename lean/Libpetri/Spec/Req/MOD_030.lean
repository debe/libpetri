import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Spec.Req.MOD_010

set_option linter.missingDocs true

/-!
# MOD-030: Action binding per instance (`spec/11-modular-composition.md`)

MOD-030 is a pure-function requirement (kind F) over an abstract per-instance binding function
`Bind : InstBindFn N A`: a module instance and an override mapping (original, un-prefixed
transition names to actions) give a derived instance or a rejection. An action is read as its
identity tag (`Act`: the built-in passthrough or another action named by an opaque id), so "the
same action object" is "the same tag".

The statement has four lines:

1. a call whose every key `k` names a transition `p/k` of the instance (`p` its prefix) succeeds;
2. a derived instance has the receiver's prefix, places, interface and handles and, position by
   position, the receiver's transitions with the same name, arcs, output specification, timing,
   priority and declared-to-actual correspondence ([MOD-031]): only actions change;
3. the transition `p/k` of a derived instance carries the action the mapping gives the key `k`;
4. a transition the mapping does not name keeps the action it carried in the receiver.

Three consequences hold for every model of the block: successive calls compose as last-wins
replacement (`mod030_lastWins`, AC6), binding never changes how a transition fires
(`mod030_toTrans`), and two instances of one definition carry the same actions until one is
rebound (`mod030_shared`, AC1, a consequence of MOD-010's line 3).

The witness is `refBindInst`, which translates each key `k` to `p/k` and binds through the
resolver form of [CORE-042], so a key that names no transition is never asked for (Rust,
Python). A key that names no transition is left open by ruling D87 (a): Java and TypeScript
reject the call, and that reading (`strictBindInst`) satisfies the block too
(`MOD_030_unknownKey_undecided`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The per-instance binding -/

section Model

variable {N A : Type}

/-- An override mapping of a `bindActions` call on an instance: pairs of an original
(un-prefixed) transition name and an action. A runtime map holds one entry per key; a key's
action here is its first entry's. -/
abbrev Overrides (A : Type) := List (String × Act A)

/-- The action an override mapping gives the key `k`, `none` when it holds no entry for `k`. -/
def ovr (m : Overrides A) (k : String) : Option (Act A) :=
  (m.find? (fun e => e.1 == k)).map (·.2)

/-- A per-instance binding function ([MOD-030]): a module instance and an override mapping give
a derived instance or a rejection with a message. -/
abbrev InstBindFn (N A : Type) := Instance N A → Overrides A → Except String (Instance N A)

/-- Under one prefix the prefixed name determines the original name, for every prefix. -/
theorem preS_cancel (p x y : String) : preS p x = preS p y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hl : x.toList = y.toList := by
    simpa [preS, String.toList_append, List.append_assoc] using congrArg String.toList h
  exact String.ext hl

/-- The action a mapping gives a transition named `n` of an instance under prefix `p`: that of
the first entry whose key `k` gives the name `p/k`, `none` when there is none. -/
def instLook (p : String) (m : Overrides A) (n : String) : Option (Act A) :=
  (m.find? (fun e => preS p e.1 == n)).map (·.2)

/-- One transition definition of an instance under prefix `p` bound with the mapping `m`: the
action the mapping gives its name, its own action when the mapping gives none; everything else
kept. -/
def bindInstDef (p : String) (m : Overrides A) (d : CDef N A) : CDef N A :=
  { d with action := (instLook p m d.core.name).getD d.action }

/-- **The reference per-instance binding** ([MOD-030]), as Rust does it
(`Instance::bind_actions` in `rust/libpetri-core/src/instance.rs`): every key `k` translated to `p/k`, the renamed
body bound through the resolver form of [CORE-042] (`PetriNet::bind_actions_with_resolver` in `rust/libpetri-core/src/petri_net.rs`),
the prefix, places, interface and handles kept. It never rejects: a key that names no transition
is never asked for. -/
def refBindInst : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (bindInstDef I.pfx m) }

/- The reference per-instance binding is the witness model of MOD-030. -/
#spec_witness refBindInst

/-- The per-instance binding as Java and TypeScript do it
(`Instance.bindActions` in `java/src/main/java/org/libpetri/core/Instance.java` and
`typescript/src/core/instance.ts`): a call with a key that names no transition of the
instance is rejected; otherwise the reference. -/
def strictBindInst : InstBindFn N A := fun I m =>
  if m.all (fun e => (I.defs.map (·.core.name)).contains (preS I.pfx e.1)) then refBindInst I m
  else .error "bindActions: no transition of that name"

/-- Looking a key up through its prefixed name is looking it up directly. -/
theorem find_preS (p k : String) (m : Overrides A) :
    m.find? (fun e => preS p e.1 == preS p k) = m.find? (fun e => e.1 == k) := by
  have hf : (fun e : String × Act A => preS p e.1 == preS p k) = (fun e => e.1 == k) := by
    funext e
    cases h : (e.1 == k) with
    | true => exact beq_iff_eq.2 ((preS_cancel p _ _).2 (beq_iff_eq.1 h))
    | false =>
      refine Bool.eq_false_iff.2 fun h' => ?_
      exact absurd (beq_iff_eq.2 ((preS_cancel p _ _).1 (beq_iff_eq.1 h'))) (by simp [h])
  rw [hf]

/-- A transition named `p/k` is given what the mapping gives `k`. -/
theorem instLook_named {p k n : String} (m : Overrides A) (hn : n = preS p k) :
    instLook p m n = ovr m k := by
  subst hn
  simp only [instLook, ovr, find_preS]

/-- A transition the mapping does not name is given nothing. -/
theorem instLook_unnamed {p n : String} {m : Overrides A}
    (hn : ∀ k, n = preS p k → ovr m k = none) : instLook p m n = none := by
  simp only [instLook]
  cases hf : m.find? (fun e => preS p e.1 == n) with
  | none => rfl
  | some e =>
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    have hnone := hn e.1 he.symm
    rw [← instLook_named m he.symm] at hnone
    simp only [instLook, hf] at hnone
    cases hnone

/-- A bound definition keeps everything but the action. -/
theorem bindInstDef_kept (p : String) (m : Overrides A) (d : CDef N A) :
    (bindInstDef p m d).core = d.core ∧ (bindInstDef p m d).out = d.out ∧
      (bindInstDef p m d).timing = d.timing ∧ (bindInstDef p m d).priority = d.priority ∧
      (bindInstDef p m d).corr = d.corr := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A definition named `p/k` takes the action the mapping gives `k`. -/
theorem bindInstDef_named {p k : String} {m : Overrides A} {d : CDef N A} {a : Act A}
    (hn : d.core.name = preS p k) (ha : ovr m k = some a) : (bindInstDef p m d).action = a := by
  show (instLook p m d.core.name).getD d.action = a
  rw [instLook_named m hn, ha]
  rfl

/-- A definition the mapping does not name keeps its action. -/
theorem bindInstDef_unnamed {p : String} {m : Overrides A} {d : CDef N A}
    (hn : ∀ k, d.core.name = preS p k → ovr m k = none) :
    (bindInstDef p m d).action = d.action := by
  show (instLook p m d.core.name).getD d.action = d.action
  rw [instLook_unnamed hn]
  rfl

/-- A relation that holds between `f d` and `d` for every element holds position by position
between the mapped list and the list. -/
theorem forall₂_map_self {α β : Type} {R : β → α → Prop} {f : α → β} :
    ∀ {l : List α}, (∀ d ∈ l, R (f d) d) → List.Forall₂ R (l.map f) l
  | [], _ => .nil
  | d :: l, h => .cons (h d (by simp)) (forall₂_map_self fun x hx => h x (by simp [hx]))

/-- Two position-by-position relations compose. -/
theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (hc : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ → List.Forall₂ T l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (hc _ _ _ h₁ h₂) (forall₂_comp hc t₁ t₂)

/-- Two position-by-position conjoined relations give the relation of their conjunction. -/
theorem forall₂_and {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ → List.Forall₂ (fun a b => R a b ∧ S a b) l₁ l₂
  | _, _, .nil, .nil => .nil
  | _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons ⟨h₁, h₂⟩ (forall₂_and t₁ t₂)

/-- A position-by-position relation that equates `f` gives equal mapped lists. -/
theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hr : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.map_cons, hr _ _ h, forall₂_map_eq hr t]

end Model

/-! ## MOD-030: Action Binding Per Instance -/

requirement MOD_030
  id "MOD-030"
  title "Action Binding Per Instance (share-by-default, override via bindActions)"
  kind F
  scope "every per-instance action binding (Instance.bindActions in Java, TypeScript and Rust; Python's Instance.bind_actions rides on the Rust binding)"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* `bindActions` is called on a module instance with prefix `p` and a mapping in which every key `k` names a transition `p/k` of the instance, the call *shall* return a derived instance."
        "*When* `bindActions` on a module instance returns a derived instance, the derived instance *shall* have the prefix, the places, the interface and the port and channel handles of the receiver and exactly as many transitions as the receiver, each with the same name, arcs, output specification, timing, priority and declared-to-actual place correspondence ([MOD-031]) as the receiver's transition at the same position."
        "*When* `bindActions` on a module instance with prefix `p` returns a derived instance and the mapping maps a key `k` to an action, the transition `p/k` *shall* carry that action in the derived instance."
        "*When* `bindActions` on a module instance with prefix `p` returns a derived instance, a transition whose name is not `p/k` for any key `k` of the mapping *shall* carry in the derived instance the action it carried in the receiver."
        "Whether a call whose mapping holds a key `k` for which the instance has no transition `p/k` returns a derived instance (Rust, Python: the key is ignored) or is rejected (Java, TypeScript: an error naming the key) is not specified."
  reading "For every per-instance binding function Bind (a module instance and an override mapping give a derived instance or a rejection):"
          "if every key k of the mapping m names a transition p/k of the instance I, where p is I's prefix, Bind I m succeeds;"
          "if Bind I m returns J, then J has I's prefix, places, port and channel handles and interface, and J's transition definitions match I's position by position (same length, same order), each with I's name and arcs (core), output specification, timing, priority and correspondence;"
          "if Bind I m returns J, the transition at each position of J carries the action a whenever I's transition there is named p/k and m gives the key k the action a;"
          "if Bind I m returns J, the transition at each position of J carries the action I's transition there carried whenever no key k with p/k equal to that transition's name is given an action by m."
  assumes "A per-instance binding is a function from a module instance (Instance: prefix, renamed places, renamed transition definitions in order, port and channel handles, interface; Spec/GlossaryCompose.lean) and an override mapping to a derived instance or a rejection (InstBindFn). The mapping is a list of (original name, action) pairs, read through ovr: a key's action is its first entry's, and a runtime map holds one entry per key. An action is read as its identity tag (Act: the built-in passthrough or another action named by an opaque id), so 'shared by reference, not by copy' and 'the same action object' are 'the same tag'; what an action does when the net fires is CORE-050's. The block is stated over every Instance record, which is stronger than 'a module instance': it also covers records no instantiate call makes (a transition name not of the form p/x, places that do not match the definitions). Both models bind every record the same way, so the stronger scope excludes no runtime behaviour on instances made by instantiate (MOD-010) whose transition names are distinct. An instantiated body can hold two transitions of one name, since no builder and no instantiation checks transition names (ruling D23 assumes them distinct and requires no check; refInst does not check either); such an instance is outside the shared unique-names assumption of rulings D10 and D23, and the block still states it. On such an instance every runtime keeps the own action of a transition the mapping does not name: the resolver defers it (none, PetriNet::bind_actions_with_resolver in rust/libpetri-core/src/petri_net.rs; null, the resolver that Instance.bindActions passes in java/src/main/java/org/libpetri/core/Instance.java and typescript/src/core/instance.ts), and the net's resolver binding keeps a deferred transition as it is. MOD_030_forbids_firstOfName kills a binding that gives such a transition the action of the first transition of its name, the behaviour RD-41 recorded. Line 2 compares the places as a list, so their order and multiplicity are kept too; every runtime keeps the receiver's place collection as it is."
          "Ruling D87 (a): a key that names no transition of the instance is out of scope. Rust and Python ignore it (Instance::bind_actions in rust/libpetri-core/src/instance.rs translates every key to p/k and binds through the resolver form, PetriNet::bind_actions_with_resolver in rust/libpetri-core/src/petri_net.rs, which asks only for the names of the body's transitions; PyInstance::bind_actions in rust/libpetri-py/src/model.rs), Java and TypeScript reject the call (the key check in Instance.bindActions, java/src/main/java/org/libpetri/core/Instance.java and typescript/src/core/instance.ts). Line 1 is therefore stated for mappings whose every key names a transition, and lines 2 to 4 for calls that return; the reference refBindInst (Rust) and strictBindInst (Java, TypeScript) both satisfy the block and differ on such a key (MOD_030_unknownKey_undecided). The quoted sentence that leaves the case unspecified records the ruling. Java checks the keys against the definition's body and TypeScript against the renamed body; for an instance made by instantiate these are the same set (MOD-010 line 3)."
          "All three runtimes bind an instance through the resolver form of CORE-042, the transition the call does not name being deferred (PetriNet::bind_actions_with_resolver in rust/libpetri-core/src/petri_net.rs, and the resolver that Instance.bindActions passes in java/src/main/java/org/libpetri/core/Instance.java and typescript/src/core/instance.ts), so CORE-042's map-form divergence (Java and TypeScript give an omitted transition passthrough) does not reach per-instance binding; a binding that does is killed by line 4 (MOD_030_mutant_clobber_killed)."
          "Line 2 is what 'a derived instance whose specified transitions carry the supplied actions instead' leaves unchanged. All three runtimes keep the prefix, the definition, the port and channel handles and the parameters (the Instance that Instance::bind_actions returns in rust/libpetri-core/src/instance.rs and that Instance.bindActions returns in java/src/main/java/org/libpetri/core/Instance.java; TypeScript rebuilds its channel handles against the rebound body by name, reboundChannelHandles in Instance.bindActions, typescript/src/core/instance.ts, which the model's name-valued handles read as unchanged) and rebuild a rebound transition through the transition builder, keeping its name, arcs, output specification, timing and priority (CORE-042 line 1) and its declared-to-actual correspondence (MOD-031: 'Binding or rebinding a transition's action ([CORE-042], [MOD-030]) MUST preserve this correspondence', rebuild_with_action and rebuild in rust/libpetri-core/src/transition.rs). A binding that rebuilds and drops the correspondence violates line 2 (MOD_030_mutant_dropCorr_killed). The parameters value is not modelled (MOD-010 AC4). By line 2 binding never changes how a transition fires (mod030_toTrans)."
          "AC1 (by default two instances of one subnet definition reference the same action object per transition) is MOD-010's line 3 (instantiation keeps every action), not a line here: mod030_shared derives, for every model of MOD-010, that two instances of one definition carry the same actions position by position. Their per-instance override is AC2 and the test derivation: MOD_030_nonvacuous binds produce on p1 and leaves p2 with the default."
          "AC2 (bindActions({\"produce\": newAction}) gives an instance whose produce transition uses newAction, the original unchanged) is lines 1 and 3; 'the original instance is unchanged' holds of every binding in the model, a function on immutable values, and is tested in the runtimes, not proven. A binding that never accepts meets lines 2 to 4 and violates line 1 (MOD_030_mutant_noAcceptance_killed)."
          "AC3 (the override map keys use original, un-prefixed transition names) is line 3's reading of a key k as the transition p/k: a binding that looks a key up as the transition's full name binds nothing under the original names and violates line 3 (MOD_030_forbids_prefixedKeys)."
          "AC4 (transitions not named in the override map retain their shared default action) and AC7 (a call that overrides t leaves the action of every u != t exactly as inherited from the receiver) are line 4: the receiver's action, which is the shared default unless an earlier call rebound it."
          "AC5 (the override is purely structural, established before the subnet is composed and fixed for the lifetime of the resulting net) is not a line: binding is a function on instance values with no runtime state, and a composed net is an immutable value whose transitions carry the actions of the instances composed into it (MOD-020, MOD-021); tested, not proven."
          "AC6 (successive calls compose as last-wins replacement; A is not invoked for t) follows from lines 2 and 3 for every model of the block (mod030_lastWins): after two calls the transition carries the second call's action. That A is not invoked at run time is that line with CORE-050 (a firing runs the transition's bound action). A binding that keeps an earlier override (first wins) violates line 3 (MOD_030_mutant_firstWins_killed). A sequential composition of A and B is not expressible over identity tags and is excluded by line 3, which gives the transition exactly the supplied tag."
          "AC8 (bindActions is non-mutating; the receiver stays usable for independent derivations) and the body's 'MUST NOT mutate the receiver' hold of every binding in the model, a function on values, and are tested in the runtimes, not proven. Java returns the receiver itself for an empty mapping (Instance.bindActions, java/src/main/java/org/libpetri/core/Instance.java), which satisfies lines 2 to 4, the receiver being immutable. 'Overriding actions on instance A does NOT affect instance B' holds for the same reason: binding takes one instance and returns another, and MOD_030_nonvacuous shows p2 unchanged after binding p1."
          "The sentence that MOD-030 extends CORE-042 into the composition layer is the reading above that per-instance binding is the resolver form of CORE-042 applied to the renamed body. Binding on a subnet definition (SubnetDef.bindActions) is MOD-051's (W11)."
  signoff "2026-11-13 6e0a241705c76f8e ai"
  statement : ∀ {N A : Type}, InstBindFn N A → Prop :=
    fun {N A} Bind =>
      (∀ (I : Instance N A) m, (∀ e ∈ m, preS I.pfx e.1 ∈ I.defs.map (·.core.name)) →
        ∃ J, Bind I m = .ok J) ∧
      (∀ (I : Instance N A) m J, Bind I m = .ok J →
        J.pfx = I.pfx ∧ J.places = I.places ∧ J.port = I.port ∧ J.chan = I.chan ∧
        J.iface = I.iface ∧
        List.Forall₂ (fun d' d => d'.core = d.core ∧ d'.out = d.out ∧ d'.timing = d.timing ∧
          d'.priority = d.priority ∧ d'.corr = d.corr) J.defs I.defs) ∧
      (∀ (I : Instance N A) m J, Bind I m = .ok J →
        List.Forall₂ (fun d' d => ∀ k a, d.core.name = preS I.pfx k → ovr m k = some a →
          d'.action = a) J.defs I.defs) ∧
      (∀ (I : Instance N A) m J, Bind I m = .ok J →
        List.Forall₂ (fun d' d => (∀ k, d.core.name = preS I.pfx k → ovr m k = none) →
          d'.action = d.action) J.defs I.defs)

/- The pinned readable form of MOD-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_030 : {N A : Type} → InstBindFn N A → Prop :=
fun {N A} Bind =>
  (∀ (I : Instance N A) (m : Overrides A),
      (∀ e ∈ m, preS I.pfx e.1 ∈ List.map (fun x => x.core.name) I.defs) → ∃ J, Bind I m = Except.ok J) ∧
    (∀ (I : Instance N A) (m : Overrides A) (J : Instance N A),
        Bind I m = Except.ok J →
          J.pfx = I.pfx ∧
            J.places = I.places ∧
              J.port = I.port ∧
                J.chan = I.chan ∧
                  J.iface = I.iface ∧
                    List.Forall₂
                      (fun d' d =>
                        d'.core = d.core ∧
                          d'.out = d.out ∧ d'.timing = d.timing ∧ d'.priority = d.priority ∧ d'.corr = d.corr)
                      J.defs I.defs) ∧
      (∀ (I : Instance N A) (m : Overrides A) (J : Instance N A),
          Bind I m = Except.ok J →
            List.Forall₂
              (fun d' d => ∀ (k : String) (a : Act A), d.core.name = preS I.pfx k → ovr m k = some a → d'.action = a)
              J.defs I.defs) ∧
        ∀ (I : Instance N A) (m : Overrides A) (J : Instance N A),
          Bind I m = Except.ok J →
            List.Forall₂
              (fun d' d => (∀ (k : String), d.core.name = preS I.pfx k → ovr m k = none) → d'.action = d.action) J.defs
              I.defs
-/
#guard_msgs in #print MOD_030

/-! ### The four lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-030: a call whose every key names a transition succeeds. -/
def mod030_line1 (Bind : InstBindFn N A) : Prop :=
  ∀ (I : Instance N A) m, (∀ e ∈ m, preS I.pfx e.1 ∈ I.defs.map (·.core.name)) →
    ∃ J, Bind I m = .ok J

/-- Line 2 of MOD-030: a derived instance keeps everything but the actions. -/
def mod030_line2 (Bind : InstBindFn N A) : Prop :=
  ∀ (I : Instance N A) m J, Bind I m = .ok J →
    J.pfx = I.pfx ∧ J.places = I.places ∧ J.port = I.port ∧ J.chan = I.chan ∧
    J.iface = I.iface ∧
    List.Forall₂ (fun d' d => d'.core = d.core ∧ d'.out = d.out ∧ d'.timing = d.timing ∧
      d'.priority = d.priority ∧ d'.corr = d.corr) J.defs I.defs

/-- Line 3 of MOD-030: the transition `p/k` carries the action the mapping gives `k`. -/
def mod030_line3 (Bind : InstBindFn N A) : Prop :=
  ∀ (I : Instance N A) m J, Bind I m = .ok J →
    List.Forall₂ (fun d' d => ∀ k a, d.core.name = preS I.pfx k → ovr m k = some a →
      d'.action = a) J.defs I.defs

/-- Line 4 of MOD-030: a transition the mapping does not name keeps its action. -/
def mod030_line4 (Bind : InstBindFn N A) : Prop :=
  ∀ (I : Instance N A) m J, Bind I m = .ok J →
    List.Forall₂ (fun d' d => (∀ k, d.core.name = preS I.pfx k → ovr m k = none) →
      d'.action = d.action) J.defs I.defs

/-- MOD-030 is its four lines. -/
theorem mod030_iff (Bind : InstBindFn N A) :
    MOD_030 Bind ↔ mod030_line1 Bind ∧ mod030_line2 Bind ∧ mod030_line3 Bind ∧ mod030_line4 Bind :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- ✓ The reference per-instance binding satisfies MOD-030 at every place and action type. Take
an instance under prefix `p1` with the transitions `p1/produce` and `p1/consume` and bind it with
the mapping `produce ↦ newAction`: the call succeeds, `p1/produce` carries `newAction`,
`p1/consume` keeps the action it had, and the prefix, the places, the handles and every
transition's name, arcs, timing, priority and correspondence stay as they were. -/
@[evidence holds MOD_030]
theorem MOD_030_reference {N A : Type} : MOD_030 (refBindInst (N := N) (A := A)) := by
  refine ⟨fun I m _ => ⟨_, rfl⟩, fun I m J h => ?_, fun I m J h => ?_, fun I m J h => ?_⟩ <;>
    cases h
  · exact ⟨rfl, rfl, rfl, rfl, rfl, forall₂_map_self fun d _ => bindInstDef_kept _ _ d⟩
  · exact forall₂_map_self fun d _ k a hn ha => bindInstDef_named hn ha
  · exact forall₂_map_self fun d _ hn => bindInstDef_unnamed hn

/-- A success of the Java and TypeScript binding is the reference's. -/
theorem strictBindInst_ok {N A : Type} {I J : Instance N A} {m : Overrides A}
    (h : strictBindInst I m = .ok J) : refBindInst I m = .ok J := by
  unfold strictBindInst at h
  split at h
  · exact h
  · cases h

/-- The Java and TypeScript binding (a key that names no transition is rejected) satisfies
MOD-030 too: it accepts every mapping whose keys all name transitions, and every success is the
reference's. -/
theorem MOD_030_strict {N A : Type} : MOD_030 (strictBindInst (N := N) (A := A)) := by
  have R := MOD_030_reference (N := N) (A := A)
  refine ⟨fun I m hm => ?_, fun I m J h => R.2.1 I m J (strictBindInst_ok h),
    fun I m J h => R.2.2.1 I m J (strictBindInst_ok h),
    fun I m J h => R.2.2.2 I m J (strictBindInst_ok h)⟩
  have hall : m.all (fun e => (I.defs.map (·.core.name)).contains (preS I.pfx e.1)) = true :=
    List.all_eq_true.2 fun e he => by simpa using hm e he
  unfold strictBindInst
  rw [if_pos hall]
  exact ⟨_, rfl⟩

/-! ### Consequences for every model of the block -/

section Consequences

variable {N A : Type}

/-- **AC6, last wins.** In every model of MOD-030, two successive calls leave each transition
`p/k` with the action the second call gives `k`: binding `t ↦ A` and then `t ↦ B` leaves `p/t`
carrying `B`, and `A` is gone. -/
theorem mod030_lastWins {Bind : InstBindFn N A} (h : MOD_030 Bind) {I J₁ J₂ : Instance N A}
    {m₁ m₂ : Overrides A} (h₁ : Bind I m₁ = .ok J₁) (h₂ : Bind J₁ m₂ = .ok J₂) :
    List.Forall₂ (fun d₂ d => ∀ k b, d.core.name = preS I.pfx k → ovr m₂ k = some b →
      d₂.action = b) J₂.defs I.defs := by
  have s := h.2.1 I m₁ J₁ h₁
  have l3 := h.2.2.1 J₁ m₂ J₂ h₂
  rw [s.1] at l3
  exact forall₂_comp (fun a b c hab hbc k x hn hx => hab k x (by rw [hbc.1]; exact hn) hx)
    l3 s.2.2.2.2.2

/-- **Binding does not change firing.** In every model of MOD-030, a derived instance's
transitions have, position by position, the firing view of the receiver's: names, arcs, output
specification and timing are untouched, so the reference firing relation treats them alike. -/
theorem mod030_toTrans {Bind : InstBindFn N A} (h : MOD_030 Bind) {I J : Instance N A}
    {m : Overrides A} (hJ : Bind I m = .ok J) :
    J.defs.map (fun d => d.toTransDef.toTrans) = I.defs.map (fun d => d.toTransDef.toTrans) :=
  forall₂_map_eq (fun a b hab => by
    show TransDef.toTrans _ = TransDef.toTrans _
    unfold TransDef.toTrans
    rw [hab.1, hab.2.1, hab.2.2.1]) (h.2.1 I m J hJ).2.2.2.2.2

/-- **AC1, shared by default.** In every model of MOD-010, two instances of one subnet definition
carry the same actions, position by position: instantiating a body whose `produce` carries the
action `act` under `p1` and under `p2` gives `p1/produce` and `p2/produce` both carrying `act`. -/
theorem mod030_shared {Nm : Naming N} {Inst : InstFn N A} (h : MOD_010 Nm Inst)
    {S : SubnetDef N A} {p q : String} {I J : Instance N A} (hI : Inst S p = .ok I)
    (hJ : Inst S q = .ok J) : I.defs.map (·.action) = J.defs.map (·.action) := by
  have key : ∀ p I, Inst S p = .ok I → I.defs.map (·.action) = S.defs.map (·.action) := by
    intro p I hI
    have := congrArg (List.map TransDef.action) (h.2.2.1 S p I hI).2
    simpa [List.map_map, Function.comp_def, TransDef.map] using this
  rw [key p I hI, key q J hJ]

end Consequences

/-! ### Example -/

/-- The example transition `produce`: an input arc on `in`, the output place `out`, the action
with id 1. -/
def mod030_produce : CDef String Nat :=
  { core := ⟨"produce", [⟨"in", .one⟩], [], [], []⟩, out := some (.place "out"),
    timing := .immediate, priority := 0, action := .other 1 }

/-- The example transition `consume`: an input arc on `out`, the action with id 2. -/
def mod030_consume : CDef String Nat :=
  { core := ⟨"consume", [⟨"out", .one⟩], [], [], []⟩, out := none,
    timing := .immediate, priority := 0, action := .other 2 }

/-- The example subnet definition `pc`: places `in` and `out`, the transitions `produce` and
`consume`. -/
def mod030_exS : SubnetDef String Nat :=
  { name := "pc", places := ["in", "out"], defs := [mod030_produce, mod030_consume],
    ports := [], chans := [] }

/-- ✓ The test derivation on the reference. Instantiate `pc` as `p1` and as `p2`: both carry the
actions 1 and 2 (shared by default). Bind `produce ↦ 9` on `p1`: `p1/produce` now carries 9,
`p1/consume` still 2, while `p2` still carries 1 and 2. Bind `produce ↦ 7` on the result: the
last call wins, `p1/produce` carries 7. A mapping with the key `nope` is accepted and changes
nothing. -/
@[evidence nonvacuous MOD_030]
theorem MOD_030_nonvacuous :
    (∃ I, refInst strNaming mod030_exS "p1" = .ok I ∧
      I.defs.map (·.action) = [.other 1, .other 2] ∧
      (∃ J, refBindInst I [("produce", .other 9)] = .ok J ∧
        J.defs.map (·.core.name) = ["p1/produce", "p1/consume"] ∧
        J.defs.map (·.action) = [.other 9, .other 2] ∧
        ∃ K, refBindInst J [("produce", .other 7)] = .ok K ∧
          K.defs.map (·.action) = [.other 7, .other 2]) ∧
      ∃ J, refBindInst I [("nope", .other 9)] = .ok J ∧
        J.defs.map (·.action) = [.other 1, .other 2]) ∧
    (∃ I, refInst strNaming mod030_exS "p2" = .ok I ∧
      I.defs.map (·.action) = [.other 1, .other 2]) := by
  refine ⟨⟨_, refInst_valid strNaming mod030_exS (by decide) rfl, ?_,
      ⟨_, rfl, ?_, ?_, _, rfl, ?_⟩, _, rfl, ?_⟩,
    ⟨_, refInst_valid strNaming mod030_exS (by decide) rfl, ?_⟩⟩ <;> decide

/-! ### Wrong bindings -/

section Wrong

variable {N A : Type}

/-- A binding that rejects every call. -/
def rejectAllBind : InstBindFn N A := fun _ _ => .error "rejected"

/-- A binding that binds as the reference and rebuilds every transition without its
declared-to-actual correspondence. -/
def dropCorrBind : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (fun d => { bindInstDef I.pfx m d with corr := none }) }

/-- A binding where the first override wins: a named transition takes the supplied action only
while it still carries passthrough. -/
def firstWinsBind : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (fun d => match d.action with
    | .passthrough => bindInstDef I.pfx m d
    | .other _ => d) }

/-- A binding with the net-level map form of Java and TypeScript ([CORE-042]): a transition the
mapping does not name gets passthrough. -/
def clobberBind : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (fun d =>
    { d with action := (instLook I.pfx m d.core.name).getD .passthrough }) }

/-- A binding that reads a key as the full (prefixed) transition name. -/
def prefixedKeysBind : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (fun d => { d with action := (ovr m d.core.name).getD d.action }) }

end Wrong

/-- The example instance `p` with one transition `p/produce` carrying the action 1 and a
declared-to-actual correspondence. -/
def mod030_I0 : Instance String Nat :=
  { pfx := "p", places := ["p/in", "p/out"],
    defs := [{ mod030_produce with
      core := { mod030_produce.core with name := "p/produce" }
      corr := some [("in", "p/in")] }],
    port := fun _ => none, chan := fun _ => none, iface := [] }

/-- ✗ A binding that reads the keys as full transition names violates MOD-030 (line 3, AC3): on
the instance `p` the mapping `produce ↦ 9` binds nothing, since no transition is named
`produce`, and `p/produce` keeps the action 1. -/
@[evidence forbids MOD_030]
theorem MOD_030_forbids_prefixedKeys : ¬ MOD_030 (prefixedKeysBind (N := String) (A := Nat)) := by
  intro h
  have := h.2.2.1 mod030_I0 [("produce", .other 9)] _ rfl
  rcases this with _ | ⟨h1, -⟩
  have := h1 "produce" (.other 9) rfl rfl
  exact absurd this (by decide)

/-! ### Mutant: line 1 dropped (no acceptance) -/

section MutantAccept

variable {N A : Type}

/-- Mutant reading: MOD-030 without line 1, the shape of a success only. -/
def MOD_030_mutant_noAcceptance (Bind : InstBindFn N A) : Prop :=
  mod030_line2 Bind ∧ mod030_line3 Bind ∧ mod030_line4 Bind

/-- The binding that rejects every call kills the mutant: it says nothing wrong about a success,
since it has none, but it rejects the empty mapping on an instance with no transitions
(line 1). -/
@[evidence mutant MOD_030]
theorem MOD_030_mutant_noAcceptance_killed :
    MOD_030_mutant_noAcceptance (rejectAllBind (N := N) (A := A)) ∧
      ¬ MOD_030 (rejectAllBind (N := N) (A := A)) := by
  refine ⟨⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩,
    fun h => ?_⟩
  obtain ⟨J, hJ⟩ := h.1 ⟨"a", [], [], fun _ => none, fun _ => none, []⟩ [] (fun _ h => nomatch h)
  cases hJ

end MutantAccept

/-! ### Mutant: line 2 dropped (the rebuild may lose the correspondence) -/

section MutantCorr

variable {N A : Type}

/-- Mutant reading: MOD-030 without line 2, only the actions constrained. -/
def MOD_030_mutant_dropCorr (Bind : InstBindFn N A) : Prop :=
  mod030_line1 Bind ∧ mod030_line3 Bind ∧ mod030_line4 Bind

end MutantCorr

/-- The binding that rebuilds every transition without its correspondence kills the mutant: its
actions are the reference's, but on the instance `p`, whose `p/produce` maps the declared place
`in` to `p/in`, the derived `p/produce` carries no correspondence (line 2), so an action that
names `in` would no longer find `p/in` ([MOD-031]). -/
@[evidence mutant MOD_030]
theorem MOD_030_mutant_dropCorr_killed :
    MOD_030_mutant_dropCorr (dropCorrBind (N := String) (A := Nat)) ∧
      ¬ MOD_030 (dropCorrBind (N := String) (A := Nat)) := by
  refine ⟨⟨fun I m _ => ⟨_, rfl⟩, fun I m J h => ?_, fun I m J h => ?_⟩, fun h => ?_⟩
  · cases h
    exact forall₂_map_self fun d _ k a hn ha => bindInstDef_named hn ha
  · cases h
    exact forall₂_map_self fun d _ hn => bindInstDef_unnamed hn
  · have := (h.2.1 mod030_I0 [] _ rfl).2.2.2.2.2
    rcases this with _ | ⟨⟨-, -, -, -, hc⟩, -⟩
    exact absurd hc (by decide)

/-! ### Mutant: line 3 dropped (first wins) -/

section MutantFirst

variable {N A : Type}

/-- Mutant reading: MOD-030 without line 3, so a call need not replace an action. -/
def MOD_030_mutant_firstWins (Bind : InstBindFn N A) : Prop :=
  mod030_line1 Bind ∧ mod030_line2 Bind ∧ mod030_line4 Bind

end MutantFirst

/-- The first-wins binding kills the mutant (AC6): it keeps every structure and every unnamed
action, but on the instance `p`, whose `p/produce` already carries the action 1, the mapping
`produce ↦ 9` leaves it at 1 (line 3). Bound first with `t ↦ A` and then `t ↦ B`, a
structure-only transition would end with `A`, not `B`. -/
@[evidence mutant MOD_030]
theorem MOD_030_mutant_firstWins_killed :
    MOD_030_mutant_firstWins (firstWinsBind (N := String) (A := Nat)) ∧
      ¬ MOD_030 (firstWinsBind (N := String) (A := Nat)) := by
  refine ⟨⟨fun I m _ => ⟨_, rfl⟩, fun I m J h => ?_, fun I m J h => ?_⟩, fun h => ?_⟩
  · cases h
    refine ⟨rfl, rfl, rfl, rfl, rfl, forall₂_map_self fun d _ => ?_⟩
    cases d.action <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases h
    refine forall₂_map_self fun d _ hn => ?_
    cases hda : d.action with
    | passthrough => simp only; exact (bindInstDef_unnamed hn).trans hda
    | other a => simp only; exact hda
  · have := h.2.2.1 mod030_I0 [("produce", .other 9)] _ rfl
    rcases this with _ | ⟨h1, -⟩
    have := h1 "produce" (.other 9) rfl rfl
    exact absurd this (by decide)

/-! ### Mutant: line 4 dropped (omitted transitions clobbered) -/

section MutantClobber

variable {N A : Type}

/-- Mutant reading: MOD-030 without line 4, so a transition the call omits may change. -/
def MOD_030_mutant_clobber (Bind : InstBindFn N A) : Prop :=
  mod030_line1 Bind ∧ mod030_line2 Bind ∧ mod030_line3 Bind

end MutantClobber

/-- The binding with the net-level map form of Java and TypeScript kills the mutant (AC4, AC7):
it gives every named transition its action, but on the instance `p` the mapping `other ↦ 9`
names no transition and still resets `p/produce` from the action 1 to passthrough (line 4). -/
@[evidence mutant MOD_030]
theorem MOD_030_mutant_clobber_killed :
    MOD_030_mutant_clobber (clobberBind (N := String) (A := Nat)) ∧
      ¬ MOD_030 (clobberBind (N := String) (A := Nat)) := by
  refine ⟨⟨fun I m _ => ⟨_, rfl⟩, fun I m J h => ?_, fun I m J h => ?_⟩, fun h => ?_⟩
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, forall₂_map_self fun d _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · cases h
    refine forall₂_map_self fun d _ k a hn ha => ?_
    show (instLook _ m d.core.name).getD _ = a
    rw [instLook_named m hn, ha]
    rfl
  · have := h.2.2.2 mod030_I0 [("other", .other 9)] _ rfl
    rcases this with _ | ⟨h1, -⟩
    have := h1 (fun k hk => by
      have : k = "produce" := (preS_cancel "p" _ _).1 hk.symm
      subst this
      decide)
    exact absurd this (by decide)

/-! ### Wrong: an unnamed transition takes the action of the first transition of its name -/

section FirstOfName

variable {N A : Type}

/-- The action a wrong resolver gives the definition `d` of the instance `I` under the mapping
`m`: the supplied one when `m` names `d`, otherwise that of the first definition of `I` with `d`'s
name. -/
def firstOfNameAct (I : Instance N A) (m : Overrides A) (d : CDef N A) : Act A :=
  let first := ((I.defs.find? (fun e => e.core.name == d.core.name)).map (·.action)).getD d.action
  (instLook I.pfx m d.core.name).getD first

/-- A wrong binding whose resolver falls back to the first transition of a name (the behaviour
RD-41 recorded): a transition the mapping names takes the supplied action, and one it does not
name takes the action of the first transition of the instance with its name. -/
def firstOfNameBind : InstBindFn N A := fun I m =>
  .ok { I with defs := I.defs.map (fun d => { d with action := firstOfNameAct I m d }) }

end FirstOfName

/-- The example transition `produce` renamed to `n` and carrying the action with id `i`. -/
def mod030_dup (n : String) (i : Nat) : CDef String Nat :=
  { mod030_produce with
    core := { mod030_produce.core with name := n }
    action := .other i }

/-- The example instance `p` with two transitions named `p/x`, carrying the actions 1 and 2, and
a transition `p/y` carrying the action 3, as instantiating a body with two transitions named `x`
gives it, since no instantiation checks transition names (ruling D23). -/
def mod030_Idup : Instance String Nat :=
  { pfx := "p", places := ["p/in", "p/out"],
    defs := [mod030_dup "p/x" 1, mod030_dup "p/x" 2, mod030_dup "p/y" 3],
    port := fun _ => none, chan := fun _ => none, iface := [] }

/-- ✗ A binding that falls back to the first transition of a name violates MOD-030 (line 4) on
an instance that holds two transitions of one name: on the instance `p` the mapping `y ↦ 9` does
not name `x`, yet the second `p/x` ends up with the action 1 of the first `p/x` instead of its own
action 2. -/
@[evidence forbids MOD_030]
theorem MOD_030_forbids_firstOfName : ¬ MOD_030 (firstOfNameBind (N := String) (A := Nat)) := by
  intro h
  have := h.2.2.2 mod030_Idup [("y", .other 9)] _ rfl
  rcases this with _ | ⟨-, _ | ⟨h2, -⟩⟩
  have := h2 (fun k hk => by
    have : k = "x" := (preS_cancel "p" _ _).1 hk.symm
    subst this
    decide)
  exact absurd this (by decide)

/-! ### Open: a key that names no transition -/

/-- ? A key that names no transition is left open (ruling D87 (a)). The Rust and Python binding
(`refBindInst`) and the Java and TypeScript binding (`strictBindInst`) both satisfy MOD-030, and
they differ on the instance `p` bound with `nope ↦ 9`, which names no transition: the first
returns the instance unchanged, the second rejects the call. -/
@[evidence undecided MOD_030]
theorem MOD_030_unknownKey_undecided :
    MOD_030 (refBindInst (N := String) (A := Nat)) ∧
    MOD_030 (strictBindInst (N := String) (A := Nat)) ∧
    (∃ J, refBindInst mod030_I0 [("nope", .other 9)] = .ok J) ∧
    (∃ msg, strictBindInst mod030_I0 [("nope", .other 9)] = .error msg) :=
  ⟨MOD_030_reference, MOD_030_strict, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end Libpetri.Spec
