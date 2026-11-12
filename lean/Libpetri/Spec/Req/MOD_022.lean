import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Reference.ComposeBind
import Libpetri.Spec.Req.MOD_006
import Libpetri.Spec.Req.MOD_011

set_option linter.missingDocs true

/-!
# MOD-022: Type compatibility at compose (`spec/11-modular-composition.md`)

MOD-022 is a behaviour requirement (kind B) scoped to the implementations whose place identity
carries the token type (Java; ruling D36 (a)). It is stated over an abstract composition function
`C : ComposeFn N A` (a builder, an instance, port bindings and channel bindings give the builder
after the call or a rejection with a message, [MOD-020]), the run-time token type `tyOf : N → T`
of a place, and the transition builder's check `Build` ([CORE-020]) through which composition
rebuilds every rewritten transition.

The block says three things about port bindings:

1. a compose call that binds a port to a caller place of another token type than the port's
   place fails;
2. when every bound port is known and bound once, the message of such a failure names a port
   bound to a place of another type, the port place's type and the caller place's type;
3. a call that binds no channel and is well typed composes, when nothing else that [MOD-020]
   rejects is present (the type is no reason to reject it).

The witness is the reference composition `refCompose tyOf Build Mg` (`Reference/ComposeBind.lean`),
which checks the port bindings (bound twice, unknown, of another type) before anything else, as
Java's `composeInternal` does. It satisfies the block for every token-type reader, transition
builder and channel merge. Jointly with the typed port block of [MOD-011], the type a binding is
checked against is the type the port was declared with (`mod022_declared`). Wrong compositions are
killed, one per line: one that accepts a binding of another type, one whose type rejection names
nothing, one that rejects well-typed bindings; and as forbidden models the composition that never
checks the type (what Rust, TypeScript and Python do, outside the scope), one that compares place
names instead of types, one whose type message leaves out the port name, and one that runs the
collision check of [MOD-020] before the type check.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The block -/

requirement MOD_022
  id "MOD-022"
  title "Type Compatibility at Compose"
  kind B
  scope "implementations whose place identity carries the token type (Java)"
  source verbatim "spec/11-modular-composition.md"
  quote "*Where* place identity carries the token type (Java), *if* a compose call binds no port twice and binds a port to a caller place whose token type differs from the token type of the port's place, *then* the compose call *shall* fail."
        "*Where* place identity carries the token type (Java), *if* a compose call binds no port twice, binds only ports of the interface and binds some port to a caller place of another token type, *then* the error message of its failure *shall* name such a port, the token type of the port's place and the token type of the caller place."
        "*Where* place identity carries the token type (Java), *when* a compose call binds no channel, binds no port twice, binds only ports of the interface, binds each port it binds to a caller place of the token type of the port's place, sends no two different port places that one transition consumes from or that one output branch of a transition names to one caller place, and every transition rewritten through the bindings passes the transition builder's checks, the compose call *shall* succeed."
  reading "For every run-time token type tyOf of a place, every transition builder check Build and every composition function C, for every builder b, instance I, port bindings ports (port name, caller place) and channel bindings chans:"
          "if no port is bound twice in ports and some binding (n, X) has a port place q = I.port n with tyOf q ≠ tyOf X, C b I ports chans fails;"
          "if no channel and no port is bound twice, every bound port is a port of I, some binding has a port place of another type than its caller place, and C b I ports chans fails with the message m, then m contains, for some binding (n, X) whose port place q has tyOf q ≠ tyOf X, the name n, the text of tyOf q and the text of tyOf X;"
          "if no port is bound twice, every bound port is a port of I, every binding's port place has its caller place's type, no definition of I has an input or output collision under the bindings, and every definition of I rewritten through the bindings passes Build, then C b I ports [] succeeds."
  assumes "Ruling D36 (a): the type check is scoped to the implementations whose place identity carries the token type, which is Java. Java's compose(instance, map) and compose(instance, bindings) both run composeInternal, which for every port binding first fails on an unknown port and then compares the token type of the renamed port place (Instance.port(name, tokenType)) with the caller place's token type, throwing IllegalArgumentException with a message that names the port, the subnet, both types and the caller place (java/src/main/java/org/libpetri/core/PetriNet.java:688-716), before the collision check, the rewrite and the channel merges. tyOf is the place record's tokenType (typedNaming's second component, Prod.snd), and the text of a type is its Class.getName()."
          "Rust, TypeScript and Python are out of scope: their place identity does not carry the token type, and their compose checks no type. Rust's bind_port::<T> and TypeScript's bindPort<T> take T from the caller place they are given and record the place without its type (rust/libpetri-core/src/compose.rs:97-107, typescript/src/core/compose-bindings.ts:73-79), Rust's compose_internal resolves a port through port_handles and never reads the port's recorded TypeId (rust/libpetri-core/src/petri_net.rs:1034-1069), and Python's compose passes names. The composition that never checks (mod022NeverCheck) violates line 1 on the typed example (MOD_022_forbids_neverCheck). The withdrawn compile-time claim (old items 1 and 2: no binding API relates the port's type to the caller place's type, since ports are bound by name) and the per-language note are the markdown's prose; the typing invariant of CORE-003 is premised on compatible emissions in every language."
          "A composition function is one implementation's compose(instance, bindings) read as a function from the builder, the instance, the port bindings as a list of (port name, caller place) and the channel bindings as a list of (channel name, caller-side definition) to the builder after the call or a rejection with a message (an exception, read as .error msg), as in MOD-020. Java's port bindings are a map, so no port is bound twice through compose(instance, map), and ComposeBindings.bindPort rejects a second binding of a port (java/src/main/java/org/libpetri/core/ComposeBindings.java:66-75); lines 1 to 3 are premised on distinct port names, which is MOD-020's matter (D72 (i)(a), RD-11)."
          "Line 2 is the markdown's 'with a message naming the port, the token type of the port's place and the token type of the caller place': to name is to contain as a substring (MsgNames, as in MOD-006 line 7). It is existential over the offending bindings: Java walks the map in hash order and reports the first offender it meets, so which offender is named when there are several is not stated. It is premised on every bound port being known and bound once, because an unknown port met first in Java's walk reports the unknown-port message instead, and on no channel being bound twice, because Java's binding builder rejects a second binding of a channel while the caller records the bindings (ComposeBindings.bindChannel, java/src/main/java/org/libpetri/core/ComposeBindings.java:98-101), before composeInternal checks any type, with the message Channel '<name>' is already bound, which names no type. It is not premised on the absence of collisions: a composition that runs MOD-020's collision check before the type check fails with the collision message, which names no type (MOD_022_forbids_collisionFirst). Java's message also names the subnet and the caller place; the line asks for the port and the two types only."
          "Line 2 does not say which of the two named types is the port's and which is the caller place's: a message that gives the two types the wrong way round meets it, as the substring reading of MOD-006 line 7 does not fix the order of words either. Substring containment is weak for a short name: the port name in occurs inside the words instance and String of any such message, so the example checks the quoted form port 'in' (MOD_022_nonvacuous), and the composition whose type message leaves out the port name is killed with a port q, whose letter occurs nowhere else in that message (MOD_022_forbids_anonPort)."
          "Line 3 is the acceptance half ('well-typed' bindings are not rejected for their type), stated for calls without channel bindings and premised on everything else MOD-020 rejects being absent: a port bound twice, an unknown port, an input collision or output collision (two different bound ports sent to one caller place, consumed by one transition or named in one AND branch) and a rewritten transition that the transition builder Build rejects. It asks nothing of the ports the call leaves unbound: a call may bind only some of the interface's ports. The ports of the interface are read through the instance's port lookup (I.port), which on every instance that instantiate produces agrees with the interface (MOD-011). Java's builder transition() rejects nothing (java/src/main/java/org/libpetri/core/PetriNet.java:320-329), so the builder b is arbitrary. Java's compose also refuses an instance whose definition's body declares a terminal place (SubnetRewriter.rejectTerminals, java/src/main/java/org/libpetri/core/PetriNet.java:682-683), which instantiate already refuses (EXEC-042 AC6), so no instance that compose is given has one. A call with channel bindings succeeds or fails by MOD-020 and MOD-021 (the channel merge); channel bindings carry no token-type check, since transitions are not typed, and arc-level type compatibility is CORE-003's."
          "The type a binding is checked against is the type of the renamed port place that the instance's port lookup returns. On Java's naming model the rename keeps the token type, so jointly with MOD-011's two blocks this is the type the port was declared with, and a binding of a port to a caller place of another type than its declared type fails (mod022_declared)."
          "AC1 (port(\"in\", String) -> Place<String> composes successfully) is line 3 in Java (MOD_022_nonvacuous: binding the String port in of the example instance r1 to the String place X composes, and r1/work then takes from X); in the other implementations it is MOD-020's acceptance. AC2 (in Java, a binding of the String port in to an Integer place is rejected at compose, through the typed overload and the map overload alike, with a message containing port 'in', String and Integer) is lines 1 and 2 (MOD_022_nonvacuous: the reference rejects that binding with a message containing port 'in', String and Integer). The test derivation is the two ACs."
  signoff "pending"
  statement : ∀ {N A T : Type} [DecidableEq N] [ToString T],
      (N → T) → (Trans N → Option String) → ComposeFn N A → Prop :=
    fun {N A _} _ _ tyOf Build C =>
      (∀ b (I : Instance N A) ports chans, PortsDistinct ports →
        ¬ PortTypesAgree tyOf I ports → ∃ m, C b I ports chans = .error m) ∧
      (∀ b (I : Instance N A) ports chans m, (chans.map (·.1)).Nodup → PortsDistinct ports →
        PortsKnown I ports →
        ¬ PortTypesAgree tyOf I ports → C b I ports chans = .error m →
        ∃ e ∈ ports, ∃ q, I.port e.1 = some q ∧ tyOf q ≠ tyOf e.2 ∧
          MsgNames m e.1 ∧ MsgNames m (toString (tyOf q)) ∧ MsgNames m (toString (tyOf e.2))) ∧
      (∀ b (I : Instance N A) ports, PortsDistinct ports → PortsKnown I ports →
        PortTypesAgree tyOf I ports →
        (∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧
          ¬ OutCollision (bindEntries I ports) d ∧
          Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
        ∃ b', C b I ports [] = .ok b')

/- The pinned readable form of MOD-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_022 : {N A T : Type} →
  [DecidableEq N] → [ToString T] → (N → T) → (Reference.Trans N → Option String) → ComposeFn N A → Prop :=
fun {N A x} x_1 x_2 tyOf Build C =>
  (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)),
      PortsDistinct ports → ¬PortTypesAgree tyOf I ports → ∃ m, C b I ports chans = Except.error m) ∧
    (∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)) (chans : List (String × CDef N A)) (m : String),
        (List.map (fun x => x.1) chans).Nodup →
          PortsDistinct ports →
            PortsKnown I ports →
              ¬PortTypesAgree tyOf I ports →
                C b I ports chans = Except.error m →
                  ∃ e ∈ ports,
                    ∃ q,
                      I.port e.1 = some q ∧
                        tyOf q ≠ tyOf e.2 ∧
                          MsgNames m e.1 ∧ MsgNames m (toString (tyOf q)) ∧ MsgNames m (toString (tyOf e.2))) ∧
      ∀ (b : Bld N A) (I : Instance N A) (ports : List (String × N)),
        PortsDistinct ports →
          PortsKnown I ports →
            PortTypesAgree tyOf I ports →
              (∀ d ∈ I.defs,
                  ¬InCollision (bindEntries I ports) d ∧
                    ¬OutCollision (bindEntries I ports) d ∧ Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
                ∃ b', C b I ports [] = Except.ok b'
-/
#guard_msgs in #print MOD_022

/-! ### The three lines, named (for the mutants) -/

section Lines

variable {N A T : Type} [DecidableEq N] [ToString T]

/-- Line 1 of MOD-022: a binding of another token type fails the call. -/
def mod022_line1 (tyOf : N → T) (C : ComposeFn N A) : Prop :=
  ∀ b (I : Instance N A) ports chans, PortsDistinct ports →
    ¬ PortTypesAgree tyOf I ports → ∃ m, C b I ports chans = .error m

/-- Line 2 of MOD-022: the failure names an offending port and both types. -/
def mod022_line2 (tyOf : N → T) (C : ComposeFn N A) : Prop :=
  ∀ b (I : Instance N A) ports chans m, (chans.map (·.1)).Nodup → PortsDistinct ports →
    PortsKnown I ports →
    ¬ PortTypesAgree tyOf I ports → C b I ports chans = .error m →
    ∃ e ∈ ports, ∃ q, I.port e.1 = some q ∧ tyOf q ≠ tyOf e.2 ∧
      MsgNames m e.1 ∧ MsgNames m (toString (tyOf q)) ∧ MsgNames m (toString (tyOf e.2))

/-- Line 3 of MOD-022: a well-typed call without channel bindings that nothing else rejects
succeeds. -/
def mod022_line3 (tyOf : N → T) (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  ∀ b (I : Instance N A) ports, PortsDistinct ports → PortsKnown I ports →
    PortTypesAgree tyOf I ports →
    (∀ d ∈ I.defs, ¬ InCollision (bindEntries I ports) d ∧
      ¬ OutCollision (bindEntries I ports) d ∧
      Build (rewriteDef (bindEntries I ports) d).toTrans = none) →
    ∃ b', C b I ports [] = .ok b'

/-- MOD-022 is its three lines. -/
theorem mod022_iff (tyOf : N → T) (Build : Trans N → Option String) (C : ComposeFn N A) :
    MOD_022 tyOf Build C ↔
      mod022_line1 tyOf C ∧ mod022_line2 tyOf C ∧ mod022_line3 tyOf Build C :=
  Iff.rfl

end Lines

/-! ### Messages -/

/-- A message `a ++ b` names what `a` names. -/
theorem mod022_msgNames_appL {a b s : String} (h : MsgNames a s) : MsgNames (a ++ b) s := by
  unfold MsgNames at *
  rw [String.toList_append]
  exact h.trans (List.prefix_append _ _).isInfix

/-- A message `a ++ b` names what `b` names. -/
theorem mod022_msgNames_appR {a b s : String} (h : MsgNames b s) : MsgNames (a ++ b) s := by
  unfold MsgNames at *
  rw [String.toList_append]
  exact h.trans (List.suffix_append _ _).isInfix

/-- The reference's type message names the port and both types. -/
theorem mod022_portTypeMsg_names {N T : Type} [ToString N] [ToString T] (pfx n : String) (tq tx : T)
    (X : N) :
    MsgNames (portTypeMsg pfx n tq tx X) n ∧ MsgNames (portTypeMsg pfx n tq tx X) (toString tq) ∧
      MsgNames (portTypeMsg pfx n tq tx X) (toString tx) :=
  ⟨mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL
      (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appR (msgNames_self n)))))))))),
    mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL (mod022_msgNames_appL
      (mod022_msgNames_appR (msgNames_self (toString tq))))))),
    mod022_msgNames_appL (mod022_msgNames_appR (msgNames_self (toString tx)))⟩

/-- The reference's type message names the port in its quoted form: for the port `in` it contains
`port 'in'`, which a message that only says `instance` or `String` does not. -/
theorem mod022_portTypeMsg_port {N T : Type} [ToString N] [ToString T] (pfx n : String) (tq tx : T)
    (X : N) : MsgNames (portTypeMsg pfx n tq tx X) ("port '" ++ n ++ "'") := by
  unfold portTypeMsg
  iterate 8 apply mod022_msgNames_appL
  have e1 : "compose: port '".toList = "compose: ".toList ++ "port '".toList := by decide
  have e2 : "' of instance prefix '".toList = "'".toList ++ " of instance prefix '".toList := by decide
  unfold MsgNames
  simp only [String.toList_append, toString, e1, e2]
  exact ⟨"compose: ".toList, " of instance prefix '".toList, by simp⟩

/-! ### The reference -/

section Reference

variable {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]

omit [DecidableEq N] [ToString N] [ToString T] in
/-- Some binding has a port place of another type exactly when the bindings do not agree in
type. -/
theorem mod022_any_portTyBad_iff {tyOf : N → T} {I : Instance N A} {ports : List (String × N)} :
    ports.any (portTyBad tyOf I) = true ↔ ¬ PortTypesAgree tyOf I ports := by
  rw [List.any_eq_true]
  unfold PortTypesAgree
  constructor
  · rintro ⟨e, he, hb⟩ h
    unfold portTyBad at hb
    cases hq : I.port e.1 with
    | none => rw [hq] at hb; cases hb
    | some q => rw [hq] at hb; exact (of_decide_eq_true hb) (h e he q hq)
  · intro h
    refine Classical.byContradiction fun hn => h fun e he q hq => ?_
    refine Classical.byContradiction fun hne => hn ⟨e, he, ?_⟩
    simp [portTyBad, hq, hne]

/-- Line 1 holds of the reference: a binding of another type rejects. -/
theorem ref022_line1 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    mod022_line1 tyOf (refCompose tyOf Build Mg) :=
  fun _ _ _ _ _ hn => refCompose_portType hn

/-- Line 2 holds of the reference: with every port known and bound once, the rejection is the
type message of the first binding of another type, which names its port and both types. -/
theorem ref022_line2 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    mod022_line2 tyOf (refCompose tyOf Build Mg) := by
  intro b I ports chans m _ h1 h2 hn hm
  cases hf : ports.find? (portTyBad tyOf I) with
  | none =>
    exfalso
    obtain ⟨e, he, hb⟩ := List.any_eq_true.1 (mod022_any_portTyBad_iff.2 hn)
    rw [List.find?_eq_none] at hf
    exact hf e he hb
  | some e =>
    rw [refCompose_portType_msg h1 h2 hf] at hm
    cases hm
    have he := List.mem_of_find?_eq_some hf
    have hb := List.find?_some hf
    unfold portTyBad at hb
    unfold portTyMsgOf
    cases hq : I.port e.1 with
    | none => rw [hq] at hb; cases hb
    | some q =>
      rw [hq] at hb
      simp only
      exact ⟨e, he, q, hq, of_decide_eq_true hb, mod022_portTypeMsg_names I.pfx e.1 (tyOf q) (tyOf e.2) e.2⟩

omit [DecidableEq N] [ToString N] [DecidableEq T] [ToString T] in
/-- No channel binding is well formed. -/
theorem mod022_chansOk_nil (I : Instance N A) : ChansOk I [] := by
  simp [ChansOk]

/-- Line 3 holds of the reference: a well-typed call without channel bindings that nothing else
rejects composes. -/
theorem ref022_line3 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    mod022_line3 tyOf Build (refCompose tyOf Build Mg) :=
  fun _ I _ h1 h2 h3 h5 =>
    refCompose_accepts h1 h2 h3 (mod022_chansOk_nil I) h5 (fun _ _ _ hc => nomatch hc)

end Reference

/-- The reference composition satisfies MOD-022 for every token-type reader, transition builder
and channel merge `Mg`: the block's lines never depend on how a channel binding is merged. -/
theorem mod022_reference_anyMerge {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    MOD_022 tyOf Build (refCompose tyOf Build Mg) :=
  ⟨ref022_line1 tyOf Build Mg, ref022_line2 tyOf Build Mg, ref022_line3 tyOf Build Mg⟩

/-- A channel merge that keeps the caller-side definition. MOD-022 does not depend on the merge
(`mod022_reference_anyMerge`); the holds evidence fixes this one. -/
def mod022Merge {N A : Type} : CDef N A → CDef N A → Except String (CDef N A) :=
  fun c _ => .ok c

/-- ✓ The reference composition satisfies MOD-022 for every token-type reader and transition
builder: it checks every port binding's type before anything else, rejects a binding of another
type with a message that names the port and both types (Java: port `in` has type String, caller
place `X` has type Integer), and composes a well-typed call that nothing else rejects. -/
@[evidence holds MOD_022]
theorem MOD_022_reference {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T]
    [ToString T] (tyOf : N → T) (Build : Trans N → Option String) :
    MOD_022 tyOf Build (refCompose (A := A) tyOf Build mod022Merge) :=
  mod022_reference_anyMerge tyOf Build mod022Merge

/-! ### Joint consequence with MOD-011 -/

/-- **A binding is checked against the declared type.** On Java's naming model (a place is a name
and a token type, and the prefix keeps the type), in every model of MOD-011 and of MOD-022, binding
a port of an instance to a caller place whose type differs from the type the port was declared
with fails: a port `in` declared on a `String` place, bound to an `Integer` place, is rejected. -/
theorem mod022_declared {A Ty : Type} [DecidableEq Ty] [ToString Ty]
    {Inst : InstFn (String × Ty) A} {Build : Trans (String × Ty) → Option String}
    {C : ComposeFn (String × Ty) A} (h11 : MOD_011 (typedNaming Ty) Inst)
    (h22 : MOD_022 Prod.snd Build C) {S : SubnetDef (String × Ty) A} {p : String}
    {I : Instance (String × Ty) A} (hI : Inst S p = .ok I) (hnd : (S.ports.map (·.name)).Nodup)
    {q : Port (String × Ty)} (hq : q ∈ S.ports) {X : String × Ty} (hX : X.2 ≠ q.place.2)
    (b : Bld (String × Ty) A) (chans : List (String × CDef (String × Ty) A)) :
    ∃ m, C b I [(q.name, X)] chans = .error m := by
  have hp : I.port q.name = some (preS p q.place.1, q.place.2) := h11.1 S p I hI hnd q hq
  refine h22.1 b I [(q.name, X)] chans (by simp [PortsDistinct]) fun h => ?_
  exact hX (h (q.name, X) (List.mem_cons_self ..) _ hp).symm

/-! ### The example -/

/-- A token type for the examples: `String` and `Integer`. -/
inductive Mod022Ty where
  /-- The type `String`. -/
  | str
  /-- The type `Integer`. -/
  | int
  deriving DecidableEq, Repr

/-- The text of an example type, as a message writes it. -/
instance : ToString Mod022Ty := ⟨fun | .str => "String" | .int => "Integer"⟩

/-- The example transition `work`: it takes one token from the `String` place `in` and puts one
into the `String` place `out`. -/
def mod022_exDef : CDef (String × Mod022Ty) Unit :=
  { core := ⟨"work", [⟨("in", .str), .one⟩], [], [], []⟩, out := some (.place ("out", .str)),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The example subnet `Worker` (AC1, AC2): the `String` places `in` and `out`, the transition
`work`, the input port `in` and the output port `out`. -/
def mod022_exS : SubnetDef (String × Mod022Ty) Unit :=
  { name := "Worker", places := [("in", .str), ("out", .str)], defs := [mod022_exDef],
    ports := [⟨"in", .input, ("in", .str)⟩, ⟨"out", .output, ("out", .str)⟩], chans := [] }

/-- The example instance: `Worker` under the prefix `r1`. -/
def mod022_exI : Instance (String × Mod022Ty) Unit :=
  renamedInstance (typedNaming Mod022Ty) mod022_exS "r1"

/-- The reference instantiates `Worker` under `r1` as the example instance. -/
theorem mod022_exI_inst : refInst (typedNaming Mod022Ty) mod022_exS "r1" = .ok mod022_exI :=
  refInst_valid (typedNaming Mod022Ty) mod022_exS (by decide) rfl

/-- The well-typed binding of the example: port `in` to the `String` place `X`. -/
def mod022_good : List (String × (String × Mod022Ty)) := [("in", ("X", .str))]

/-- The wrong-typed binding of the example: port `in` to the `Integer` place `X`. -/
def mod022_bad : List (String × (String × Mod022Ty)) := [("in", ("X", .int))]

/-- An `Except` value that is `ok` on its option view is `ok`. -/
theorem mod022_ok_of_isSome {ε α : Type} {x : Except ε α} (h : x.toOption.isSome = true) :
    ∃ a, x = .ok a := by
  cases x with
  | ok a => exact ⟨a, rfl⟩
  | error _ => cases h

/-- The reference composes the well-typed binding of the example, and the composed transition
`r1/work` takes from `X` and puts into `r1/out`. -/
theorem mod022_ex_good :
    ∃ b', refCompose Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_good [] = .ok b' ∧
      b'.defs.map (fun d => (d.core.name, d.namedPlaces)) =
        [("r1/work", [("X", .str), ("r1/out", .str)])] := by
  have hs : ((refCompose Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_good
      []).toOption.map fun b => b.defs.map fun d => (d.core.name, d.namedPlaces)) =
      some [("r1/work", [("X", .str), ("r1/out", .str)])] := by decide
  obtain ⟨b', hb⟩ := mod022_ok_of_isSome (x := refCompose Prod.snd refBuild mod022Merge Bld.empty
    mod022_exI mod022_good []) (by rw [← Option.isSome_map (f := fun b : Bld (String × Mod022Ty) Unit =>
      b.defs.map fun d => (d.core.name, d.namedPlaces)), hs]; rfl)
  rw [hb] at hs
  exact ⟨b', hb, Option.some.inj hs⟩

/-- What the reference's success on the well-typed binding gives: the binding is distinct, known
and well typed, and the rewritten `work` neither collides nor fails the transition builder. -/
theorem mod022_good_premises :
    PortsDistinct mod022_good ∧ PortsKnown mod022_exI mod022_good ∧
      PortTypesAgree Prod.snd mod022_exI mod022_good ∧
      (∀ d ∈ mod022_exI.defs, ¬ InCollision (bindEntries mod022_exI mod022_good) d ∧
        ¬ OutCollision (bindEntries mod022_exI mod022_good) d ∧
        refBuild (rewriteDef (bindEntries mod022_exI mod022_good) d).toTrans = none) := by
  obtain ⟨b', hb, -⟩ := mod022_ex_good
  obtain ⟨h1, h2, h3, -, h5, -⟩ := refCompose_ok_iff.1 hb
  exact ⟨h1, h2, h3, h5⟩

/-- The wrong-typed binding of the example is not well typed. -/
theorem mod022_bad_any : mod022_bad.any (portTyBad Prod.snd mod022_exI) = true := by decide

/-- The well-typed binding of the example has no binding of another type. -/
theorem mod022_good_any : mod022_good.any (portTyBad Prod.snd mod022_exI) = false := by decide

/-- The reference rejects the wrong-typed binding of the example with its type message: port `in`
of `r1` has type `String`, the caller place `X` has type `Integer`. -/
theorem mod022_bad_msg :
    refCompose Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_bad [] =
      .error (portTypeMsg "r1" "in" Mod022Ty.str Mod022Ty.int ("X", Mod022Ty.int)) := by
  have h1 : PortsDistinct mod022_bad := by simp [PortsDistinct, mod022_bad]
  have h2 : PortsKnown mod022_exI mod022_bad := by
    intro e he; simp only [mod022_bad, List.mem_singleton] at he; subst he; decide
  have hf : mod022_bad.find? (portTyBad Prod.snd mod022_exI) = some ("in", ("X", .int)) := by decide
  rw [refCompose_portType_msg h1 h2 hf]
  have hp : mod022_exI.port "in" = some ("r1/in", .str) := by decide
  simp only [portTyMsgOf, hp]
  rfl

/-- ✓ Every line of MOD-022 is exercised by the reference: `Worker` instantiated under `r1`, its
`String` port `in` bound to the `String` place `X` composes, and `r1/work` then takes from `X`
(AC1); bound to an `Integer` place `X` instead, the call is rejected with a message that contains
`port 'in'`, the type `String` and the type `Integer` (AC2). -/
@[evidence nonvacuous MOD_022]
theorem MOD_022_nonvacuous :
    refInst (typedNaming Mod022Ty) mod022_exS "r1" = .ok mod022_exI ∧
      (∃ b', refCompose Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_good [] = .ok b' ∧
        b'.defs.map (fun d => (d.core.name, d.namedPlaces)) =
          [("r1/work", [("X", .str), ("r1/out", .str)])]) ∧
      ∃ m, refCompose Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_bad [] = .error m ∧
        MsgNames m "port 'in'" ∧ MsgNames m "String" ∧ MsgNames m "Integer" := by
  obtain ⟨-, hS, hI⟩ := mod022_portTypeMsg_names (N := String × Mod022Ty) "r1" "in" Mod022Ty.str
    Mod022Ty.int ("X", .int)
  exact ⟨mod022_exI_inst, mod022_ex_good, _, mod022_bad_msg,
    mod022_portTypeMsg_port "r1" "in" Mod022Ty.str Mod022Ty.int ("X", Mod022Ty.int), hS, hI⟩

/-! ### Wrong compositions -/

section Wrong

variable {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]

/-- A composition that accepts a call with a binding of another type, leaving the builder as it
was, and otherwise is the reference. -/
def mod022AcceptMismatch (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  if ports.any (portTyBad tyOf I) then .ok b else refCompose tyOf Build Mg b I ports chans

/-- A composition that rejects a binding of another type with the bare message `rejected`, and
otherwise is the reference. -/
def mod022VagueMsg (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  if ports.any (portTyBad tyOf I) then .error "rejected" else refCompose tyOf Build Mg b I ports chans

/-- A composition that is the reference on a call with a binding of another type and rejects
every well-typed call. -/
def mod022RejectWellTyped (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  if ports.any (portTyBad tyOf I) then refCompose tyOf Build Mg b I ports chans else .error "rejected"

/-- The composition that never checks a token type: the reference over a type reader that gives
every place the same type (what Rust, TypeScript and Python do, outside the block's scope). -/
def mod022NeverCheck (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A :=
  refCompose (fun _ : N => ()) Build Mg

/-- Without a binding of another type, each wrong composition above but the last is the
reference, so it meets line 3. -/
theorem mod022_line3_of_agree {tyOf : N → T} {Build : Trans N → Option String}
    {Mg : CDef N A → CDef N A → Except String (CDef N A)} {C : ComposeFn N A}
    (hC : ∀ b I ports chans, PortTypesAgree tyOf I ports →
      C b I ports chans = refCompose tyOf Build Mg b I ports chans) :
    mod022_line3 tyOf Build C := fun b I ports h1 h2 h3 h5 => by
  rw [hC b I ports [] h3]
  exact ref022_line3 tyOf Build Mg b I ports h1 h2 h3 h5

end Wrong

/-- A composition (places by name and type) that rejects a binding whose caller place's name
differs from its port place's name, comparing names where it should compare types, and otherwise
is the reference. -/
def mod022CompareNames {Ty : Type} [DecidableEq Ty] [ToString Ty]
    (Build : Trans (String × Ty) → Option String)
    (Mg : CDef (String × Ty) Unit → CDef (String × Ty) Unit → Except String (CDef (String × Ty) Unit)) :
    ComposeFn (String × Ty) Unit := fun b I ports chans =>
  if ports.any (fun e => match I.port e.1 with | some q => q.1 != e.2.1 | none => false) then
    .error "rejected"
  else refCompose Prod.snd Build Mg b I ports chans

/-- ✗ The composition that never checks a token type violates MOD-022 (line 1): it composes the
`String` port `in` of the example bound to an `Integer` place, which Java rejects. -/
@[evidence forbids MOD_022]
theorem MOD_022_forbids_neverCheck :
    ¬ MOD_022 Prod.snd refBuild (mod022NeverCheck (N := String × Mod022Ty) (A := Unit) refBuild mod022Merge) := by
  intro h
  have hn : ¬ PortTypesAgree Prod.snd mod022_exI mod022_bad := mod022_any_portTyBad_iff.1 mod022_bad_any
  obtain ⟨m, hm⟩ := h.1 Bld.empty mod022_exI mod022_bad [] (by simp [PortsDistinct, mod022_bad]) hn
  have hs : (mod022NeverCheck refBuild mod022Merge Bld.empty mod022_exI mod022_bad
      []).toOption.isSome = true := by decide
  rw [hm] at hs
  cases hs

/-- ✗ A composition that compares place names instead of types violates MOD-022 (line 3): it
rejects the well-typed binding of the example's `String` port `in` to the `String` place `X`,
because `X` is not named `r1/in`. -/
@[evidence forbids MOD_022]
theorem MOD_022_forbids_compareNames :
    ¬ MOD_022 Prod.snd refBuild (mod022CompareNames (Ty := Mod022Ty) refBuild mod022Merge) := by
  intro h
  obtain ⟨h1, h2, h3, h5⟩ := mod022_good_premises
  obtain ⟨b', hb⟩ := h.2.2 Bld.empty mod022_exI mod022_good h1 h2 h3 h5
  have hs : (mod022CompareNames refBuild mod022Merge Bld.empty mod022_exI mod022_good
      []).toOption.isSome = false := by decide
  rw [hb] at hs
  cases hs

/-! ### Two realistic slips of Java's check -/

section Slips

variable {N A T : Type} [DecidableEq N] [ToString N] [DecidableEq T] [ToString T]

/-- A type message that leaves out the port name (and the caller place). -/
def mod022AnonMsg (pfx : String) (tq tx : T) : String :=
  "compose: a port of instance prefix '" ++ pfx ++ "' has token type " ++ toString tq ++
    " but its caller place has token type " ++ toString tx ++ " (MOD-022)"

/-- The port checks in Java's order (bound twice, unknown, of another type), with the type message
that leaves out the port name. -/
def mod022AnonPortCheck (tyOf : N → T) (I : Instance N A) (ports : List (String × N)) :
    Option String :=
  match bindDup (ports.map (·.1)) with
  | some n => some (Libpetri.Reference.dupPortMsg n)
  | none =>
    match ports.find? (fun e => (I.port e.1).isNone) with
    | some e => some (Libpetri.Reference.unknownPortMsg I.pfx e.1)
    | none =>
      match ports.find? (portTyBad tyOf I) with
      | some e =>
        match I.port e.1 with
        | some q => some (mod022AnonMsg I.pfx (tyOf q) (tyOf e.2))
        | none => some (Libpetri.Reference.unknownPortMsg I.pfx e.1)
      | none => none

/-- A composition whose type message leaves out the port name, and otherwise is the reference. -/
def mod022AnonCompose (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  match mod022AnonPortCheck tyOf I ports with
  | some m => .error m
  | none => refCompose tyOf Build Mg b I ports chans

omit [DecidableEq N] in
/-- The anonymous port checks pass exactly when the reference's port checks pass. -/
theorem mod022AnonPortCheck_none_iff {tyOf : N → T} {I : Instance N A}
    {ports : List (String × N)} :
    mod022AnonPortCheck tyOf I ports = none ↔ portCheck tyOf I ports = none := by
  unfold mod022AnonPortCheck portCheck
  cases bindDup (ports.map (·.1)) <;> simp only
  cases ports.find? (fun e => (I.port e.1).isNone) <;> simp only
  cases ports.find? (portTyBad tyOf I) with
  | none => simp
  | some e => simp only [reduceCtorEq, iff_false]; split <;> simp

/-- The composition with the anonymous type message meets lines 1 and 3, so only line 2 can
reject it. -/
theorem mod022AnonCompose_lines13 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    mod022_line1 tyOf (mod022AnonCompose tyOf Build Mg) ∧
      mod022_line3 tyOf Build (mod022AnonCompose tyOf Build Mg) := by
  refine ⟨fun b I ports chans _ hn => ?_, fun b I ports h1 h2 h3 h5 => ?_⟩
  · cases hs : mod022AnonPortCheck tyOf I ports with
    | some m => exact ⟨m, by simp [mod022AnonCompose, hs]⟩
    | none =>
      exfalso
      exact hn (portCheck_eq_none_iff.1 (mod022AnonPortCheck_none_iff.1 hs)).2.2
  · have hs : mod022AnonPortCheck tyOf I ports = none :=
      mod022AnonPortCheck_none_iff.2 (portCheck_eq_none_iff.2 ⟨h1, h2, h3⟩)
    obtain ⟨b', hb'⟩ := ref022_line3 tyOf Build Mg b I ports h1 h2 h3 h5
    exact ⟨b', by simp [mod022AnonCompose, hs, hb']⟩

/-- A composition that runs the collision pass of [MOD-020] over every definition first (the
transition builder not yet asked), and then is the reference. -/
def mod022CollFirst (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) : ComposeFn N A := fun b I ports chans =>
  match I.defs.mapM (bindStep (fun _ => none) I.pfx (bindEntries I ports)) with
  | .error m => .error m
  | .ok _ => refCompose tyOf Build Mg b I ports chans

/-- The composition that checks collisions first meets lines 1 and 3, so only line 2 can reject
it. -/
theorem mod022CollFirst_lines13 (tyOf : N → T) (Build : Trans N → Option String)
    (Mg : CDef N A → CDef N A → Except String (CDef N A)) :
    mod022_line1 tyOf (mod022CollFirst tyOf Build Mg) ∧
      mod022_line3 tyOf Build (mod022CollFirst tyOf Build Mg) := by
  refine ⟨fun b I ports chans _ hn => ?_, fun b I ports h1 h2 h3 h5 => ?_⟩
  · unfold mod022CollFirst
    cases I.defs.mapM (bindStep (fun _ => none) I.pfx (bindEntries I ports)) with
    | error m => exact ⟨m, rfl⟩
    | ok _ => exact refCompose_portType hn
  · have hc : I.defs.mapM (bindStep (fun _ => none) I.pfx (bindEntries I ports)) =
        .ok (I.defs.map (rewriteDef (bindEntries I ports))) :=
      mapM_bindStep_ok_iff.2 ⟨fun d hd => ⟨(h5 d hd).1, (h5 d hd).2.1, rfl⟩, rfl⟩
    obtain ⟨b', hb'⟩ := ref022_line3 tyOf Build Mg b I ports h1 h2 h3 h5
    exact ⟨b', by simp only [mod022CollFirst, hc, hb']⟩

end Slips

/-- `Worker` with its input port called `q` (on the place `in`). -/
def mod022_anonS : SubnetDef (String × Mod022Ty) Unit :=
  { mod022_exS with ports := [⟨"q", .input, ("in", .str)⟩, ⟨"out", .output, ("out", .str)⟩] }

/-- The instance `r1` of `Worker` with the port `q`. -/
def mod022_anonI : Instance (String × Mod022Ty) Unit :=
  renamedInstance (typedNaming Mod022Ty) mod022_anonS "r1"

/-- Port `q` bound to the `Integer` place `X`. -/
def mod022_anonBad : List (String × (String × Mod022Ty)) := [("q", ("X", .int))]

/-- The anonymous composition rejects port `q` bound to `X` with the message that leaves out the
port name. -/
theorem mod022_anon_q_msg :
    mod022AnonCompose Prod.snd refBuild mod022Merge Bld.empty mod022_anonI mod022_anonBad [] =
      .error (mod022AnonMsg (T := Mod022Ty) "r1" .str .int) := by
  have hd : bindDup (mod022_anonBad.map (·.1)) = none := by decide
  have hk : mod022_anonBad.find? (fun e => (mod022_anonI.port e.1).isNone) = none := by decide
  have hf : mod022_anonBad.find? (portTyBad Prod.snd mod022_anonI) = some ("q", ("X", .int)) := by
    decide
  have hp : mod022_anonI.port "q" = some ("r1/in", .str) := by decide
  have hpfx : mod022_anonI.pfx = "r1" := rfl
  simp only [mod022AnonCompose, mod022AnonPortCheck, hd, hk, hf, hp, hpfx]

/-- The message that leaves out the port name has no letter `q`. -/
theorem mod022_anon_no_q : 'q' ∉ (mod022AnonMsg (T := Mod022Ty) "r1" .str .int).toList := by
  unfold mod022AnonMsg
  simp only [String.toList_append, List.mem_append, not_or]
  decide

/-- ✗ A composition whose type message leaves out the port name violates MOD-022 (line 2). It
checks the bindings in Java's order and rejects every binding of another type, but when the
`String` port `q` of `Worker` under `r1` is bound to the `Integer` place `X`, its message says
only that "a port" of `r1` has type `String` and "its caller place" has type `Integer`: the letter
`q` occurs nowhere in it, so the user cannot tell which binding is wrong. -/
@[evidence forbids MOD_022]
theorem MOD_022_forbids_anonPort :
    ¬ MOD_022 Prod.snd refBuild
      (mod022AnonCompose (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) := by
  intro h
  have hn : ¬ PortTypesAgree Prod.snd mod022_anonI mod022_anonBad :=
    mod022_any_portTyBad_iff.1 (by decide)
  have h2 : PortsKnown mod022_anonI mod022_anonBad := by
    intro e he; simp only [mod022_anonBad, List.mem_singleton] at he; subst he; decide
  obtain ⟨e, he, -, -, -, hn1, -, -⟩ := h.2.1 Bld.empty mod022_anonI mod022_anonBad [] _ List.nodup_nil
    (by simp [PortsDistinct, mod022_anonBad]) h2 hn mod022_anon_q_msg
  simp only [mod022_anonBad, List.mem_singleton] at he
  subst he
  exact not_msgNames (ch := 'q') (by decide) mod022_anon_no_q hn1

/-- The places of the collision example, with printed names that are plain text: the instance's
`r1/pa` (`String`), `r1/pb` (`Integer`), `r1/out` (`String`), and the caller's `X` (`String`). -/
inductive Mod022CP where
  /-- The instance place `r1/pa`. -/
  | pa
  /-- The instance place `r1/pb`. -/
  | pb
  /-- The instance place `r1/out`. -/
  | out
  /-- The caller place `X`. -/
  | X
  deriving DecidableEq, Repr

/-- The printed name of a place of the collision example. -/
instance : ToString Mod022CP :=
  ⟨fun | .pa => "r1/pa" | .pb => "r1/pb" | .out => "r1/out" | .X => "X"⟩

/-- The token type of each place of the collision example. -/
def mod022CpTy : Mod022CP → Mod022Ty
  | .pa => .str | .pb => .int | .out => .str | .X => .str

/-- `r1/t` takes one token from `r1/pa` and one from `r1/pb` and puts one into `r1/out`. -/
def mod022CpDef : CDef Mod022CP Unit :=
  { core := ⟨"r1/t", [⟨.pa, .one⟩, ⟨.pb, .one⟩], [], [], []⟩, out := some (.place .out),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The instance `r1` of the collision example: input port `a` on `r1/pa` (`String`) and input
port `b` on `r1/pb` (`Integer`). -/
def mod022CpI : Instance Mod022CP Unit :=
  { pfx := "r1", places := [.pa, .pb, .out], defs := [mod022CpDef],
    port := fun | "a" => some .pa | "b" => some .pb | _ => none,
    chan := fun _ => none,
    iface := [⟨"a", .input, .pa⟩, ⟨"b", .input, .pb⟩] }

/-- Both ports bound to the `String` place `X`: `b` is bound to a place of another type, and both
port places feed `r1/t`, so the binding is also an input collision. -/
def mod022CpPorts : List (String × Mod022CP) := [("a", .X), ("b", .X)]

/-- The first input collision of `r1/t` under the bindings is `a` and `b`, both sent to `X`. -/
theorem mod022_cp_inPairs :
    (inPairs (bindEntries mod022CpI mod022CpPorts) mod022CpDef).head? =
      some (⟨.pa, "a", .X⟩, ⟨.pb, "b", .X⟩) := by decide

/-- The composition that checks collisions first rejects the example with the input collision
message. -/
theorem mod022_collFirst_cp :
    mod022CollFirst mod022CpTy refBuild mod022Merge Bld.empty mod022CpI mod022CpPorts [] =
      .error (inCollMsg "r1" ⟨Mod022CP.pa, "a", Mod022CP.X⟩ ⟨Mod022CP.pb, "b", Mod022CP.X⟩ "r1/t") := by
  have h : bindStep (fun _ => none) "r1" (bindEntries mod022CpI mod022CpPorts) mod022CpDef =
      .error (inCollMsg "r1" ⟨Mod022CP.pa, "a", Mod022CP.X⟩ ⟨Mod022CP.pb, "b", Mod022CP.X⟩ "r1/t") :=
    bindStep_inColl mod022_cp_inPairs
  have hd : mod022CpI.defs = [mod022CpDef] := rfl
  have hp : mod022CpI.pfx = "r1" := rfl
  simp only [mod022CollFirst, hd, hp, List.mapM_cons, h]
  rfl

/-- The input collision message of the example has no capital `I`, so it names no `Integer`. -/
theorem mod022_cp_no_I :
    'I' ∉ (inCollMsg "r1" ⟨Mod022CP.pa, "a", Mod022CP.X⟩ ⟨Mod022CP.pb, "b", Mod022CP.X⟩
      "r1/t").toList := by
  simp only [inCollMsg, String.toList_append, List.mem_append, not_or]
  decide

/-- ✗ A composition that runs the collision check of MOD-020 before the type check violates
MOD-022 (line 2). Ports `a` (`String`) and `b` (`Integer`) both feed the transition `r1/t`, and
the call binds both to the `String` place `X`: port `b` has the wrong type, but the call fails
with the message about two ports sent to one place, which never says `Integer`. -/
@[evidence forbids MOD_022]
theorem MOD_022_forbids_collisionFirst :
    ¬ MOD_022 mod022CpTy refBuild
      (mod022CollFirst (N := Mod022CP) (A := Unit) mod022CpTy refBuild mod022Merge) := by
  intro h
  have hn : ¬ PortTypesAgree mod022CpTy mod022CpI mod022CpPorts :=
    mod022_any_portTyBad_iff.1 (by decide)
  have h1 : PortsDistinct mod022CpPorts := by simp [PortsDistinct, mod022CpPorts]
  have h2 : PortsKnown mod022CpI mod022CpPorts := by
    intro e he
    simp only [mod022CpPorts, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide
  obtain ⟨e, he, q, hq, hne, -, hT, -⟩ :=
    h.2.1 Bld.empty mod022CpI mod022CpPorts [] _ List.nodup_nil h1 h2 hn mod022_collFirst_cp
  simp only [mod022CpPorts, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · have : q = .pa := Option.some.inj hq.symm
    subst this
    exact hne rfl
  · have : q = .pb := Option.some.inj hq.symm
    subst this
    exact not_msgNames (ch := 'I') (by decide) mod022_cp_no_I hT

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-022 without line 1, so a binding of another type may compose. -/
def MOD_022_mutant_noReject {N A T : Type} [DecidableEq N] [ToString T] (tyOf : N → T)
    (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  mod022_line2 tyOf C ∧ mod022_line3 tyOf Build C

/-- The composition that accepts a binding of another type kills the mutant: it never fails on
such a binding, so line 2 asks nothing of it, and it is the reference on well-typed calls (line
3); but it composes the example's `String` port `in` bound to an `Integer` place (line 1). -/
@[evidence mutant MOD_022]
theorem MOD_022_mutant_noReject_killed :
    MOD_022_mutant_noReject Prod.snd refBuild
        (mod022AcceptMismatch (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) ∧
      ¬ MOD_022 Prod.snd refBuild
        (mod022AcceptMismatch (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) := by
  refine ⟨⟨fun b I ports chans m _ _ _ hn hm => ?_, mod022_line3_of_agree (Mg := mod022Merge) fun b I ports chans h3 => ?_⟩,
    fun h => ?_⟩
  · rw [mod022AcceptMismatch, if_pos (mod022_any_portTyBad_iff.2 hn)] at hm
    cases hm
  · have : ports.any (portTyBad Prod.snd I) = false := by
      cases hh : ports.any (portTyBad Prod.snd I)
      · rfl
      · exact absurd h3 (mod022_any_portTyBad_iff.1 hh)
    rw [mod022AcceptMismatch, this, if_neg (by decide)]
  · have hn : ¬ PortTypesAgree Prod.snd mod022_exI mod022_bad := mod022_any_portTyBad_iff.1 mod022_bad_any
    obtain ⟨m, hm⟩ := h.1 Bld.empty mod022_exI mod022_bad [] (by simp [PortsDistinct, mod022_bad]) hn
    rw [mod022AcceptMismatch, if_pos mod022_bad_any] at hm
    cases hm

/-- Mutant reading: MOD-022 without line 2, so a type rejection may name nothing. -/
def MOD_022_mutant_noMsg {N A T : Type} [DecidableEq N] [ToString T] (tyOf : N → T)
    (Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  mod022_line1 tyOf C ∧ mod022_line3 tyOf Build C

/-- The composition whose type rejection says only `rejected` kills the mutant: it rejects every
binding of another type (line 1) and is the reference on well-typed calls (line 3); but its
message for the example's `String` port `in` bound to an `Integer` place does not name `in`
(line 2). -/
@[evidence mutant MOD_022]
theorem MOD_022_mutant_noMsg_killed :
    MOD_022_mutant_noMsg Prod.snd refBuild
        (mod022VagueMsg (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) ∧
      ¬ MOD_022 Prod.snd refBuild
        (mod022VagueMsg (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) := by
  refine ⟨⟨fun b I ports chans _ hn => ?_, mod022_line3_of_agree (Mg := mod022Merge) fun b I ports chans h3 => ?_⟩,
    fun h => ?_⟩
  · rw [mod022VagueMsg, if_pos (mod022_any_portTyBad_iff.2 hn)]
    exact ⟨_, rfl⟩
  · have : ports.any (portTyBad Prod.snd I) = false := by
      cases hh : ports.any (portTyBad Prod.snd I)
      · rfl
      · exact absurd h3 (mod022_any_portTyBad_iff.1 hh)
    rw [mod022VagueMsg, this, if_neg (by decide)]
  · have hn : ¬ PortTypesAgree Prod.snd mod022_exI mod022_bad := mod022_any_portTyBad_iff.1 mod022_bad_any
    have h2 : PortsKnown mod022_exI mod022_bad := by
      intro e he; simp only [mod022_bad, List.mem_singleton] at he; subst he; decide
    have hm : mod022VagueMsg Prod.snd refBuild mod022Merge Bld.empty mod022_exI mod022_bad [] =
        .error "rejected" := by
      rw [mod022VagueMsg, if_pos mod022_bad_any]
    obtain ⟨e, he, -, -, -, hn1, -, -⟩ := h.2.1 Bld.empty mod022_exI mod022_bad [] _ List.nodup_nil (by simp [PortsDistinct, mod022_bad]) h2
      hn hm
    simp only [mod022_bad, List.mem_singleton] at he
    subst he
    exact not_msgNames (ch := 'i') (by decide) (by decide) hn1

/-- Mutant reading: MOD-022 without line 3, so a well-typed call may be rejected. -/
def MOD_022_mutant_noAccept {N A T : Type} [DecidableEq N] [ToString T] (tyOf : N → T)
    (_Build : Trans N → Option String) (C : ComposeFn N A) : Prop :=
  mod022_line1 tyOf C ∧ mod022_line2 tyOf C

/-- The composition that rejects every well-typed call kills the mutant: on a binding of another
type it is the reference (lines 1 and 2); but it rejects the example's `String` port `in` bound
to the `String` place `X`, which nothing else rejects (line 3). -/
@[evidence mutant MOD_022]
theorem MOD_022_mutant_noAccept_killed :
    MOD_022_mutant_noAccept Prod.snd refBuild
        (mod022RejectWellTyped (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) ∧
      ¬ MOD_022 Prod.snd refBuild
        (mod022RejectWellTyped (N := String × Mod022Ty) (A := Unit) Prod.snd refBuild mod022Merge) := by
  refine ⟨⟨fun b I ports chans h1 hn => ?_, fun b I ports chans m hu h1 h2 hn hm => ?_⟩, fun h => ?_⟩
  · rw [mod022RejectWellTyped, if_pos (mod022_any_portTyBad_iff.2 hn)]
    exact ref022_line1 Prod.snd refBuild mod022Merge b I ports chans h1 hn
  · rw [mod022RejectWellTyped, if_pos (mod022_any_portTyBad_iff.2 hn)] at hm
    exact ref022_line2 Prod.snd refBuild mod022Merge b I ports chans m hu h1 h2 hn hm
  · obtain ⟨h1, h2, h3, h5⟩ := mod022_good_premises
    obtain ⟨b', hb⟩ := h.2.2 Bld.empty mod022_exI mod022_good h1 h2 h3 h5
    rw [mod022RejectWellTyped, mod022_good_any] at hb
    cases hb

end Libpetri.Spec
