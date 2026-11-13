import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Spec.Req.MOD_010
import Libpetri.Spec.Text.MOD_011

set_option linter.missingDocs true

/-!
# MOD-011: Instance handles (`spec/11-modular-composition.md`)

MOD-011 is a pure-function requirement (kind F) in two blocks.

The first block, `MOD_011`, binds every implementation. It is stated over an abstract
instantiation function `Inst : InstFn N A` and a naming model `Nm : Naming N`, like [MOD-010],
and says what the handles of a successful instantiation under prefix `p` answer: the port
lookup gives, for a port that exposes the body place `x`, the place `x` renamed under `p`; the
channel lookup gives, for a channel that exposes the body transition `t`, the name `p/t`; a name
the interface does not declare gives nothing (an error); and the prefix is `p`.

The second block, `MOD_011_typed`, binds the implementations that keep a run-time token type
for each port (Java, Rust; ruling D36 (a)). It is stated over a typed port lookup
`PortAs : Instance N A → String → T → Except String N` and the run-time token type `tyOf : N → T`
a place handle carries, and says that the typed lookup is the port lookup followed by a type
check: it returns the port's renamed place when the requested type is the type that place
carries, and fails when the type differs or the port name is unknown. Both runtimes are read at
the typed naming model `typedNaming`, a place handle being its name and its token type: for Java
the place record, for Rust the renamed name with the `TypeId` its port captured. There the type
the handle carries is the type the port was declared with (`mod011_typed_declared`), which is
how the spec words the check; a type read off the place's name alone is not what Rust checks
(`MOD_011_typed_forbids_byPlaceName`).

The witnesses are the reference instantiation `refInst Nm` ([MOD-010]) and the reference typed
lookup `refPortAs tyOf` (below). Jointly with [MOD-010] the handles name nodes of the renamed
body (`mod011_handles_resolve`), and on the typed naming model the typed lookup accepts exactly the
type the port was declared with (`mod011_typed_declared`). Wrong handles are killed, one per
line: a port lookup that returns the unrenamed place, a channel lookup that returns the
unrenamed transition name, lookups that invent a place or transition for an unknown name, an
instance that reports the definition's name as its prefix, and typed lookups that reject
everything, skip the type check or invent a place for an unknown name.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The handle block -/

requirement MOD_011
  id "MOD-011"
  title "Instance Handle Map (typed port + channel handles)"
  kind F
  scope "every module instance (Java, TypeScript, Rust, Python)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_011.s1, MOD_011.s2, MOD_011.s3, MOD_011.s4, MOD_011.s5
  reading "For every naming model Nm (how a prefix renames a place) and every instantiation function Inst, whenever Inst returns an instance I for the subnet definition S under the prefix p:"
          "if the port names of S are distinct, then for every port q of S, I.port q.name is some (Nm.pre p q.place): the place the port exposes, renamed under p;"
          "if the channel names of S are distinct, then for every channel c of S, I.chan c.name is some (p/c.trans): the name of the transition the channel exposes, renamed under p;"
          "for every name n that is no port name of S, I.port n is none (the lookup fails);"
          "for every name n that is no channel name of S, I.chan n is none (the lookup fails);"
          "I.pfx is p."
  assumes "The handles are the Instance fields port (a port name to the renamed place, none for an unknown name) and chan (a channel name to the renamed transition's name, none for an unknown name), and pfx. 'Fails' is none: Rust panics (instance.rs port and channel), Java throws IllegalArgumentException (Instance.java port and channel), TypeScript throws an Error (instance.ts port and channel), Python raises (rust/libpetri-py/src/model.rs port_place_name and channel, through the Rust panic). The messages are not stated."
          "The channel handle is the renamed transition's name. Java and TypeScript return the renamed Transition object and Rust and Python its name; under ruling D10 a transition of a net is identified by its name, so the two are one handle. Port places are the abstract N of the naming model, as in MOD-010: a place by name (TypeScript, Rust, Python: strNaming) or by name and token type (Java: typedNaming)."
          "Lines 1 and 2 are premised on distinct port names and distinct channel names. Every subnet definition the subnet builder accepts has them (MOD-006 lines 3 and 4); the Lean type SubnetDef allows definitions beyond the built ones, on which the reference answers with the first port or channel of the name and the runtimes' maps keep the last one. The handle answers whether or not the port's place was later bound by a composition: it is fixed at instantiation (Rust Instance::port in rust/libpetri-core/src/instance.rs reads the instance's port_handles, which SubnetDef::instantiate fills and no method of Instance changes; compose takes the instance by reference)."
          "That the handles name nodes of the renamed body (the port's place is a renamed body place, the channel's transition a renamed body transition) is a joint consequence with MOD-010, for every model of both blocks (mod011_handles_resolve): MOD-010 line 3 gives the renamed body and its line 2 the success on a built definition."
          "Item 3 and AC5 (params() returns the parameter value supplied at instantiation): the parameters value is not modelled (InstFn, Spec/GlossaryCompose.lean); Java, TypeScript and Rust return the value they were given, and Python's definitions take no parameters, so its Instance has no params(). Tested, not proven."
          "Item 1's type parameter, the MUST sentence on the token type and AC2 (port(\"input\", Integer) is rejected) are the second block, MOD_011_typed, scoped to the implementations that keep a run-time token type for each port (ruling D36 (a)). The requirement makes no compile-time claim: no runtime reports a mismatched port type when compiling."
          "AC1 (port(\"input\", String) returns the renamed Place<String>) is line 1 (MOD_011_nonvacuous on the reference: port input on place slots under r1 gives r1/slots) and, with its type, mod011_typed_declared. AC3 (channel(\"attempt\") returns the renamed transition whose original name was attempt) is line 2 (MOD_011_nonvacuous: r1/attempt). AC4 (an unknown port or channel name produces an error) is lines 3 and 4."
  signoff "2026-11-13 879e996ee6e16a6f ai"
  statement : ∀ {N A : Type}, Naming N → InstFn N A → Prop :=
    fun {N A} Nm Inst =>
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I → (S.ports.map (·.name)).Nodup →
        ∀ q ∈ S.ports, I.port q.name = some (Nm.pre p q.place)) ∧
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I → (S.chans.map (·.name)).Nodup →
        ∀ c ∈ S.chans, I.chan c.name = some (preS p c.trans)) ∧
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I →
        ∀ n, n ∉ S.ports.map (·.name) → I.port n = none) ∧
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I →
        ∀ n, n ∉ S.chans.map (·.name) → I.chan n = none) ∧
      (∀ (S : SubnetDef N A) p I, Inst S p = .ok I → I.pfx = p)

/- The pinned readable form of MOD-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_011 : {N A : Type} → Naming N → InstFn N A → Prop :=
fun {N A} Nm Inst =>
  (∀ (S : SubnetDef N A) (p : String) (I : Instance N A),
      Inst S p = Except.ok I →
        (List.map (fun x => x.name) S.ports).Nodup → ∀ q ∈ S.ports, I.port q.name = some (Nm.pre p q.place)) ∧
    (∀ (S : SubnetDef N A) (p : String) (I : Instance N A),
        Inst S p = Except.ok I →
          (List.map (fun x => x.name) S.chans).Nodup → ∀ c ∈ S.chans, I.chan c.name = some (preS p c.trans)) ∧
      (∀ (S : SubnetDef N A) (p : String) (I : Instance N A),
          Inst S p = Except.ok I → ∀ n ∉ List.map (fun x => x.name) S.ports, I.port n = none) ∧
        (∀ (S : SubnetDef N A) (p : String) (I : Instance N A),
            Inst S p = Except.ok I → ∀ n ∉ List.map (fun x => x.name) S.chans, I.chan n = none) ∧
          ∀ (S : SubnetDef N A) (p : String) (I : Instance N A), Inst S p = Except.ok I → I.pfx = p
-/
#guard_msgs in #print MOD_011

/-! ### The five lines, named (for the mutants) -/

section Lines

variable {N A : Type}

/-- Line 1 of MOD-011: a port name gives the renamed place its port exposes. -/
def mod011_line1 (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I → (S.ports.map (·.name)).Nodup →
    ∀ q ∈ S.ports, I.port q.name = some (Nm.pre p q.place)

/-- Line 2 of MOD-011: a channel name gives the renamed name of the transition it exposes. -/
def mod011_line2 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I → (S.chans.map (·.name)).Nodup →
    ∀ c ∈ S.chans, I.chan c.name = some (preS p c.trans)

/-- Line 3 of MOD-011: an unknown port name gives nothing. -/
def mod011_line3 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I → ∀ n, n ∉ S.ports.map (·.name) → I.port n = none

/-- Line 4 of MOD-011: an unknown channel name gives nothing. -/
def mod011_line4 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I → ∀ n, n ∉ S.chans.map (·.name) → I.chan n = none

/-- Line 5 of MOD-011: the instance's prefix is the one it was instantiated under. -/
def mod011_line5 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) p I, Inst S p = .ok I → I.pfx = p

/-- MOD-011 is its five lines. -/
theorem mod011_iff (Nm : Naming N) (Inst : InstFn N A) :
    MOD_011 Nm Inst ↔ mod011_line1 Nm Inst ∧ mod011_line2 Inst ∧ mod011_line3 Inst ∧
      mod011_line4 Inst ∧ mod011_line5 Inst :=
  Iff.rfl

end Lines

/-! ### Lookup by name -/

section Find

variable {α : Type}

/-- In a list whose names are distinct, looking an element's name up finds that element. -/
theorem mod011_find_of_nodup (key : α → String) :
    ∀ (l : List α) (a : α), a ∈ l → (l.map key).Nodup → l.find? (key · == key a) = some a
  | [], _, h, _ => nomatch h
  | b :: l, a, h, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hb : key b ≠ key a := fun he => hnd.1 (he ▸ List.mem_map_of_mem h')
      rw [show (key b == key a) = false from by simp [hb]]
      exact mod011_find_of_nodup key l a h' hnd.2

/-- Looking up a name no element carries finds nothing. -/
theorem mod011_find_none (key : α → String) (l : List α) (n : String)
    (h : n ∉ l.map key) : l.find? (key · == n) = none := by
  rw [List.find?_eq_none]
  intro x hx he
  exact h (by rw [beq_iff_eq] at he; rw [← he]; exact List.mem_map_of_mem hx)

end Find

/-! ### The reference -/

section Reference

variable {N A : Type}

/-- A success of the reference instantiation is the renamed instance. -/
theorem refInst_eq {Nm : Naming N} {S : SubnetDef N A} {p : String} {I : Instance N A}
    (h : refInst Nm S p = .ok I) : I = renamedInstance Nm S p := by
  obtain ⟨hp, ht, -⟩ := refInst_ok h
  rw [refInst_valid Nm S hp ht] at h
  exact (Except.ok.inj h).symm

/-- The renamed instance meets line 1: a port name gives its port's place, renamed. -/
theorem renamed_port (Nm : Naming N) (S : SubnetDef N A) (p : String)
    (hnd : (S.ports.map (·.name)).Nodup) {q : Port N} (hq : q ∈ S.ports) :
    (renamedInstance Nm S p).port q.name = some (Nm.pre p q.place) := by
  show (S.ports.find? (·.name == q.name)).map _ = _
  rw [mod011_find_of_nodup Port.name S.ports q hq hnd]
  rfl

/-- The renamed instance meets line 2: a channel name gives its transition's name, renamed. -/
theorem renamed_chan (Nm : Naming N) (S : SubnetDef N A) (p : String)
    (hnd : (S.chans.map (·.name)).Nodup) {c : Chan} (hc : c ∈ S.chans) :
    (renamedInstance Nm S p).chan c.name = some (preS p c.trans) := by
  show (S.chans.find? (·.name == c.name)).map _ = _
  rw [mod011_find_of_nodup Chan.name S.chans c hc hnd]
  rfl

/-- The renamed instance meets line 3: an unknown port name gives nothing. -/
theorem renamed_port_none (Nm : Naming N) (S : SubnetDef N A) (p : String) {n : String}
    (hn : n ∉ S.ports.map (·.name)) : (renamedInstance Nm S p).port n = none := by
  show (S.ports.find? (·.name == n)).map _ = _
  rw [mod011_find_none Port.name S.ports n hn]
  rfl

/-- The renamed instance meets line 4: an unknown channel name gives nothing. -/
theorem renamed_chan_none (Nm : Naming N) (S : SubnetDef N A) (p : String) {n : String}
    (hn : n ∉ S.chans.map (·.name)) : (renamedInstance Nm S p).chan n = none := by
  show (S.chans.find? (·.name == n)).map _ = _
  rw [mod011_find_none Chan.name S.chans n hn]
  rfl

end Reference

/-- ✓ The reference instantiation satisfies MOD-011 for every naming model: its port handle
looks the port up by name and renames the place the port exposes, its channel handle looks the
channel up by name and renames the transition's name, both answer nothing for a name the
interface does not declare, and the instance keeps the prefix it was given. -/
@[evidence holds MOD_011]
theorem MOD_011_reference {N A : Type} (Nm : Naming N) : MOD_011 Nm (refInst (A := A) Nm) := by
  refine ⟨fun S p I hI hnd q hq => ?_, fun S p I hI hnd c hc => ?_, fun S p I hI n hn => ?_,
    fun S p I hI n hn => ?_, fun S p I hI => ?_⟩ <;> rw [refInst_eq hI]
  · exact renamed_port Nm S p hnd hq
  · exact renamed_chan Nm S p hnd hc
  · exact renamed_port_none Nm S p hn
  · exact renamed_chan_none Nm S p hn
  · rfl

/-! ### Joint consequence with MOD-010 -/

/-- **The handles name nodes of the renamed body.** In every model of MOD-010 and MOD-011, a
subnet definition with distinct port and channel names, every port on a body place and every
channel on a body transition, and no terminal place, instantiated under a valid prefix `p`,
gives an instance with prefix `p` whose port handle gives, for every port, a place of the
instance named `p/x` for the name `x` of the place the port exposes, and whose channel handle
gives, for every channel, the name of a transition of the instance. Instantiating a buffer
under `r1` gives a port `input` that names the instance's place `r1/slots`, and a channel
`attempt` that names its transition `r1/attempt`. -/
theorem mod011_handles_resolve {N A : Type} {Nm : Naming N} {Inst : InstFn N A}
    (h10 : MOD_010 Nm Inst) (h11 : MOD_011 Nm Inst) (S : SubnetDef N A) {p : String}
    (hp : ValidPrefix p) (ht : S.terminals = []) (hpl : ∀ q ∈ S.ports, q.place ∈ S.places)
    (htr : ∀ c ∈ S.chans, c.trans ∈ S.defs.map (·.core.name))
    (hpn : (S.ports.map (·.name)).Nodup) (hcn : (S.chans.map (·.name)).Nodup) :
    ∃ I, Inst S p = .ok I ∧ I.pfx = p ∧
      (∀ q ∈ S.ports, ∃ x, I.port q.name = some x ∧ x ∈ I.places ∧
        Nm.name x = preS p (Nm.name q.place)) ∧
      (∀ c ∈ S.chans, ∃ t, I.chan c.name = some t ∧ t ∈ I.defs.map (·.core.name)) := by
  obtain ⟨I, hI⟩ := h10.2.1 S p hp ht hpl htr
  obtain ⟨hplaces, hdefs⟩ := h10.2.2.1 S p I hI
  refine ⟨I, hI, h11.2.2.2.2 S p I hI, fun q hq => ⟨Nm.pre p q.place, h11.1 S p I hI hpn q hq,
    (hplaces _).2 (List.mem_map_of_mem (hpl q hq)), Nm.pre_name p q.place⟩,
    fun c hc => ⟨preS p c.trans, h11.2.1 S p I hI hcn c hc, ?_⟩⟩
  have he : I.defs.map (·.core.name) = (I.defs.map CDef.toTransDef).map (·.core.name) := by
    rw [List.map_map]; rfl
  rw [he, hdefs, List.map_map]
  obtain ⟨d, hd, hdn⟩ := List.mem_map.1 (htr c hc)
  rw [← hdn]
  exact List.mem_map_of_mem (f := (fun x => x.core.name) ∘
    fun d : CDef N A => d.toTransDef.map (Nm.pre p) (preS p)) hd

/-! ### Example -/

/-- The example body transition `attempt`: an input arc on `slots` and the output place `out`. -/
def mod011_exDef : CDef String Unit :=
  { core := ⟨"attempt", [⟨"slots", .one⟩], [], [], []⟩, out := some (.place "out"),
    timing := .immediate, priority := 0, action := .other () }

/-- The example subnet definition `retry` (AC1, AC3 and the test derivation): the places `slots`
and `out`, the transition `attempt`, the port `input` on `slots` and the channel `attempt` on the
transition `attempt`. The port name differs from its place's name. -/
def mod011_exS : SubnetDef String Unit :=
  { name := "retry", places := ["slots", "out"], defs := [mod011_exDef],
    ports := [⟨"input", .input, "slots"⟩], chans := [⟨"attempt", "attempt"⟩] }

/-- ✓ Every line of MOD-011 is exercised by the reference: instantiating `retry` under `r1`
gives an instance whose port `input` is the place `r1/slots` (AC1), whose channel `attempt` is
the transition `r1/attempt` (AC3), whose port lookup for `output` and channel lookup for `retry`
fail because the interface declares neither (AC4), and whose prefix is `r1`. -/
@[evidence nonvacuous MOD_011]
theorem MOD_011_nonvacuous :
    ∃ I, refInst strNaming mod011_exS "r1" = .ok I ∧
      I.port "input" = some "r1/slots" ∧ I.chan "attempt" = some "r1/attempt" ∧
      I.port "output" = none ∧ I.chan "retry" = none ∧ I.pfx = "r1" := by
  refine ⟨_, refInst_valid strNaming mod011_exS (by decide) rfl, ?_⟩
  decide

/-! ### Wrong handles -/

section Wrong

variable {N A : Type}

/-- The reference instantiation with the handles of its result changed by `g`. -/
def withHandles (Nm : Naming N) (g : SubnetDef N A → String → Instance N A → Instance N A) :
    InstFn N A := fun S p =>
  match refInst Nm S p with
  | .ok I => .ok (g S p I)
  | .error e => .error e

/-- A success of `withHandles` is `g` applied to the renamed instance. -/
theorem withHandles_ok {Nm : Naming N} {g : SubnetDef N A → String → Instance N A → Instance N A}
    {S : SubnetDef N A} {p : String} {J : Instance N A} (h : withHandles Nm g S p = .ok J) :
    J = g S p (renamedInstance Nm S p) := by
  unfold withHandles at h
  split at h
  · rename_i I hI
    cases h
    rw [refInst_eq hI]
  · cases h

/-- On a valid prefix and a body without terminal places, `withHandles` succeeds. -/
theorem withHandles_valid (Nm : Naming N) (g : SubnetDef N A → String → Instance N A → Instance N A)
    (S : SubnetDef N A) {p : String} (hp : ValidPrefix p) (ht : S.terminals = []) :
    withHandles Nm g S p = .ok (g S p (renamedInstance Nm S p)) := by
  unfold withHandles
  rw [refInst_valid Nm S hp ht]

/-- A port handle that looks the port up but does not rename its place. -/
def unrenamedPortInst (Nm : Naming N) : InstFn N A :=
  withHandles Nm fun S _ I => { I with port := fun n => (S.ports.find? (·.name == n)).map (·.place) }

/-- A channel handle that looks the channel up but does not rename its transition's name. -/
def origChanInst (Nm : Naming N) : InstFn N A :=
  withHandles Nm fun S _ I => { I with chan := fun n => (S.chans.find? (·.name == n)).map (·.trans) }

/-- A channel handle that answers an unknown channel name `n` with the transition name `p/n`. -/
def freshChanInst (Nm : Naming N) : InstFn N A :=
  withHandles Nm fun _ p I => { I with chan := fun n => some ((I.chan n).getD (preS p n)) }

/-- An instance that reports the definition's name as its prefix. -/
def defNamePfxInst (Nm : Naming N) : InstFn N A :=
  withHandles Nm fun S _ I => { I with pfx := S.name }

/-- An instantiation that answers every handle lookup with nothing. -/
def noHandlesInst (Nm : Naming N) : InstFn N A :=
  withHandles Nm fun _ _ I => { I with port := fun _ => none, chan := fun _ => none }

end Wrong

/-- A port handle (places by name) that answers an unknown port name `n` with the place `p/n`. -/
def freshPortInst : InstFn String Unit :=
  withHandles strNaming fun _ p I => { I with port := fun n => some ((I.port n).getD (preS p n)) }

/-- A port handle (places by name) built from the port's own name, `p/portName`, not from the
place the port exposes. -/
def portByPortNameInst : InstFn String Unit :=
  withHandles strNaming fun S p I =>
    { I with port := fun n => (S.ports.find? (·.name == n)).map (fun q => preS p q.name) }

/-- ✗ A port handle built as `p/portName` violates MOD-011 (line 1): the example's port `input`
gives `r1/input`, but the port exposes the place `slots`, so the handle must give `r1/slots`. -/
@[evidence forbids MOD_011]
theorem MOD_011_forbids_portByPortName : ¬ MOD_011 strNaming portByPortNameInst := by
  intro h
  have hI := withHandles_valid strNaming (fun S p I =>
    { I with port := fun n => (S.ports.find? (·.name == n)).map (fun q => preS p q.name) })
    mod011_exS (p := "r1") (by decide) rfl
  have := h.1 _ _ _ hI (by decide) ⟨"input", .input, "slots"⟩ (List.mem_cons_self ..)
  exact absurd this (by decide)

/-- ✗ An instantiation whose handles answer nothing violates MOD-011 (line 1): the example's
port `input` must give `r1/slots`. -/
@[evidence forbids MOD_011]
theorem MOD_011_forbids_noHandles : ¬ MOD_011 strNaming (noHandlesInst (A := Unit) strNaming) := by
  intro h
  have hI := withHandles_valid strNaming (fun _ _ (I : Instance String Unit) =>
    { I with port := fun _ => none, chan := fun _ => none }) mod011_exS (p := "r1") (by decide) rfl
  have := h.1 _ _ _ hI (by decide) ⟨"input", .input, "slots"⟩ (List.mem_cons_self ..)
  exact absurd this (by decide)

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-011 without line 1, so the port handle need not rename the place. -/
def MOD_011_mutant_noPortRename {N A : Type} (_Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod011_line2 Inst ∧ mod011_line3 Inst ∧ mod011_line4 Inst ∧ mod011_line5 Inst

/-- The port handle that returns the unrenamed place kills the mutant: it meets lines 2 to 5,
but the example's port `input` under `r1` gives `slots` instead of `r1/slots` (line 1). -/
@[evidence mutant MOD_011]
theorem MOD_011_mutant_noPortRename_killed :
    MOD_011_mutant_noPortRename strNaming (unrenamedPortInst (A := Unit) strNaming) ∧
      ¬ MOD_011 strNaming (unrenamedPortInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p I hI hnd c hc => ?_, fun S p I hI n hn => ?_, fun S p I hI n hn => ?_,
    fun S p I hI => ?_⟩, fun h => ?_⟩
  · rw [withHandles_ok hI]; exact renamed_chan strNaming S p hnd hc
  · rw [withHandles_ok hI]
    show (S.ports.find? (·.name == n)).map _ = _
    rw [mod011_find_none Port.name S.ports n hn]; rfl
  · rw [withHandles_ok hI]; exact renamed_chan_none strNaming S p hn
  · rw [withHandles_ok hI]; rfl
  · have hI := withHandles_valid strNaming (fun S _ (I : Instance String Unit) =>
      { I with port := fun n => (S.ports.find? (·.name == n)).map (·.place) })
      mod011_exS (p := "r1") (by decide) rfl
    have := h.1 _ _ _ hI (by decide) ⟨"input", .input, "slots"⟩ (List.mem_cons_self ..)
    exact absurd this (by decide)

/-- Mutant reading: MOD-011 without line 2, so the channel handle need not rename the
transition. -/
def MOD_011_mutant_noChanRename {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod011_line1 Nm Inst ∧ mod011_line3 Inst ∧ mod011_line4 Inst ∧ mod011_line5 Inst

/-- The channel handle that returns the unrenamed transition name kills the mutant: it meets
lines 1, 3, 4 and 5, but the example's channel `attempt` under `r1` gives `attempt` instead of
`r1/attempt` (line 2). -/
@[evidence mutant MOD_011]
theorem MOD_011_mutant_noChanRename_killed :
    MOD_011_mutant_noChanRename strNaming (origChanInst (A := Unit) strNaming) ∧
      ¬ MOD_011 strNaming (origChanInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p I hI hnd q hq => ?_, fun S p I hI n hn => ?_, fun S p I hI n hn => ?_,
    fun S p I hI => ?_⟩, fun h => ?_⟩
  · rw [withHandles_ok hI]; exact renamed_port strNaming S p hnd hq
  · rw [withHandles_ok hI]; exact renamed_port_none strNaming S p hn
  · rw [withHandles_ok hI]
    show (S.chans.find? (·.name == n)).map _ = _
    rw [mod011_find_none Chan.name S.chans n hn]; rfl
  · rw [withHandles_ok hI]; rfl
  · have hI := withHandles_valid strNaming (fun S _ (I : Instance String Unit) =>
      { I with chan := fun n => (S.chans.find? (·.name == n)).map (·.trans) })
      mod011_exS (p := "r1") (by decide) rfl
    have := h.2.1 _ _ _ hI (by decide) ⟨"attempt", "attempt"⟩ (List.mem_cons_self ..)
    exact absurd this (by decide)

/-- Mutant reading: MOD-011 without line 3, so an unknown port name may give a place. -/
def MOD_011_mutant_unknownPort {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod011_line1 Nm Inst ∧ mod011_line2 Inst ∧ mod011_line4 Inst ∧ mod011_line5 Inst

/-- The port handle that invents the place `p/n` for an unknown port name `n` kills the mutant:
it meets lines 1, 2, 4 and 5, but the example's lookup of the port `output`, which the interface
does not declare, gives `r1/output` instead of failing (line 3). -/
@[evidence mutant MOD_011]
theorem MOD_011_mutant_unknownPort_killed :
    MOD_011_mutant_unknownPort strNaming freshPortInst ∧ ¬ MOD_011 strNaming freshPortInst := by
  refine ⟨⟨fun S p I hI hnd q hq => ?_, fun S p I hI hnd c hc => ?_, fun S p I hI n hn => ?_,
    fun S p I hI => ?_⟩, fun h => ?_⟩
  · rw [withHandles_ok hI]
    show some (((renamedInstance strNaming S p).port q.name).getD _) = _
    rw [renamed_port strNaming S p hnd hq]; rfl
  · rw [withHandles_ok hI]; exact renamed_chan strNaming S p hnd hc
  · rw [withHandles_ok hI]; exact renamed_chan_none strNaming S p hn
  · rw [withHandles_ok hI]; rfl
  · have hI := withHandles_valid strNaming (fun _ p (I : Instance String Unit) =>
      { I with port := fun n => some ((I.port n).getD (preS p n)) })
      mod011_exS (p := "r1") (by decide) rfl
    have := h.2.2.1 _ _ _ hI "output" (by decide)
    exact absurd this (by decide)

/-- Mutant reading: MOD-011 without line 4, so an unknown channel name may give a transition. -/
def MOD_011_mutant_unknownChan {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod011_line1 Nm Inst ∧ mod011_line2 Inst ∧ mod011_line3 Inst ∧ mod011_line5 Inst

/-- The channel handle that invents the transition `p/n` for an unknown channel name `n` kills
the mutant: it meets lines 1, 2, 3 and 5, but the example's lookup of the channel `retry`, which
the interface does not declare, gives `r1/retry` instead of failing (line 4). -/
@[evidence mutant MOD_011]
theorem MOD_011_mutant_unknownChan_killed :
    MOD_011_mutant_unknownChan strNaming (freshChanInst (A := Unit) strNaming) ∧
      ¬ MOD_011 strNaming (freshChanInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p I hI hnd q hq => ?_, fun S p I hI hnd c hc => ?_, fun S p I hI n hn => ?_,
    fun S p I hI => ?_⟩, fun h => ?_⟩
  · rw [withHandles_ok hI]; exact renamed_port strNaming S p hnd hq
  · rw [withHandles_ok hI]
    show some (((renamedInstance strNaming S p).chan c.name).getD _) = _
    rw [renamed_chan strNaming S p hnd hc]; rfl
  · rw [withHandles_ok hI]; exact renamed_port_none strNaming S p hn
  · rw [withHandles_ok hI]; rfl
  · have hI := withHandles_valid strNaming (fun _ p (I : Instance String Unit) =>
      { I with chan := fun n => some ((I.chan n).getD (preS p n)) })
      mod011_exS (p := "r1") (by decide) rfl
    have := h.2.2.2.1 _ _ _ hI "retry" (by decide)
    exact absurd this (by decide)

/-- Mutant reading: MOD-011 without line 5, so the instance may report another prefix. -/
def MOD_011_mutant_noPrefix {N A : Type} (Nm : Naming N) (Inst : InstFn N A) : Prop :=
  mod011_line1 Nm Inst ∧ mod011_line2 Inst ∧ mod011_line3 Inst ∧ mod011_line4 Inst

/-- The instance that reports the definition's name as its prefix kills the mutant: its handles
meet lines 1 to 4, but instantiating `retry` under `r1` reports the prefix `retry` (line 5). -/
@[evidence mutant MOD_011]
theorem MOD_011_mutant_noPrefix_killed :
    MOD_011_mutant_noPrefix strNaming (defNamePfxInst (A := Unit) strNaming) ∧
      ¬ MOD_011 strNaming (defNamePfxInst (A := Unit) strNaming) := by
  refine ⟨⟨fun S p I hI hnd q hq => ?_, fun S p I hI hnd c hc => ?_, fun S p I hI n hn => ?_,
    fun S p I hI n hn => ?_⟩, fun h => ?_⟩
  · rw [withHandles_ok hI]; exact renamed_port strNaming S p hnd hq
  · rw [withHandles_ok hI]; exact renamed_chan strNaming S p hnd hc
  · rw [withHandles_ok hI]; exact renamed_port_none strNaming S p hn
  · rw [withHandles_ok hI]; exact renamed_chan_none strNaming S p hn
  · have hI := withHandles_valid strNaming (fun S _ (I : Instance String Unit) =>
      { I with pfx := S.name }) mod011_exS (p := "r1") (by decide) rfl
    have := h.2.2.2.2 _ _ _ hI
    exact absurd this (by decide)

/-! ## The typed port block -/

/-- A typed port lookup ([MOD-011]): an instance, a port name and a requested token type give
the port's place or a rejection with a message. -/
abbrev PortAsFn (N A T : Type) := Instance N A → String → T → Except String N

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri.Spec

/-- **The reference typed port lookup** ([MOD-011], Java `Instance.port(name, tokenType)`, Rust
`Instance::port::<T>(name)`): look the port up, then compare the requested type with the token
type `tyOf` of the place the handle names. The messages are stand-ins. -/
def refPortAs {N A T : Type} [DecidableEq T] (tyOf : N → T) : PortAsFn N A T := fun I n ty =>
  match I.port n with
  | none => .error s!"No port named '{n}' in instance '{I.pfx}'"
  | some x => if tyOf x = ty then .ok x else .error s!"Port '{n}' has another token type"

/- The reference typed lookup is the witness model of the typed port block. -/
#spec_witness refPortAs

end Libpetri.Reference

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

requirement MOD_011_typed
  id "MOD-011"
  title "Instance Handle Map, the typed port lookup"
  kind F
  scope "implementations that keep a run-time token type for each port (Java, Rust)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_011.s6, MOD_011.s7, MOD_011.s8
  reading "For every reader tyOf of the token type a place handle carries and every typed port lookup PortAs, for every instance I, name n and requested type ty:"
          "if the port handle I.port n gives the place x (the port's renamed place, MOD_011 line 1) and ty is tyOf x, the type x carries (on typedNaming the type the port was declared with, mod011_typed_declared), PortAs I n ty returns x;"
          "if I.port n gives the place x and ty is not tyOf x (on typedNaming a type other than the one the port was declared with), PortAs I n ty fails;"
          "if I.port n gives nothing, PortAs I n ty fails."
  assumes "Ruling D36 (a): the type check is scoped to the implementations that keep a run-time token type for each port. Java's Instance.port(name, tokenType) compares the requested class with the token type of the renamed place it returns, which keeps the token type of the body place the port was declared on, and throws IllegalArgumentException on a difference (java/src/main/java/org/libpetri/core/Instance.java). Rust's Instance::port::<T>(name) compares TypeId::of::<T>() with port_types[name], the TypeId that Port::new captured from the Place<T> handle the port was declared with (rust/libpetri-core/src/interface.rs), copied per port name at instantiation (SubnetDef::instantiate in rust/libpetri-core/src/subnet_def.rs); it panics on a difference and otherwise returns Place::<T>::new on the renamed name (rust/libpetri-core/src/instance.rs). TypeScript's port<T>(name) takes T as an annotation it does not check (Instance.port in typescript/src/core/instance.ts) and Python's port_place_name(name) takes no type; neither is in scope. The messages are not stated."
          "Both runtimes are read at the typed naming model typedNaming, a place handle being its name and its token type, and tyOf is Prod.snd. For Java the handle is the place record (name, tokenType). For Rust it is the pair of the renamed name (port_handles[name]) and the captured TypeId (port_types[name]); on success the Place<T> Rust returns has the requested T, equal to the captured one, so it is that pair. The type is the port's, not a function of the place's name: Rust identifies places by name (MOD-024, strNaming in MOD_011), and one place name can carry two token types, for two definitions instantiated under one prefix whose ports declare the body place slots as Place<String> and as Place<i32>, or for two ports over one body place (MOD-003 AC5) that captured different TypeIds. A lookup that reads the type off the place's name is forbidden (MOD_011_typed_forbids_byPlaceName). On typedNaming the rename keeps the type, so the type the handle carries is the type the port was declared with, the spec's wording: every model of MOD-011 and of this block accepts exactly the declared type of the port's body place (mod011_typed_declared)."
          "The block is stated for every instance, not only for one instantiate returns: Java and Rust check the type on whatever instance the lookup is called on. Which place the port lookup returns, the port's renamed place, and that it fails on an unknown name, is the handle block MOD_011 (lines 1 and 3)."
          "The requirement makes no compile-time claim (ruling D36 (a)): no runtime reports a mismatched port type when compiling, since an instance's handle map is not typed by its interface."
          "AC1 with its type (port(\"input\", String) on an instance whose interface declared input: Input<String> returns the renamed Place<String>) is line 1, and AC2 (port(\"input\", Integer) on the same instance is rejected) is line 2: MOD_011_typed_nonvacuous on the reference at typedNaming, and mod011_typed_declared for every model of both blocks."
  signoff "2026-11-13 05a41fb75002f423 ai"
  statement : ∀ {N A T : Type}, (N → T) → PortAsFn N A T → Prop :=
    fun {N A T} tyOf PortAs =>
      (∀ (I : Instance N A) n x (ty : T), I.port n = some x → tyOf x = ty → PortAs I n ty = .ok x) ∧
      (∀ (I : Instance N A) n x (ty : T), I.port n = some x → tyOf x ≠ ty →
        ∃ msg, PortAs I n ty = .error msg) ∧
      (∀ (I : Instance N A) n (ty : T), I.port n = none → ∃ msg, PortAs I n ty = .error msg)

/- The pinned readable form of the typed port block. -/
/--
info: def Libpetri.Spec.MOD_011_typed : {N A T : Type} → (N → T) → PortAsFn N A T → Prop :=
fun {N A T} tyOf PortAs =>
  (∀ (I : Instance N A) (n : String) (x : N) (ty : T), I.port n = some x → tyOf x = ty → PortAs I n ty = Except.ok x) ∧
    (∀ (I : Instance N A) (n : String) (x : N) (ty : T),
        I.port n = some x → tyOf x ≠ ty → ∃ msg, PortAs I n ty = Except.error msg) ∧
      ∀ (I : Instance N A) (n : String) (ty : T), I.port n = none → ∃ msg, PortAs I n ty = Except.error msg
-/
#guard_msgs in #print MOD_011_typed

section TypedLines

variable {N A T : Type}

/-- Line 1 of the typed block: the requested type of the returned place gives that place. -/
def mod011t_line1 (tyOf : N → T) (PortAs : PortAsFn N A T) : Prop :=
  ∀ (I : Instance N A) n x ty, I.port n = some x → tyOf x = ty → PortAs I n ty = .ok x

/-- Line 2 of the typed block: another requested type fails. -/
def mod011t_line2 (tyOf : N → T) (PortAs : PortAsFn N A T) : Prop :=
  ∀ (I : Instance N A) n x ty, I.port n = some x → tyOf x ≠ ty → ∃ msg, PortAs I n ty = .error msg

/-- Line 3 of the typed block: an unknown port name fails. -/
def mod011t_line3 (PortAs : PortAsFn N A T) : Prop :=
  ∀ (I : Instance N A) n ty, I.port n = none → ∃ msg, PortAs I n ty = .error msg

/-- The typed block is its three lines. -/
theorem mod011t_iff (tyOf : N → T) (PortAs : PortAsFn N A T) :
    MOD_011_typed tyOf PortAs ↔
      mod011t_line1 tyOf PortAs ∧ mod011t_line2 tyOf PortAs ∧ mod011t_line3 PortAs :=
  Iff.rfl

end TypedLines

/-- ✓ The reference typed lookup satisfies the typed block for every token-type reader: it
returns the place the port handle names when the requested type is that place's type, and fails
when the type differs or the port name is unknown. -/
@[evidence holds MOD_011_typed]
theorem MOD_011_typed_reference {N A T : Type} [DecidableEq T] (tyOf : N → T) :
    MOD_011_typed tyOf (refPortAs (A := A) tyOf) := by
  refine ⟨fun I n x ty hx ht => ?_, fun I n x ty hx ht => ?_, fun I n ty hx => ?_⟩
  · simp [refPortAs, hx, ht]
  · simp [refPortAs, hx, ht]
  · simp [refPortAs, hx]

/-- **AC1 and AC2 at the declared type.** On the typed naming model (a place handle is a name and a
token type, and the prefix keeps the type: Java's place record, Rust's renamed name with the
`TypeId` its port captured), every model of MOD-011 and of the typed block gives, for a
port `q` of a definition with distinct port names instantiated under `p`, the renamed place when
the requested type is the type of the place the port was declared on, and a failure for any
other type: a port `input` declared on a `String` place answers `port("input", String)` with
`r1/slots` and rejects `port("input", Integer)`. -/
theorem mod011_typed_declared {A Ty : Type} {Inst : InstFn (String × Ty) A}
    {PortAs : PortAsFn (String × Ty) A Ty} (h11 : MOD_011 (typedNaming Ty) Inst)
    (ht : MOD_011_typed Prod.snd PortAs) {S : SubnetDef (String × Ty) A} {p : String}
    {I : Instance (String × Ty) A} (hI : Inst S p = .ok I) (hnd : (S.ports.map (·.name)).Nodup)
    {q : Port (String × Ty)} (hq : q ∈ S.ports) :
    PortAs I q.name q.place.2 = .ok (preS p q.place.1, q.place.2) ∧
      ∀ ty, ty ≠ q.place.2 → ∃ msg, PortAs I q.name ty = .error msg := by
  have hp := h11.1 S p I hI hnd q hq
  exact ⟨ht.1 I q.name _ _ hp rfl, fun ty hty => ht.2.1 I q.name _ ty hp (Ne.symm hty)⟩

/-- A token type for the examples: `String` and `Integer`. -/
inductive Mod011Ty where
  /-- The type `String`. -/
  | str
  /-- The type `Integer`. -/
  | int
  deriving DecidableEq, Repr

/-- The example transition `attempt` at the typed naming model: an input arc on the `String` place
`slots` and the output place `out`. -/
def mod011_exDefT : CDef (String × Mod011Ty) Unit :=
  { core := ⟨"attempt", [⟨("slots", .str), .one⟩], [], [], []⟩, out := some (.place ("out", .str)),
    timing := .immediate, priority := 0, action := .other () }

/-- The example of AC1 and AC2 at the typed naming model: the place `slots` of type `String`, the
transition `attempt`, the port `input` on `slots` and the channel `attempt`. -/
def mod011_exT : SubnetDef (String × Mod011Ty) Unit :=
  { name := "retry", places := [("slots", .str), ("out", .str)], defs := [mod011_exDefT],
    ports := [⟨"input", .input, ("slots", .str)⟩], chans := [⟨"attempt", "attempt"⟩] }

/-- ✓ Every line of the typed block is exercised by the reference: instantiating `retry` under
`r1` on the typed naming model and asking for the port `input` as a `String` gives the place
`r1/slots` of type `String` (AC1), asking for it as an `Integer` fails (AC2), and asking for the
undeclared port `output` fails (AC4). -/
@[evidence nonvacuous MOD_011_typed]
theorem MOD_011_typed_nonvacuous :
    ∃ I, refInst (typedNaming Mod011Ty) mod011_exT "r1" = .ok I ∧
      refPortAs Prod.snd I "input" Mod011Ty.str = .ok ("r1/slots", .str) ∧
      (∃ msg, refPortAs Prod.snd I "input" Mod011Ty.int = .error msg) ∧
      (∃ msg, refPortAs Prod.snd I "output" Mod011Ty.str = .error msg) :=
  ⟨_, refInst_valid (typedNaming Mod011Ty) mod011_exT (by decide) rfl, rfl,
    by simp [refPortAs, renamedInstance, mod011_exT, typedNaming],
    by simp [refPortAs, renamedInstance, mod011_exT, typedNaming]⟩

/-! ### Wrong typed lookups -/

section WrongTyped

variable {N A T : Type}

/-- A typed lookup that rejects everything. -/
def rejectAllPortAs : PortAsFn N A T := fun _ _ _ => .error "rejected"

/-- A typed lookup that does not check the type (TypeScript's `port<T>(name)`, which is out of
the block's scope). -/
def uncheckedPortAs : PortAsFn N A T := fun I n _ =>
  match I.port n with
  | none => .error "no port"
  | some x => .ok x

end WrongTyped

/-- A typed lookup (places by name and type) that answers an unknown port name `n` with the
place `p/n` of the requested type. -/
def freshPortAs {A T : Type} [DecidableEq T] : PortAsFn (String × T) A T := fun I n ty =>
  match I.port n with
  | none => .ok (preS I.pfx n, ty)
  | some x => if x.2 = ty then .ok x else .error "type"

/-- The example instance: the port `input` names `r1/slots` of type `String`, nothing else. -/
def mod011_exI : Instance (String × Mod011Ty) Unit where
  pfx := "r1"
  places := [("r1/slots", .str)]
  defs := []
  port n := if n = "input" then some ("r1/slots", .str) else none
  chan _ := none
  iface := []

/-- Mutant reading: the typed block without line 1, so a lookup of the right type need not
succeed. -/
def MOD_011_typed_mutant_noAccept {N A T : Type} (tyOf : N → T) (PortAs : PortAsFn N A T) :
    Prop :=
  mod011t_line2 tyOf PortAs ∧ mod011t_line3 PortAs

/-- The typed lookup that rejects everything kills the mutant: it meets lines 2 and 3, but asking
the example instance for the port `input` as a `String` fails (line 1). -/
@[evidence mutant MOD_011_typed]
theorem MOD_011_typed_mutant_noAccept_killed :
    MOD_011_typed_mutant_noAccept Prod.snd (rejectAllPortAs (N := String × Mod011Ty) (A := Unit)) ∧
      ¬ MOD_011_typed Prod.snd (rejectAllPortAs (N := String × Mod011Ty) (A := Unit)) := by
  refine ⟨⟨fun _ _ _ _ _ _ => ⟨_, rfl⟩, fun _ _ _ _ => ⟨_, rfl⟩⟩, fun h => ?_⟩
  have := h.1 mod011_exI "input" ("r1/slots", .str) .str rfl rfl
  exact nomatch this

/-- Mutant reading: the typed block without line 2, so a lookup of another type may succeed. -/
def MOD_011_typed_mutant_noCheck {N A T : Type} (tyOf : N → T) (PortAs : PortAsFn N A T) :
    Prop :=
  mod011t_line1 tyOf PortAs ∧ mod011t_line3 PortAs

/-- The typed lookup without a type check kills the mutant: it meets lines 1 and 3, but asking
the example instance for the `String` port `input` as an `Integer` returns the place (line 2). -/
@[evidence mutant MOD_011_typed]
theorem MOD_011_typed_mutant_noCheck_killed :
    MOD_011_typed_mutant_noCheck Prod.snd (uncheckedPortAs (N := String × Mod011Ty) (A := Unit)) ∧
      ¬ MOD_011_typed Prod.snd (uncheckedPortAs (N := String × Mod011Ty) (A := Unit)) := by
  refine ⟨⟨fun I n x ty hx _ => ?_, fun I n ty hx => ?_⟩, fun h => ?_⟩
  · simp [uncheckedPortAs, hx]
  · exact ⟨"no port", by simp [uncheckedPortAs, hx]⟩
  · obtain ⟨msg, hm⟩ := h.2.1 mod011_exI "input" ("r1/slots", .str) .int rfl (by decide)
    exact nomatch hm

/-- Mutant reading: the typed block without line 3, so an unknown port name may give a place. -/
def MOD_011_typed_mutant_unknown {N A T : Type} (tyOf : N → T) (PortAs : PortAsFn N A T) :
    Prop :=
  mod011t_line1 tyOf PortAs ∧ mod011t_line2 tyOf PortAs

/-- The typed lookup that invents a place for an unknown port name kills the mutant: it meets
lines 1 and 2, but asking the example instance for the undeclared port `output` returns the place
`r1/output` (line 3). -/
@[evidence mutant MOD_011_typed]
theorem MOD_011_typed_mutant_unknown_killed :
    MOD_011_typed_mutant_unknown Prod.snd (freshPortAs (A := Unit) (T := Mod011Ty)) ∧
      ¬ MOD_011_typed Prod.snd (freshPortAs (A := Unit) (T := Mod011Ty)) := by
  refine ⟨⟨fun I n x ty hx ht => ?_, fun I n x ty hx ht => ?_⟩, fun h => ?_⟩
  · simp [freshPortAs, hx, ht]
  · exact ⟨"type", by simp [freshPortAs, hx, ht]⟩
  · obtain ⟨msg, hm⟩ := h.2.2 mod011_exI "output" .str rfl
    exact nomatch hm


/-! ### The type is the port's, not the place name's -/

/-- A typed lookup (places by name and type) that reads the token type off the place's name: it
takes the type of the first place of the instance with the name of the port's place, and returns
that name at the requested type. This is the type check keyed on the place by name, which Rust
does not do: Rust compares with the `TypeId` its port captured. -/
def byPlaceNamePortAs {A T : Type} [DecidableEq T] : PortAsFn (String × T) A T := fun I n ty =>
  match I.port n with
  | none => .error "no port"
  | some x =>
    match I.places.find? (·.1 == x.1) with
    | none => .error "no place"
    | some y => if y.2 = ty then .ok (x.1, ty) else .error "type"

/-- An instance with one place name carrying two token types (two ports over one body place that
were declared at different types, MOD-003 AC5, as Rust allows): the port `a` names `r1/slots` as a
`String` and the port `b` names it as an `Integer`. -/
def mod011_exI2 : Instance (String × Mod011Ty) Unit where
  pfx := "r1"
  places := [("r1/slots", .str), ("r1/slots", .int)]
  defs := []
  port n := if n = "a" then some ("r1/slots", .str) else
    if n = "b" then some ("r1/slots", .int) else none
  chan _ := none
  iface := []

/-- The reference typed lookup keys the type on the port: on the instance whose place `r1/slots`
two ports name at two types, it accepts the port `a` as a `String` and the port `b` as an
`Integer`, each at its own declared type. -/
theorem mod011_typed_perPort :
    refPortAs Prod.snd mod011_exI2 "a" Mod011Ty.str = .ok ("r1/slots", .str) ∧
      refPortAs Prod.snd mod011_exI2 "b" Mod011Ty.int = .ok ("r1/slots", .int) :=
  ⟨rfl, rfl⟩

/-- ✗ A typed lookup that reads the token type off the place's name violates the typed block
(line 1): on the instance whose place `r1/slots` the port `a` names as a `String` and the port `b`
as an `Integer`, asking for `b` as an `Integer` fails, since the first place named `r1/slots` is
the `String` one. -/
@[evidence forbids MOD_011_typed]
theorem MOD_011_typed_forbids_byPlaceName :
    ¬ MOD_011_typed Prod.snd (byPlaceNamePortAs (A := Unit) (T := Mod011Ty)) := by
  intro h
  have := h.1 mod011_exI2 "b" ("r1/slots", .int) .int rfl rfl
  exact nomatch this

end Libpetri.Spec
