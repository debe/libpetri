import Libpetri.Spec.GlossaryCompose

set_option linter.missingDocs true

/-!
# RefCompose: instantiation

The instantiation slice of the composition model ([MOD-010]): `refInst Nm`, the reference
instantiation function for the naming model `Nm` (`Spec/GlossaryCompose.lean`). It checks the
prefix (non-empty, no `/`, ruling D25 (a)), refuses a body that declares a terminal place
([EXEC-042] AC6), and otherwise renames the body: every place through `Nm.pre p`, every
transition definition through one rewrite pass `CDef.map (Nm.pre p) (preS p)` (arc and
output-spec places renamed, name `p/name`, timing, priority and action kept), in the body's
order. The handles resolve port and channel names through the rename ([MOD-011]).

The order of the two checks follows Rust (`SubnetDef::instantiate` in
`rust/libpetri-core/src/subnet_def.rs`: the prefix, then the terminal places). The terminal-place rejection names the first terminal place,
as in every runtime ([MOD-010] line 4); the prefix message is a stand-in.
-/

namespace Libpetri.Reference

open Libpetri Libpetri.Spec

variable {N A : Type}

/-- The module instance of `S` under prefix `p`: the places renamed through `Nm.pre p`, the
definitions through one rewrite pass `CDef.map (Nm.pre p) (preS p)`, in order, a port name
resolved to its renamed place, a channel name to its renamed transition name, and the
definition's ports kept unrenamed. -/
def renamedInstance (Nm : Naming N) (S : SubnetDef N A) (p : String) : Instance N A where
  pfx := p
  places := S.places.map (Nm.pre p)
  defs := S.defs.map (CDef.map (Nm.pre p) (preS p))
  port n := (S.ports.find? (·.name == n)).map (fun q => Nm.pre p q.place)
  chan n := (S.chans.find? (·.name == n)).map (fun c => preS p c.trans)
  iface := S.ports

/-- The rejection of a body with a declared terminal place ([EXEC-042] AC6): it names the first
terminal place, as every runtime's message does (`reject_subnet_terminals` called from
`SubnetDef::instantiate` in `rust/libpetri-core/src/subnet_def.rs`, `SubnetRewriter.rejectTerminals`
in `java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java`, `rejectSubnetTerminals`
called from `renameNet` in `typescript/src/core/internal/subnet-rewriter.ts`). -/
def instTermMsg (Nm : Naming N) (S : SubnetDef N A) : String :=
  match S.terminals with
  | [] => s!"subnet '{S.name}' declares no terminal place"
  | x :: _ =>
    s!"subnet '{S.name}' declares terminal place '{Nm.name x}'; a subnet body may not (EXEC-042)"

/-- **The reference instantiation** ([MOD-010]): reject an invalid prefix, then a body with a
declared terminal place ([EXEC-042] AC6), naming the first one; otherwise the renamed instance.
The prefix message is a stand-in. -/
def refInst (Nm : Naming N) : InstFn N A := fun S p =>
  if ValidPrefix p then
    if S.terminals.isEmpty then .ok (renamedInstance Nm S p)
    else .error (instTermMsg Nm S)
  else .error s!"prefix '{p}' must be non-empty and must not contain '/' (MOD-010)"

/- The reference instantiation is the witness model of the instantiation blocks. -/
#spec_witness refInst

/-- The reference instantiation rejects an invalid prefix. -/
theorem refInst_invalid (Nm : Naming N) (S : SubnetDef N A) {p : String} (hp : ¬ ValidPrefix p) :
    refInst Nm S p = .error s!"prefix '{p}' must be non-empty and must not contain '/' (MOD-010)" :=
  if_neg hp

/-- The reference instantiation rejects a body that declares a terminal place ([EXEC-042] AC6). -/
theorem refInst_terminals (Nm : Naming N) (S : SubnetDef N A) (p : String)
    (ht : S.terminals ≠ []) : ∃ msg, refInst Nm S p = .error msg := by
  unfold refInst
  split
  · rw [if_neg (by simpa [List.isEmpty_iff] using ht)]; exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The terminal-place message names a terminal place of the body. -/
theorem instTermMsg_names (Nm : Naming N) (S : SubnetDef N A) (ht : S.terminals ≠ []) :
    ∃ x ∈ S.terminals, MsgNames (instTermMsg Nm S) (Nm.name x) := by
  unfold instTermMsg
  split
  · exact absurd ‹S.terminals = []› ht
  · rename_i x _ hx
    exact ⟨x, hx ▸ List.mem_cons_self, msgNames_app _ (msgNames_end _ _)⟩

/-- Under a valid prefix the reference instantiation rejects a body with a terminal place with a
message that names one of its terminal places ([EXEC-042] AC6). -/
theorem refInst_terminals_named (Nm : Naming N) (S : SubnetDef N A) {p : String}
    (hp : ValidPrefix p) (ht : S.terminals ≠ []) :
    refInst Nm S p = .error (instTermMsg Nm S) := by
  unfold refInst
  rw [if_pos hp, if_neg (by simpa [List.isEmpty_iff] using ht)]

/-- The reference instantiation succeeds on a valid prefix and a body without terminal places. -/
theorem refInst_valid (Nm : Naming N) (S : SubnetDef N A) {p : String} (hp : ValidPrefix p)
    (ht : S.terminals = []) :
    refInst Nm S p = .ok (renamedInstance Nm S p) := by
  unfold refInst
  rw [if_pos hp, if_pos (by simp [ht])]

/-- A success of the reference instantiation is at a valid prefix and on a body without terminal
places, and holds the renamed places and definitions. -/
theorem refInst_ok {Nm : Naming N} {S : SubnetDef N A} {p : String} {I : Instance N A}
    (h : refInst Nm S p = .ok I) :
    ValidPrefix p ∧ S.terminals = [] ∧ I.pfx = p ∧ I.places = S.places.map (Nm.pre p) ∧
      I.defs = S.defs.map (CDef.map (Nm.pre p) (preS p)) ∧ I.iface = S.ports := by
  unfold refInst at h
  split at h
  · rename_i hp
    split at h
    · rename_i ht
      cases h
      exact ⟨hp, List.isEmpty_iff.1 ht, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

end Libpetri.Reference
