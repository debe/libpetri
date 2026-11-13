import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryCompose
import Libpetri.Reference.ComposeDef
import Libpetri.Spec.Req.MOD_006

set_option linter.missingDocs true

/-!
# MOD-004: Port direction semantics (`spec/11-modular-composition.md`)

MOD-004 is a behaviour requirement (kind B) over two abstract functions: the subnet builder
`SB : SubnetMake N A` of [MOD-006] and the instantiation function `Inst : InstFn N A` of
[MOD-010]. It says that a port's direction is metadata the two functions do not read: changing
only the directions of the ports changes neither whether a subnet builds, nor whether it
instantiates, nor what an instance holds apart from those directions. It also says that the
built definition keeps the declared direction of every port, so that the direction can be
queried.

The witness pair is the reference subnet builder `refSubnetBuild NB` (for every net builder `NB`)
and the reference instantiation `refInst Nm` (for every naming model `Nm`). Jointly with MOD-006,
line 1 needs no proof of its own: MOD-006 decides acceptance from port names and places alone
(`mod004_line1_of_mod006`). Wrong builders are killed: one that rejects an `Input` port whose
place no transition consumes from, one that rejects an `Output` port whose place a transition
consumes from, one that rejects two ports of one direction over one place (the sentence ruling
D35 dropped from MOD-003), one that moves the direction check to instantiation, one whose
instance correspondence depends on the directions, and one that forgets the declared direction.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N A : Type}

/-- A port without its direction: its name and the body place it exposes. Two port lists with the
same `undirected` image differ only in the directions of their ports. -/
def Port.undirected (q : Port N) : String × N := (q.name, q.place)

/-! ## MOD-004: Port Direction Semantics -/

requirement MOD_004
  id "MOD-004"
  title "Port Direction Semantics (advisory; arcs govern flow)"
  kind B
  scope "every subnet builder and every instantiation of a subnet definition"
  source verbatim "spec/11-modular-composition.md"
  quote "*When* two subnet declarations differ only in the directions of their ports, building the subnet definition *shall* succeed for both or fail for both."
        "*When* two subnet definitions differ only in the directions of their ports, `instantiate` with one prefix *shall* succeed for both or fail for both, and two successes *shall* give the same places, the same transitions, the same port and channel handles, and the same ports apart from their directions."
        "*When* building a subnet definition succeeds, the definition *shall* have a port with the name of each declared port, and each such port *shall* carry the declared direction."
  reading "For every naming model Nm (the renaming an instantiation uses, MOD-010; the lines do not read it), every subnet builder SB and every instantiation function Inst:"
          "if the port list ps has, port by port, the names and places of the ports of the subnet input S, then SB succeeds on S exactly when it succeeds on S with its ports replaced by ps;"
          "if ps has, port by port, the names and places of the ports of the subnet definition S, then for every prefix p Inst succeeds on S under p exactly when it succeeds on S with its ports replaced by ps, and two such successes I and J hold the same places (as a set), the same transition definitions (whole, with timing, priority, action and correspondence, in order), the same port handle and channel handle for every name, and the same names and places of ports (as a set);"
          "if SB builds the definition D from S, then for every port q that S declares, D has a port with the name of q, and every port of D with the name of q has the direction of q."
  assumes "Kind B at MUST, rulings D20 and R-MA7 (2): the requirement was SHOULD, but its normative sentence is the MUST NOT on rejecting a subnet for a direction-versus-arc mismatch, so its priority is raised to MUST. No runtime changes: Rust, Java and TypeScript read a port's direction only in the doc generators (render_port_channel_badges in rust/libpetri-docgen/src/subnet_header.rs, SubnetHeader.renderPortChannelBadges in java/src/main/java/org/libpetri/doclet/SubnetHeader.java) and in the verification harness of MOD-051 (verify_subnet_with_options in rust/libpetri-verification/src/harness.rs, SubnetDef.verify in java/src/main/java/org/libpetri/core/SubnetDef.java and in typescript/src/core/subnet-def.ts). In rust/libpetri-core/src the only uses of PortDirection are the declaration and the three port constructors (input_port, output_port and inout_port of SubnetDefBuilder in rust/libpetri-core/src/subnet_def.rs and of InterfaceBuilder in rust/libpetri-core/src/interface.rs); Java encodes the direction as the record class of the port (the sealed interface Interface.Port in java/src/main/java/org/libpetri/core/Interface.java), and no class of java/src/main/java/org/libpetri/core switches on it outside verify. Python rides on Rust."
          "Line 1 is the MUST NOT ('MUST NOT reject the subnet on direction-versus-arc mismatch') and AC2 and AC3 read for every builder: a subnet that builds with some directions builds with every other choice of directions, so no arc structure under a port can make its direction a reason to reject. It states acceptance only, not the message of a failure nor the built value: Rust keeps the ports of an interface in a hash map (the ports field of Interface in rust/libpetri-core/src/interface.rs), so two builds need not list ports in one order, and which offender a message names is MOD-006's line 7. Line 1 depends on ruling D35 (a), which dropped MOD-003's sentence that two ports of one direction over one body place are rejected: no runtime implements that check (SubnetDefBuilder::build in rust/libpetri-core/src/subnet_def.rs, SubnetDef.Builder.build in java/src/main/java/org/libpetri/core/SubnetDef.java, SubnetDefBuilder.build in typescript/src/core/subnet-def.ts), and a builder that does violates line 1 (MOD_004_forbids_sameDirCheck). Jointly with MOD-006 line 1 follows (mod004_line1_of_mod006), since MOD-006 decides acceptance from the body and the names and places of the ports; the line is kept so that MOD-004 says it on its own."
          "Line 2 states for instantiate what line 1 states for the subnet builder, and adds what an instance holds: its places as a set (Rust collects them through a hash map, rename_net in rust/libpetri-core/src/rewriter.rs), its transition definitions in order and whole (arcs, timing, priority, action and the declared-to-actual correspondence of MOD-031; no runtime's rewriter reads a direction, rebuild_with_name and build_local_name_map in rust/libpetri-core/src/rewriter.rs, so an instantiation that builds a correspondence from the directions is rejected, MOD_004_forbids_inputCorr), its port and channel handles name by name (MOD-011), and its interface ports as a set of names and places. It does not compare the prefix nor the messages of failures. The instance's interface ports carry the definition's directions in the reference (refInst keeps the ports); that the instance keeps them is not stated, since MOD-004 AC1 asks only that the direction be queryable on the definition's port and the instance handle of MOD-011 returns a place without a direction (Instance::port in rust/libpetri-core/src/instance.rs)."
          "Line 3 is AC1 (direction metadata is preserved and queryable via the port handle): the port handle is the interface's port, looked up by name (the test interface_builder_basic_ports in rust/libpetri-core/src/interface.rs tests exactly this). The line asks that a port of every declared name exists and carries the declared direction, which the lookup by name then returns. It compares ports by name and not as a list, since Rust's interface is a hash map. A declaration with two ports of one name never builds (MOD-006 line 3), so line 3 asks nothing contradictory of a builder that meets MOD-006. That the definition holds exactly the declared ports, channels and body is MOD-001's line; a builder that stores every port as InOut meets lines 1 and 2 and is killed by line 3 alone (MOD_004_mutant_noDirection_killed)."
          "AC2 (a subnet whose Output port place is also written internally by transitions is accepted at build) and AC3 (a subnet whose Input port place is also read internally by transitions is accepted at build) are exercised on the reference by MOD_004_nonvacuous: the subnet relay, whose Output port place out is written by take and consumed by drain and whose Input port place in is read by peek and consumed by take, builds, and so does the same subnet with the two directions swapped. For every builder that meets MOD-006 over the reference net builder, relay builds with every choice of directions (mod004_relay_builds). The block alone does not force a build: a builder that rejects everything meets lines 1 to 3, and acceptance is MOD-006's line 6."
          "AC4 (where a warning channel exists, an obvious mismatch MAY emit a warning but MUST NOT raise an error) is line 1 for the error half: MOD_004_nonvacuous builds watch, an Input port whose place no transition consumes from, and the same subnet with an Output port that no transition produces into. The warning half is not stated: no runtime emits such a warning (no warn call in the subnet or interface sources of any language), and a warning channel is not modelled. The sentence 'Implementations MAY emit a build-time warning when declared direction conflicts with the arc structure' is a MAY with no runtime witness, recorded as kind N in the plan."
          "The sentence that direction does not constrain arc flow at run time ('Actual token flow at run time is governed exclusively by arcs declared per CORE-030..CORE-035') is line 2's 'the same transitions': an instance's transitions, and so its firing (MOD-010's mod010_firesAsBody), do not depend on any direction. That composition does not read direction either (prose of the reworded first sentence) is a property of the composition functions of MOD-020 to MOD-025 and is not stated here; the composition wave states their lines on names and places only."
  signoff "2026-11-13 2717b76b98d3dc75 ai"
  statement : ∀ {N A : Type}, Naming N → SubnetMake N A → InstFn N A → Prop :=
    fun {N A} _Nm SB Inst =>
      (∀ (S : SubnetIn N A) (ps : List (Port N)),
        S.ports.map Port.undirected = ps.map Port.undirected →
        ((∃ D, SB S = .ok D) ↔ ∃ D, SB { S with ports := ps } = .ok D)) ∧
      (∀ (S : SubnetDef N A) (ps : List (Port N)) p,
        S.ports.map Port.undirected = ps.map Port.undirected →
        ((∃ I, Inst S p = .ok I) ↔ ∃ I, Inst { S with ports := ps } p = .ok I) ∧
        ∀ I J, Inst S p = .ok I → Inst { S with ports := ps } p = .ok J →
          (∀ x, x ∈ I.places ↔ x ∈ J.places) ∧
          I.defs = J.defs ∧
          (∀ n, I.port n = J.port n) ∧ (∀ n, I.chan n = J.chan n) ∧
          ∀ k, k ∈ I.iface.map Port.undirected ↔ k ∈ J.iface.map Port.undirected) ∧
      (∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q ∈ S.ports,
        (∃ r ∈ D.ports, r.name = q.name) ∧ ∀ r ∈ D.ports, r.name = q.name → r.dir = q.dir)

/- The pinned readable form of MOD-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_004 : {N A : Type} → Naming N → SubnetMake N A → InstFn N A → Prop :=
fun {N A} _Nm SB Inst =>
  (∀ (S : SubnetIn N A) (ps : List (Port N)),
      List.map Port.undirected S.ports = List.map Port.undirected ps →
        ((∃ D, SB S = Except.ok D) ↔
          ∃ D,
            SB
                { name := S.name, places := S.places, defs := S.defs, terminals := S.terminals, ports := ps,
                  chans := S.chans } =
              Except.ok D)) ∧
    (∀ (S : SubnetDef N A) (ps : List (Port N)) (p : String),
        List.map Port.undirected S.ports = List.map Port.undirected ps →
          ((∃ I, Inst S p = Except.ok I) ↔
              ∃ I,
                Inst
                    { name := S.name, places := S.places, defs := S.defs, terminals := S.terminals, ports := ps,
                      chans := S.chans }
                    p =
                  Except.ok I) ∧
            ∀ (I J : Instance N A),
              Inst S p = Except.ok I →
                Inst
                      { name := S.name, places := S.places, defs := S.defs, terminals := S.terminals, ports := ps,
                        chans := S.chans }
                      p =
                    Except.ok J →
                  (∀ (x : N), x ∈ I.places ↔ x ∈ J.places) ∧
                    I.defs = J.defs ∧
                      (∀ (n : String), I.port n = J.port n) ∧
                        (∀ (n : String), I.chan n = J.chan n) ∧
                          ∀ (k : String × N),
                            k ∈ List.map Port.undirected I.iface ↔ k ∈ List.map Port.undirected J.iface) ∧
      ∀ (S : SubnetIn N A) (D : SubnetDef N A),
        SB S = Except.ok D →
          ∀ q ∈ S.ports, (∃ r ∈ D.ports, r.name = q.name) ∧ ∀ r ∈ D.ports, r.name = q.name → r.dir = q.dir
-/
#guard_msgs in #print MOD_004

/-! ### The three lines, named (for the mutants) -/

section Lines

/-- Line 1 of MOD-004: whether a subnet builds does not depend on the directions of its ports. -/
def mod004_line1 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) (ps : List (Port N)),
    S.ports.map Port.undirected = ps.map Port.undirected →
    ((∃ D, SB S = .ok D) ↔ ∃ D, SB { S with ports := ps } = .ok D)

/-- Line 2 of MOD-004: whether and to what a subnet definition instantiates does not depend on
the directions of its ports, apart from those directions. -/
def mod004_line2 (Inst : InstFn N A) : Prop :=
  ∀ (S : SubnetDef N A) (ps : List (Port N)) p,
    S.ports.map Port.undirected = ps.map Port.undirected →
    ((∃ I, Inst S p = .ok I) ↔ ∃ I, Inst { S with ports := ps } p = .ok I) ∧
    ∀ I J, Inst S p = .ok I → Inst { S with ports := ps } p = .ok J →
      (∀ x, x ∈ I.places ↔ x ∈ J.places) ∧
      I.defs = J.defs ∧
      (∀ n, I.port n = J.port n) ∧ (∀ n, I.chan n = J.chan n) ∧
      ∀ k, k ∈ I.iface.map Port.undirected ↔ k ∈ J.iface.map Port.undirected

/-- Line 3 of MOD-004: a built definition keeps the declared direction of every port. -/
def mod004_line3 (SB : SubnetMake N A) : Prop :=
  ∀ (S : SubnetIn N A) D, SB S = .ok D → ∀ q ∈ S.ports,
    (∃ r ∈ D.ports, r.name = q.name) ∧ ∀ r ∈ D.ports, r.name = q.name → r.dir = q.dir

/-- MOD-004 is its three lines. -/
theorem mod004_iff (Nm : Naming N) (SB : SubnetMake N A) (Inst : InstFn N A) :
    MOD_004 Nm SB Inst ↔ mod004_line1 SB ∧ mod004_line2 Inst ∧ mod004_line3 SB :=
  Iff.rfl

end Lines

/-! ### Port lists that differ only in directions -/

section Undirected

/-- Two port lists that differ only in directions have the same port names, in order. -/
theorem Port.names_of_undirected {ps rs : List (Port N)}
    (h : ps.map Port.undirected = rs.map Port.undirected) :
    ps.map (·.name) = rs.map (·.name) := by
  have := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def, Port.undirected] using this

/-- Two port lists that differ only in directions expose the same places, in order. -/
theorem Port.places_of_undirected {ps rs : List (Port N)}
    (h : ps.map Port.undirected = rs.map Port.undirected) :
    ps.map (·.place) = rs.map (·.place) := by
  have := congrArg (List.map Prod.snd) h
  simpa [List.map_map, Function.comp_def, Port.undirected] using this

/-- A property of every port's place holds of one list exactly when it holds of a list that
differs only in directions. -/
theorem Port.forall_place_of_undirected {ps rs : List (Port N)}
    (h : ps.map Port.undirected = rs.map Port.undirected) (P : N → Prop) :
    (∀ q ∈ ps, P q.place) ↔ ∀ q ∈ rs, P q.place := by
  have hp := Port.places_of_undirected h
  constructor
  · intro hq r hr
    have : r.place ∈ ps.map (·.place) := hp ▸ List.mem_map_of_mem hr
    obtain ⟨q, hq', he⟩ := List.mem_map.1 this
    exact he ▸ hq q hq'
  · intro hr q hq
    have : q.place ∈ rs.map (·.place) := hp ▸ List.mem_map_of_mem hq
    obtain ⟨r, hr', he⟩ := List.mem_map.1 this
    exact he ▸ hr r hr'

/-- Two ports of a list with pairwise distinct names that carry one name are one port. -/
theorem Port.eq_of_name {N : Type} :
    ∀ {ps : List (Port N)}, (ps.map (·.name)).Nodup →
      ∀ {q r : Port N}, q ∈ ps → r ∈ ps → q.name = r.name → q = r
  | [], _, _, _, hq, _, _ => nomatch hq
  | x :: xs, hnd, q, r, hq, hr, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hq with rfl | hq'
    · rcases List.mem_cons.1 hr with rfl | hr'
      · rfl
      · exact absurd (he ▸ List.mem_map_of_mem hr') hnd.1
    · rcases List.mem_cons.1 hr with rfl | hr'
      · exact absurd (he ▸ List.mem_map_of_mem hq') hnd.1
      · exact Port.eq_of_name hnd.2 hq' hr' he

/-- The walk of MOD-006's port and channel checks gives the same result on two lists whose
entries agree on everything the walk reads. -/
theorem checkList_congr {α β : Type} {key : α → String} {ok : α → Prop} [DecidablePred ok]
    {dup bad : α → String} (k : α → β)
    (hk : ∀ x y, k x = k y → key x = key y ∧ (ok x ↔ ok y) ∧ dup x = dup y ∧ bad x = bad y) :
    ∀ {seen : List String} {xs ys : List α}, xs.map k = ys.map k →
      checkList key ok dup bad seen xs = checkList key ok dup bad seen ys
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | seen, x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hkey, hok, hdup, hbad⟩ := hk x y h.1
    have ih := checkList_congr (key := key) (ok := ok) (dup := dup) (bad := bad) k hk
      (seen := key y :: seen) h.2
    unfold checkList
    rw [hkey, hdup, hbad, ih]
    by_cases hs : key y ∈ seen
    · rw [if_pos hs, if_pos hs]
    · by_cases ho : ok y
      · rw [if_neg hs, if_neg hs, if_pos (hok.2 ho), if_pos ho]
      · rw [if_neg hs, if_neg hs, if_neg (fun h' => ho (hok.1 h')), if_neg ho]

/-- Looking a port up by name and mapping its place gives the same result on two lists that
differ only in directions. -/
theorem Port.find_of_undirected {β : Type} (f : N → β) (n : String) :
    ∀ {ps rs : List (Port N)}, ps.map Port.undirected = rs.map Port.undirected →
      (ps.find? (·.name == n)).map (fun q => f q.place) =
        (rs.find? (·.name == n)).map (fun q => f q.place)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | q :: ps, r :: rs, h => by
    simp only [List.map_cons, List.cons.injEq, Port.undirected, Prod.mk.injEq] at h
    obtain ⟨⟨hn, hp⟩, ht⟩ := h
    simp only [List.find?_cons, hn]
    split
    · simp [hp]
    · exact Port.find_of_undirected f n ht

/-- A success of a mapped result is a success of the result. -/
theorem except_map_ok_iff {ε α β : Type} (f : α → β) (x : Except ε α) :
    (∃ y, x.map f = .ok y) ↔ ∃ y, x = .ok y := by
  cases x <;> simp [Except.map]

end Undirected

/-! ### The reference -/

section Ref

variable [DecidableEq N] [ToString N]

/-- The reference port check reads only the names and places of the ports. -/
theorem refPortCheck_undirected (S : SubnetIn N A) (ps : List (Port N))
    (h : S.ports.map Port.undirected = ps.map Port.undirected) (b : BuiltNet N A) :
    refPortCheck { S with ports := ps } b = refPortCheck S b := by
  unfold refPortCheck
  refine (checkList_congr Port.undirected (fun x y hxy => ?_) h).symm
  simp only [Port.undirected, Prod.mk.injEq] at hxy
  obtain ⟨hn, hp⟩ := hxy
  refine ⟨hn, by rw [hp], ?_, ?_⟩
  · simp only [dupPortMsg, hn]
  · simp only [portPlaceMsg, hn, hp]

/-- **The reference subnet builder does not read directions.** Changing only the directions of
the ports gives the same result, with the new ports in the built definition. -/
theorem refSubnetBuild_undirected (NB : NetBuilder (defsTB N A)) (S : SubnetIn N A)
    (ps : List (Port N)) (h : S.ports.map Port.undirected = ps.map Port.undirected) :
    refSubnetBuild NB { S with ports := ps } =
      (refSubnetBuild NB S).map (fun D => { D with ports := ps }) := by
  have hb : ({ S with ports := ps } : SubnetIn N A).body = S.body := rfl
  have hc : ∀ b, refChanCheck ({ S with ports := ps } : SubnetIn N A) b = refChanCheck S b :=
    fun _ => rfl
  unfold refSubnetBuild subnetVia
  rw [hb]
  cases NB S.body with
  | error e => rfl
  | ok b =>
    simp only [refPortCheck_undirected S ps h b, hc b]
    cases refPortCheck S b with
    | some m => rfl
    | none => cases refChanCheck S b <;> rfl

/-- A success of the reference subnet builder keeps the declared ports, and their names are
pairwise distinct. -/
theorem refSubnetBuild_ok_ports {NB : NetBuilder (defsTB N A)} {S : SubnetIn N A}
    {D : SubnetDef N A} (h : refSubnetBuild NB S = .ok D) :
    D.ports = S.ports ∧ (S.ports.map (·.name)).Nodup := by
  unfold refSubnetBuild subnetVia at h
  split at h
  · cases h
  · rename_i b _
    split at h
    · cases h
    · rename_i hp
      split at h
      · cases h
      · cases h
        exact ⟨rfl, ((refPortCheck_none S b).1 hp).2⟩

/-- Line 1 for the reference subnet builder. -/
theorem refSubnetBuild_line1 (NB : NetBuilder (defsTB N A)) : mod004_line1 (refSubnetBuild NB) := by
  intro S ps h
  rw [refSubnetBuild_undirected NB S ps h, except_map_ok_iff]

/-- Line 3 for the reference subnet builder. -/
theorem refSubnetBuild_line3 (NB : NetBuilder (defsTB N A)) : mod004_line3 (refSubnetBuild NB) := by
  intro S D hD q hq
  obtain ⟨hp, hnd⟩ := refSubnetBuild_ok_ports hD
  rw [hp]
  exact ⟨⟨q, hq, rfl⟩, fun r hr he => by rw [Port.eq_of_name hnd hr hq he]⟩

end Ref

/-- The reference instantiation succeeds exactly at a valid prefix on a body without terminal
places. -/
theorem refInst_ok_iff (Nm : Naming N) (S : SubnetDef N A) (p : String) :
    (∃ I, refInst Nm S p = .ok I) ↔ ValidPrefix p ∧ S.terminals = [] := by
  constructor
  · rintro ⟨I, hI⟩
    obtain ⟨hp, ht, -⟩ := refInst_ok hI
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨_, refInst_valid Nm S hp ht⟩

/-- Line 2 for the reference instantiation. -/
theorem refInst_line2 (Nm : Naming N) : mod004_line2 (refInst (A := A) Nm) := by
  intro S ps p h
  refine ⟨by rw [refInst_ok_iff, refInst_ok_iff], fun I J hI hJ => ?_⟩
  obtain ⟨hp, ht, -⟩ := refInst_ok hI
  rw [refInst_valid Nm S hp ht] at hI
  rw [refInst_valid Nm { S with ports := ps } hp ht] at hJ
  cases hI; cases hJ
  refine ⟨fun _ => Iff.rfl, rfl, fun n => ?_, fun _ => rfl, fun k => ?_⟩
  · exact Port.find_of_undirected (Nm.pre p) n h
  · show k ∈ S.ports.map Port.undirected ↔ k ∈ ps.map Port.undirected
    rw [h]

/-- The reference subnet builder over every net builder and the reference instantiation under
every naming model satisfy MOD-004. -/
theorem mod004_reference_all {N A : Type} [DecidableEq N] [ToString N]
    (NB : NetBuilder (defsTB N A)) (Nm : Naming N) :
    MOD_004 Nm (refSubnetBuild NB) (refInst Nm) :=
  ⟨refSubnetBuild_line1 NB, refInst_line2 Nm, refSubnetBuild_line3 NB⟩

/-- ✓ The reference subnet builder and the reference instantiation satisfy MOD-004 for every
naming model: neither reads a port's direction, and a built definition keeps the declared ports.
So the subnet `relay` builds whether its port `in` is an `Input` or an `Output` port, and
instantiating it under `r1` gives the same renamed places and transitions either way. -/
@[evidence holds MOD_004]
theorem MOD_004_reference {N A : Type} [DecidableEq N] [ToString N] (Nm : Naming N) :
    MOD_004 Nm (refSubnetBuild refNetBuild) (refInst (A := A) Nm) :=
  mod004_reference_all refNetBuild Nm

/-! ### Joint with MOD-006: line 1 follows -/

/-- Under MOD-006 a subnet builds exactly when the net builder builds the body, every port exposes
a place of the built body, every channel names a transition of it, and the port names and the
channel names are each pairwise distinct. -/
theorem mod006_accepts_iff {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (h : MOD_006 NB SB) (S : SubnetIn N A) :
    (∃ D, SB S = .ok D) ↔ ∃ b, NB S.body = .ok b ∧ (∀ q ∈ S.ports, q.place ∈ b.places) ∧
      (∀ c ∈ S.chans, c.trans ∈ b.trans.map (·.core.name)) ∧
      (S.ports.map (·.name)).Nodup ∧ (S.chans.map (·.name)).Nodup := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  constructor
  · rintro ⟨D, hD⟩
    have nf : ∀ msg, SB S ≠ .error msg := fun msg he => by rw [hD] at he; cases he
    cases hb : NB S.body with
    | error e =>
      obtain ⟨m, hm⟩ := h5 S e hb
      exact absurd hm (nf m)
    | ok b =>
      refine ⟨b, rfl, fun q hq => ?_, fun c hc => ?_, ?_, ?_⟩
      · by_contra hn
        obtain ⟨m, hm⟩ := h1 S b hb q hq hn
        exact nf m hm
      · by_contra hn
        obtain ⟨m, hm⟩ := h2 S b hb c hc hn
        exact nf m hm
      · by_contra hn
        obtain ⟨m, hm⟩ := h3 S hn
        exact nf m hm
      · by_contra hn
        obtain ⟨m, hm⟩ := h4 S hn
        exact nf m hm
  · rintro ⟨b, hb, hp, hc, hpn, hcn⟩
    exact h6 S b hb hp hc hpn hcn

/-- **Line 1 follows from MOD-006.** MOD-006 decides whether a subnet builds from its body and
the names and places of its ports and channels, never from a direction; so every subnet builder
that meets MOD-006, for any net builder, also meets line 1 of MOD-004. -/
theorem mod004_line1_of_mod006 {NB : NetBuilder (defsTB N A)} {SB : SubnetMake N A}
    (h : MOD_006 NB SB) : mod004_line1 SB := by
  intro S ps hu
  rw [mod006_accepts_iff h, mod006_accepts_iff h]
  have hb : ({ S with ports := ps } : SubnetIn N A).body = S.body := rfl
  rw [hb]
  refine exists_congr fun b => and_congr Iff.rfl (and_congr ?_ (and_congr Iff.rfl ?_))
  · exact Port.forall_place_of_undirected hu (· ∈ b.places)
  · show (S.ports.map (·.name)).Nodup ∧ _ ↔ (ps.map (·.name)).Nodup ∧ _
    rw [Port.names_of_undirected hu]

/-! ### Examples -/

/-- `peek`: a read arc on `in`, the output place `seen`. -/
def mod004_peek : CDef String Unit :=
  { core := ⟨"peek", [], [], ["in"], []⟩, out := some (.place "seen"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- `take`: an input arc on `in`, the output place `out`. -/
def mod004_take : CDef String Unit :=
  { core := ⟨"take", [⟨"in", .one⟩], [], [], []⟩, out := some (.place "out"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- `drain`: an input arc on `out`, the output place `seen`. -/
def mod004_drain : CDef String Unit :=
  { core := ⟨"drain", [⟨"out", .one⟩], [], [], []⟩, out := some (.place "seen"),
    timing := .immediate, priority := 0, action := .passthrough }

/-- The subnet `relay` with the port `in` of direction `di` on the place `in` and the port `out`
of direction `do` on the place `out`. Inside, `peek` reads `in`, `take` moves a token from `in`
to `out`, and `drain` consumes from `out`. -/
def mod004_relayD (di dout : Dir) : SubnetIn String Unit :=
  { name := "relay", places := ["in", "out", "seen"],
    defs := [mod004_peek, mod004_take, mod004_drain],
    ports := [⟨"in", di, "in"⟩, ⟨"out", dout, "out"⟩], chans := [] }

/-- The subnet `relay` as declared: `in` an `Input` port, `out` an `Output` port. Its `Output`
port's place is written by `take` and consumed by `drain` (AC2); its `Input` port's place is read
by `peek` (AC3). -/
def mod004_relay : SubnetIn String Unit := mod004_relayD .input .output

/-- The subnet `watch` with the port `in` of direction `d` on the place `in`, which `peek` only
reads: no transition consumes from it and none produces into it. -/
def mod004_watchD (d : Dir) : SubnetIn String Unit :=
  { name := "watch", places := ["in", "seen"], defs := [mod004_peek],
    ports := [⟨"in", d, "in"⟩], chans := [] }

/-- The definition `relay` as the reference builds it (its places are those the body declares
and its arcs name). -/
def mod004_relayDefD (di dout : Dir) : SubnetDef String Unit :=
  { name := "relay", places := ["in", "out", "seen"],
    defs := [mod004_peek, mod004_take, mod004_drain],
    ports := [⟨"in", di, "in"⟩, ⟨"out", dout, "out"⟩], chans := [] }

/-- ✓ Every line of MOD-004 is exercised by the reference over the reference net builder. The
subnet `relay` builds: its `Output` port `out` sits on a place that `take` writes and `drain`
consumes from (AC2), and its `Input` port `in` on a place that `peek` reads (AC3). The built
definition keeps both ports with their directions (line 3, AC1). With the two directions swapped
it still builds (line 1). The subnet `watch`, whose `Input` port has no consumer, builds, and so
does `watch` with an `Output` port that nothing produces into (AC4). Instantiating `relay` under
`r1` gives the port handle `out` as `r1/out`, and so does the swapped `relay` (line 2). -/
@[evidence nonvacuous MOD_004]
theorem MOD_004_nonvacuous :
    (∃ D, refSubnetBuild refNetBuild mod004_relay = .ok D ∧
      D.ports = [⟨"in", .input, "in"⟩, ⟨"out", .output, "out"⟩]) ∧
    (∃ D, refSubnetBuild refNetBuild (mod004_relayD .output .input) = .ok D) ∧
    (∃ D, refSubnetBuild refNetBuild (mod004_watchD .input) = .ok D) ∧
    (∃ D, refSubnetBuild refNetBuild (mod004_watchD .output) = .ok D) ∧
    (refInst strNaming (mod004_relayDefD .input .output) "r1").map (·.port "out") =
      .ok (some "r1/out") ∧
    (refInst strNaming (mod004_relayDefD .output .input) "r1").map (·.port "out") =
      .ok (some "r1/out") :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, rfl, rfl⟩

/-- **AC2 and AC3 for every builder that meets MOD-006.** Every subnet builder that meets MOD-006
over the reference net builder builds `relay` with every choice of directions for its two ports:
an `Output` port place that is written and consumed inside, or an `Input` port place that is read
inside, is no reason to reject. -/
theorem mod004_relay_builds {SB : SubnetMake String Unit} (h : MOD_006 refNetBuild SB)
    (di dout : Dir) : ∃ D, SB (mod004_relayD di dout) = .ok D := by
  cases di <;> cases dout <;>
    exact h.2.2.2.2.2.1 _ _ rfl
      (by intro q hq; simp [mod004_relayD] at hq; rcases hq with rfl | rfl <;> decide)
      (by intro c hc; simp [mod004_relayD] at hc) (by decide) (by decide)

/-! ### Wrong builders and instantiations -/

section Wrong

variable [DecidableEq N] [ToString N]

/-- Some transition definition has an input arc on `x`. -/
def mod004_consumed (defs : List (CDef N A)) (x : N) : Bool :=
  defs.any fun d => d.core.inputs.any fun i => decide (i.place = x)

/-- Some `Input` port's place has no transition consuming from it (AC4's "obvious mismatch"). -/
def mod004_unconsumedInput (ports : List (Port N)) (defs : List (CDef N A)) : Bool :=
  ports.any fun q => decide (q.dir = .input) && !mod004_consumed defs q.place

/-- Some `Output` port's place has a transition consuming from it. -/
def mod004_consumedOutput (ports : List (Port N)) (defs : List (CDef N A)) : Bool :=
  ports.any fun q => decide (q.dir = .output) && mod004_consumed defs q.place

/-- Two ports of different names and one direction expose one place: the case MOD-003 rejected
before ruling D35 (a). -/
def mod004_sameDirShared (ports : List (Port N)) : Bool :=
  ports.any fun q => ports.any fun r =>
    decide (q.name ≠ r.name ∧ q.dir = r.dir ∧ q.place = r.place)

/-- A subnet builder that rejects when `bad` holds of the declaration and is the reference
otherwise. -/
def mod004_guardSB (bad : SubnetIn N A → Bool) (NB : NetBuilder (defsTB N A)) :
    SubnetMake N A := fun S =>
  if bad S then .error "direction does not match the arcs" else refSubnetBuild NB S

/-- An instantiation that rejects when `bad` holds of the definition and is the reference
otherwise. -/
def mod004_guardInst (bad : SubnetDef N A → Bool) (Nm : Naming N) : InstFn N A := fun S p =>
  if bad S then .error "direction does not match the arcs" else refInst Nm S p

/-- A subnet builder that builds as the reference and stores every port as `InOut`. -/
def mod004_forgetDirSB (NB : NetBuilder (defsTB N A)) : SubnetMake N A := fun S =>
  (refSubnetBuild NB S).map fun D => { D with ports := D.ports.map fun q => { q with dir := .inout } }

/-- A guarded builder meets line 3: what it builds, the reference builds. -/
theorem mod004_guardSB_line3 (bad : SubnetIn N A → Bool) (NB : NetBuilder (defsTB N A)) :
    mod004_line3 (mod004_guardSB bad NB) := by
  intro S D hD
  unfold mod004_guardSB at hD
  split at hD
  · cases hD
  · exact refSubnetBuild_line3 NB S D hD

end Wrong

/-- ✗ A builder that rejects an `Input` port whose place no transition consumes from violates
MOD-004 (line 1, AC4): it rejects `watch`, whose `Input` port `in` is only read by `peek`, but
builds the same subnet with `in` declared an `Output` port. -/
@[evidence forbids MOD_004]
theorem MOD_004_forbids_unconsumedInput :
    ¬ MOD_004 strNaming (mod004_guardSB (fun S => mod004_unconsumedInput S.ports S.defs) refNetBuild)
      (refInst (A := Unit) strNaming) := by
  intro h
  have := (h.1 (mod004_watchD .input) [⟨"in", .output, "in"⟩] rfl).2 ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := this
  cases hD

/-- ✗ A builder that rejects an `Output` port whose place a transition consumes from violates
MOD-004 (line 1, AC2): it rejects `relay`, whose `Output` port place `out` is consumed by `drain`,
but builds `relay` with `out` declared an `InOut` port. -/
@[evidence forbids MOD_004]
theorem MOD_004_forbids_consumedOutput :
    ¬ MOD_004 strNaming (mod004_guardSB (fun S => mod004_consumedOutput S.ports S.defs) refNetBuild)
      (refInst (A := Unit) strNaming) := by
  intro h
  have := (h.1 mod004_relay [⟨"in", .input, "in"⟩, ⟨"out", .inout, "out"⟩] rfl).2 ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := this
  cases hD

/-- The subnet `relay` with two `Input` ports, `a` and `b`, both on the place `in`. -/
def mod004_twoInputs : SubnetIn String Unit :=
  { mod004_relay with ports := [⟨"a", .input, "in"⟩, ⟨"b", .input, "in"⟩] }

/-- ✗ A builder that rejects two ports of one direction over one place, as MOD-003 asked before
ruling D35 (a), violates MOD-004 (line 1): it rejects `relay` with two `Input` ports `a` and `b`
on the place `in`, but builds it once `b` is declared an `Output` port. -/
@[evidence forbids MOD_004]
theorem MOD_004_forbids_sameDirCheck :
    ¬ MOD_004 strNaming (mod004_guardSB (fun S => mod004_sameDirShared S.ports) refNetBuild)
      (refInst (A := Unit) strNaming) := by
  intro h
  have := (h.1 mod004_twoInputs [⟨"a", .input, "in"⟩, ⟨"b", .output, "in"⟩] rfl).2 ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := this
  cases hD

/-- The correspondence of `d` without the entries whose declared place an `Input` port exposes. -/
def mod004_dropInputCorr [DecidableEq N] (ports : List (Port N)) (d : CDef N A) : CDef N A :=
  { d with corr := d.corr.map (List.filter fun e =>
      !(ports.any fun q => decide (q.dir = .input) && decide (q.place = e.1))) }

/-- An instantiation that renames as the reference does but leaves the places of `Input` ports out
of each transition's correspondence, as if composition rebound them later. -/
def mod004_inputCorrInst [DecidableEq N] (Nm : Naming N) : InstFn N A := fun S p =>
  (refInst Nm S p).map fun I => { I with defs := I.defs.map (mod004_dropInputCorr S.ports) }

/-- ✗ An instantiation whose correspondence depends on the port directions violates MOD-004
(line 2): `relay` with `in` an `Input` port and the same `relay` with `in` an `Output` port
instantiate under `r1` with the same places, arcs and handles, but `take`, which names `in`, loses
the entry for `in` in the first. Its arcs, names, timing, priority and action are the
reference's, so only the whole-definition comparison rejects it. -/
@[evidence forbids MOD_004]
theorem MOD_004_forbids_inputCorr :
    ¬ MOD_004 strNaming (refSubnetBuild (A := Unit) (refNetBuild (N := String)))
      (mod004_inputCorrInst strNaming) := by
  intro h
  have := (h.2.1 (mod004_relayDefD .input .output) [⟨"in", .output, "in"⟩, ⟨"out", .input, "out"⟩]
    "r1" rfl).2 _ _ rfl rfl
  have := congrArg (List.map (·.corr)) this.2.1
  revert this; decide

/-! ### Mutant: line 1 dropped (direction may decide acceptance) -/

/-- Mutant reading: MOD-004 without line 1, so a subnet builder may reject on a
direction-versus-arc mismatch. -/
def MOD_004_mutant_noBuildLine (_Nm : Naming N) (SB : SubnetMake N A) (Inst : InstFn N A) : Prop :=
  mod004_line2 Inst ∧ mod004_line3 SB

/-- The builder that rejects an `Input` port without a consumer kills the mutant: it keeps every
declared direction (line 3), and the reference instantiation meets line 2, but it rejects `watch`
and builds `watch` with an `Output` port (line 1). -/
@[evidence mutant MOD_004]
theorem MOD_004_mutant_noBuildLine_killed :
    MOD_004_mutant_noBuildLine strNaming
        (mod004_guardSB (fun S => mod004_unconsumedInput S.ports S.defs) refNetBuild)
        (refInst (A := Unit) strNaming) ∧
      ¬ MOD_004 strNaming (mod004_guardSB (fun S => mod004_unconsumedInput S.ports S.defs) refNetBuild)
        (refInst (A := Unit) strNaming) :=
  ⟨⟨refInst_line2 strNaming, mod004_guardSB_line3 _ refNetBuild⟩,
    MOD_004_forbids_unconsumedInput⟩

/-! ### Mutant: line 2 dropped (direction may decide instantiation) -/

/-- Mutant reading: MOD-004 without line 2, so an instantiation may read directions. -/
def MOD_004_mutant_noInstLine (_Nm : Naming N) (SB : SubnetMake N A) (_Inst : InstFn N A) : Prop :=
  mod004_line1 SB ∧ mod004_line3 SB

/-- The definition `watch` with the port `in` of direction `d`. -/
def mod004_watchDefD (d : Dir) : SubnetDef String Unit :=
  { name := "watch", places := ["in", "seen"], defs := [mod004_peek],
    ports := [⟨"in", d, "in"⟩], chans := [] }

/-- The instantiation that moves the direction check to `instantiate` kills the mutant: the
reference builder meets lines 1 and 3, but this instantiation rejects `watch` under `w1`, whose
`Input` port `in` has no consumer, and instantiates `watch` with an `Output` port (line 2). -/
@[evidence mutant MOD_004]
theorem MOD_004_mutant_noInstLine_killed :
    MOD_004_mutant_noInstLine strNaming (refSubnetBuild (A := Unit) (refNetBuild (N := String)))
        (mod004_guardInst (fun S => mod004_unconsumedInput S.ports S.defs) strNaming) ∧
      ¬ MOD_004 strNaming (refSubnetBuild (A := Unit) (refNetBuild (N := String)))
        (mod004_guardInst (fun S => mod004_unconsumedInput S.ports S.defs) strNaming) := by
  refine ⟨⟨refSubnetBuild_line1 _, refSubnetBuild_line3 _⟩, fun h => ?_⟩
  have := ((h.2.1 (mod004_watchDefD .input) [⟨"in", .output, "in"⟩] "w1" rfl).1).2 ⟨_, rfl⟩
  obtain ⟨I, hI⟩ := this
  cases hI

/-! ### Mutant: line 3 dropped (direction may be forgotten) -/

/-- Mutant reading: MOD-004 without line 3, so a built definition need not keep the declared
direction. -/
def MOD_004_mutant_noDirection (_Nm : Naming N) (SB : SubnetMake N A) (Inst : InstFn N A) : Prop :=
  mod004_line1 SB ∧ mod004_line2 Inst

/-- The builder that stores every port as `InOut` kills the mutant: it builds exactly what the
reference builds, so it meets line 1, and the reference instantiation meets line 2, but the built
`relay` has its port `in` as `InOut`, not as the declared `Input` (line 3, AC1). -/
@[evidence mutant MOD_004]
theorem MOD_004_mutant_noDirection_killed :
    MOD_004_mutant_noDirection strNaming (mod004_forgetDirSB (A := Unit) (refNetBuild (N := String)))
        (refInst strNaming) ∧
      ¬ MOD_004 strNaming (mod004_forgetDirSB (A := Unit) (refNetBuild (N := String))) (refInst strNaming) := by
  refine ⟨⟨fun S ps hu => ?_, refInst_line2 strNaming⟩, fun h => ?_⟩
  · simp only [mod004_forgetDirSB, except_map_ok_iff]
    exact refSubnetBuild_line1 _ S ps hu
  · have hD : mod004_forgetDirSB refNetBuild mod004_relay = .ok _ := rfl
    have := (h.2.2 mod004_relay _ hD ⟨"in", .input, "in"⟩ (List.mem_cons_self ..)).2
      ⟨"in", .inout, "in"⟩ (List.mem_cons_self ..) rfl
    cases this

end Libpetri.Spec
