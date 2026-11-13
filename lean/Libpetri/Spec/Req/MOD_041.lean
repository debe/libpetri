import Libpetri.Spec.Registry
import Libpetri.Spec.Req.MOD_040
import Libpetri.Spec.Text.MOD_041

set_option linter.missingDocs true

/-!
# MOD-041: Debug protocol subnet instances (`spec/11-modular-composition.md`)

MOD-041 is a pure-function requirement (kind F) over an abstract debug view
`V : Mod041.SubnetView`: from the place and transition names of a net it computes the list of
subnet instance descriptors of the `Subscribed` response, and the `instancePrefix` field of each
`PlaceInfo` and `TransitionInfo`. Under ruling D71 (a) everything is a function of the names of
the flat net: a descriptor exists for each distinct instance prefix (the part of a node name
before its last `/`) that some node carries, it lists the transitions and the listed places
(those an arc or output specification names) under that prefix, its parent is the instance prefix
of its own prefix, and a node's `instancePrefix` is the instance prefix of its name.

Names are strings, and the instance prefix of a name is the export glossary's `instancePrefix`
(`Spec/GlossaryExportCluster.lean`), the function [MOD-040]'s helper and the cluster key of
[EXP-016] are stated with; it is written over the characters of a name, so the examples close by
`decide`. So a node's `instancePrefix` field and [MOD-040]'s helper agree on every node
(`mod041_nodePrefix_eq_helper`). The witness is `Mod041.refView`, the grouping that Rust, Java and
TypeScript implement. Wrong views are killed: one that lists a descriptor for every path segment,
one that lists a prefix twice (transition and place prefixes joined without merging), one that
lists only port places (none survive composition with a prefix), one without parents, one whose
`instancePrefix` answers MOD-040's reference `subnetOf` (`refSubnetOf`), and four plausible wrong readings (a descriptor per
top-level instance, prefixes taken from transitions only, nested nodes counted in the outer
descriptor, the parent taken at the first `/` instead of the last).
-/

namespace Libpetri.Spec

namespace Mod041

/-- The names of a net the debug protocol reads: its listed places and its transitions. -/
structure NameNet where
  /-- The listed place names: the places that some arc or output specification of a transition
  names (the session's place list; a place no arc or output names is not among them). -/
  places : List String
  /-- The transition names. -/
  transitions : List String
deriving DecidableEq

/-- Every node name of a net: its transitions, then its places. -/
def NameNet.nodes (X : NameNet) : List String := X.transitions ++ X.places

/-- One subnet instance descriptor of the `Subscribed` response. -/
structure Descriptor where
  /-- The instance prefix it describes. -/
  pfx : String
  /-- Its parent prefix, if any. -/
  parent : Option String
  /-- The transitions it lists. -/
  transitions : List String
  /-- The places it lists (the wire field `exposedPlaceNames`). -/
  places : List String
deriving DecidableEq

/-- A debug view of subnet instances: the descriptor list of a net, and the `instancePrefix`
field of a node of a net (none when the field is absent). -/
structure SubnetView where
  /-- The descriptor list of the `Subscribed` response for a net. -/
  descs : NameNet → List Descriptor
  /-- The `instancePrefix` field of a `PlaceInfo` or `TransitionInfo`. -/
  nodePrefix : NameNet → String → Option String

/-- A list without repeated entries, each entry of the input kept once. -/
def uniq : List String → List String
  | [] => []
  | x :: xs => if x ∈ xs then uniq xs else x :: uniq xs

theorem mem_uniq {a : String} : ∀ {l : List String}, a ∈ uniq l ↔ a ∈ l
  | [] => by simp [uniq]
  | x :: xs => by
    unfold uniq
    by_cases hx : x ∈ xs
    · rw [if_pos hx, mem_uniq]
      constructor
      · exact List.mem_cons_of_mem x
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · exact hx
        · exact h
    · rw [if_neg hx, List.mem_cons, List.mem_cons, mem_uniq]

theorem nodup_uniq : ∀ l : List String, (uniq l).Nodup
  | [] => by simp [uniq]
  | x :: xs => by
    unfold uniq
    by_cases hx : x ∈ xs
    · rw [if_pos hx]; exact nodup_uniq xs
    · rw [if_neg hx, List.nodup_cons, mem_uniq]; exact ⟨hx, nodup_uniq xs⟩

/-- The descriptor the reference builds for the prefix `P` of the net `X`: every transition and
every place whose instance prefix is `P`, and the parent `instancePrefix P`. -/
def mkDesc (X : NameNet) (P : String) : Descriptor :=
  { pfx := P, parent := instancePrefix P,
    transitions := X.transitions.filter fun n => decide (instancePrefix n = some P),
    places := X.places.filter fun n => decide (instancePrefix n = some P) }

/-- The distinct instance prefixes of the nodes of a net. -/
def prefixes (X : NameNet) : List String := uniq (X.nodes.filterMap instancePrefix)

/-- The reference descriptor list: one `mkDesc` per distinct instance prefix of a node. -/
def refDescriptors (X : NameNet) : List Descriptor := (prefixes X).map (mkDesc X)

/-- The reference debug view: the descriptors of `refDescriptors`, and the instance prefix of
the node's name as its `instancePrefix` field. -/
def refView : SubnetView := { descs := refDescriptors, nodePrefix := fun _ => instancePrefix }

#spec_witness refView

end Mod041

open Mod041

/-! ## MOD-041: Debug Protocol Subnet Instances -/

requirement MOD_041
  id "MOD-041"
  title "Debug Protocol Subnet Instances"
  kind F
  scope "every debug protocol implementation (Java, TypeScript, Rust; Python has none)"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_041.s1, MOD_041.s2, MOD_041.s3, MOD_041.s4
  reading "For every debug view V and every net X (its transition names and its listed place names, the places that some arc or output specification of a transition names; instancePrefix n is the part of n before its last '/', none when n has no '/' or that part is empty):"
          "the prefixes of the descriptors V.descs X are pairwise distinct, and a string P is the prefix of some descriptor exactly when P is the instance prefix of some transition or listed place of X;"
          "for every descriptor d of V.descs X and every name n, n is among d's transitions exactly when n is a transition of X with instance prefix d.pfx, and n is among d's places exactly when n is a place of X with instance prefix d.pfx;"
          "for every descriptor d of V.descs X, d's parent is the instance prefix of d.pfx;"
          "for every place or transition n of X, the instancePrefix field V.nodePrefix X n is the instance prefix of n (none when n has none)."
  assumes "Ruling D71 (a): the descriptors are a function of the names of the flat net, which carries no instance provenance (MOD-023). A descriptor exists for each distinct last-slash prefix of a node name, its place set is every listed place under that prefix, its parent is the prefix's own prefix. This is what all three debug protocol implementations do: build_subnet_instances in rust/libpetri-debug/src/debug_session_registry.rs (and its test subscribed_composed_net_populated_subnet_instances, which asserts the internal place p1/nextItem in exposed_place_names), buildSubnetInstances in java/src/main/java/org/libpetri/debug/DebugSessionRegistry.java, buildSubnetInstances in typescript/src/debug/debug-session-registry.ts. After composition the places under a prefix are the instance's internal places and its unbound ports: a bound port takes the caller place's name and has no prefix."
          "The places of X are the listed places (the markdown's term): the places that some input, inhibitor, read or reset arc or some output specification of a transition names. Every runtime builds the session's place list, which gives both the PlaceInfo entries and the places the descriptors group, from the arcs and output specifications alone (PlaceAnalysis::from_net in rust/libpetri-debug/src/place_analysis.rs, used by register_with_tags in debug_session_registry.rs and read by build_subnet_instances; PlaceAnalysis.from in java/src/main/java/org/libpetri/export/PlaceAnalysis.java, used by DebugSessionRegistry.register and read by buildSubnetInstances; PlaceAnalysis.from in typescript/src/debug/place-analysis.ts, used by DebugSessionRegistry.register in debug-session-registry.ts and read by buildSubnetInstances). A place the builder holds that no arc or output names (an explicit place, PetriNetBuilder::place in rust/libpetri-core/src/petri_net.rs, PetriNet.Builder.places in java/src/main/java/org/libpetri/core/PetriNet.java, PetriNetBuilder.place in typescript/src/core/petri-net.ts, or a terminal place no arc names, PetriNetBuilder::terminal in petri_net.rs) has no PlaceInfo and is in no descriptor in all three runtimes. The runtimes agree and the debug protocol describes no other place, so the markdown sentences say listed places and the block states them; such a place is not in X."
          "Names are strings, read as their characters, and the instance prefix is the export glossary's instancePrefix (Spec/GlossaryExportCluster.lean), the helper of MOD-040 line 5 and the AUTO cluster key of EXP-016: the part of a name before its last '/', none for a name without '/' and for a name whose only '/' is its first character, as instancePrefixOf and parentOf do in every runtime (instance_prefix_of and parent_of in rust/libpetri-core/src/subnet_prefixes.rs, java/src/main/java/org/libpetri/export/SubnetPrefixes.java, typescript/src/export/subnet-prefixes.ts); parentOf is instancePrefixOf applied to the prefix, so line 3 uses instancePrefix for both. So the instancePrefix field and MOD-040's helper agree on every node (mod041_nodePrefix_eq_helper), and the debug descriptors, the helper and the export clusters speak about one prefix."
          "Lines 1 and 2 compare sets: the order of the descriptor list and of the names in a descriptor is not stated (Rust sorts the prefixes through a BTreeMap, build_subnet_instances in debug_session_registry.rs; Java and TypeScript keep discovery order, transitions first), nor are repetitions within a descriptor's name lists (a net holds each name once)."
          "Items 2 and 3 (the subnet definition's name and the parameter value, 'where available') are not stated: the markdown records that current runtimes keep neither after composition, and every runtime leaves the definition name absent (build_subnet_instances in debug_session_registry.rs, buildSubnetInstances in DebugSessionRegistry.java) and carries no parameter value."
          "That the Subscribed response carries the descriptor list beside the place and transition descriptors, and the field names (subnetInstances, prefix, parentPrefix, transitionNames, exposedPlaceNames, instancePrefix), are wire shape, tested and not proven. The sentence that the requirement is observability-only is true of any function of the net's names and has no line. The instancePrefix the event converter adds to events (netEventConverter_emitsInstancePrefixForPrefixedEvents) is not stated here."
          "Scope: a session over a live net, as each sentence says. A session over an imported archive carries no net topology, and the markdown leaves its list unspecified: Java and TypeScript return an empty list, Rust groups the transition names it holds (build_subnet_instances, debug_session_registry.rs); not stated. Python has no debug protocol (spec/coverage-matrix.md, the MOD-041 row)."
          "AC1 (one descriptor per distinct instance prefix that some transition or listed place name carries) is line 1; its 'one' is the no-repeat half (MOD_041_mutant_dupPrefix_killed). AC2 (the transition and exposed-place sets of a descriptor enumerate exactly the transitions and listed places under its prefix) is line 2. AC3 (a node whose name has an instance prefix carries it as instancePrefix, one whose name has none carries none) is line 4; the bound port src of the pipeline carries none (MOD_041_nonvacuous). AC4 (a nested instance reports its parent prefix) is line 3; the reference example outer/inner with parent outer is MOD_041_nonvacuous. AC5 (a net with no '/' in any name gives an empty list and no instancePrefix field) follows from lines 1 and 4 for every model of the block (mod041_flat)."
  signoff "2026-11-13 8576984852e6d00a ai"
  statement : SubnetView → Prop :=
    fun V =>
      (∀ X, ((V.descs X).map (·.pfx)).Nodup ∧
        ∀ P, P ∈ (V.descs X).map (·.pfx) ↔ ∃ n ∈ X.nodes, instancePrefix n = some P) ∧
      (∀ X, ∀ d ∈ V.descs X, ∀ n,
        (n ∈ d.transitions ↔ n ∈ X.transitions ∧ instancePrefix n = some d.pfx) ∧
        (n ∈ d.places ↔ n ∈ X.places ∧ instancePrefix n = some d.pfx)) ∧
      (∀ X, ∀ d ∈ V.descs X, d.parent = instancePrefix d.pfx) ∧
      (∀ X, ∀ n ∈ X.nodes, V.nodePrefix X n = instancePrefix n)

/- The pinned readable form of MOD-041: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_041 : SubnetView → Prop :=
fun V =>
  (∀ (X : NameNet),
      (List.map (fun x => x.pfx) (V.descs X)).Nodup ∧
        ∀ (P : String), P ∈ List.map (fun x => x.pfx) (V.descs X) ↔ ∃ n ∈ X.nodes, instancePrefix n = some P) ∧
    (∀ (X : NameNet),
        ∀ d ∈ V.descs X,
          ∀ (n : String),
            (n ∈ d.transitions ↔ n ∈ X.transitions ∧ instancePrefix n = some d.pfx) ∧
              (n ∈ d.places ↔ n ∈ X.places ∧ instancePrefix n = some d.pfx)) ∧
      (∀ (X : NameNet), ∀ d ∈ V.descs X, d.parent = instancePrefix d.pfx) ∧
        ∀ (X : NameNet), ∀ n ∈ X.nodes, V.nodePrefix X n = instancePrefix n
-/
#guard_msgs in #print MOD_041

/-! ### The four lines, named (for the mutants) -/

section Lines

/-- Line 1 of MOD-041: one descriptor per distinct instance prefix of a node, and no other. -/
def mod041_line1 (V : SubnetView) : Prop :=
  ∀ X, ((V.descs X).map (·.pfx)).Nodup ∧
    ∀ P, P ∈ (V.descs X).map (·.pfx) ↔ ∃ n ∈ X.nodes, instancePrefix n = some P

/-- Line 2 of MOD-041: a descriptor lists exactly the transitions and places under its prefix. -/
def mod041_line2 (V : SubnetView) : Prop :=
  ∀ X, ∀ d ∈ V.descs X, ∀ n,
    (n ∈ d.transitions ↔ n ∈ X.transitions ∧ instancePrefix n = some d.pfx) ∧
    (n ∈ d.places ↔ n ∈ X.places ∧ instancePrefix n = some d.pfx)

/-- Line 3 of MOD-041: a descriptor's parent is the instance prefix of its prefix. -/
def mod041_line3 (V : SubnetView) : Prop :=
  ∀ X, ∀ d ∈ V.descs X, d.parent = instancePrefix d.pfx

/-- Line 4 of MOD-041: a node's `instancePrefix` field is the instance prefix of its name. -/
def mod041_line4 (V : SubnetView) : Prop :=
  ∀ X, ∀ n ∈ X.nodes, V.nodePrefix X n = instancePrefix n

/-- MOD-041 is its four lines. -/
theorem mod041_iff (V : SubnetView) :
    MOD_041 V ↔ mod041_line1 V ∧ mod041_line2 V ∧ mod041_line3 V ∧ mod041_line4 V :=
  Iff.rfl

end Lines

/-! ### The reference -/

namespace Mod041

/-- The prefixes of `mkDesc` over a list are that list. -/
theorem map_pfx_mkDesc (X : NameNet) (Ps : List String) : (Ps.map (mkDesc X)).map (·.pfx) = Ps := by
  rw [List.map_map]
  exact List.map_id' Ps

/-- Every list of `mkDesc` descriptors meets line 2 and line 3. -/
theorem mkDesc_lines (X : NameNet) (Ps : List String) :
    (∀ d ∈ Ps.map (mkDesc X), ∀ n,
      (n ∈ d.transitions ↔ n ∈ X.transitions ∧ instancePrefix n = some d.pfx) ∧
      (n ∈ d.places ↔ n ∈ X.places ∧ instancePrefix n = some d.pfx)) ∧
    (∀ d ∈ Ps.map (mkDesc X), d.parent = instancePrefix d.pfx) := by
  refine ⟨fun d hd n => ?_, fun d hd => ?_⟩
  · obtain ⟨P, -, rfl⟩ := List.mem_map.1 hd
    simp [mkDesc, List.mem_filter]
  · obtain ⟨P, -, rfl⟩ := List.mem_map.1 hd
    rfl

/-- The reference prefixes meet line 1. -/
theorem prefixes_line1 (X : NameNet) :
    ((refDescriptors X).map (·.pfx)).Nodup ∧
      ∀ P, P ∈ (refDescriptors X).map (·.pfx) ↔ ∃ n ∈ X.nodes, instancePrefix n = some P := by
  unfold refDescriptors
  rw [map_pfx_mkDesc]
  exact ⟨nodup_uniq _, fun P => by rw [prefixes, mem_uniq, List.mem_filterMap]⟩

end Mod041

/-- ✓ The reference debug view satisfies MOD-041: it groups the node names by the part before
their last `/`, one descriptor per distinct group, each holding the transitions and places of its
group and the group's own prefix as parent, and it gives every node its group as its
`instancePrefix` field. -/
@[evidence holds MOD_041]
theorem MOD_041_reference : MOD_041 refView :=
  ⟨prefixes_line1, fun X => (mkDesc_lines X _).1, fun X => (mkDesc_lines X _).2,
    fun _ _ _ => rfl⟩

/-! ### Consequences for every model of the block -/

section Consequences

/-- **AC5.** In every model of MOD-041, a net with no `/` in any name gets an empty descriptor list and no `instancePrefix` field on any node: a net with the
places `idle` and `busy` and the transition `start` has no subnet instance. -/
theorem mod041_flat {V : SubnetView} (h : MOD_041 V) {X : NameNet}
    (hX : ∀ n ∈ X.nodes, '/' ∉ n.toList) :
    V.descs X = [] ∧ ∀ n ∈ X.nodes, V.nodePrefix X n = none := by
  refine ⟨List.eq_nil_iff_forall_not_mem.2 fun d hd => ?_, fun n hn => ?_⟩
  · obtain ⟨n, hn, hP⟩ := ((h.1 X).2 d.pfx).1 (List.mem_map_of_mem hd)
    rw [instancePrefix_eq_none_of n (hX n hn)] at hP
    cases hP
  · rw [h.2.2.2 X n hn, instancePrefix_eq_none_of n (hX n hn)]

/-- **One prefix with MOD-040.** In every model of MOD-041 and every model of MOD-040, the
`instancePrefix` field of a node is what MOD-040's instance-prefix helper answers for its name:
the place `s1/obs/TURN` carries `s1/obs` in both. -/
theorem mod041_nodePrefix_eq_helper {V : SubnetView} {M : SubnetAccess} (h : MOD_041 V)
    (hM : MOD_040 M) {X : NameNet} {n : String} (hn : n ∈ X.nodes) :
    V.nodePrefix X n = M.prefixOf n := by
  rw [h.2.2.2 X n hn, mod040_prefixOf_eq hM.2.2.2.2 n]

/-- The reference view gives a net with no `/` in any name no descriptor and no
`instancePrefix` field. -/
theorem refView_flat {X : NameNet} (hX : ∀ n ∈ X.nodes, '/' ∉ n.toList) :
    refView.descs X = [] ∧ ∀ n ∈ X.nodes, refView.nodePrefix X n = none :=
  mod041_flat MOD_041_reference hX

end Consequences

/-! ### Examples -/

namespace Mod041

/-- A two-instance pipeline (the test derivation): the caller places `src`, `mid` and `sink`,
the instances `p1` and `p2`, each with the transition `produce` and the internal place
`nextItem`; the ports of both were bound to caller places, so they carry no prefix. -/
def exPipeline : NameNet :=
  { places := ["src", "p1/nextItem", "mid", "p2/nextItem", "sink"],
    transitions := ["p1/produce", "p2/produce"] }

/-- A composed producer: its port was bound to the caller place `P`, its internal place
`b1/next` kept the prefix. -/
def exProducer : NameNet := { places := ["P", "b1/next"], transitions := ["b1/produce"] }

/-- A nested instance `outer/inner`, all of whose nodes sit in the nested instance. -/
def exNested : NameNet :=
  { places := ["outer/inner/p"], transitions := ["outer/inner/t"] }

/-- A subnet `s1` with a `/` in its own namespace: the place `obs/TURN` became `s1/obs/TURN`. -/
def exObs : NameNet := { places := ["s1/obs/TURN"], transitions := ["s1/t"] }

/-- An outer instance with a transition of its own and a nested instance. -/
def exTwoLevels : NameNet :=
  { places := [], transitions := ["outer/t", "outer/inner/t"] }

/-- A net with a prefixed place and no transition. -/
def exPlaceOnly : NameNet := { places := ["x/y"], transitions := [] }

/-- A three-level instance: the place `a/b/c/p`, whose instance prefix `a/b/c` has the parent
`a/b`. -/
def exThree : NameNet := { places := ["a/b/c/p"], transitions := [] }

end Mod041

/-- ✓ Every line of MOD-041 is exercised by the reference. The two-instance pipeline gets two
descriptors, `p1` and `p2`, each with its transition `produce` and its internal place `nextItem`,
no parent, and the place `p1/nextItem` carries the field `p1` while `src` carries none (AC1,
AC2, AC3). The nested instance gets the one descriptor `outer/inner` with parent `outer` (AC4).
The place `s1/obs/TURN` gets the descriptor `s1/obs`, the part before its last `/`. A flat net
with the places `idle` and `busy` and the transition `start` gets no descriptor (AC5). -/
@[evidence nonvacuous MOD_041]
theorem MOD_041_nonvacuous :
    refView.descs exPipeline =
      [⟨"p1", none, ["p1/produce"], ["p1/nextItem"]⟩,
       ⟨"p2", none, ["p2/produce"], ["p2/nextItem"]⟩] ∧
    refView.nodePrefix exPipeline "p1/nextItem" = some "p1" ∧
    refView.nodePrefix exPipeline "src" = none ∧
    refView.descs exNested =
      [⟨"outer/inner", some "outer", ["outer/inner/t"], ["outer/inner/p"]⟩] ∧
    (refView.descs exObs).map (·.pfx) = ["s1", "s1/obs"] ∧
    refView.descs ⟨["idle", "busy"], ["start"]⟩ = [] := by
  decide

/-! ### Wrong views -/

namespace Mod041

/-- The ancestors of a name, nearest first: its instance prefix, that prefix's instance prefix,
and so on (`k` bounds the walk). -/
def ancestors : Nat → String → List String
  | 0, _ => []
  | k + 1, n => match instancePrefix n with
    | none => []
    | some P => P :: ancestors k P

/-- The instance prefix of a name is among its ancestors. -/
theorem mem_ancestors {n P : String} (h : instancePrefix n = some P) :
    P ∈ ancestors n.toList.length n := by
  cases hl : n.toList.length with
  | zero => simp [instancePrefix, lastCut, List.length_eq_zero_iff.1 hl] at h
  | succ k => simp [ancestors, h]

/-- A view with one descriptor for every path segment: `outer/inner/x` gives descriptors for
`outer/inner` and for `outer`. -/
def perSegmentView : SubnetView :=
  { descs := fun X => (uniq (X.nodes.flatMap fun n => ancestors n.toList.length n)).map (mkDesc X),
    nodePrefix := fun _ => instancePrefix }

/-- A view that reads item 5 literally, listing only the port places of an instance. The flat
net carries no port, and a bound port lost its prefix, so it lists no place. -/
def portPlacesOnlyView : SubnetView :=
  { descs := fun X => (prefixes X).map fun P => { mkDesc X P with places := [] },
    nodePrefix := fun _ => instancePrefix }

/-- A view that reports no parent prefix. -/
def noParentView : SubnetView :=
  { descs := fun X => (prefixes X).map fun P => { mkDesc X P with parent := none },
    nodePrefix := fun _ => instancePrefix }

/-- A view whose `instancePrefix` field answers MOD-040's reference `subnetOf` (`refSubnetOf`, on
the net's names with no membership entry) instead of the part before the last `/`. -/
def subnetOfView : SubnetView :=
  { descs := refDescriptors
    nodePrefix := fun X n => refSubnetOf ⟨X.places, X.transitions, fun _ => none⟩ n }

/-- The part of a name before its first `/`. -/
def firstSeg (n : String) : String := String.ofList (n.toList.takeWhile (· ≠ '/'))

/-- The first segment of a name with an instance prefix: its top-level instance. -/
def topPrefix (n : String) : Option String := (instancePrefix n).map fun _ => firstSeg n

/-- A view with one descriptor per top-level instance (the acceptance criterion's first wording
read literally), grouping nested nodes into their outer instance. -/
def topLevelView : SubnetView :=
  { descs := fun X => (uniq (X.nodes.filterMap topPrefix)).map fun P =>
      { pfx := P, parent := none,
        transitions := X.transitions.filter fun n => decide (topPrefix n = some P),
        places := X.places.filter fun n => decide (topPrefix n = some P) },
    nodePrefix := fun _ => topPrefix }

/-- A view that discovers prefixes from transition names only. -/
def transitionsOnlyView : SubnetView :=
  { descs := fun X => (uniq (X.transitions.filterMap instancePrefix)).map (mkDesc X),
    nodePrefix := fun _ => instancePrefix }

/-- A view whose descriptor lists every node whose name starts with its prefix, nested nodes
included. -/
def subtreeView : SubnetView :=
  { descs := fun X => (prefixes X).map fun P =>
      { mkDesc X P with
        transitions := X.transitions.filter fun n => decide (IsSlashPrefix P n),
        places := X.places.filter fun n => decide (IsSlashPrefix P n) },
    nodePrefix := fun _ => instancePrefix }

/-- A view that collects the instance prefixes of transitions and of places separately and joins
the two lists without merging them, so a prefix carried by a transition and a place is listed
twice. -/
def concatView : SubnetView :=
  { descs := fun X =>
      (uniq (X.transitions.filterMap instancePrefix) ++ uniq (X.places.filterMap instancePrefix)).map
        (mkDesc X),
    nodePrefix := fun _ => instancePrefix }

/-- A parent taken at the first `/` of the prefix instead of its last: `a/b/c` gets `a`. -/
def parentFirst (P : String) : Option String := (instancePrefix P).map fun _ => firstSeg P

/-- A view whose parent is `parentFirst`; everything else is the reference's. -/
def parentFirstView : SubnetView :=
  { descs := fun X => (prefixes X).map fun P => { mkDesc X P with parent := parentFirst P },
    nodePrefix := fun _ => instancePrefix }

end Mod041

/-- ✗ A view that takes the parent at the first `/` violates MOD-041 (line 3): the place
`a/b/c/p` gets the descriptor `a/b/c`, whose parent is `a/b`, but the view reports `a`. On two
levels (`outer/inner` with parent `outer`) the two readings agree. -/
@[evidence forbids MOD_041]
theorem MOD_041_forbids_parentFirst : ¬ MOD_041 parentFirstView := by
  intro h
  have hd : (⟨"a/b/c", some "a", [], ["a/b/c/p"]⟩ : Descriptor) ∈
      parentFirstView.descs exThree := by decide
  have := h.2.2.1 exThree _ hd
  exact absurd this (by decide)

/-- ✗ A view with one descriptor per top-level instance violates MOD-041 (line 1): the nested
instance `outer/inner` gets the descriptor `outer`, a prefix no node carries, and no descriptor
`outer/inner`. -/
@[evidence forbids MOD_041]
theorem MOD_041_forbids_topLevel : ¬ MOD_041 topLevelView := by
  intro h
  have := ((h.1 exNested).2 "outer")
  exact absurd this (by decide)

/-- ✗ A view that takes prefixes from transition names only violates MOD-041 (line 1): the net
with the place `x/y` and no transition gets no descriptor `x`. -/
@[evidence forbids MOD_041]
theorem MOD_041_forbids_transitionsOnly : ¬ MOD_041 transitionsOnlyView := by
  intro h
  have := ((h.1 exPlaceOnly).2 "x")
  exact absurd this (by decide)

/-- ✗ A view that counts nested nodes in the outer descriptor violates MOD-041 (line 2): the
descriptor `outer` lists the transition `outer/inner/t`, which belongs to `outer/inner`. -/
@[evidence forbids MOD_041]
theorem MOD_041_forbids_subtree : ¬ MOD_041 subtreeView := by
  intro h
  have hd : (⟨"outer", none, ["outer/t", "outer/inner/t"], []⟩ : Descriptor) ∈
      subtreeView.descs exTwoLevels := by decide
  have := (h.2.1 exTwoLevels _ hd "outer/inner/t").1
  exact absurd this (by decide)

/-! ### Mutant: line 1 read as "every prefix has a descriptor" -/

/-- Mutant reading of line 1: every instance prefix of a node has exactly one descriptor, with no
"and no other descriptor"; lines 2 to 4 as in MOD-041. -/
def MOD_041_mutant_perSegment (V : SubnetView) : Prop :=
  (∀ X, ((V.descs X).map (·.pfx)).Nodup ∧
    ∀ n ∈ X.nodes, ∀ P, instancePrefix n = some P → P ∈ (V.descs X).map (·.pfx)) ∧
  mod041_line2 V ∧ mod041_line3 V ∧ mod041_line4 V

/-- The view with a descriptor per path segment kills the mutant: it lists every node's prefix
once and fills each descriptor correctly, but the nested instance `outer/inner` also gets a
descriptor `outer`, which is no node's instance prefix (line 1). -/
@[evidence mutant MOD_041]
theorem MOD_041_mutant_perSegment_killed :
    MOD_041_mutant_perSegment perSegmentView ∧ ¬ MOD_041 perSegmentView := by
  refine ⟨⟨fun X => ⟨?_, fun n hn P hP => ?_⟩, fun X => (mkDesc_lines X _).1,
    fun X => (mkDesc_lines X _).2, fun _ _ _ => rfl⟩, fun h => ?_⟩
  · show ((List.map (mkDesc X) _).map (·.pfx)).Nodup
    rw [map_pfx_mkDesc]; exact nodup_uniq _
  · show P ∈ (List.map (mkDesc X) _).map (·.pfx)
    rw [map_pfx_mkDesc, mem_uniq, List.mem_flatMap]
    exact ⟨n, hn, mem_ancestors hP⟩
  · have := ((h.1 exNested).2 "outer")
    exact absurd this (by decide)

/-! ### Mutant: line 1 without "exactly one" -/

/-- Mutant reading of line 1: the descriptor prefixes are exactly the instance prefixes of the
nodes, but a prefix may have several descriptors; lines 2 to 4 as in MOD-041. -/
def MOD_041_mutant_dupPrefix (V : SubnetView) : Prop :=
  (∀ X, ∀ P, P ∈ (V.descs X).map (·.pfx) ↔ ∃ n ∈ X.nodes, instancePrefix n = some P) ∧
  mod041_line2 V ∧ mod041_line3 V ∧ mod041_line4 V

/-- The view that joins transition prefixes and place prefixes without merging them kills the
mutant: each of its descriptors is filled correctly and every prefix is listed, but the
two-instance pipeline gets `p1` and `p2` twice each, once for `produce` and once for `nextItem`
(line 1, "exactly one descriptor"). -/
@[evidence mutant MOD_041]
theorem MOD_041_mutant_dupPrefix_killed :
    MOD_041_mutant_dupPrefix concatView ∧ ¬ MOD_041 concatView := by
  refine ⟨⟨fun X P => ?_, fun X => (mkDesc_lines X _).1, fun X => (mkDesc_lines X _).2,
    fun _ _ _ => rfl⟩, fun h => ?_⟩
  · show P ∈ (List.map (mkDesc X) _).map (·.pfx) ↔ _
    rw [map_pfx_mkDesc, List.mem_append, mem_uniq, mem_uniq, List.mem_filterMap,
      List.mem_filterMap]
    constructor
    · rintro (⟨n, hn, hP⟩ | ⟨n, hn, hP⟩)
      · exact ⟨n, List.mem_append_left _ hn, hP⟩
      · exact ⟨n, List.mem_append_right _ hn, hP⟩
    · rintro ⟨n, hn, hP⟩
      rcases List.mem_append.1 hn with hn | hn
      · exact Or.inl ⟨n, hn, hP⟩
      · exact Or.inr ⟨n, hn, hP⟩
  · have := (h.1 exPipeline).1
    exact absurd this (by decide)

/-! ### Mutant: line 2 without its place half -/

/-- Mutant reading of line 2 (item 5 read literally: the place set holds exposed port places,
which the flat net cannot tell, so the line leaves it free): a descriptor lists exactly the
transitions under its prefix; lines 1, 3 and 4 as in MOD-041. -/
def MOD_041_mutant_portPlacesOnly (V : SubnetView) : Prop :=
  mod041_line1 V ∧
  (∀ X, ∀ d ∈ V.descs X, ∀ n,
    n ∈ d.transitions ↔ n ∈ X.transitions ∧ instancePrefix n = some d.pfx) ∧
  mod041_line3 V ∧ mod041_line4 V

/-- The view that lists only port places kills the mutant: it meets lines 1, 3 and 4 and the
transition half of line 2, but the composed producer's descriptor `b1` lists no place, although
the internal place `b1/next` sits under `b1` (line 2). -/
@[evidence mutant MOD_041]
theorem MOD_041_mutant_portPlacesOnly_killed :
    MOD_041_mutant_portPlacesOnly portPlacesOnlyView ∧ ¬ MOD_041 portPlacesOnlyView := by
  have hm : ∀ X, (portPlacesOnlyView.descs X).map (·.pfx) = (refDescriptors X).map (·.pfx) := by
    intro X
    show List.map _ (List.map _ _) = List.map _ (List.map _ _)
    rw [List.map_map, List.map_map]; rfl
  refine ⟨⟨fun X => by rw [hm]; exact prefixes_line1 X, fun X d hd n => ?_, fun X d hd => ?_,
    fun _ _ _ => rfl⟩, fun h => ?_⟩
  · obtain ⟨P, -, rfl⟩ := List.mem_map.1 hd
    simp [mkDesc, List.mem_filter]
  · obtain ⟨P, -, rfl⟩ := List.mem_map.1 hd
    rfl
  · have hd : (⟨"b1", none, ["b1/produce"], []⟩ : Descriptor) ∈
        portPlacesOnlyView.descs exProducer := by decide
    have := (h.2.1 exProducer _ hd "b1/next").2
    exact absurd this (by decide)

/-! ### Mutant: line 3 dropped (no parent) -/

/-- Mutant reading: MOD-041 without line 3, so a descriptor need not carry its parent. -/
def MOD_041_mutant_noParent (V : SubnetView) : Prop :=
  mod041_line1 V ∧ mod041_line2 V ∧ mod041_line4 V

/-- The view without parents kills the mutant: it meets lines 1, 2 and 4, but the nested
instance `outer/inner` is reported without its parent `outer` (line 3, AC4). -/
@[evidence mutant MOD_041]
theorem MOD_041_mutant_noParent_killed :
    MOD_041_mutant_noParent noParentView ∧ ¬ MOD_041 noParentView := by
  have hm : ∀ X, (noParentView.descs X).map (·.pfx) = (refDescriptors X).map (·.pfx) := by
    intro X
    show List.map _ (List.map _ _) = List.map _ (List.map _ _)
    rw [List.map_map, List.map_map]; rfl
  refine ⟨⟨fun X => by rw [hm]; exact prefixes_line1 X, fun X d hd n => ?_, fun _ _ _ => rfl⟩,
    fun h => ?_⟩
  · obtain ⟨P, -, rfl⟩ := List.mem_map.1 hd
    simp [mkDesc, List.mem_filter]
  · have hd : (⟨"outer/inner", none, ["outer/inner/t"], ["outer/inner/p"]⟩ :
        Descriptor) ∈ noParentView.descs exNested := by decide
    have := h.2.2.1 exNested _ hd
    exact absurd this (by decide)

/-! ### Mutant: line 4 dropped (the field answers `subnetOf`) -/

/-- Mutant reading: MOD-041 without line 4, so the `instancePrefix` field is free (and may
answer MOD-040's `subnetOf`). -/
def MOD_041_mutant_subnetOfAsPrefix (V : SubnetView) : Prop :=
  mod041_line1 V ∧ mod041_line2 V ∧ mod041_line3 V

/-- The view whose field answers `subnetOf` kills the mutant: its descriptors are the
reference's, but the place `s1/obs/TURN` gets the field `s1` (the instance that has a
transition) instead of `s1/obs`, the part before its last `/` (line 4). -/
@[evidence mutant MOD_041]
theorem MOD_041_mutant_subnetOfAsPrefix_killed :
    MOD_041_mutant_subnetOfAsPrefix subnetOfView ∧ ¬ MOD_041 subnetOfView := by
  refine ⟨⟨MOD_041_reference.1, MOD_041_reference.2.1, MOD_041_reference.2.2.1⟩, fun h => ?_⟩
  have := h.2.2.2 exObs "s1/obs/TURN" (by decide)
  exact absurd this (by decide)

end Libpetri.Spec
