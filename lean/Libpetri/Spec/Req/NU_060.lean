import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNu
import Libpetri.Spec.Req.MOD_021
import Libpetri.Reference.Nu

set_option linter.missingDocs true

/-!
# NU-060: Match-arc composition (`spec/12-nu-nets.md`)

NU-060 says what the channel merge of [MOD-021] does with a ν-net match. It is a pure-function
requirement (kind F) over two merge functions of one implementation: the plain merge
`Mg : MergeFn N A` (MOD-021's, on definitions without a match) and the ν merge
`NMg : NuMergeFn N A K` (the same merge on definitions that may carry a match, `NuCDef`).

* **Line 1** (a correlated input behaves as the input arc it layers on; no match is dropped):
  when at most one side carries a match, the ν merge is the plain merge of the two definitions
  without their matches, with that side's match attached unchanged (or no match when neither
  side has one). Its rejections are the plain merge's rejections.
* **Line 2** (ruling D81 (a), clash nu-b#7): when both sides carry a match, whatever places the
  two matches key, the merge is rejected with a message that names the caller-side transition.

The reference is `refNuMerge Mg`, which checks the two matches and otherwise runs `Mg`; it is
`merge_match_specs` (`rust/libpetri-core/src/rewriter.rs:708-727`), Java `mergeMatchSpecs`
(`SubnetRewriter.java:616-624`) and TypeScript `mergeMatchSpecs` (`subnet-rewriter.ts:566-577`)
around the plain merge. The witness pair of the composition wave is `refMerge Build sq cm`
with `refNuMerge (refMerge Build sq cm)` (`NU_060_with_MOD_021`).

Consequences: a success keeps the surviving match (`NU_060_keeps`, `NU_060_neverDrops`); with
MOD-021 the merged correlated input follows the canonical merge table, so a correlated `one()`
and the other side's `one()` give one correlated `exactly(2)` (`NU_060_table`); and on the
reference the surviving match still keys input places and relays into output places of the
merged transition (`refNuMerge_keysOnInputs`, `refNuMerge_relaysOK`), so NU-020's build checks
accept the merged transition again.

The record `NuCDef` (a composition definition with its match) is in `Reference/Nu.lean`, beside
`NuDef`, as the composition model's `CDef` has no match field; `NuCDef.toNuDef` reads it as the
`NuDef` of NU-030's rebuild, with the same firing view (`NuCDef.toNuTrans_comp`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## The definitions with a match, and the ν merge -/

section Vocab

variable {N A K : Type}

/-- A ν channel merge: the caller-side and the instance-side definition, each perhaps with a
match, give the merged definition or a rejection message. -/
abbrev NuMergeFn (N A K : Type) := NuCDef N A K → NuCDef N A K → Except String (NuCDef N A K)

/-- The rejection of two matches, naming the caller-side transition. The text is a stand-in for
the runtimes' (only the caller's name in it is stated). -/
def nuMatchMsg (name : String) : String :=
  "Channel composition '" ++ name ++ "': both the caller-side and instance-side transition carry a ν-net match; refusing to fuse two independent correlations into one transition (NU-060). Resolve explicitly by keeping the match on a single side."

/-- **The reference ν merge** over a plain merge `Mg`: two matches reject naming the caller;
otherwise the plain merge of the two definitions without their matches, with the one match
(if any) attached unchanged. -/
def refNuMerge (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | mc, mi => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (mc.or mi))

/- The reference ν merge is the witness model of the block. -/
#spec_witness refNuMerge

/-- The ν-merge rejection names the caller-side transition. -/
theorem nuMatchMsg_names (name : String) : mod021_names (nuMatchMsg name) name :=
  mod021_names_app _ (mod021_names_end _ name)

end Vocab

/-! ## NU-060: Match-Arc Composition -/

requirement NU_060
  id "NU-060"
  title "Match-Arc Composition"
  kind F
  scope "channel composition in every implementation: the merge of a caller-side transition with the instance-side channel transition it is bound to, when either carries a ν-net match"
  source verbatim "spec/12-nu-nets.md"
  quote "A correlated input behaves, under channel composition ([MOD-021]), as the input arc it layers on: its arc dedup/conflict rules are unchanged."
        "A merge MUST NOT silently drop a match, and no implementation fuses two matches into one: when both merged sides carry a match, whatever places the two matches correlate, the merge MUST be rejected with an error naming the caller-side transition."
        "*When* at most one side of a channel merge carries a match, the channel merge *shall* reject with the same error when the same merge of the two transitions without their matches rejects, and otherwise *shall* give the merged transition of that merge with that side's match unchanged, or with no match when neither side carries one."
        "*If* both sides of a channel merge carry a match, *then* the channel merge *shall* be rejected with an error that names the caller-side transition."
  reading "For every plain channel merge Mg (MOD-021's, on definitions without a match) and every ν channel merge NMg of the same implementation (on definitions c, i that may carry a match):"
          "line 1: if c or i carries no match, NMg c i is Mg applied to c and i without their matches, with every success given the match c.mspec.or i.mspec (c's when c has one, i's when i has one, none when neither has one), and every rejection the same rejection;"
          "line 2: if c and i both carry a match, NMg c i fails with a message that contains c's name."
  assumes "Model scope. A ν merge takes the caller-side definition c and the instance-side channel definition i, each a CDef (MOD-021's definition with the MOD-031 declared-place correspondence) with an optional match specification (NuCDef), and gives the merged definition or a rejection message, as Rust merge_transitions (rust/libpetri-core/src/rewriter.rs:611-698, with merge_match_specs at :708-727), Java SubnetRewriter.mergeTransitions (java/src/main/java/org/libpetri/core/internal/SubnetRewriter.java:529-598, mergeMatchSpecs at :616-624) and TypeScript mergeTransitions (typescript/src/core/internal/subnet-rewriter.ts:483-555, mergeMatchSpecs at :566-577) do; Python uses the Rust code. The block relates the ν merge to the plain merge Mg of the same implementation, whose lines are MOD-021's; the witness is refNuMerge Mg for every Mg (NU_060_reference), and refNuMerge (refMerge Build sq cm) satisfies both blocks (NU_060_with_MOD_021). The scope of MOD-021 (ruling D42 (m): a caller-side transition not yet in the builder and with no arc on a port bound in the same call) applies here too."
          "Ruling D81 (a), clash nu-b#7: every runtime rejects a merge in which both sides carry a match, whatever places the two matches key, and none fuses two matches (merge_match_specs and mergeMatchSpecs compare no places). The markdown said 'on the same place' and allowed 'fuse to a single coherent correlation or reject'; it now states the runtime rule. The literal old reading, rejecting only matches that share a place and fusing the others, is the wrong model of NU_060_forbids_fuseDisjoint; keeping the caller's match is NU_060_forbids_callerWins."
          "Line 1 says that a match changes nothing else about the merge: timing, priority, action, the output specification, the inhibitor, read and reset arcs and the input arcs are merged as MOD-021 merges them, and the same pairs are rejected with the same messages (NU_060_forbids_ownError: a merge that reports its own message for a pair with one match that the plain merge rejects; NU_060_forbids_rejectShared: a merge that rejects a pair with one match that the plain merge accepts). The definitions that enter a merge are built transitions, so each side's match already passes NU-020's and NU-054's build checks on its own side; line 1 is also stated for definitions whose match would fail them, which no runtime hands to the merge. In the runtimes the one match passes merge_match_specs unchanged, and the merged transition goes through the transition builder with the match, whose NU-020 checks pass again for such a match: the keys of the surviving match are still input places of the merged transition and its relay targets still output places (refNuMerge_keysOnInputs, refNuMerge_relaysOK, shown on the reference; the builder's own checks are MOD-021's line 7). A merged transition carries the surviving match unchanged, key projections and relay targets included; no place remap happens at the merge, since both sides already name host places (the remap is NU-030's, done by the rewrite before the merge)."
          "Consequence for the correlated input: with MOD-021, a success of the ν merge has the input arcs MOD-021's line 2 gives, correlated or not, and keeps the match (NU_060_table). The sentence 'A correlated input is therefore merged by the canonical input-arc merge table like any other input arc' holds of this block together with MOD-021, not of this block alone, so it is not quoted here: NU_060_table carries it as cited evidence. A correlated one() on P and the other side's one() on P give one exactly(2) arc on P that the match still keys (NU_060_nonvacuous); the other side's uncorrelated one() therefore stops taking the queue head and takes a token of the chosen name, as ruling D16 reads a correlated input. Keeping the match with the correlated arc at its pre-merge count is the wrong model of NU_060_forbids_countStays."
          "Line 2 claims a rejection that names the caller-side transition, not which reason the message gives. Rust and TypeScript check the timing before the matches, Java checks the arc kinds and then the timing before the matches (rewriter.rs:624-634, SubnetRewriter.java:544-548, subnet-rewriter.ts:496-511), so a pair that also breaks a rule of MOD-021 is rejected with that rule's message in some runtimes; each of those messages names the caller-side transition too (MOD-021 lines 8 and 9). The markdown sentence 'Which error a merge reports when it also breaks a rule of [MOD-021] is not specified.' says so. The reference checks the matches first; the message text is a stand-in (nuMatchMsg)."
          "AC1 (composing a transition that carries a match with a side that carries none preserves the match on the flat net) is line 1 with NU_060_neverDrops: a success carries the caller's match when the caller has one and the instance's when the instance has one (NU_060_nonvacuous: a matched join keyed on P and R merged with a passthrough side keeps its keys P and R; a plain caller merged with a matched channel transition keyed on U and V keeps U and V). Putting the merged definition into the composed net is MOD-020's. Dropping the match is NU_060_forbids_dropMatch, keeping the caller's match only NU_060_forbids_callerOnly."
          "AC2 (a merge of two transitions that both carry a match is rejected with an error naming the caller-side transition, whatever places the two matches correlate) is line 2 (NU_060_nonvacuous: join T keyed on P and R against a channel transition keyed on U and V is rejected naming T)."
          "Mutants: line 1 is load-bearing (NU_060_mutant_line2Only_killed: a merge that drops every match but rejects two matches meets line 2 alone); line 2 is load-bearing (NU_060_mutant_line1Only_killed: caller wins meets line 1 alone); the naming in line 2 is load-bearing (NU_060_mutant_anyMessage_killed: a rejection with an empty message)."
  signoff "pending"
  statement : ∀ {N A K : Type}, MergeFn N A → NuMergeFn N A K → Prop :=
    fun Mg NMg =>
      (∀ c i, (c.mspec = none ∨ i.mspec = none) →
        NMg c i = (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (c.mspec.or i.mspec))) ∧
      (∀ c i ms ms', c.mspec = some ms → i.mspec = some ms' →
        ∃ m, NMg c i = .error m ∧ mod021_names m c.core.name)

/- The pinned readable form of NU-060: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_060 : {N A K : Type} → MergeFn N A → NuMergeFn N A K → Prop :=
fun {N A K} Mg NMg =>
  (∀ (c i : NuCDef N A K),
      c.mspec = none ∨ i.mspec = none →
        NMg c i = Except.map (fun x => NuCDef.ofCDef x (c.mspec.or i.mspec)) (Mg c.toCDef i.toCDef)) ∧
    ∀ (c i : NuCDef N A K) (ms ms' : MatchSpec N K),
      c.mspec = some ms → i.mspec = some ms' → ∃ m, NMg c i = Except.error m ∧ mod021_names m c.core.name
-/
#guard_msgs in #print NU_060

/-! ## The two lines, named (for the mutants) -/

section Lines

variable {N A K : Type}

/-- Line 1: with at most one match, the ν merge is the plain merge with that match attached. -/
def nu060_line1 (Mg : MergeFn N A) (NMg : NuMergeFn N A K) : Prop :=
  ∀ c i : NuCDef N A K, (c.mspec = none ∨ i.mspec = none) →
    NMg c i = (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (c.mspec.or i.mspec))

/-- Line 2: two matches reject, naming the caller-side transition. -/
def nu060_line2 (NMg : NuMergeFn N A K) : Prop :=
  ∀ (c i : NuCDef N A K) (ms ms' : MatchSpec N K), c.mspec = some ms → i.mspec = some ms' →
    ∃ m, NMg c i = .error m ∧ mod021_names m c.core.name

/-- NU-060 is its two lines. -/
theorem nu060_iff (Mg : MergeFn N A) (NMg : NuMergeFn N A K) :
    NU_060 Mg NMg ↔ nu060_line1 Mg NMg ∧ nu060_line2 NMg := Iff.rfl

end Lines

/-! ## Holds -/

section Holds

variable {N A K : Type}

/-- ✓ The reference ν merge satisfies NU-060 over every plain merge: with at most one match it
runs the plain merge and attaches that match, and with two matches it rejects with a message
that starts `Channel composition '<caller>'`. -/
@[evidence holds NU_060]
theorem NU_060_reference (Mg : MergeFn N A) : NU_060 Mg (refNuMerge (K := K) Mg) := by
  refine ⟨fun c i h => ?_, fun c i ms ms' hc hi => ⟨_, ?_, nuMatchMsg_names c.core.name⟩⟩
  · cases hc : c.mspec with
    | none => cases hi : i.mspec <;> simp [refNuMerge, hc, hi]
    | some ms =>
      cases hi : i.mspec with
      | none => simp [refNuMerge, hc, hi]
      | some ms' => rw [hc, hi] at h; simp at h
  · simp [refNuMerge, hc, hi]

/-- The witness pair of the composition wave satisfies MOD-021 and NU-060 together: the
reference channel merge for the plain definitions, and the reference ν merge over it. -/
theorem NU_060_with_MOD_021 [DecidableEq N] [ToString N] (Build : Trans N → Option String)
    (sq : Act A → Act A → Act A) (cm : CorrMergeFn N A) :
    MOD_021 Build sq cm timingStr (refMerge Build sq cm) ∧
      NU_060 (refMerge Build sq cm) (refNuMerge (K := K) (refMerge Build sq cm)) :=
  ⟨MOD_021_reference Build sq cm, NU_060_reference _⟩

end Holds

/-! ## Consequences -/

section Consequences

variable {N A K : Type} {Mg : MergeFn N A} {NMg : NuMergeFn N A K}

/-- **A success keeps the match** (AC1): a successful ν merge has at most one side with a match,
carries that match (none when neither side has one), and its definition without the match is a
success of the plain merge. -/
theorem NU_060_keeps (h : NU_060 Mg NMg) {c i d : NuCDef N A K} (hd : NMg c i = .ok d) :
    (c.mspec = none ∨ i.mspec = none) ∧ d.mspec = c.mspec.or i.mspec ∧
      Mg c.toCDef i.toCDef = .ok d.toCDef := by
  have hone : c.mspec = none ∨ i.mspec = none := by
    cases hc : c.mspec with
    | none => exact Or.inl rfl
    | some ms =>
      cases hi : i.mspec with
      | none => exact Or.inr rfl
      | some ms' =>
        obtain ⟨m, hm, -⟩ := h.2 c i ms ms' hc hi
        rw [hm] at hd; cases hd
  refine ⟨hone, ?_⟩
  rw [h.1 c i hone] at hd
  obtain ⟨x, hx, rfl⟩ := except_map_ok_iff.1 hd
  exact ⟨rfl, hx⟩

/-- **No match is dropped** (AC1): when a ν merge succeeds, a caller's match and an instance's
match are both still on the merged definition. -/
theorem NU_060_neverDrops (h : NU_060 Mg NMg) {c i d : NuCDef N A K} (hd : NMg c i = .ok d)
    {ms : MatchSpec N K} : (c.mspec = some ms → d.mspec = some ms) ∧
      (i.mspec = some ms → d.mspec = some ms) := by
  obtain ⟨hone, hm, -⟩ := NU_060_keeps h hd
  refine ⟨fun hc => by rw [hm, hc]; rfl, fun hi => ?_⟩
  rcases hone with hc | hi'
  · rw [hm, hc, hi]; rfl
  · rw [hi'] at hi; cases hi

/-- **A correlated input is merged by the table** (with [MOD-021]): when neither side has two
input arcs on one place and a ν merge succeeds, the merged definition has the input arcs MOD-021's
line 2 gives, whether an arc is correlated or not, and it keeps the match. So a correlated
`one()` on a place and the other side's `one()` on the same place give one `exactly(2)` arc, and
the match that survives still keys that place. -/
@[evidence cites "NU-060" "A correlated input is therefore merged by the canonical input-arc merge table like any other input arc: a correlated `one()` and the other side's `one()` on the same place give one `exactly(2)` arc that the surviving match still correlates."]
theorem NU_060_table [DecidableEq N] [ToString N] {Build : Trans N → Option String}
    {sq : Act A → Act A → Act A} {cm : CorrMergeFn N A} {tstr : Timing → String}
    (h21 : MOD_021 Build sq cm tstr Mg) (h : NU_060 Mg NMg) {c i d : NuCDef N A K}
    (hc : mod021_inOnce c.toCDef) (hi : mod021_inOnce i.toCDef) (hd : NMg c i = .ok d) :
    mod021_inputsMerged c.toCDef i.toCDef d.toCDef ∧ d.mspec = c.mspec.or i.mspec := by
  obtain ⟨-, hm, hok⟩ := NU_060_keeps h hd
  exact ⟨h21.2.1 _ _ _ hc hi hok, hm⟩

/-- **NU-060 fixes the ν merge** once the plain merge is fixed: two ν merges that satisfy the
block over the same plain merge give the same result on every pair with at most one match, and
both reject every pair with two matches. -/
theorem NU_060_determined {NMg' : NuMergeFn N A K} (h : NU_060 Mg NMg) (h' : NU_060 Mg NMg')
    (c i : NuCDef N A K) :
    ((c.mspec = none ∨ i.mspec = none) → NMg c i = NMg' c i) ∧
      (∀ ms ms', c.mspec = some ms → i.mspec = some ms' →
        (∃ m, NMg c i = .error m) ∧ ∃ m, NMg' c i = .error m) := by
  refine ⟨fun hone => by rw [h.1 c i hone, h'.1 c i hone], fun ms ms' hc hi => ?_⟩
  obtain ⟨m, hm, -⟩ := h.2 c i ms ms' hc hi
  obtain ⟨m', hm', -⟩ := h'.2 c i ms ms' hc hi
  exact ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩

end Consequences

/-! ## The surviving match still correlates (on the reference) -/

section StillCorrelates

variable {N A K : Type} [DecidableEq N]

/-- Inserting an arc into a list of arcs keeps every place of the list and adds the inserted
arc's place. -/
theorem nu060_insertInE_keeps :
    ∀ (acc : List (NInSpec N)) (s : NInSpec N) (acc' : List (NInSpec N)),
      insertInE acc s = .ok acc' →
        s.place ∈ acc'.map (·.place) ∧ ∀ p ∈ acc.map (·.place), p ∈ acc'.map (·.place)
  | [], s, acc', h => by
    simp only [insertInE, Except.ok.injEq] at h
    subst h
    simp
  | a :: rest, s, acc', h => by
    unfold insertInE at h
    split at h
    · rename_i he
      split at h
      · cases h
        refine ⟨by simp [he], fun p hp => ?_⟩
        simp only [List.map_cons, List.mem_cons] at hp ⊢
        exact hp
      · cases h
    · obtain ⟨r, hr, rfl⟩ := except_map_ok_iff.1 h
      obtain ⟨h1, h2⟩ := nu060_insertInE_keeps rest s r hr
      refine ⟨by simp only [List.map_cons, List.mem_cons]; exact Or.inr h1, fun p hp => ?_⟩
      simp only [List.map_cons, List.mem_cons] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (h2 p hp)

/-- Folding arcs in keeps every place of the start list and of the folded arcs. -/
theorem nu060_foldlM_keeps :
    ∀ (xs acc ys : List (NInSpec N)), xs.foldlM insertInE acc = .ok ys →
      ∀ p, p ∈ acc.map (·.place) ++ xs.map (·.place) → p ∈ ys.map (·.place)
  | [], acc, ys, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | x :: xs, acc, ys, h => by
    rw [List.foldlM_cons] at h
    cases hx : insertInE acc x with
    | error e => rw [hx] at h; cases h
    | ok acc' =>
      rw [hx] at h
      simp only [bind, Except.bind] at h
      obtain ⟨h1, h2⟩ := nu060_insertInE_keeps acc x acc' hx
      intro p hp
      apply nu060_foldlM_keeps xs acc' ys h p
      simp only [List.map_cons, List.mem_append, List.mem_cons] at hp
      rcases hp with hp | hp | hp
      · exact List.mem_append_left _ (h2 p hp)
      · subst hp; exact List.mem_append_left _ h1
      · exact List.mem_append_right _ hp

/-- **Merging drops no place**: every place of an input arc is the place of a merged arc. -/
theorem nu060_mergeInputsE_keeps {xs ys : List (NInSpec N)} (h : mergeInputsE xs = .ok ys) :
    ∀ p ∈ xs.map (·.place), p ∈ ys.map (·.place) := fun p hp =>
  nu060_foldlM_keeps xs [] ys h p (by simpa using hp)

variable [ToString N] {Build : Trans N → Option String} {sq : Act A → Act A → Act A}
  {cm : CorrMergeFn N A}

/-- **The surviving match still keys input places** ([NU-020]): when the reference ν merge
succeeds, the match of either side keys only input places of the merged transition, if it keyed
only input places of its side. -/
theorem refNuMerge_keysOnInputs {c i d : NuCDef N A K} {ms : MatchSpec N K}
    (hd : refNuMerge (refMerge Build sq cm) c i = .ok d) :
    (c.mspec = some ms → KeysOnInputs c.toNuTrans ms → KeysOnInputs d.toNuTrans ms) ∧
      (i.mspec = some ms → KeysOnInputs i.toNuTrans ms → KeysOnInputs d.toNuTrans ms) := by
  obtain ⟨-, -, hok⟩ := NU_060_keeps (NU_060_reference _) hd
  have hin := (refMerge_ok_fields hok).2.2.2.2.2.2.2.2.1
  have keep := nu060_mergeInputsE_keeps hin
  refine ⟨fun _ hk p hp => ?_, fun _ hk p hp => ?_⟩
  · have := hk p hp
    simp only [inPlaces, NuCDef.toNuTrans, TransDef.toTrans] at this ⊢
    exact keep p (by rw [List.map_append]; exact List.mem_append_left _ this)
  · have := hk p hp
    simp only [inPlaces, NuCDef.toNuTrans, TransDef.toTrans] at this ⊢
    exact keep p (by rw [List.map_append]; exact List.mem_append_right _ this)

/-- **The surviving match still relays into output places** ([NU-054]): when the reference ν
merge succeeds, the relay targets of either side's match are declared once each and are output
places of the merged transition, if they were so on that side. -/
theorem refNuMerge_relaysOK {c i d : NuCDef N A K} {ms : MatchSpec N K}
    (hd : refNuMerge (refMerge Build sq cm) c i = .ok d) :
    (c.mspec = some ms → RelaysOK c.toNuTrans ms → RelaysOK d.toNuTrans ms) ∧
      (i.mspec = some ms → RelaysOK i.toNuTrans ms → RelaysOK d.toNuTrans ms) := by
  obtain ⟨-, -, hok⟩ := NU_060_keeps (NU_060_reference _) hd
  have hout : d.out = mergeOut c.out i.out := (refMerge_ok_fields hok).2.2.2.1
  refine ⟨fun _ ⟨hnd, hr⟩ => ⟨hnd, fun p hp => ?_⟩, fun _ ⟨hnd, hr⟩ => ⟨hnd, fun p hp => ?_⟩⟩
  · obtain ⟨o, ho, hpo⟩ := hr p hp
    simp only [NuCDef.toNuTrans, TransDef.toTrans] at ho ⊢
    cases hi : i.out with
    | none => exact ⟨o, by rw [hout, ho, hi]; rfl, hpo⟩
    | some oi =>
      exact ⟨.and o oi, by rw [hout, ho, hi]; rfl, by simp [outPlaces, hpo]⟩
  · obtain ⟨o, ho, hpo⟩ := hr p hp
    simp only [NuCDef.toNuTrans, TransDef.toTrans] at ho ⊢
    cases hc : c.out with
    | none => exact ⟨o, by rw [hout, ho, hc]; rfl, hpo⟩
    | some oc =>
      exact ⟨.and oc o, by rw [hout, ho, hc]; rfl, by simp [outPlaces, hpo]⟩

end StillCorrelates

/-! ## Examples over named places, list actions and named keys -/

section Examples

/-- An example match keyed on places `P` and `R`, both by the key `orderId`. -/
def nu060_msPR : MatchSpec String String := ⟨[("P", "orderId"), ("R", "orderId")], []⟩

/-- An example match keyed on places `U` and `V`, both by the key `orderId`. -/
def nu060_msUV : MatchSpec String String := ⟨[("U", "orderId"), ("V", "orderId")], []⟩

/-- An example definition: name, input arcs, output specification and match. -/
def nu060_def (nm : String) (ins : List (NInSpec String)) (out : Option (Out String))
    (ms : Option (MatchSpec String String)) : NuCDef String (List String) String :=
  NuCDef.ofCDef (mergeExDef nm ins out) ms

/-- The matched join `T`: one token from `P` and one from `R`, joined by name, into `Q`. -/
def nu060_join : NuCDef String (List String) String :=
  nu060_def "T" [⟨"P", .one⟩, ⟨"R", .one⟩] (some (.place "Q")) (some nu060_msPR)

/-- A passthrough channel transition `C`: one token from `X` into `Y`, no match. -/
def nu060_side : NuCDef String (List String) String :=
  nu060_def "C" [⟨"X", .one⟩] (some (.place "Y")) none

/-- A channel transition `C` without a match that also takes one token from `P`. -/
def nu060_sideP : NuCDef String (List String) String :=
  nu060_def "C" [⟨"P", .one⟩] (some (.place "Y")) none

/-- A caller `T` without a match: one token from `X` into `Q`. -/
def nu060_plain : NuCDef String (List String) String :=
  nu060_def "T" [⟨"X", .one⟩] (some (.place "Q")) none

/-- A matched channel transition `C`: one token from `U` and one from `V`, joined by name, into
`Y`. -/
def nu060_joinUV : NuCDef String (List String) String :=
  nu060_def "C" [⟨"U", .one⟩, ⟨"V", .one⟩] (some (.place "Y")) (some nu060_msUV)

/-- A channel transition `C` without a match that takes every token from `P`: `one()` and `all()`
on one place have no merge in the table, so the plain merge with the join `T` rejects. -/
def nu060_sideAllP : NuCDef String (List String) String :=
  nu060_def "C" [⟨"P", .all⟩] (some (.place "Y")) none

/-- What a successful merge holds: its input arcs and the places its match keys. -/
def nu060_view (r : Except String (NuCDef String (List String) String)) :
    Option (List (String × Card) × Option (List String)) :=
  r.toOption.map fun d => (d.core.inputs.map fun s => (s.place, s.card), d.mspec.map (·.keyPlaces))

/-- The message of a rejection, `none` for a success. -/
def nu060_msg (r : Except String (NuCDef String (List String) String)) : Option String :=
  match r with
  | .error m => some m
  | .ok _ => none

set_option maxRecDepth 20000 in
/-- ✓ Worked example on the reference merge (the reference builder, list actions). A join `T`
that takes one token each from `P` and `R` by name, merged with a passthrough channel
transition that takes from `X`, gives one transition taking from `P`, `R` and `X` that still
joins on `P` and `R`. If the channel transition instead takes one token from `P` too, the two
`one()` arcs on `P` become one `exactly(2)` arc, and the match still keys `P`: the merged join
takes two tokens of the chosen name there. A plain caller merged with a matched channel
transition keeps the channel transition's match on `U` and `V`. Two matched sides are rejected
with the message that starts `Channel composition 'T'`. -/
@[evidence nonvacuous NU_060]
theorem NU_060_nonvacuous :
    nu060_view (refNuMerge mergeEx nu060_join nu060_side) =
      some ([("P", .one), ("R", .one), ("X", .one)], some ["P", "R"]) ∧
    nu060_view (refNuMerge mergeEx nu060_join nu060_sideP) =
      some ([("P", .exactly 2), ("R", .one)], some ["P", "R"]) ∧
    nu060_view (refNuMerge mergeEx nu060_plain nu060_joinUV) =
      some ([("X", .one), ("U", .one), ("V", .one)], some ["U", "V"]) ∧
    nu060_msg (refNuMerge mergeEx nu060_join nu060_joinUV) = some (nuMatchMsg "T") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Examples

/-! ## Wrong merges -/

section Wrong

variable {N A K : Type}

/-- Caller wins: never reject, keep the caller's match when both sides carry one. -/
def nu060_callerWins (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (c.mspec.or i.mspec))

/-- Drop the match: reject two matches, but never carry a match into the merged transition. -/
def nu060_dropMatch (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | _, _ => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · none)

/-- Caller only: reject two matches, and carry the caller's match only. -/
def nu060_callerOnly (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | mc, _ => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · mc)

/-- A definition with its input arcs on the places `ks` removed. -/
def nu060_dropArcsOn [DecidableEq N] (ks : List N) (d : CDef N A) : CDef N A :=
  { d with core := { d.core with inputs := d.core.inputs.filter fun s => decide (s.place ∉ ks) } }

/-- The count stays: keep the match, but merge without the other side's input arcs on the keyed
places, so a correlated arc keeps its pre-merge count. -/
def nu060_countStays [DecidableEq N] (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | some ms, none =>
    (Mg c.toCDef (nu060_dropArcsOn ms.keyPlaces i.toCDef)).map (NuCDef.ofCDef · (some ms))
  | none, some ms =>
    (Mg (nu060_dropArcsOn ms.keyPlaces c.toCDef) i.toCDef).map (NuCDef.ofCDef · (some ms))
  | none, none => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · none)

/-- The old text read literally: reject two matches that key a common place, and fuse two
matches on different places into one match with the keys and relays of both. -/
def nu060_fuseDisjoint [DecidableEq N] (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some a, some b =>
    if a.keyPlaces.any (· ∈ b.keyPlaces) then .error (nuMatchMsg c.core.name)
    else (Mg c.toCDef i.toCDef).map
      (NuCDef.ofCDef · (some ⟨a.keys ++ b.keys, a.relays ++ b.relays⟩))
  | mc, mi => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (mc.or mi))

/-- Own error: with one match, report the match rejection whenever the plain merge rejects,
in place of the plain merge's own message. -/
def nu060_ownError (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | none, none => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · none)
  | mc, mi =>
    match Mg c.toCDef i.toCDef with
    | .error _ => .error (nuMatchMsg c.core.name)
    | .ok d => .ok (NuCDef.ofCDef d (mc.or mi))

/-- Reject shared places: with one match, reject when the other side has an input arc on a place
the match keys (refusing to merge a correlated arc with an uncorrelated one). -/
def nu060_rejectShared [DecidableEq N] (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error (nuMatchMsg c.core.name)
  | some ms, none =>
    if (i.core.inputs.map (·.place)).any (· ∈ ms.keyPlaces) then .error (nuMatchMsg c.core.name)
    else (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (some ms))
  | none, some ms =>
    if (c.core.inputs.map (·.place)).any (· ∈ ms.keyPlaces) then .error (nuMatchMsg c.core.name)
    else (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (some ms))
  | none, none => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · none)

/-- Reject two matches with an empty message. -/
def nu060_silent (Mg : MergeFn N A) : NuMergeFn N A K := fun c i =>
  match c.mspec, i.mspec with
  | some _, some _ => .error ""
  | mc, mi => (Mg c.toCDef i.toCDef).map (NuCDef.ofCDef · (mc.or mi))

/-- Line 1 at a pair, read off a decided view: if the two sides of line 1 have different views,
the line fails. -/
theorem nu060_line1_view {NMg : NuMergeFn String (List String) String}
    (h : NU_060 mergeEx NMg) {c i : NuCDef String (List String) String}
    (hone : c.mspec = none ∨ i.mspec = none)
    (hv : nu060_view (NMg c i) ≠
      nu060_view ((mergeEx c.toCDef i.toCDef).map (NuCDef.ofCDef · (c.mspec.or i.mspec)))) :
    False :=
  hv (by rw [h.1 c i hone])

/-- Line 1 at a pair, read off a decided message: if the two sides of line 1 give different
rejection messages (or one rejects and the other does not), the line fails. -/
theorem nu060_line1_msg {NMg : NuMergeFn String (List String) String}
    (h : NU_060 mergeEx NMg) {c i : NuCDef String (List String) String}
    (hone : c.mspec = none ∨ i.mspec = none)
    (hv : nu060_msg (NMg c i) ≠
      nu060_msg ((mergeEx c.toCDef i.toCDef).map (NuCDef.ofCDef · (c.mspec.or i.mspec)))) :
    False :=
  hv (by rw [h.1 c i hone])

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that reports its own error. The join `T` takes one token from `P`
by name; the channel transition takes every token from `P`. `one()` and `all()` have no merge,
so the plain merge rejects with the message about the two arcs on `P`. This merge rejects with
the message about two matches, although only `T` has a match, so line 1 fails: the same pair
must be rejected with the same message. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_ownError : ¬ NU_060 mergeEx (nu060_ownError (K := String) mergeEx) :=
  fun h => nu060_line1_msg h (c := nu060_join) (i := nu060_sideAllP) (Or.inr rfl) (by decide)

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that refuses to merge a correlated arc with an uncorrelated one.
The join `T` keyed on `P` and `R` merged with a channel transition that also takes one token
from `P` must give one `exactly(2)` arc on `P` that the match still keys, as the plain merge
does; this merge rejects the pair, so line 1 fails. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_rejectShared :
    ¬ NU_060 mergeEx (nu060_rejectShared (K := String) mergeEx) :=
  fun h => nu060_line1_msg h (c := nu060_join) (i := nu060_sideP) (Or.inr rfl) (by decide)

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that keeps no match. The join `T` keyed on `P` and `R` merged with
a passthrough side must still join on `P` and `R`; this merge gives a transition with the same
arcs and no match, so line 1 fails (and AC1 with it). -/
@[evidence forbids NU_060]
theorem NU_060_forbids_dropMatch : ¬ NU_060 mergeEx (nu060_dropMatch (K := String) mergeEx) :=
  fun h => nu060_line1_view h (c := nu060_join) (i := nu060_side) (Or.inr rfl) (by decide)

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that keeps only the caller's match. A plain caller merged with the
channel transition keyed on `U` and `V` must keep that match; this merge drops it, so line 1
fails. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_callerOnly : ¬ NU_060 mergeEx (nu060_callerOnly (K := String) mergeEx) :=
  fun h => nu060_line1_view h (c := nu060_plain) (i := nu060_joinUV) (Or.inl rfl) (by decide)

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that keeps the match but leaves the correlated arc at its count.
The join `T` takes one token from `P` by name, and the channel transition takes one from `P`
too; the merged join must take `exactly(2)` from `P`. This merge leaves `one()`, so line 1
fails. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_countStays : ¬ NU_060 mergeEx (nu060_countStays (K := String) mergeEx) :=
  fun h => nu060_line1_view h (c := nu060_join) (i := nu060_sideP) (Or.inr rfl) (by decide)

set_option maxRecDepth 20000 in
/-- ✗ Worked example: caller wins. The join `T` keyed on `P` and `R` merged with the channel
transition keyed on `U` and `V` must be rejected; this merge succeeds with `T`'s match and drops
the other, so line 2 fails. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_callerWins : ¬ NU_060 mergeEx (nu060_callerWins (K := String) mergeEx) := by
  intro h
  obtain ⟨m, hm, -⟩ := h.2 nu060_join nu060_joinUV _ _ rfl rfl
  have hv : nu060_msg (nu060_callerWins mergeEx nu060_join nu060_joinUV) = none := by decide
  rw [hm] at hv
  cases hv

set_option maxRecDepth 20000 in
/-- ✗ Worked example: the old text read literally (ruling D81). The two matches key `P`, `R` and
`U`, `V`, no common place, so this merge fuses them into one match on all four places. Every
runtime rejects the pair, and so must the merge: line 2 fails. -/
@[evidence forbids NU_060]
theorem NU_060_forbids_fuseDisjoint :
    ¬ NU_060 mergeEx (nu060_fuseDisjoint (K := String) mergeEx) := by
  intro h
  obtain ⟨m, hm, -⟩ := h.2 nu060_join nu060_joinUV _ _ rfl rfl
  have hv : nu060_msg (nu060_fuseDisjoint mergeEx nu060_join nu060_joinUV) = none := by decide
  rw [hm] at hv
  cases hv

/-! ### Mutants: the block without one of its parts -/

/-- NU-060 without line 2: only line 1. -/
def NU_060_mutant_line1Only (Mg : MergeFn N A) (NMg : NuMergeFn N A K) : Prop :=
  nu060_line1 Mg NMg

/-- NU-060 without line 1: only line 2 (the plain merge `Mg` is not read). -/
def NU_060_mutant_line2Only (_Mg : MergeFn N A) (NMg : NuMergeFn N A K) : Prop :=
  nu060_line2 NMg

/-- NU-060 with line 2 asking for a rejection, not for one that names the caller. -/
def NU_060_mutant_anyMessage (Mg : MergeFn N A) (NMg : NuMergeFn N A K) : Prop :=
  nu060_line1 Mg NMg ∧
    ∀ (c i : NuCDef N A K) (ms ms' : MatchSpec N K), c.mspec = some ms → i.mspec = some ms' →
      ∃ m, NMg c i = .error m

/-- ✗ Worked example: caller wins meets line 1 (with at most one match it is the plain merge
with that match), but not NU-060: two matched sides merge. Line 2 is load-bearing. -/
@[evidence mutant NU_060]
theorem NU_060_mutant_line1Only_killed :
    NU_060_mutant_line1Only mergeEx (nu060_callerWins (K := String) mergeEx) ∧
      ¬ NU_060 mergeEx (nu060_callerWins (K := String) mergeEx) :=
  ⟨fun _ _ _ => rfl, NU_060_forbids_callerWins⟩

/-- ✗ Worked example: the merge that drops every match meets line 2 (it rejects two matches,
naming the caller), but not NU-060: a matched join merged with a passthrough side loses its
match. Line 1 is load-bearing. -/
@[evidence mutant NU_060]
theorem NU_060_mutant_line2Only_killed :
    NU_060_mutant_line2Only mergeEx (nu060_dropMatch (K := String) mergeEx) ∧
      ¬ NU_060 mergeEx (nu060_dropMatch (K := String) mergeEx) :=
  ⟨fun c i ms ms' hc hi =>
      ⟨_, by simp [nu060_dropMatch, hc, hi], nuMatchMsg_names c.core.name⟩,
    NU_060_forbids_dropMatch⟩

set_option maxRecDepth 20000 in
/-- ✗ Worked example: a merge that rejects two matched sides with an empty message meets line 1
and rejects the pair, but the message does not name the caller `T`. The naming in line 2 is
load-bearing. -/
@[evidence mutant NU_060]
theorem NU_060_mutant_anyMessage_killed :
    NU_060_mutant_anyMessage mergeEx (nu060_silent (K := String) mergeEx) ∧
      ¬ NU_060 mergeEx (nu060_silent (K := String) mergeEx) := by
  refine ⟨⟨fun c i hone => ?_, fun c i ms ms' hc hi => ⟨"", by simp [nu060_silent, hc, hi]⟩⟩, ?_⟩
  · rcases hone with hc | hi
    · simp [nu060_silent, hc]
    · cases hc : c.mspec <;> simp [nu060_silent, hc, hi]
  · intro h
    obtain ⟨m, hm, hn⟩ := h.2 nu060_join nu060_joinUV _ _ rfl rfl
    have : m = "" := by
      have e : nu060_silent (K := String) mergeEx nu060_join nu060_joinUV = .error "" := rfl
      rw [e] at hm; cases hm; rfl
    subst this
    have hT : nu060_join.core.name = "T" := rfl
    rw [hT] at hn
    unfold mod021_names at hn
    simp at hn

end Wrong

end Libpetri.Spec
