/-
# The enablement machinery: presence bits and the dirty-set optimization

Models the control state of `PrecompiledBackend`
(`rust/libpetri-runtime/src/precompiled_backend.rs`) at bit granularity:
`marking_bitmap` (presence), `enabled_bitmap`, `dirty_bitmap`. The u64 word
packing and the two-level summaries are not modelled (PERF-042 AC4 pins the
words to the bit semantics differentially); `enabled_word_summary` exactness
and `dirty_word_summary` over-approximation are word-layer facts with no
bit-level content.

The theorems here are the plan's PB/EN group:

* PB1 `PresenceOK` + its preservation — `marking_bitmap` bit `p` ⟺
  `token_counts[p] > 0`. The subtle direction is clearing: only *consumption*
  places are re-examined after a firing (`update_bitmap_after_consumption`),
  which suffices exactly because only consumption places lose tokens.
* EN5 `fireConsume_dirty_sound` — the load-bearing dirty-set soundness
  (CONC-005): any state change that can flip another transition's
  enablement marks it dirty, because `mark_place_dirty` covers
  `affected_transitions` = every transition touching the place via input,
  read, inhibitor, or reset arc, and `canEnable` only reads touched places.
* `disable_frame` — `disable` (EXEC-003 loser path) changes no place counts,
  so not marking dirty is sound.
* EN6 `updateEnablement_sync` — after the dirty scan, every transition's
  `enabled` bit equals `canEnable`, given the running invariant
  `EnabledSync` (clean bits are accurate).
-/
import Libpetri.Conservation

namespace Libpetri

/-- Transition id — the dense index `CompiledNet` assigns. -/
abbrev TId := Nat

/-- The compiled net, as the tid-indexed list of its transitions. -/
abbrev Net := List Transition

/-- The backend's control-plus-storage state:
`ring` = the flat token pool, `presence` = `marking_bitmap`,
`enabled` = `enabled_bitmap`, `dirty` = `dirty_bitmap` — all at bit
granularity. -/
structure PBState where
  ring     : Pool
  presence : PlaceId → Bool
  enabled  : TId → Bool
  dirty    : TId → Bool

/-- `t` references `p` through any arc — membership in
`CompiledNet::affected_transitions(p)` (`compiled_net.rs`, the reverse index
over input ∪ read ∪ inhibitor ∪ reset arcs; its `Vec` iteration order is
nondeterministic and deliberately not modelled — only membership matters). -/
def touches (t : Transition) (p : PlaceId) : Prop :=
  (∃ sp ∈ t.inputs, sp.place = p) ∨ p ∈ t.reads ∨ p ∈ t.inhibitors ∨ p ∈ t.resets

instance (t : Transition) (p : PlaceId) : Decidable (touches t p) := by
  unfold touches
  infer_instance

/-- The places `t` consumes from: input places then reset places —
`CompiledNet::consumption_place_ids` (there deduplicated; duplication is
harmless here since only membership matters). -/
def consumptionPlaces (t : Transition) : List PlaceId :=
  t.inputs.map (·.place) ++ t.resets

/-- `t` consumes from `p`. -/
def consumesFrom (t : Transition) (p : PlaceId) : Prop :=
  p ∈ consumptionPlaces t

instance (t : Transition) (p : PlaceId) : Decidable (consumesFrom t p) := by
  unfold consumesFrom
  infer_instance

theorem consumesFrom_iff {t : Transition} {p : PlaceId} :
    consumesFrom t p ↔ (∃ sp ∈ t.inputs, sp.place = p) ∨ p ∈ t.resets := by
  unfold consumesFrom consumptionPlaces
  rw [List.mem_append, List.mem_map]

theorem consumesFrom_touches {t : Transition} {p : PlaceId}
    (h : consumesFrom t p) : touches t p := by
  rcases consumesFrom_iff.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))

private theorem all_congr' {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- `canEnable` reads only touched places (CONC-005's justification): pools
agreeing on every touched place's count agree on enablement. -/
theorem canEnable_congr {s₁ s₂ : Pool} {t : Transition}
    (h : ∀ p, touches t p → s₁.cnt p = s₂.cnt p) :
    canEnable s₁ t = canEnable s₂ t := by
  unfold canEnable
  have hA : t.inputs.all (fun sp =>
        decide (0 < s₁.cnt sp.place) && decide (sp.card.required ≤ s₁.cnt sp.place))
      = t.inputs.all (fun sp =>
        decide (0 < s₂.cnt sp.place) && decide (sp.card.required ≤ s₂.cnt sp.place)) :=
    all_congr' (fun sp hsp => by rw [h sp.place (Or.inl ⟨sp, hsp, rfl⟩)])
  have hB : t.reads.all (fun p => decide (0 < s₁.cnt p))
      = t.reads.all (fun p => decide (0 < s₂.cnt p)) :=
    all_congr' (fun p hp => by rw [h p (Or.inr (Or.inl hp))])
  have hC : t.inhibitors.all (fun p => s₁.cnt p == 0)
      = t.inhibitors.all (fun p => s₂.cnt p == 0) :=
    all_congr' (fun p hp => by rw [h p (Or.inr (Or.inr (Or.inl hp)))])
  rw [hA, hB, hC]

/-! ## The state transformers (untimed projections) -/

/-- `update_bitmap_after_consumption` + the consume itself: run
`consume_for_firing`'s pool effect, clear the presence bit of every
consumption place that hit zero, and mark every transition touching a
consumption place dirty. -/
def fireConsume (net : Net) (st : PBState) (tid : TId) : PBState :=
  match net[tid]? with
  | none => st
  | some t =>
    let r := (consumeForFiring st.ring t).1
    { ring := r.pool
      presence := fun p =>
        if consumesFrom t p ∧ r.pool.cnt p = 0 then false else st.presence p
      enabled := st.enabled
      dirty := fun tid' =>
        st.dirty tid' || match net[tid']? with
          | some t' => decide (∃ p ∈ consumptionPlaces t, touches t' p)
          | none => false }

/-- `produce_token` for a compiled place: `ring_add_last`, set the presence
bit, `mark_place_dirty`. -/
def produceOne (net : Net) (st : PBState) (p : PlaceId) (c : Colour) : PBState :=
  { ring := st.ring.addLast p c
    presence := fun q => if q = p then true else st.presence q
    enabled := st.enabled
    dirty := fun tid' =>
      st.dirty tid' || match net[tid']? with
        | some t' => decide (touches t' p)
        | none => false }

/-- `post_fire`: clear the enabled bit, mark the fired transition dirty. -/
def postFire (st : PBState) (tid : TId) : PBState :=
  { st with
    enabled := fun tid' => if tid' = tid then false else st.enabled tid'
    dirty := fun tid' => if tid' = tid then true else st.dirty tid' }

/-- `disable` (the EXEC-003 recheck-failed path): clear the enabled bit,
*without* marking dirty. -/
def disable (st : PBState) (tid : TId) : PBState :=
  { st with
    enabled := fun tid' => if tid' = tid then false else st.enabled tid' }

/-- `update_enablement` (untimed projection): re-evaluate every dirty
transition, clear the dirty set. -/
def updateEnablement (net : Net) (st : PBState) : PBState :=
  { st with
    enabled := fun tid => match net[tid]? with
      | some t => if st.dirty tid then canEnable st.ring t else st.enabled tid
      | none => st.enabled tid
    dirty := fun _ => false }

/-! ## Invariants -/

/-- PB1: the presence bit is exactly "the ring is non-empty". -/
def PresenceOK (st : PBState) : Prop :=
  ∀ p, p < st.ring.nplaces → (st.presence p = true ↔ 0 < st.ring.cnt p)

/-- The dirty-set contract: a *clean* transition's enabled bit is accurate.
This is what makes re-evaluating only dirty transitions (CONC-005) an
optimization instead of a soundness hole. -/
def EnabledSync (net : Net) (st : PBState) : Prop :=
  ∀ tid t, net[tid]? = some t → st.dirty tid = false →
    st.enabled tid = canEnable st.ring t

/-- Standing per-net hypotheses: every transition is compile-clean (fix (c))
and references only real places. -/
def NetOK (net : Net) (n : Nat) : Prop :=
  ∀ t ∈ net, DistinctInputPlaces t ∧ PlacesInBounds t n

/-! ## The consume frame: only consumption places change -/

/-- `consume_for_firing` changes counts only at consumption places. -/
theorem consumeForFiring_cnt_frame {s : Pool} (hwf : Pool.WF s)
    {t : Transition} (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t s.nplaces) (hen : canEnable s t = true) :
    ∀ q, q < s.nplaces → ¬consumesFrom t q →
      (consumeForFiring s t).1.pool.cnt q = s.cnt q := by
  intro q hq hnc
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs (r₀ := ⟨s, emptyBag, emptyBag⟩)
    hwf hdist (fun sp hm => hb.inputs sp hm) (fun sp hm => (henin sp hm).2)
  obtain ⟨j1, j2, j3, j4, j5⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hb.resets p hm)
  have hqin : ∀ sp ∈ t.inputs, sp.place ≠ q := by
    intro sp hm h
    exact hnc (consumesFrom_iff.mpr (Or.inl ⟨sp, hm, h⟩))
  have hqres : q ∉ t.resets := fun h => hnc (consumesFrom_iff.mpr (Or.inr h))
  obtain ⟨f2, f3⟩ := i5 q hq hqin
  obtain ⟨_, g2⟩ := j4 q (by rw [i2]; exact hq) hqres
  have hproj : (consumeForFiring s t).1.pool.proj q = s.proj q := by
    change (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
        (t.resets.map .reset)).pool.proj q = s.proj q
    rw [g2, f2]
  have hlen1 : ((consumeForFiring s t).1.pool.proj q).length
      = (consumeForFiring s t).1.pool.cnt q := by
    change ((execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
        (t.resets.map .reset)).pool.proj q).length = _
    exact Pool.proj_length j1 (by rw [j2, i2]; exact hq)
  have hlen2 : (s.proj q).length = s.cnt q := Pool.proj_length hwf hq
  rw [hproj, hlen2] at hlen1
  exact hlen1.symm

/-- WF and place-count survive the consume phase. -/
theorem consumeForFiring_wf {s : Pool} (hwf : Pool.WF s) {t : Transition}
    (hdist : DistinctInputPlaces t) (hb : PlacesInBounds t s.nplaces)
    (hen : canEnable s t = true) :
    Pool.WF (consumeForFiring s t).1.pool ∧
    (consumeForFiring s t).1.pool.nplaces = s.nplaces := by
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, _, _, _, _⟩ := execOps_inputs (r₀ := ⟨s, emptyBag, emptyBag⟩)
    hwf hdist (fun sp hm => hb.inputs sp hm) (fun sp hm => (henin sp hm).2)
  obtain ⟨j1, j2, _, _, _⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hb.resets p hm)
  refine ⟨j1, ?_⟩
  change (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
      (t.resets.map .reset)).pool.nplaces = s.nplaces
  rw [j2, i2]

/-- Consuming never creates tokens: per-place counts only shrink. -/
theorem consumeForFiring_cnt_le {s : Pool} (hwf : Pool.WF s) {t : Transition}
    (hdist : DistinctInputPlaces t) (hb : PlacesInBounds t s.nplaces)
    (hen : canEnable s t = true) :
    ∀ q, q < s.nplaces →
      (consumeForFiring s t).1.pool.cnt q ≤ s.cnt q := by
  intro q hq
  obtain ⟨hwf', hnp'⟩ := consumeForFiring_wf hwf hdist hb hen
  have hcons := token_conservation hwf hdist hb hen q hq
  have hlen1 : ((consumeForFiring s t).1.pool.proj q).length
      = (consumeForFiring s t).1.pool.cnt q :=
    Pool.proj_length hwf' (by rw [hnp']; exact hq)
  have hlen2 : (s.proj q).length = s.cnt q := Pool.proj_length hwf hq
  have := congrArg List.length hcons
  simp only [List.length_append] at this
  omega

/-! ## EN5 — dirty-set soundness -/

/-- **EN5 (CONC-005): the dirty set is sound over a firing's consume phase.**
If some transition's enablement could have flipped, it is marked dirty:
`canEnable` reads only touched places, only consumption places changed, and
every transition touching a consumption place got marked. -/
theorem fireConsume_dirty_sound {net : Net} {st : PBState} {tid : TId}
    {t : Transition} (hnet : net[tid]? = some t)
    (hwf : Pool.WF st.ring) (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t st.ring.nplaces)
    (hen : canEnable st.ring t = true)
    (htb : ∀ t' ∈ net, ∀ p, touches t' p → p < st.ring.nplaces) :
    ∀ tid' t', net[tid']? = some t' →
      canEnable (fireConsume net st tid).ring t' ≠ canEnable st.ring t' →
      (fireConsume net st tid).dirty tid' = true := by
  intro tid' t' hnet' hflip
  unfold fireConsume at hflip ⊢
  rw [hnet] at hflip ⊢
  show (st.dirty tid' || match net[tid']? with
    | some t'' => decide (∃ p ∈ consumptionPlaces t, touches t'' p)
    | none => false) = true
  rw [hnet']
  by_cases htouch : ∃ p ∈ consumptionPlaces t, touches t' p
  · simp [htouch]
  · exfalso
    apply hflip
    apply canEnable_congr
    intro p hp
    by_cases hc : consumesFrom t p
    · exact absurd ⟨p, hc, hp⟩ htouch
    · exact consumeForFiring_cnt_frame hwf hdist hb hen p
        (htb t' (List.mem_of_getElem? hnet') p hp) hc

/-- `disable` changes no counts, so every transition's enablement is
untouched — not marking dirty is sound (the EXEC-003 loser was already
marked by the winner's consume). -/
theorem disable_frame (st : PBState) (tid : TId) :
    ∀ t', canEnable (disable st tid).ring t' = canEnable st.ring t' :=
  fun _ => rfl

/-! ## PB1 preservation -/

theorem fireConsume_presence {net : Net} {st : PBState} {tid : TId}
    {t : Transition} (hnet : net[tid]? = some t)
    (hwf : Pool.WF st.ring) (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t st.ring.nplaces)
    (hen : canEnable st.ring t = true)
    (hpres : PresenceOK st) : PresenceOK (fireConsume net st tid) := by
  intro p hp
  unfold fireConsume at hp ⊢
  rw [hnet] at hp ⊢
  obtain ⟨hwf', hnp'⟩ := consumeForFiring_wf hwf hdist hb hen
  show (if consumesFrom t p ∧ (consumeForFiring st.ring t).1.pool.cnt p = 0
      then false else st.presence p) = true
    ↔ 0 < (consumeForFiring st.ring t).1.pool.cnt p
  have hp0 : p < st.ring.nplaces := by
    change p < (consumeForFiring st.ring t).1.pool.nplaces at hp
    rw [hnp'] at hp
    exact hp
  by_cases hzero : consumesFrom t p ∧ (consumeForFiring st.ring t).1.pool.cnt p = 0
  · rw [if_pos hzero]
    constructor
    · intro h; cases h
    · intro h; omega
  · rw [if_neg hzero]
    by_cases hc : consumesFrom t p
    · have hne : (consumeForFiring st.ring t).1.pool.cnt p ≠ 0 := by
        intro h
        exact hzero ⟨hc, h⟩
      have hmono := consumeForFiring_cnt_le hwf hdist hb hen p hp0
      rw [hpres p hp0]
      omega
    · rw [consumeForFiring_cnt_frame hwf hdist hb hen p hp0 hc]
      exact hpres p hp0

theorem produceOne_presence {net : Net} {st : PBState} {p : PlaceId}
    {c : Colour} (hwf : Pool.WF st.ring) (hp : p < st.ring.nplaces)
    (hpres : PresenceOK st) : PresenceOK (produceOne net st p c) := by
  intro q hq
  unfold produceOne at hq ⊢
  have hnp : (st.ring.addLast p c).nplaces = st.ring.nplaces := by
    unfold Pool.addLast
    by_cases hfull : st.ring.cnt p = st.ring.cap p <;>
      simp [hfull, Pool.pushLast, Pool.growRing]
  change q < (st.ring.addLast p c).nplaces at hq
  rw [hnp] at hq
  show (if q = p then true else st.presence q) = true
    ↔ 0 < (st.ring.addLast p c).cnt q
  have hlen : ((st.ring.addLast p c).proj q).length = (st.ring.addLast p c).cnt q :=
    Pool.proj_length (Pool.addLast_wf hwf hp c) (by rw [hnp]; exact hq)
  by_cases hqp : q = p
  · subst hqp
    rw [if_pos rfl]
    have hproj := Pool.addLast_proj_self hwf hp c
    have hl := congrArg List.length hproj
    rw [hlen, List.length_append] at hl
    simp only [List.length_cons, List.length_nil] at hl
    constructor
    · intro _; omega
    · intro _; rfl
  · rw [if_neg hqp]
    have hproj := Pool.addLast_proj_other hwf hp hq hqp c
    have hl := congrArg List.length hproj
    rw [hlen, Pool.proj_length hwf hq] at hl
    rw [hpres q hq]
    omega

/-! ## EN6 — the dirty scan restores full accuracy -/

/-- After `update_enablement`, every transition's enabled bit equals
`canEnable` — clean bits were already accurate (`EnabledSync`), dirty bits
are recomputed. This is the theorem that makes the dirty-set *optimization*
behaviorally invisible. -/
theorem updateEnablement_sync {net : Net} {st : PBState}
    (hsync : EnabledSync net st) :
    ∀ tid t, net[tid]? = some t →
      (updateEnablement net st).enabled tid = canEnable st.ring t := by
  intro tid t hnet
  show (match net[tid]? with
    | some t => if st.dirty tid then canEnable st.ring t else st.enabled tid
    | none => st.enabled tid) = canEnable st.ring t
  rw [hnet]
  show (if st.dirty tid then canEnable st.ring t else st.enabled tid)
      = canEnable st.ring t
  by_cases hd : st.dirty tid
  · rw [if_pos hd]
  · rw [if_neg hd]
    exact hsync tid t hnet (by simp at hd; exact hd)

/-- After the scan nothing is dirty. -/
theorem updateEnablement_clean (net : Net) (st : PBState) :
    ∀ tid, (updateEnablement net st).dirty tid = false := fun _ => rfl

end Libpetri
