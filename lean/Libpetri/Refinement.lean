/-
# The fast-path refinement: `PrecompiledBackend` ≡ `BitmapBackend`

The headline of the engine formalization. `BBState` is the reference
executor's state at `CMarking` level — `bitmap_backend.rs` keeps its tokens
in exactly that shape (`Marking` = FIFO list per place) — with the *same*
control formulas the precompiled backend uses (both are driven by the shared
`Executor` loop of `executor_core/executor.rs`). `Rel` relates a precompiled
state to a reference state by projecting the flat pool (`Pool.proj` =
`materialize_marking`) and demanding identical control bits.

`precompiled_refines_bitmap_immediate` then states: on the untimed/immediate
fragment (the `fast_path_available` production path, `collect_ready_immediate`
firing enabled transitions in ascending tid order), any number of executor
cycles started from related states end in related states — in particular the
materialized marking of the precompiled backend is the reference marking,
cycle for cycle. Actions are abstracted to a pure emission function `emit`
(same on both sides — both backends run the *same* action object); it
receives the delivered `inputs` and `reads` bags, which the bag-correspondence
lemmas prove identical, so identical outputs are sound, not assumed.

Scope: untimed, non-ν, sync fragment; fix (c) (`DistinctInputPlaces`) is a
standing hypothesis exactly because compilation now enforces it.

**The EXEC-003 recheck is idealized — identically on both sides.**
`pcRecheck` / `bbRecheck` below re-run enablement against the *live* marking.
The shipped `recheck_can_fire` does not, and since the EXEC-003 AC3/AC4 work
it diverges from the live marking in two ways, not one:

* presence comes from the fire-pass snapshot (`marking_bitmap`'s second half
  / `firing_snap_buffer`), copied from live once per pass when the ready list
  is collected and thereafter only ever *cleared*, one place at a time, by
  `update_bitmap_after_consumption`; and
* the counting checks run with `pre_deposit = true`, so `can_enable`
  subtracts the pass's `deposit_delta` from every cardinality gate and defers
  wholesale any ν-join whose correlated input took a same-pass deposit.

Here, by contrast, `pcFire` / `bbFire` append `emit`'s outputs into the very
marking the rest of the fold reads, so a same-pass deposit can re-enable a
later transition in this model where the shipped executor will not fire it
until the next cycle. Both backends implement the snapshot and the delta in
lockstep (`bitmap_backend.rs:708-713` and its precompiled twin call the same
`can_enable` shape), so the idealization is *equal* on the two sides and the
refinement statement below stands as a statement about their agreement — but
it is precisely why divergence #5 (a wholesale snapshot refresh on one side
only) was invisible here, and the AC4 counting side is invisible for the same
reason. Modelling the snapshot and the delta explicitly is the open item
recorded in `lean/README.md`.

**The consume is idealized the same way (EXEC-003 AC5).** Because this fold's
marking really does carry a same-pass deposit, this is the one model in the
development that *reaches* the case `Conservation.lean`'s header excludes: a
drain (`.all`, `.atLeast`, a reset) firing later in the fold takes that
deposit too, where both shipped backends stop at `drainable(p, live)` and
leave it for the next cycle. `consumeForFiring` and `bbConsumeMarking` both
drain to the live count, and the two `drainable`s agree body for body (place
name against pid lookup aside), are called at the same sites, and are gated by
the same per-pass `has_deposits`, so this idealization is *equal* on the two
sides exactly as the recheck one is: the theorem below
still says what it says about their agreement. What it would not see is an
AC5 divergence between them — the same blind spot, now with a third mechanism
behind it.
-/
import Libpetri.Refinement.Correspondence

namespace Libpetri

/-! ## `specAt` under distinct input places -/

private theorem find?_place_of_mem {l : List InSpec}
    (hdist : (l.map (·.place)).Pairwise (· ≠ ·))
    {sp : InSpec} (hmem : sp ∈ l) :
    l.find? (fun s => s.place == sp.place) = some sp := by
  induction l with
  | nil => cases hmem
  | cons a rest ih =>
    rw [List.map_cons, List.pairwise_cons] at hdist
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [List.find?_cons_of_pos (by simp)]
    · have hne : a.place ≠ sp.place :=
        hdist.1 sp.place (List.mem_map.mpr ⟨sp, hmem', rfl⟩)
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact ih hdist.2 hmem'

theorem specAt_eq_of_mem {t : Transition} (hdist : DistinctInputPlaces t)
    {sp : InSpec} (hmem : sp ∈ t.inputs) : specAt t sp.place = some sp :=
  find?_place_of_mem hdist hmem

theorem specAt_some_mem {t : Transition} {q : PlaceId} {sp : InSpec}
    (h : specAt t q = some sp) : sp ∈ t.inputs ∧ sp.place = q := by
  unfold specAt at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem specAt_none {t : Transition} {q : PlaceId}
    (h : specAt t q = none) : ∀ sp ∈ t.inputs, sp.place ≠ q := by
  intro sp hmem
  unfold specAt at h
  have := List.find?_eq_none.mp h sp hmem
  simpa using this

/-! ## Consume-phase correspondence -/

/-- The consume phase: pool projection lands on the reference marking. -/
theorem consume_marking_rel {n : Nat} {st : PBState} {bb : BBState}
    (hrel : Rel n st bb) {t : Transition} (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t n) (hen : canEnable st.ring t = true) :
    ∀ q, q < n →
      (consumeForFiring st.ring t).1.pool.proj q = bbConsumeMarking bb.marking t q := by
  intro q hq
  have hbs : PlacesInBounds t st.ring.nplaces := by rw [hrel.np]; exact hb
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs
    (r₀ := ⟨st.ring, emptyBag, emptyBag⟩)
    hrel.wf hdist (fun sp hm => hbs.inputs sp hm) (fun sp hm => (henin sp hm).2)
  obtain ⟨j1, j2, j3, j4, j5⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hbs.resets p hm)
  have hq' : q < st.ring.nplaces := by rw [hrel.np]; exact hq
  have hcnt : st.ring.cnt q = (bb.marking q).length := by
    rw [← hrel.prj q hq, Pool.proj_length hrel.wf hq']
  unfold bbConsumeMarking
  change (execOpsFrom (execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩
      (t.inputs.map opOfSpec)) (t.resets.map .reset)).pool.proj q = _
  by_cases hqres : q ∈ t.resets
  · obtain ⟨_, g2⟩ := j5 q (by rw [i2]; exact hq') hqres
    rw [g2, if_pos hqres]
  · obtain ⟨_, g2⟩ := j4 q (by rw [i2]; exact hq') hqres
    rw [g2, if_neg hqres]
    unfold bbPostInput
    cases hspec : specAt t q with
    | some sp =>
      obtain ⟨hmem, hplace⟩ := specAt_some_mem hspec
      obtain ⟨_, f2⟩ := i6 sp hmem
      rw [hplace] at f2
      rw [f2, hrel.prj q hq, hcnt]
    | none =>
      obtain ⟨f2, _⟩ := i5 q hq' (fun sp hm h => specAt_none hspec sp hm h)
      rw [f2]
      exact hrel.prj q hq

/-- The delivered `inputs` bags coincide — the action sees identical tokens. -/
theorem inputs_bag_rel {n : Nat} {st : PBState} {bb : BBState}
    (hrel : Rel n st bb) {t : Transition} (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t n) (hen : canEnable st.ring t = true) :
    (consumeForFiring st.ring t).1.inputs = bbInputsBag bb.marking t := by
  funext q
  have hbs : PlacesInBounds t st.ring.nplaces := by rw [hrel.np]; exact hb
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs
    (r₀ := ⟨st.ring, emptyBag, emptyBag⟩)
    hrel.wf hdist (fun sp hm => hbs.inputs sp hm) (fun sp hm => (henin sp hm).2)
  obtain ⟨j1, j2, j3, j4, j5⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hbs.resets p hm)
  change (execOpsFrom (execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩
      (t.inputs.map opOfSpec)) (t.resets.map .reset)).inputs q = _
  rw [j3]
  unfold bbInputsBag
  cases hspec : specAt t q with
  | some sp =>
    obtain ⟨hmem, hplace⟩ := specAt_some_mem hspec
    obtain ⟨f1, _⟩ := i6 sp hmem
    rw [hplace] at f1
    rw [f1]
    have hq : q < n := by
      have := hbs.inputs sp hmem
      rw [hplace] at this
      rw [← hrel.np]
      exact this
    have hq' : q < st.ring.nplaces := by rw [hrel.np]; exact hq
    have hcnt : st.ring.cnt q = (bb.marking q).length := by
      rw [← hrel.prj q hq, Pool.proj_length hrel.wf hq']
    show emptyBag q ++ _ = _
    rw [hrel.prj q hq, hcnt]
    simp [emptyBag]
  | none =>
    rw [i4 q (fun sp hm h => specAt_none hspec sp hm h)]
    rfl

/-- The `reads` bags coincide. -/
theorem reads_bag_rel {n : Nat} {st : PBState} {bb : BBState}
    (hrel : Rel n st bb) {t : Transition} (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t n) (hen : canEnable st.ring t = true) :
    (consumeForFiring st.ring t).2 = bbReadsBag (bbPostInput bb.marking t) t.reads := by
  have hbs : PlacesInBounds t st.ring.nplaces := by rw [hrel.np]; exact hb
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs
    (r₀ := ⟨st.ring, emptyBag, emptyBag⟩)
    hrel.wf hdist (fun sp hm => hbs.inputs sp hm) (fun sp hm => (henin sp hm).2)
  have hpt : ∀ p ∈ t.reads,
      (execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)).pool.peekFirst p
        = (bbPostInput bb.marking t p).head? := by
    intro p hmem
    have hp : p < n := by rw [← hrel.np]; exact hbs.reads p hmem
    have hp' : p < st.ring.nplaces := by rw [hrel.np]; exact hp
    rw [Pool.peekFirst_eq_head i1 (by rw [i2]; exact hp')]
    congr 1
    unfold bbPostInput
    cases hspec : specAt t p with
    | some sp =>
      obtain ⟨hmem', hplace⟩ := specAt_some_mem hspec
      obtain ⟨_, f2⟩ := i6 sp hmem'
      rw [hplace] at f2
      rw [f2]
      have hcnt : st.ring.cnt p = (bb.marking p).length := by
        rw [← hrel.prj p hp, Pool.proj_length hrel.wf hp']
      rw [hrel.prj p hp, hcnt]
    | none =>
      obtain ⟨f2, _⟩ := i5 p hp' (fun sp hm h => specAt_none hspec sp hm h)
      rw [f2]
      exact hrel.prj p hp
  show peekReads (execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩
      (t.inputs.map opOfSpec)).pool t.reads = _
  unfold peekReads bbReadsBag
  have : ∀ (l : List PlaceId), (∀ p ∈ l,
      (execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)).pool.peekFirst p
        = (bbPostInput bb.marking t p).head?) →
      ∀ (b : TokenBag),
      l.foldl (fun b p => addBag b p ((execOpsFrom ⟨st.ring, emptyBag, emptyBag⟩
          (t.inputs.map opOfSpec)).pool.peekFirst p).toList) b
        = l.foldl (fun b p => addBag b p (bbPostInput bb.marking t p).head?.toList) b := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons p rest ih =>
      intro h b
      show List.foldl _ (addBag b p _) rest = List.foldl _ (addBag b p _) rest
      rw [h p List.mem_cons_self]
      exact ih (fun p' hm => h p' (List.mem_cons_of_mem _ hm)) _
  exact this t.reads hpt emptyBag

/-! ## `Rel` preservation, operation by operation -/

theorem fireConsume_rel {n : Nat} {net : Net} {st : PBState} {bb : BBState}
    {tid : TId} {t : Transition} (hnet : net[tid]? = some t)
    (hrel : Rel n st bb) (hdist : DistinctInputPlaces t)
    (hb : PlacesInBounds t n) (hen : canEnable st.ring t = true) :
    Rel n (fireConsume net st tid) (bbFireConsume net bb tid) := by
  have hbs : PlacesInBounds t st.ring.nplaces := by rw [hrel.np]; exact hb
  obtain ⟨hwf', hnp'⟩ := consumeForFiring_wf hrel.wf hdist hbs hen
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [fireConsume_ring hnet]
    exact hwf'
  · rw [fireConsume_ring hnet, hnp', hrel.np]
  · intro p hp
    rw [fireConsume_ring hnet, bbFireConsume_marking hnet]
    exact consume_marking_rel hrel hdist hb hen p hp
  · rw [fireConsume_enabled, bbFireConsume_enabled]
    exact hrel.en
  · rw [fireConsume_dirty hnet, bbFireConsume_dirty hnet, hrel.dt]

theorem produceOne_rel {n : Nat} {net : Net} {st : PBState} {bb : BBState}
    {p : PlaceId} {c : Colour} (hrel : Rel n st bb) (hp : p < n) :
    Rel n (produceOne net st p c) (bbProduceOne net bb p c) := by
  have hp' : p < st.ring.nplaces := by rw [hrel.np]; exact hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Pool.addLast_wf hrel.wf hp' c
  · show (st.ring.addLast p c).nplaces = n
    rw [addLast_nplaces, hrel.np]
  · intro q hq
    have hq' : q < st.ring.nplaces := by rw [hrel.np]; exact hq
    show (st.ring.addLast p c).proj q
        = if q = p then bb.marking q ++ [c] else bb.marking q
    by_cases hqp : q = p
    · subst hqp
      rw [if_pos rfl, Pool.addLast_proj_self hrel.wf hp' c, hrel.prj q hq]
    · rw [if_neg hqp, Pool.addLast_proj_other hrel.wf hp' hq' hqp c,
        hrel.prj q hq]
  · exact hrel.en
  · show (fun tid' => st.dirty tid' || _) = fun tid' => bb.dirty tid' || _
    rw [hrel.dt]
    rfl

theorem produceMany_rel {n : Nat} {net : Net} {outs : List (PlaceId × Colour)} :
    ∀ {st : PBState} {bb : BBState}, Rel n st bb →
    (∀ e ∈ outs, e.1 < n) →
    Rel n (produceMany net st outs) (bbProduceMany net bb outs) := by
  induction outs with
  | nil => intro st bb hrel _; exact hrel
  | cons e rest ih =>
    intro st bb hrel hbound
    obtain ⟨p, c⟩ := e
    show Rel n (produceMany net (produceOne net st p c) rest)
        (bbProduceMany net (bbProduceOne net bb p c) rest)
    exact ih (produceOne_rel hrel (hbound (p, c) List.mem_cons_self))
      (fun e' hm => hbound e' (List.mem_cons_of_mem _ hm))

theorem postFire_rel {n : Nat} {st : PBState} {bb : BBState} {tid : TId}
    (hrel : Rel n st bb) : Rel n (postFire st tid) (bbPostFire bb tid) := by
  refine ⟨hrel.wf, hrel.np, hrel.prj, ?_, ?_⟩
  · show (fun tid' => if tid' = tid then false else st.enabled tid') = _
    rw [hrel.en]
    rfl
  · show (fun tid' => if tid' = tid then true else st.dirty tid') = _
    rw [hrel.dt]
    rfl

theorem disable_rel {n : Nat} {st : PBState} {bb : BBState} {tid : TId}
    (hrel : Rel n st bb) : Rel n (disable st tid) (bbDisable bb tid) := by
  refine ⟨hrel.wf, hrel.np, hrel.prj, ?_, hrel.dt⟩
  show (fun tid' => if tid' = tid then false else st.enabled tid') = _
  rw [hrel.en]
  rfl

theorem updateEnablement_rel {n : Nat} {net : Net} {st : PBState} {bb : BBState}
    (hrel : Rel n st bb) (hok : NetOK net n) :
    Rel n (updateEnablement net st) (bbUpdateEnablement net bb) := by
  refine ⟨hrel.wf, hrel.np, hrel.prj, ?_, rfl⟩
  funext tid
  show (match net[tid]? with
    | some t => if st.dirty tid then canEnable st.ring t else st.enabled tid
    | none => st.enabled tid) = (match net[tid]? with
    | some t => if bb.dirty tid then bbCanEnable bb.marking t else bb.enabled tid
    | none => bb.enabled tid)
  cases hnet : net[tid]? with
  | none =>
    show st.enabled tid = bb.enabled tid
    rw [hrel.en]
  | some t =>
    show (if st.dirty tid then canEnable st.ring t else st.enabled tid)
        = (if bb.dirty tid then bbCanEnable bb.marking t else bb.enabled tid)
    rw [hrel.dt, hrel.en,
      canEnable_rel hrel (hok t (List.mem_of_getElem? hnet)).2]

theorem recheck_rel {n : Nat} {net : Net} {st : PBState} {bb : BBState}
    {tid : TId} (hrel : Rel n st bb) (hok : NetOK net n) :
    pcRecheck net st tid = bbRecheck net bb tid := by
  unfold pcRecheck bbRecheck
  rw [hrel.en]
  cases hnet : net[tid]? with
  | none => rfl
  | some t =>
    show (bb.enabled tid && canEnable st.ring t)
        = (bb.enabled tid && bbCanEnable bb.marking t)
    rw [canEnable_rel hrel (hok t (List.mem_of_getElem? hnet)).2]

theorem pcFire_rel {n : Nat} {net : Net} {emit : Emit} {st : PBState}
    {bb : BBState} {tid : TId} (hrel : Rel n st bb) (hok : NetOK net n)
    (hemit : EmitOK emit n) (hre : pcRecheck net st tid = true) :
    Rel n (pcFire net emit st tid) (bbFire net emit bb tid) := by
  unfold pcFire bbFire
  cases hnet : net[tid]? with
  | none => exact hrel
  | some t =>
    have hmem := List.mem_of_getElem? hnet
    have hdist := (hok t hmem).1
    have hb := (hok t hmem).2
    have hen : canEnable st.ring t = true := by
      unfold pcRecheck at hre
      rw [hnet] at hre
      exact (Bool.and_eq_true .. |>.mp hre).2
    have hbags : emit tid (consumeForFiring st.ring t).1.inputs
          (consumeForFiring st.ring t).2
        = emit tid (bbInputsBag bb.marking t)
          (bbReadsBag (bbPostInput bb.marking t) t.reads) := by
      rw [inputs_bag_rel hrel hdist hb hen, reads_bag_rel hrel hdist hb hen]
    show Rel n (postFire (produceMany net (fireConsume net st tid) _) tid)
        (bbPostFire (bbProduceMany net (bbFireConsume net bb tid) _) tid)
    rw [hbags]
    exact postFire_rel (produceMany_rel
      (fireConsume_rel hnet hrel hdist hb hen)
      (fun e hm => hemit tid _ _ e hm))

/-! ## The cycle and the headline -/

theorem foldFire_rel {n : Nat} {net : Net} {emit : Emit} {ready : List TId} :
    ∀ {st : PBState} {bb : BBState}, Rel n st bb → NetOK net n →
    EmitOK emit n →
    Rel n
      (ready.foldl (fun s tid =>
        if pcRecheck net s tid then pcFire net emit s tid else disable s tid) st)
      (ready.foldl (fun b tid =>
        if bbRecheck net b tid then bbFire net emit b tid else bbDisable b tid) bb) := by
  induction ready with
  | nil => intro st bb hrel _ _; exact hrel
  | cons tid rest ih =>
    intro st bb hrel hok hemit
    show Rel n (rest.foldl _ (if pcRecheck net st tid then _ else _))
        (rest.foldl _ (if bbRecheck net bb tid then _ else _))
    rw [← recheck_rel hrel hok]
    by_cases hre : pcRecheck net st tid = true
    · rw [if_pos hre, if_pos hre]
      exact ih (pcFire_rel hrel hok hemit hre) hok hemit
    · rw [if_neg hre, if_neg hre]
      exact ih (disable_rel hrel) hok hemit

/-- One executor cycle preserves the refinement (immediate fragment:
`update_enablement`, then `collect_ready_immediate`'s ascending-tid pass with
the EXEC-003 recheck before each firing). -/
theorem pcCycle_rel {n : Nat} {net : Net} {emit : Emit} {st : PBState}
    {bb : BBState} (hrel : Rel n st bb) (hok : NetOK net n)
    (hemit : EmitOK emit n) :
    Rel n (pcCycle net emit st) (bbCycle net emit bb) := by
  unfold pcCycle bbCycle
  have hrel1 := updateEnablement_rel hrel hok
  have hready : ((List.range net.length).filter
        ((updateEnablement net st).enabled ·))
      = ((List.range net.length).filter
        ((bbUpdateEnablement net bb).enabled ·)) := by
    rw [hrel1.en]
  rw [hready]
  exact foldFire_rel hrel1 hok hemit

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iterate f k (f a)

/-- **The fast-path refinement headline.** On the untimed/immediate fragment,
any number of executor cycles keeps the precompiled backend's state related
to the reference backend's: the materialized marking (`Pool.proj` =
`materialize_marking`) equals the reference `Marking`, and the control bits
coincide — so the two executors fire the same transitions in the same order
and end every cycle with the same observable marking. -/
theorem precompiled_refines_bitmap_immediate {n : Nat} {net : Net}
    {emit : Emit} {st₀ : PBState} {bb₀ : BBState}
    (hrel : Rel n st₀ bb₀) (hok : NetOK net n) (hemit : EmitOK emit n) :
    ∀ k, Rel n (iterate (pcCycle net emit) k st₀) (iterate (bbCycle net emit) k bb₀) := by
  intro k
  induction k generalizing st₀ bb₀ with
  | zero => exact hrel
  | succ k ih =>
    show Rel n (iterate _ k (pcCycle net emit st₀)) (iterate _ k (bbCycle net emit bb₀))
    exact ih (pcCycle_rel hrel hok hemit)

/-- Corollary: the materialized markings agree after every run prefix. -/
theorem marking_agreement {n : Nat} {net : Net} {emit : Emit} {st₀ : PBState}
    {bb₀ : BBState} (hrel : Rel n st₀ bb₀) (hok : NetOK net n)
    (hemit : EmitOK emit n) :
    ∀ k p, p < n →
      (iterate (pcCycle net emit) k st₀).ring.proj p
        = (iterate (bbCycle net emit) k bb₀).marking p :=
  fun k p hp =>
    (precompiled_refines_bitmap_immediate hrel hok hemit k).prj p hp

end Libpetri
