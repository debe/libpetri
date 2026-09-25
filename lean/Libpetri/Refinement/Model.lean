/-
# Refinement: the reference executor, both cycles, the relation

The `bitmap_backend.rs` state and operations, the two executors' immediate
cycle, the refinement relation `Rel` and the state transformers' component
equations, split out of `Refinement.lean`, which proves the refinement.
-/
import Libpetri.Enablement

namespace Libpetri

/-! ## The reference state and operations (`bitmap_backend.rs`) -/

/-- The reference executor's state: `marking` is `BitmapBackend`'s `Marking`
(FIFO token list per place), control bits as in the precompiled backend. -/
structure BBState where
  marking : CMarking
  enabled : TId → Bool
  dirty   : TId → Bool

/-- Reference enablement (`bitmap_backend.rs` `can_enable`, untimed non-ν
projection): identical formula to `canEnable`, over list lengths. -/
def bbCanEnable (m : CMarking) (t : Transition) : Bool :=
  t.inputs.all (fun sp =>
    decide (0 < (m sp.place).length)
      && decide (sp.card.required ≤ (m sp.place).length))
    && t.reads.all (fun p => decide (0 < (m p).length))
    && t.inhibitors.all (fun p => (m p).length == 0)

/-- Reference marking after the input phase (One/Exactly take their required
count, All/AtLeast drain — `bitmap_backend.rs` `consume_for_firing`). The
drain is to the live count, i.e. the shipped `drainable` idealized as in the
module header; `consumeForFiring` idealizes it identically. -/
def bbPostInput (m : CMarking) (t : Transition) : CMarking :=
  fun p =>
    match specAt t p with
    | some sp => (m p).drop (consumeCountAt (m p).length sp.card)
    | none => m p

/-- Reference marking after the whole consume (inputs then resets). The reset
empties the place outright, again the module header's AC5 idealization — the
shipped reset clears the pass-start prefix only. -/
def bbConsumeMarking (m : CMarking) (t : Transition) : CMarking :=
  fun p => if p ∈ t.resets then [] else bbPostInput m t p

/-- The reference `inputs` bag delivered to the action. -/
def bbInputsBag (m : CMarking) (t : Transition) : TokenBag :=
  fun p =>
    match specAt t p with
    | some sp => (m p).take (consumeCountAt (m p).length sp.card)
    | none => []

/-- The reference `reads` bag: the oldest post-input token per read arc. -/
def bbReadsBag (m : CMarking) (reads : List PlaceId) : TokenBag :=
  reads.foldl (fun b p => addBag b p (m p).head?.toList) emptyBag

def bbFireConsume (net : Net) (bb : BBState) (tid : TId) : BBState :=
  match net[tid]? with
  | none => bb
  | some t =>
    { marking := bbConsumeMarking bb.marking t
      enabled := bb.enabled
      dirty := fun tid' =>
        bb.dirty tid' || match net[tid']? with
          | some t' => decide (∃ p ∈ consumptionPlaces t, touches t' p)
          | none => false }

def bbProduceOne (net : Net) (bb : BBState) (p : PlaceId) (c : Colour) : BBState :=
  { marking := fun q => if q = p then bb.marking q ++ [c] else bb.marking q
    enabled := bb.enabled
    dirty := fun tid' =>
      bb.dirty tid' || match net[tid']? with
        | some t' => decide (touches t' p)
        | none => false }

def bbProduceMany (net : Net) (bb : BBState) : List (PlaceId × Colour) → BBState
  | [] => bb
  | (p, c) :: rest => bbProduceMany net (bbProduceOne net bb p c) rest

def bbPostFire (bb : BBState) (tid : TId) : BBState :=
  { bb with
    enabled := fun tid' => if tid' = tid then false else bb.enabled tid'
    dirty := fun tid' => if tid' = tid then true else bb.dirty tid' }

def bbDisable (bb : BBState) (tid : TId) : BBState :=
  { bb with
    enabled := fun tid' => if tid' = tid then false else bb.enabled tid' }

def bbUpdateEnablement (net : Net) (bb : BBState) : BBState :=
  { bb with
    enabled := fun tid => match net[tid]? with
      | some t => if bb.dirty tid then bbCanEnable bb.marking t else bb.enabled tid
      | none => bb.enabled tid
    dirty := fun _ => false }

/-! ## The two executors' cycle (shared `Executor::run_sync` loop, immediate
fragment: `collect_ready_immediate` fires enabled transitions in ascending
tid order, each behind the EXEC-003 `recheck_can_fire`). -/

/-- Actions abstracted to a pure emission function: given the fired tid and
the delivered `inputs`/`reads` bags, the tokens the action produces, in
emission order. Both backends run the same action object, so both cycles use
the same `emit`. -/
abbrev Emit := TId → TokenBag → TokenBag → List (PlaceId × Colour)

def produceMany (net : Net) (st : PBState) : List (PlaceId × Colour) → PBState
  | [] => st
  | (p, c) :: rest => produceMany net (produceOne net st p c) rest

/-- The EXEC-003 recheck before each firing, **idealized**: `canEnable` over
the live pool. The shipped `recheck_can_fire` reads the fire-pass snapshot
and the deposit delta instead — see the module header. -/
def pcRecheck (net : Net) (st : PBState) (tid : TId) : Bool :=
  st.enabled tid && match net[tid]? with
    | some t => canEnable st.ring t
    | none => false

def pcFire (net : Net) (emit : Emit) (st : PBState) (tid : TId) : PBState :=
  match net[tid]? with
  | none => st
  | some t =>
    let res := consumeForFiring st.ring t
    postFire (produceMany net (fireConsume net st tid) (emit tid res.1.inputs res.2)) tid

def pcCycle (net : Net) (emit : Emit) (st : PBState) : PBState :=
  ((List.range net.length).filter ((updateEnablement net st).enabled ·)).foldl
    (fun s tid => if pcRecheck net s tid then pcFire net emit s tid else disable s tid)
    (updateEnablement net st)

/-- The reference's EXEC-003 recheck, idealized the same way as `pcRecheck`
— which is what makes the correspondence below fair, and what makes it blind
to the snapshot/deposit machinery both backends share. -/
def bbRecheck (net : Net) (bb : BBState) (tid : TId) : Bool :=
  bb.enabled tid && match net[tid]? with
    | some t => bbCanEnable bb.marking t
    | none => false

def bbFire (net : Net) (emit : Emit) (bb : BBState) (tid : TId) : BBState :=
  match net[tid]? with
  | none => bb
  | some t =>
    bbPostFire
      (bbProduceMany net (bbFireConsume net bb tid)
        (emit tid (bbInputsBag bb.marking t)
          (bbReadsBag (bbPostInput bb.marking t) t.reads)))
      tid

def bbCycle (net : Net) (emit : Emit) (bb : BBState) : BBState :=
  ((List.range net.length).filter ((bbUpdateEnablement net bb).enabled ·)).foldl
    (fun b tid => if bbRecheck net b tid then bbFire net emit b tid else bbDisable b tid)
    (bbUpdateEnablement net bb)

/-! ## The refinement relation -/

/-- Precompiled state `st` refines reference state `bb`: the pool is
well-formed, covers `n` places, projects to the reference marking, and the
control bits coincide. `Pool.proj` is `materialize_marking`, so `mk` says the
two backends' observable markings are equal. -/
structure Rel (n : Nat) (st : PBState) (bb : BBState) : Prop where
  wf : Pool.WF st.ring
  np : st.ring.nplaces = n
  prj : ∀ p, p < n → st.ring.proj p = bb.marking p
  en : st.enabled = bb.enabled
  dt : st.dirty = bb.dirty

/-- Emissions target real places. -/
def EmitOK (emit : Emit) (n : Nat) : Prop :=
  ∀ tid bi br, ∀ e ∈ emit tid bi br, e.1 < n

theorem touches_lt {t : Transition} {n : Nat} (hb : PlacesInBounds t n)
    {p : PlaceId} (h : touches t p) : p < n := by
  rcases h with ⟨sp, hm, rfl⟩ | h | h | h
  · exact hb.inputs sp hm
  · exact hb.reads p h
  · exact hb.inhibitors p h
  · exact hb.resets p h

/-! ## Component equations for the state transformers -/

theorem fireConsume_ring {net : Net} {st : PBState} {tid : TId} {t : Transition}
    (hnet : net[tid]? = some t) :
    (fireConsume net st tid).ring = (consumeForFiring st.ring t).1.pool := by
  unfold fireConsume
  rw [hnet]

theorem fireConsume_enabled (net : Net) (st : PBState) (tid : TId) :
    (fireConsume net st tid).enabled = st.enabled := by
  unfold fireConsume
  cases net[tid]? <;> rfl

theorem fireConsume_dirty {net : Net} {st : PBState} {tid : TId} {t : Transition}
    (hnet : net[tid]? = some t) :
    (fireConsume net st tid).dirty = fun tid' =>
      st.dirty tid' || match net[tid']? with
        | some t' => decide (∃ p ∈ consumptionPlaces t, touches t' p)
        | none => false := by
  unfold fireConsume
  rw [hnet]
  rfl

theorem bbFireConsume_marking {net : Net} {bb : BBState} {tid : TId}
    {t : Transition} (hnet : net[tid]? = some t) :
    (bbFireConsume net bb tid).marking = bbConsumeMarking bb.marking t := by
  unfold bbFireConsume
  rw [hnet]

theorem bbFireConsume_enabled (net : Net) (bb : BBState) (tid : TId) :
    (bbFireConsume net bb tid).enabled = bb.enabled := by
  unfold bbFireConsume
  cases net[tid]? <;> rfl

theorem bbFireConsume_dirty {net : Net} {bb : BBState} {tid : TId}
    {t : Transition} (hnet : net[tid]? = some t) :
    (bbFireConsume net bb tid).dirty = fun tid' =>
      bb.dirty tid' || match net[tid']? with
        | some t' => decide (∃ p ∈ consumptionPlaces t, touches t' p)
        | none => false := by
  unfold bbFireConsume
  rw [hnet]

end Libpetri
