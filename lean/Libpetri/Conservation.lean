/-
# Token conservation through `consume_for_firing` — "no missing tokens"

Models the fast (non-ν) consume path of
`rust/libpetri-runtime/src/precompiled_backend.rs` `consume_for_firing`
*post-fix*: input opcodes run first, read arcs peek at the
`reset_ops_start` boundary, then the RESET tail drains (EXEC-012/EXEC-013).
Every removed token is either delivered into the action's `inputs` map or
destroyed by a reset — and the headline theorem `token_conservation` states
this as a per-place *list equality*, not merely a permutation: the pre-fire
queue is exactly `delivered ++ destroyed ++ survivors`, in order.

* FR1 `consume_faithful` — what lands in `inputs` is the IO-007 FIFO prefix
  (`One`/`Exactly`) or the full drain (`All`/`AtLeast`), in order.
* FR2 `token_conservation` — the headline.
* FR3 `peekReads` — read arcs are non-destructive by construction (they
  produce a bag and return the pool untouched); their EXEC-012 content is a
  clone of the oldest post-input token per read arc.
* FR5 `produceAll_spec` — outputs append at the FIFO tail in emission order
  (EXEC-020), via `ring_add_last`.

**Scope: the drains modelled here are the deposit-free ones (EXEC-003 AC5).**
Every draining site of the shipped `consume_for_firing` — the `all()` and
`at_least(n)` arms, their ν-matched twins, and the RESET tail — takes
`drainable(p, live)` tokens, not `live`: `live` minus whatever a same-pass
synchronous action deposited into `p` since the ready list was collected
(`drainable`, both backends). `drainable` returns `live` unchanged whenever no
deposit is outstanding at `p`. That is every firing of a pass in which no
earlier firing's action produced into `p`: always the first firing of any
pass, and always every firing of a pass whose actions are asynchronous, since
`begin_firing_pass` drops the previous pass's delta before the fire loop and
an async completion produces in loop step 1 of a later cycle. It is the case
`execOp` models.

**Not covered: a drain in a pass where an earlier firing already deposited
into the drained place.** There the shipped code splits the queue earlier than
`consumeCountAt` computes, so `consume_faithful`'s prefix is the deposit-free
prefix and nothing more; `token_conservation`'s list equality has the same
shape under either split (the code still delivers a prefix and leaves the
rest), but the split point it names is the deposit-free one. This model has no
notion of a pass at all, so it cannot state the deposited case — and no
theorem below is weakened to pretend otherwise. `Refinement.lean` has the one
cycle-level model in this development that *does* reach the case, and records
there why its statement survives.
-/
import Libpetri.Compile

namespace Libpetri

/-- Per-place token lists accumulated during a firing — the Lean image of the
executor's pooled `inputs: HashMap<Arc<str>, Vec<ErasedToken>>` and of the
`emit_removed` stream restricted to RESET removals. -/
abbrev TokenBag := PlaceId → List Colour

def emptyBag : TokenBag := fun _ => []

def addBag (b : TokenBag) (p : PlaceId) (l : List Colour) : TokenBag :=
  fun q => if q = p then b q ++ l else b q

@[simp] theorem addBag_self (b : TokenBag) (p : PlaceId) (l : List Colour) :
    addBag b p l p = b p ++ l := by simp [addBag]
theorem addBag_other (b : TokenBag) {p q : PlaceId} (l : List Colour)
    (hne : q ≠ p) : addBag b p l q = b q := by simp [addBag, hne]

/-! ## `ring_remove_first` iterated: the per-opcode token loop -/

/-- `k` iterations of `ring_remove_first` at one place, collecting the
removed tokens in removal (= FIFO) order. This is the body of every consume
opcode's `for _ in 0..count` loop. -/
def popN (s : Pool) (p : PlaceId) : Nat → Pool × List Colour
  | 0 => (s, [])
  | k + 1 =>
    let c := s.first p
    let rest := popN (s.removeFirst p) p k
    (rest.1, c.toList ++ rest.2)

/-- A non-empty ring projects as a cons, headed by `first`. -/
theorem proj_cons {s : Pool} (hwf : Pool.WF s) {p : PlaceId}
    (hp : p < s.nplaces) (hcnt : 0 < s.cnt p) :
    ∃ c rest, s.first p = some c ∧ s.proj p = c :: rest := by
  obtain ⟨c, hc, _⟩ := Pool.toList_of_isSome (Pool.first_isSome hwf hp hcnt)
  have hhead := Pool.first_eq_head hwf hp hcnt
  rw [hc] at hhead
  cases hproj : s.proj p with
  | nil => rw [hproj] at hhead; cases hhead
  | cons a rest =>
    rw [hproj] at hhead
    have hca : c = a := Option.some.inj hhead
    exact ⟨c, rest, hc, by rw [hca]⟩

/-- The full spec of `popN`: totality (WF out), FIFO faithfulness (the
collected tokens are `take k`, the survivors `drop k`), the frame on other
places, and the count bookkeeping. -/
theorem popN_spec {s : Pool} (hwf : Pool.WF s) {p : PlaceId}
    (hp : p < s.nplaces) {k : Nat} (hk : k ≤ s.cnt p) :
    Pool.WF (popN s p k).1 ∧
    (popN s p k).1.nplaces = s.nplaces ∧
    (popN s p k).2 = (s.proj p).take k ∧
    (popN s p k).1.proj p = (s.proj p).drop k ∧
    (∀ q, q < s.nplaces → q ≠ p → (popN s p k).1.proj q = s.proj q) ∧
    (∀ q, (popN s p k).1.cnt q = if q = p then s.cnt q - k else s.cnt q) := by
  induction k generalizing s with
  | zero =>
    refine ⟨hwf, rfl, rfl, rfl, fun q _ _ => rfl, fun q => ?_⟩
    by_cases hq : q = p <;> simp [popN, hq]
  | succ k ih =>
    have hcnt : 0 < s.cnt p := by omega
    obtain ⟨c, rest, hc, hproj⟩ := proj_cons hwf hp hcnt
    have hwf' := Pool.removeFirst_wf hwf hp hcnt
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ :=
      ih hwf' (by rw [Pool.removeFirst_nplaces]; exact hp)
        (by rw [Pool.removeFirst_cnt_self]; omega)
    have hproj' : (s.removeFirst p).proj p = rest := by
      rw [Pool.removeFirst_proj_self hwf hp hcnt, hproj, List.tail_cons]
    have hstep1 : (popN s p (k + 1)).1 = (popN (s.removeFirst p) p k).1 := rfl
    have hstep2 : (popN s p (k + 1)).2
        = (s.first p).toList ++ (popN (s.removeFirst p) p k).2 := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep1]; exact ih1
    · rw [hstep1, ih2, Pool.removeFirst_nplaces]
    · rw [hstep2, hc, ih3, hproj', hproj]
      rfl
    · rw [hstep1, ih4, hproj', hproj]
      rfl
    · intro q hq hne
      rw [hstep1, ih5 q (by rw [Pool.removeFirst_nplaces]; exact hq) hne,
        Pool.removeFirst_proj_other hwf hp hq hne]
    · intro q
      rw [hstep1, ih6 q]
      by_cases hqp : q = p
      · subst hqp
        rw [if_pos rfl, if_pos rfl, Pool.removeFirst_cnt_self]
        omega
      · rw [if_neg hqp, if_neg hqp, Pool.removeFirst_cnt_other s hqp]

/-! ## The opcode interpreter -/

/-- The evolving result of one firing's consume phase: the pool plus the
`inputs` bag (tokens delivered to the action) and the `destroyed` bag
(tokens removed by RESET — `emit_removed` sees them, the action does not). -/
structure ConsumeResult where
  pool      : Pool
  inputs    : TokenBag
  destroyed : TokenBag

/-- One opcode (`precompiled_backend.rs` `consume_for_firing`, fast path):
`CONSUME_ONE` pops 1, `CONSUME_N` pops its count, `CONSUME_ALL` and
`CONSUME_ATLEAST` drain `token_counts[pid]` (the `atLeast` minimum is
skipped), `RESET` drains into `destroyed`.

The three drain arms are the shipped `drainable(pid, token_counts[pid])` in
its `drainable = token_counts[pid]` case — see the AC5 scope note in the
module header for the case they are not. -/
def execOp (r : ConsumeResult) : ConsumeOp → ConsumeResult
  | .one p =>
    { r with pool := (popN r.pool p 1).1
             inputs := addBag r.inputs p (popN r.pool p 1).2 }
  | .n p k =>
    { r with pool := (popN r.pool p k).1
             inputs := addBag r.inputs p (popN r.pool p k).2 }
  | .all p =>
    { r with pool := (popN r.pool p (r.pool.cnt p)).1
             inputs := addBag r.inputs p (popN r.pool p (r.pool.cnt p)).2 }
  | .atLeast p _ =>
    { r with pool := (popN r.pool p (r.pool.cnt p)).1
             inputs := addBag r.inputs p (popN r.pool p (r.pool.cnt p)).2 }
  | .reset p =>
    { r with pool := (popN r.pool p (r.pool.cnt p)).1
             destroyed := addBag r.destroyed p (popN r.pool p (r.pool.cnt p)).2 }

def execOpsFrom (r : ConsumeResult) (ops : List ConsumeOp) : ConsumeResult :=
  ops.foldl execOp r

@[simp] theorem execOpsFrom_nil (r : ConsumeResult) : execOpsFrom r [] = r := rfl
@[simp] theorem execOpsFrom_cons (r : ConsumeResult) (op : ConsumeOp)
    (ops : List ConsumeOp) :
    execOpsFrom r (op :: ops) = execOpsFrom (execOp r op) ops := rfl
theorem execOpsFrom_append (r : ConsumeResult) (a b : List ConsumeOp) :
    execOpsFrom r (a ++ b) = execOpsFrom (execOpsFrom r a) b :=
  List.foldl_append ..

/-- The common shape of every input opcode: pop `k` at one place into
`inputs`. -/
theorem execOp_pop_spec {r : ConsumeResult} (hwf : Pool.WF r.pool)
    {p : PlaceId} (hp : p < r.pool.nplaces) {k : Nat}
    (hk : k ≤ r.pool.cnt p) {r' : ConsumeResult}
    (hr' : r' = { r with pool := (popN r.pool p k).1
                         inputs := addBag r.inputs p (popN r.pool p k).2 }) :
    Pool.WF r'.pool ∧ r'.pool.nplaces = r.pool.nplaces ∧
    r'.destroyed = r.destroyed ∧
    r'.inputs p = r.inputs p ++ (r.pool.proj p).take k ∧
    r'.pool.proj p = (r.pool.proj p).drop k ∧
    (∀ q, q ≠ p → r'.inputs q = r.inputs q) ∧
    (∀ q, q < r.pool.nplaces → q ≠ p →
      r'.pool.proj q = r.pool.proj q ∧
      r'.pool.cnt q = r.pool.cnt q) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := popN_spec hwf hp hk
  subst hr'
  refine ⟨h1, h2, rfl, ?_, h4, fun q hne => ?_, fun q hq hne => ⟨h5 q hq hne, ?_⟩⟩
  · show addBag r.inputs p (popN r.pool p k).2 p = _
    rw [addBag_self, h3]
  · show addBag r.inputs p (popN r.pool p k).2 q = r.inputs q
    exact addBag_other _ _ hne
  · show (popN r.pool p k).1.cnt q = r.pool.cnt q
    rw [h6 q, if_neg hne]

/-- One *input* opcode's effect: delivers the IO-007 `consumptionCount`
prefix into `inputs`, leaves `destroyed` alone, and frames every other
place. -/
theorem execOp_input_spec {r : ConsumeResult} (hwf : Pool.WF r.pool)
    {sp : InSpec} (hp : sp.place < r.pool.nplaces)
    (hreq : sp.card.required ≤ r.pool.cnt sp.place) :
    Pool.WF (execOp r (opOfSpec sp)).pool ∧
    (execOp r (opOfSpec sp)).pool.nplaces = r.pool.nplaces ∧
    (execOp r (opOfSpec sp)).destroyed = r.destroyed ∧
    (execOp r (opOfSpec sp)).inputs sp.place
      = r.inputs sp.place
        ++ (r.pool.proj sp.place).take
            (consumeCountAt (r.pool.cnt sp.place) sp.card) ∧
    (execOp r (opOfSpec sp)).pool.proj sp.place
      = (r.pool.proj sp.place).drop
          (consumeCountAt (r.pool.cnt sp.place) sp.card) ∧
    (∀ q, q ≠ sp.place → (execOp r (opOfSpec sp)).inputs q = r.inputs q) ∧
    (∀ q, q < r.pool.nplaces → q ≠ sp.place →
      (execOp r (opOfSpec sp)).pool.proj q = r.pool.proj q ∧
      (execOp r (opOfSpec sp)).pool.cnt q = r.pool.cnt q) := by
  cases hcard : sp.card with
  | one =>
    have h := execOp_pop_spec hwf hp (k := 1)
      (by rw [hcard] at hreq; exact hreq)
      (r' := execOp r (opOfSpec sp)) (by simp [opOfSpec, hcard, execOp])
    simpa only [consumeCountAt] using h
  | exactly n =>
    have h := execOp_pop_spec hwf hp (k := n)
      (by rw [hcard] at hreq; exact hreq)
      (r' := execOp r (opOfSpec sp)) (by simp [opOfSpec, hcard, execOp])
    simpa only [consumeCountAt] using h
  | all =>
    have h := execOp_pop_spec hwf hp (k := r.pool.cnt sp.place)
      (Nat.le_refl _)
      (r' := execOp r (opOfSpec sp)) (by simp [opOfSpec, hcard, execOp])
    simpa only [consumeCountAt] using h
  | atLeast m =>
    have h := execOp_pop_spec hwf hp (k := r.pool.cnt sp.place)
      (Nat.le_refl _)
      (r' := execOp r (opOfSpec sp)) (by simp [opOfSpec, hcard, execOp])
    simpa only [consumeCountAt] using h

/-- The input half of the compiled program (`..reset_ops_start`): each input
place receives its IO-007 prefix into `inputs`; everything else is framed.
Distinct input places (Fix (c)'s compile guarantee) make the per-spec effects
independent, so each is stated against the *initial* pool. -/
theorem execOps_inputs {specs : List InSpec} :
    ∀ {r₀ : ConsumeResult}, Pool.WF r₀.pool →
    (specs.map (·.place)).Pairwise (· ≠ ·) →
    (∀ sp ∈ specs, sp.place < r₀.pool.nplaces) →
    (∀ sp ∈ specs, sp.card.required ≤ r₀.pool.cnt sp.place) →
    Pool.WF (execOpsFrom r₀ (specs.map opOfSpec)).pool ∧
    (execOpsFrom r₀ (specs.map opOfSpec)).pool.nplaces = r₀.pool.nplaces ∧
    (execOpsFrom r₀ (specs.map opOfSpec)).destroyed = r₀.destroyed ∧
    (∀ q, (∀ sp ∈ specs, sp.place ≠ q) →
      (execOpsFrom r₀ (specs.map opOfSpec)).inputs q = r₀.inputs q) ∧
    (∀ q, q < r₀.pool.nplaces → (∀ sp ∈ specs, sp.place ≠ q) →
      (execOpsFrom r₀ (specs.map opOfSpec)).pool.proj q = r₀.pool.proj q ∧
      (execOpsFrom r₀ (specs.map opOfSpec)).pool.cnt q = r₀.pool.cnt q) ∧
    (∀ sp ∈ specs,
      (execOpsFrom r₀ (specs.map opOfSpec)).inputs sp.place
        = r₀.inputs sp.place
          ++ (r₀.pool.proj sp.place).take
              (consumeCountAt (r₀.pool.cnt sp.place) sp.card) ∧
      (execOpsFrom r₀ (specs.map opOfSpec)).pool.proj sp.place
        = (r₀.pool.proj sp.place).drop
            (consumeCountAt (r₀.pool.cnt sp.place) sp.card)) := by
  induction specs with
  | nil =>
    intro r₀ hwf _ _ _
    exact ⟨hwf, rfl, rfl, fun q _ => rfl, fun q _ _ => ⟨rfl, rfl⟩,
      fun sp h => absurd h (List.not_mem_nil)⟩
  | cons sp rest ih =>
    intro r₀ hwf hdist hbound hreq
    have hdist' := hdist
    rw [List.map_cons, List.pairwise_cons] at hdist'
    have hrestne : ∀ sp' ∈ rest, sp'.place ≠ sp.place := by
      intro sp' hmem h
      exact hdist'.1 sp'.place (List.mem_map.mpr ⟨sp', hmem, rfl⟩) h.symm
    have hspb : sp.place < r₀.pool.nplaces := hbound sp List.mem_cons_self
    have hspr : sp.card.required ≤ r₀.pool.cnt sp.place :=
      hreq sp List.mem_cons_self
    obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := execOp_input_spec hwf hspb hspr
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (r₀ := execOp r₀ (opOfSpec sp)) s1
      hdist'.2
      (fun sp' hmem => by rw [s2]; exact hbound sp' (List.mem_cons_of_mem _ hmem))
      (fun sp' hmem => by
        obtain ⟨_, hcnt⟩ := s7 sp'.place
          (hbound sp' (List.mem_cons_of_mem _ hmem)) (hrestne sp' hmem)
        rw [hcnt]
        exact hreq sp' (List.mem_cons_of_mem _ hmem))
    rw [List.map_cons]
    rw [execOpsFrom_cons]
    refine ⟨i1, by rw [i2, s2], by rw [i3, s3], ?_, ?_, ?_⟩
    · intro q hnone
      have hqne : sp.place ≠ q := hnone sp List.mem_cons_self
      rw [i4 q (fun sp' hmem => hnone sp' (List.mem_cons_of_mem _ hmem)),
        s6 q (Ne.symm hqne)]
    · intro q hq hnone
      have hqne : sp.place ≠ q := hnone sp List.mem_cons_self
      obtain ⟨f2, f3⟩ := i5 q (by rw [s2]; exact hq)
        (fun sp' hmem => hnone sp' (List.mem_cons_of_mem _ hmem))
      obtain ⟨g2, g3⟩ := s7 q hq (Ne.symm hqne)
      exact ⟨by rw [f2, g2], by rw [f3, g3]⟩
    · intro sp' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · obtain ⟨f2, f3⟩ := i5 sp'.place (by rw [s2]; exact hspb) hrestne
        have f1 := i4 sp'.place hrestne
        exact ⟨by rw [f1, s4], by rw [f2, s5]⟩
      · obtain ⟨f1, f2⟩ := i6 sp' hmem'
        obtain ⟨g2, g3⟩ := s7 sp'.place
          (hbound sp' (List.mem_cons_of_mem _ hmem')) (hrestne sp' hmem')
        exact ⟨by rw [f1, s6 sp'.place (hrestne sp' hmem'), g2, g3],
          by rw [f2, g2, g3]⟩

/-- The RESET tail (`reset_ops_start..`): each reset place is drained into
`destroyed`; `inputs` and non-reset places are framed. Tolerates duplicate
reset arcs (a second drain of the same place removes nothing). -/
theorem execOps_resets {resets : List PlaceId} :
    ∀ {r₀ : ConsumeResult}, Pool.WF r₀.pool →
    (∀ p ∈ resets, p < r₀.pool.nplaces) →
    Pool.WF (execOpsFrom r₀ (resets.map .reset)).pool ∧
    (execOpsFrom r₀ (resets.map .reset)).pool.nplaces = r₀.pool.nplaces ∧
    (execOpsFrom r₀ (resets.map .reset)).inputs = r₀.inputs ∧
    (∀ q, q < r₀.pool.nplaces → q ∉ resets →
      (execOpsFrom r₀ (resets.map .reset)).destroyed q = r₀.destroyed q ∧
      (execOpsFrom r₀ (resets.map .reset)).pool.proj q = r₀.pool.proj q) ∧
    (∀ q, q < r₀.pool.nplaces → q ∈ resets →
      (execOpsFrom r₀ (resets.map .reset)).destroyed q
        = r₀.destroyed q ++ r₀.pool.proj q ∧
      (execOpsFrom r₀ (resets.map .reset)).pool.proj q = []) := by
  induction resets with
  | nil =>
    intro r₀ hwf _
    exact ⟨hwf, rfl, rfl, fun q _ _ => ⟨rfl, rfl⟩,
      fun q _ h => absurd h (List.not_mem_nil)⟩
  | cons p rest ih =>
    intro r₀ hwf hbound
    have hpb : p < r₀.pool.nplaces := hbound p List.mem_cons_self
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      popN_spec hwf hpb (k := r₀.pool.cnt p) (Nat.le_refl _)
    have hlen : (r₀.pool.proj p).length = r₀.pool.cnt p :=
      Pool.proj_length hwf hpb
    have hd1self : (execOp r₀ (.reset p)).destroyed p
        = r₀.destroyed p ++ r₀.pool.proj p := by
      show addBag r₀.destroyed p (popN r₀.pool p (r₀.pool.cnt p)).2 p = _
      rw [addBag_self, h3, ← hlen, List.take_length]
    have hd1other : ∀ q, q ≠ p →
        (execOp r₀ (.reset p)).destroyed q = r₀.destroyed q := by
      intro q hq
      show addBag r₀.destroyed p (popN r₀.pool p (r₀.pool.cnt p)).2 q = _
      exact addBag_other _ _ hq
    have hp1self : (execOp r₀ (.reset p)).pool.proj p = [] := by
      show (popN r₀.pool p (r₀.pool.cnt p)).1.proj p = []
      rw [h4, ← hlen, List.drop_length]
    have hp1other : ∀ q, q < r₀.pool.nplaces → q ≠ p →
        (execOp r₀ (.reset p)).pool.proj q = r₀.pool.proj q := by
      intro q hq hne
      show (popN r₀.pool p (r₀.pool.cnt p)).1.proj q = _
      exact h5 q hq hne
    have hnp1 : (execOp r₀ (.reset p)).pool.nplaces = r₀.pool.nplaces := h2
    have hwf1 : Pool.WF (execOp r₀ (.reset p)).pool := h1
    have hin1 : (execOp r₀ (.reset p)).inputs = r₀.inputs := rfl
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih (r₀ := execOp r₀ (.reset p)) hwf1
      (fun q hmem => by
        rw [hnp1]; exact hbound q (List.mem_cons_of_mem _ hmem))
    rw [List.map_cons, execOpsFrom_cons]
    refine ⟨i1, by rw [i2, hnp1], by rw [i3, hin1], ?_, ?_⟩
    · intro q hq hqmem
      have hqp : q ≠ p := fun h => hqmem (h ▸ List.mem_cons_self)
      have hqrest : q ∉ rest := fun h => hqmem (List.mem_cons_of_mem _ h)
      obtain ⟨f1, f2⟩ := i4 q (by rw [hnp1]; exact hq) hqrest
      exact ⟨by rw [f1, hd1other q hqp], by rw [f2, hp1other q hq hqp]⟩
    · intro q hq hqmem
      by_cases hqrest : q ∈ rest
      · obtain ⟨f1, f2⟩ := i5 q (by rw [hnp1]; exact hq) hqrest
        by_cases hqp : q = p
        · subst hqp
          exact ⟨by rw [f1, hd1self, hp1self, List.append_nil], f2⟩
        · exact ⟨by rw [f1, hd1other q hqp, hp1other q hq hqp], f2⟩
      · have hqp : q = p := by
          rcases List.mem_cons.mp hqmem with h | h
          · exact h
          · exact absurd h hqrest
        subst hqp
        obtain ⟨f1, f2⟩ := i4 q (by rw [hnp1]; exact hq) hqrest
        exact ⟨by rw [f1, hd1self], by rw [f2, hp1self]⟩

/-! ## Read peeks and the composed firing -/

/-- The read loop (`peek_reads`, post-fix at the `reset_ops_start` boundary):
clone the oldest token of each read place. Pure — the pool is not an output,
which *is* FR3 (reads are non-destructive). -/
def peekReads (s : Pool) (reads : List PlaceId) : TokenBag :=
  reads.foldl (fun b p => addBag b p (s.peekFirst p).toList) emptyBag

/-- `consume_for_firing` (fast path, post-fix order): input opcodes, then
read peeks against the post-input pre-reset pool, then the RESET tail. -/
def consumeForFiring (s : Pool) (t : Transition) : ConsumeResult × TokenBag :=
  let r₁ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)
  (execOpsFrom r₁ (t.resets.map .reset), peekReads r₁.pool t.reads)

/-- The pool/bag half of `consumeForFiring` is exactly the compiled program
`compileConsumeOps` run start to finish — the read peek at the
`reset_ops_start` boundary observes but does not touch the pool. -/
theorem consumeForFiring_eq_program (s : Pool) (t : Transition) :
    (consumeForFiring s t).1
      = execOpsFrom ⟨s, emptyBag, emptyBag⟩ (compileConsumeOps t) := by
  unfold consumeForFiring compileConsumeOps
  rw [execOpsFrom_append]

/-- Unpack `canEnable` into its per-arc facts. -/
theorem canEnable_spec {s : Pool} {t : Transition} (h : canEnable s t = true) :
    (∀ sp ∈ t.inputs, 0 < s.cnt sp.place ∧ sp.card.required ≤ s.cnt sp.place) ∧
    (∀ p ∈ t.reads, 0 < s.cnt p) ∧
    (∀ p ∈ t.inhibitors, s.cnt p = 0) := by
  unfold canEnable at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨fun sp hm => (h.1.1 sp hm), fun p hm => h.1.2 p hm,
    fun p hm => h.2 p hm⟩

/-- **FR2 — token conservation, the "no missing tokens" theorem.**

Over one firing's consume phase, every place's pre-fire FIFO queue is
*exactly* the tokens delivered to the action, then the tokens destroyed by
resets, then the surviving queue — as a list equality, so nothing is lost,
nothing is duplicated, and order is preserved. Places the transition does not
touch are equal on the nose.

Stated at the split `consumeCountAt` computes, hence for a drain with no
same-pass deposit outstanding (module header, AC5 scope). -/
theorem token_conservation {s : Pool} (hwf : Pool.WF s) {t : Transition}
    (hdist : DistinctInputPlaces t) (hb : PlacesInBounds t s.nplaces)
    (hen : canEnable s t = true) :
    ∀ q, q < s.nplaces →
      s.proj q
        = (consumeForFiring s t).1.inputs q
          ++ (consumeForFiring s t).1.destroyed q
          ++ (consumeForFiring s t).1.pool.proj q := by
  intro q hq
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs (r₀ := ⟨s, emptyBag, emptyBag⟩)
    hwf hdist (fun sp hm => hb.inputs sp hm) (fun sp hm => (henin sp hm).2)
  obtain ⟨j1, j2, j3, j4, j5⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hb.resets p hm)
  change s.proj q
      = (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
          (t.resets.map .reset)).inputs q
        ++ (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
          (t.resets.map .reset)).destroyed q
        ++ (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
          (t.resets.map .reset)).pool.proj q
  rw [j3]
  by_cases hqin : ∃ sp ∈ t.inputs, sp.place = q
  · obtain ⟨sp, hsp, rfl⟩ := hqin
    obtain ⟨f1, f2⟩ := i6 sp hsp
    by_cases hqres : sp.place ∈ t.resets
    · obtain ⟨g1, g2⟩ := j5 sp.place (by rw [i2]; exact hq) hqres
      rw [f1, g1, i3, g2, f2]
      show s.proj sp.place
          = (emptyBag sp.place ++ (s.proj sp.place).take _)
            ++ (emptyBag sp.place ++ (s.proj sp.place).drop _) ++ []
      simp [emptyBag, List.take_append_drop]
    · obtain ⟨g1, g2⟩ := j4 sp.place (by rw [i2]; exact hq) hqres
      rw [f1, g1, i3, g2, f2]
      show s.proj sp.place
          = (emptyBag sp.place ++ (s.proj sp.place).take _)
            ++ emptyBag sp.place ++ (s.proj sp.place).drop _
      simp [emptyBag, List.take_append_drop]
  · have hnone : ∀ sp ∈ t.inputs, sp.place ≠ q := by
      intro sp hm h
      exact hqin ⟨sp, hm, h⟩
    have f1 := i4 q hnone
    obtain ⟨f2, _⟩ := i5 q hq hnone
    by_cases hqres : q ∈ t.resets
    · obtain ⟨g1, g2⟩ := j5 q (by rw [i2]; exact hq) hqres
      rw [f1, g1, i3, g2, f2]
      show s.proj q = emptyBag q ++ (emptyBag q ++ s.proj q) ++ []
      simp [emptyBag]
    · obtain ⟨g1, g2⟩ := j4 q (by rw [i2]; exact hq) hqres
      rw [f1, g1, i3, g2, f2]
      show s.proj q = emptyBag q ++ emptyBag q ++ s.proj q
      simp [emptyBag]

/-- **FR1 — consumption faithfulness** (EXEC-010, IO-007): each input place
delivers exactly the `consumptionCount(available)` FIFO prefix into the
action's `inputs`, in queue order.

This is the statement EXEC-003 AC5 moves: on a draining arc the shipped
`available` is `drainable(p, live)`, so the prefix is `consumptionCount` of the
pass-start count, not of the live count. Equal whenever no same-pass deposit is
outstanding at `p` — the modelled case (module header) — and the `One`/`Exactly`
arms are equal unconditionally, since a fixed count off the FIFO head stays
inside the pre-deposit prefix that the AC4 recheck already required. -/
theorem consume_faithful {s : Pool} (hwf : Pool.WF s) {t : Transition}
    (hdist : DistinctInputPlaces t) (hb : PlacesInBounds t s.nplaces)
    (hen : canEnable s t = true) :
    ∀ sp ∈ t.inputs,
      (consumeForFiring s t).1.inputs sp.place
        = (s.proj sp.place).take (consumeCountAt (s.cnt sp.place) sp.card) := by
  intro sp hsp
  obtain ⟨henin, _, _⟩ := canEnable_spec hen
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := execOps_inputs (r₀ := ⟨s, emptyBag, emptyBag⟩)
    hwf hdist (fun sp' hm => hb.inputs sp' hm) (fun sp' hm => (henin sp' hm).2)
  obtain ⟨j1, j2, j3, j4, j5⟩ := execOps_resets
    (r₀ := execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec)) i1
    (fun p hm => by rw [i2]; exact hb.resets p hm)
  obtain ⟨f1, _⟩ := i6 sp hsp
  change (execOpsFrom (execOpsFrom ⟨s, emptyBag, emptyBag⟩ (t.inputs.map opOfSpec))
      (t.resets.map .reset)).inputs sp.place
      = (s.proj sp.place).take (consumeCountAt (s.cnt sp.place) sp.card)
  rw [j3, f1]
  show emptyBag sp.place ++ _ = _
  simp [emptyBag]

/-- **FR5 — output determinism** (EXEC-020): produced tokens append at the
FIFO tail of their target place, in emission order, via `ring_add_last`. -/
def produceAll (s : Pool) : List (PlaceId × Colour) → Pool
  | [] => s
  | (p, c) :: rest => produceAll (s.addLast p c) rest

theorem produceAll_spec {outs : List (PlaceId × Colour)} :
    ∀ {s : Pool}, Pool.WF s → (∀ e ∈ outs, e.1 < s.nplaces) →
    Pool.WF (produceAll s outs) ∧
    (produceAll s outs).nplaces = s.nplaces ∧
    ∀ q, q < s.nplaces →
      (produceAll s outs).proj q
        = s.proj q ++ outs.filterMap (fun e => if e.1 = q then some e.2 else none) := by
  induction outs with
  | nil =>
    intro s hwf _
    exact ⟨hwf, rfl, fun q _ => by simp [produceAll]⟩
  | cons e rest ih =>
    intro s hwf hbound
    obtain ⟨p, c⟩ := e
    have hpb : p < s.nplaces := hbound (p, c) List.mem_cons_self
    have hwf' := Pool.addLast_wf hwf hpb c
    have hnp : (s.addLast p c).nplaces = s.nplaces := by
      unfold Pool.addLast
      by_cases hfull : s.cnt p = s.cap p <;> simp [hfull, Pool.pushLast, Pool.growRing]
    obtain ⟨i1, i2, i3⟩ := ih (s := s.addLast p c) hwf'
      (fun e' hm => by rw [hnp]; exact hbound e' (List.mem_cons_of_mem _ hm))
    have hstep : produceAll s ((p, c) :: rest) = produceAll (s.addLast p c) rest := rfl
    refine ⟨by rw [hstep]; exact i1, by rw [hstep, i2, hnp], ?_⟩
    intro q hq
    rw [hstep, i3 q (by rw [hnp]; exact hq)]
    by_cases hqp : q = p
    · subst hqp
      rw [Pool.addLast_proj_self hwf hpb c]
      simp [List.append_assoc]
    · rw [Pool.addLast_proj_other hwf hpb hq (fun h => hqp h) c]
      have hnone : (if p = q then some c else none) = none :=
        if_neg (fun h => hqp h.symm)
      simp [hnone]

end Libpetri
