/-
# ν-match cache lockstep: the NU-020 fast path of `PrecompiledBackend`

`PrecompiledBackend` keeps one `IncrementalMatcher` per *fast-path eligible*
matched transition (`match_caches`, `precompiled_backend.rs:90`) so that a
ν-join's enablement read (`can_enable`, `precompiled_backend.rs:581-592`) is
O(1) instead of the O(n) index rebuild `find_match_binding`
(`precompiled_backend.rs:601-638`). The doc comment on `init_match_caches`
(`precompiled_backend.rs:200-208`) argues that under its eligibility
conditions "the cache can never desync". This module turns that prose into
theorems over the flat-pool model of `Ring.lean`:

* `Sync` — the lockstep invariant: one correlated input's per-name cache
  queues equal `recompute` of the live ring projection (the from-scratch
  answer the cache claims to match).
* **`match_cache_lockstep`** — the main theorem: the invariant survives ANY
  finite sequence of the modeled backend mutations, provided the mutations
  that hit the cached place are the ones eligibility permits (token adds and
  the owning join's matched consume). Mutations addressed to *other* places
  are unrestricted — any of the four kinds, in any interleaving.
* `fire_muts_lockstep` — the bridge from the eligibility predicate to that
  hypothesis: under the exact three-conjunct gate of `init_match_caches`,
  the consume phase of ANY transition firing (`consume_for_firing`,
  `precompiled_backend.rs:924`) performs only permitted mutations on the
  cached place — a foreign firing performs none at all
  (`foreign_fire_emits_nothing`), the owner performs exactly one matched
  consume with equal ring/cache counts (`owner_fire_emits_lockstep`).
* three `*_is_necessary` witnesses — for each conjunct of the eligibility
  predicate, a minimal concrete configuration in which that conjunct alone
  fails and a mutation the shipped code really performs desyncs the cache.

## The eligibility predicate (spec NU-020, `init_match_caches`)

For every correlated input place `p` of a matched transition `tid`
(`precompiled_backend.rs:245-268`), the code requires — beyond `p` being a
compiled place id (`:246-249`, absorbed here by dense `PlaceId`s; unknown
places live in `extra_marking`, outside both the pool and the caches,
CORE-072):

1. the input spec on `p` is `One`/`Exactly` — a **fixed consume count**
   (`:254-262`, the `_ => eligible = false` arm also catching a missing
   spec);
2. `p` is **never a reset target** of any transition (`:264`,
   `reset_target` built at `:217-232`);
3. `tid` is the **sole input consumer** of `p` —
   `input_consumers[pid] == [tid]` (`:264`, map built at `:217-232`; one
   entry per input spec, so a duplicate input arc of `tid` itself also
   fails the test).

`FastPathEligible` states exactly these conjuncts; `fixedRequired`,
`resetTarget` and `inputConsumers` mirror the three code artifacts.

## Scope and modelling assumptions

* **Per-key granularity.** The matcher's state is one FIFO-per-name queue
  map per correlated input (`IncrementalMatcher.ts`,
  `match_engine.rs:154-156`), and `consume` acts on each input's component
  independently (`match_engine.rs:195-208`). The theorems here cover one
  correlated input (place + key extractor); the whole cache is the
  conjunction of this statement over the join's key places, each place
  eligible by the same gate.
* **Queue contents, not selection.** `MinQueue` stores only each token's
  `created_at`; the model keeps the whole colour, which determines the
  timestamp, so equality here is strictly finer than equality of the
  shipped queues. Which name `best()` then returns — the `select_match_name`
  equivalence, heap/FIFO internals, tie-breaks — is NU-022 AC2, pinned
  differentially by `incremental_matches_select_byte_for_byte`; it is out
  of scope here. Lockstep of the *contents* is exactly the part that
  differential test assumes and cannot itself establish.
* `Mut.consumeFirst` guards `ring_remove_first` by `0 < cnt`, modelling the
  executor's cardinality gate (`can_enable`; `Ring.lean`'s `first_isSome`
  is the totality fact). A reset drains by `cnt` repeated head removals,
  exactly as `consume_for_firing`'s RESET tail does (`:1005-1013`).
* A matched firing with no binding cannot reach the consume phase
  (`can_enable`'s `no_binding` bail-out, `:584-592`), so the firing model
  carries the chosen name.
* `cache_add_token` at a *different* place touches other key indices of the
  matcher only, never this input's queues — the frame case of `applyStep`.
* Timing, priorities and the async loop are out of scope as everywhere in
  this development; a mutation sequence here is the projection of an
  executor trace onto pool/cache effects.
-/
import Libpetri.Compile

namespace Libpetri

/-! ## Names, keys, cache state -/

/-- A correlation name. `libpetri-core/src/name.rs` `NameId` is an interned
string; only equality matters for lockstep (NU-001 ordering matters to
selection, which is out of scope here), so `Nat` suffices. -/
abbrev Name := Nat

/-- A match key's projection, `MatchKey::extract` as used at
`precompiled_backend.rs:307` and `:285`: `value → Option<NameId>` — a token
whose extraction fails is invisible to the matcher. -/
abbrev KeyOf := Colour → Option Name

/-- The ν-net name-equality test — the `pred` closure the matched consume
builds at `precompiled_backend.rs:955-960`:
`matches!((key(v), &chosen), (Some(n), Some(c)) if n == *c)`. Per NU-021 this
is the *only* per-token filter in the system. -/
def keyPred (key : KeyOf) (n : Name) : Colour → Bool := fun c => key c == some n

/-- One correlated input's cache component: `name → FIFO queue`, modelling
`IncrementalMatcher.ts[i] : HashMap<NameId, MinQueue>`
(`match_engine.rs:154-156`). The `MinQueue` keeps each token's `created_at`
only; the model keeps the whole colour (which determines the timestamp), and
a name mapped to `[]` is the map's absent entry. -/
abbrev CacheQ := Name → List Colour

/-- `IncrementalMatcher::add` (`match_engine.rs:186-191`) as called by
`cache_add_token` (`precompiled_backend.rs:299-316`): if the key extracts a
name, push the token at the back of that name's queue; otherwise do
nothing. -/
def cacheAdd (key : KeyOf) (q : CacheQ) (c : Colour) : CacheQ :=
  fun n => if key c == some n then q n ++ [c] else q n

/-- One `q.pop_front()` on name `m`'s queue (`match_engine.rs:197-199`,
`MinQueue::pop_front` at `:102-109`): FIFO-within-name removal, a no-op on
an empty queue. -/
def cachePop (q : CacheQ) (m : Name) : CacheQ :=
  fun n => if n == m then (q n).tail else q n

/-- `IncrementalMatcher::consume`'s per-input loop
`for _ in 0..requireds[i] { q.pop_front() }` (`match_engine.rs:195-201`):
`k` single pops of name `m`'s queue. -/
def cachePopN (q : CacheQ) (m : Name) : Nat → CacheQ
  | 0 => q
  | k + 1 => cachePopN (cachePop q m) m k

/-- The from-scratch answer the cache claims to equal: walk the ring
projection in FIFO order and keep, per name, the tokens extracting to it.
This is what the seeding loop of `init_match_caches` builds
(`precompiled_backend.rs:274-293`) and the queue-level ground truth
underlying `find_match_binding`'s `(count, min_created_at)` index
(`precompiled_backend.rs:617-632`) — the index is the image of these
queues. -/
def recompute (key : KeyOf) (l : List Colour) : CacheQ :=
  fun n => l.filter (keyPred key n)

theorem recompute_eq (key : KeyOf) (l : List Colour) (n : Name) :
    recompute key l n = l.filter (keyPred key n) := rfl

theorem cacheAdd_eq (key : KeyOf) (q : CacheQ) (c : Colour) (n : Name) :
    cacheAdd key q c n = if key c == some n then q n ++ [c] else q n := rfl

theorem cachePop_eq (q : CacheQ) (m n : Name) :
    cachePop q m n = if n == m then (q n).tail else q n := rfl

/-- **The lockstep invariant**: the cache component for place `p` equals the
recompute of `p`'s live ring projection, name by name. -/
def Sync (key : KeyOf) (s : Pool) (p : PlaceId) (q : CacheQ) : Prop :=
  ∀ n, q n = recompute key (s.proj p) n

/-- Seeding establishes the invariant: `init_match_caches` walks the ring in
FIFO order and `add`s every extracting token (`precompiled_backend.rs:
277-290`), which is `recompute` by construction. -/
theorem sync_seed (key : KeyOf) (s : Pool) (p : PlaceId) :
    Sync key s p (recompute key (s.proj p)) := fun _ => rfl

/-! ## The modeled mutation set

Every way the shipped backend can touch a compiled place's ring, with the
cache mirroring exactly the calls the code makes (and only those). -/

/-- The ring side of one matched consume: `to_consume` iterations of
`ring_remove_matching` (`precompiled_backend.rs:968-975`), each removing the
first `pred`-satisfying token or nothing. -/
def matchedRemoveIter (s : Pool) (p : PlaceId) (pred : Colour → Bool) :
    Nat → Pool
  | 0 => s
  | k + 1 => matchedRemoveIter (s.removeMatching p pred).2 p pred k

/-- A reset drain: `token_counts[pid]` repeated `ring_remove_first` calls
(`precompiled_backend.rs:1005-1013`). -/
def drainIter (s : Pool) (p : PlaceId) : Nat → Pool
  | 0 => s
  | k + 1 => drainIter (s.removeFirst p) p k

/-- One backend mutation addressed to one place.

* `add c` — `produce_token` / `inject_external_token`
  (`precompiled_backend.rs:1092-1102`, `:1121-1131`): `cache_add_token`
  then `ring_add_last`. The only mutations that *insert* into a ring.
* `matchedConsume pred m ringK cacheK` — the matched branch of
  `consume_for_firing` on one correlated input: `ringK` iterations of
  `ring_remove_matching pred` (`:961-975`) plus `cache.consume(m)` popping
  `cacheK` tokens of `m`'s queue for this input (`:997-1001`,
  `match_engine.rs:195-201`). The shipped eligible path always has
  `pred = keyPred key m` (the `:955-960` closure) and
  `ringK = cacheK = required`; the counts are carried separately precisely
  so `one_exactly_is_necessary` can exhibit why `One`/`Exactly` is
  load-bearing.
* `consumeFirst` — one foreign `ring_remove_first` (`:329-336`; the opcode
  path of `consume_for_firing` and the matched path's non-correlated
  inputs). **No cache call exists on this path.**
* `reset` — the RESET drain (`:1005-1013`). **No cache call exists on this
  path either.** -/
inductive Mut where
  | add (c : Colour)
  | matchedConsume (pred : Colour → Bool) (m : Name) (ringK cacheK : Nat)
  | consumeFirst
  | reset

/-- Pool effect of a mutation at place `r`. `consumeFirst` is guarded by the
executor's cardinality gate (`can_enable` never fires a consumer of an empty
ring; `Ring.lean`'s `first_isSome` is the `.unwrap()` totality); `reset`
drains the current count, as the shipped loop reads `token_counts[pid]`
first. -/
def applyMutPool (r : PlaceId) (s : Pool) : Mut → Pool
  | .add c => s.addLast r c
  | .matchedConsume pred _ ringK _ => matchedRemoveIter s r pred ringK
  | .consumeFirst => if 0 < s.cnt r then s.removeFirst r else s
  | .reset => drainIter s r (s.cnt r)

/-- Cache effect of a mutation at the cached place itself: `add` is mirrored
by `cache_add_token`, a matched consume by `cache.consume`; `consumeFirst`
and `reset` have **no mirror** in the shipped code — which is exactly why
eligibility must exclude them from the cached place. -/
def applyMutCache (key : KeyOf) (q : CacheQ) : Mut → CacheQ
  | .add c => cacheAdd key q c
  | .matchedConsume _ m _ cacheK => cachePopN q m cacheK
  | .consumeFirst => q
  | .reset => q

/-- One step of the joint system: the pool takes the mutation at its target
place; the cache component for `p` is touched only when the target is `p`
(`cache_add_token` at another place feeds other key indices of the matcher,
never this queue map). -/
def applyStep (key : KeyOf) (p : PlaceId) (sq : Pool × CacheQ) :
    PlaceId × Mut → Pool × CacheQ
  | (r, op) =>
    (applyMutPool r sq.1 op, if r = p then applyMutCache key sq.2 op else sq.2)

/-- A whole mutation sequence, left to right. -/
def runSteps (key : KeyOf) (p : PlaceId) :
    List (PlaceId × Mut) → Pool × CacheQ → Pool × CacheQ
  | [], sq => sq
  | st :: rest, sq => runSteps key p rest (applyStep key p sq st)

/-- The mutations eligibility permits **on the cached place**: token adds
(always mirrored), and matched consumes whose predicate is the name-equality
test for the popped name and whose ring/cache counts agree — the shape
`consume_for_firing` produces exactly when the correlated input is
`One`/`Exactly` (conjunct 1). `consumeFirst` and `reset` are forbidden —
conjuncts 3 and 2 respectively (`fire_muts_lockstep` derives all of this
from `FastPathEligible`). -/
def LockstepMut (key : KeyOf) : Mut → Prop
  | .add _ => True
  | .matchedConsume pred m ringK cacheK => pred = keyPred key m ∧ ringK = cacheK
  | .consumeFirst => False
  | .reset => False

/-! ## List and `beq` helpers (dependency-free, house-rolled) -/

theorem filter_eq_nil_of_false {l : List Colour} {g : Colour → Bool}
    (h : ∀ c ∈ l, g c = false) : l.filter g = [] := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [List.filter_cons, h c (by simp), if_neg Bool.false_ne_true]
    exact ih fun c' hc' => h c' (by simp [hc'])

/-- A token extracting to `m` never counts toward another name's queue. -/
theorem keyPred_other {key : KeyOf} {c : Colour} {m n : Name}
    (hm : key c = some m) (hne : n ≠ m) : keyPred key n c = false := by
  show (key c == some n) = false
  rw [hm]
  cases hb : ((some m : Option Name) == some n) with
  | false => rfl
  | true => exact absurd (Option.some.inj (eq_of_beq hb)).symm hne

theorem append_eq_nil' {α : Type} {l₁ l₂ : List α} (h : l₁ ++ l₂ = []) :
    l₁ = [] ∧ l₂ = [] := by
  cases l₁ with
  | nil => exact ⟨rfl, h⟩
  | cons a as => nomatch h

theorem countP_zero_all {α : Type} {g : α → Bool} {l : List α} :
    l.countP g = 0 → ∀ a ∈ l, g a = false := by
  induction l with
  | nil => intro _ a ha; cases ha
  | cons x rest ih =>
    intro h a ha
    rw [List.countP_cons] at h
    cases hx : g x with
    | true =>
      rw [hx, if_pos rfl] at h
      exact absurd h (by omega)
    | false =>
      rw [hx, if_neg Bool.false_ne_true, Nat.add_zero] at h
      cases ha with
      | head => exact hx
      | tail _ hm => exact ih h a hm

theorem flatMap_if_nil {α β : Type} {l : List α} {g : α → Bool}
    {f : α → List β} (h : ∀ a ∈ l, g a = false) :
    (l.flatMap fun a => if g a then f a else []) = [] := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, h a (by simp), if_neg Bool.false_ne_true,
      List.nil_append]
    exact ih fun a' ha' => h a' (by simp [ha'])

theorem flatMap_if_single {α β : Type} {g : α → Bool} {f : α → List β}
    {a₀ : α} :
    ∀ {l : List α}, l.countP g = 1 → l.find? g = some a₀ →
      (l.flatMap fun a => if g a then f a else []) = f a₀ := by
  intro l
  induction l with
  | nil => intro _ hfind; nomatch hfind
  | cons a rest ih =>
    intro hcount hfind
    rw [List.flatMap_cons]
    cases hg : g a with
    | true =>
      have ha : a = a₀ := by
        rw [List.find?_cons_of_pos hg] at hfind
        exact Option.some.inj hfind
      subst ha
      rw [List.countP_cons, hg, if_pos rfl] at hcount
      have h0 : rest.countP g = 0 := by omega
      rw [if_pos rfl, flatMap_if_nil (countP_zero_all h0), List.append_nil]
    | false =>
      rw [if_neg Bool.false_ne_true, List.nil_append]
      rw [List.countP_cons, hg, if_neg Bool.false_ne_true, Nat.add_zero]
        at hcount
      refine ih hcount ?_
      rw [List.find?_cons_of_neg (by simp [hg])] at hfind
      exact hfind

theorem any_eq_false_all {α : Type} {g : α → Bool} {l : List α}
    (h : l.any g = false) : ∀ a ∈ l, g a = false := by
  induction l with
  | nil => intro a ha; cases ha
  | cons x rest ih =>
    rw [List.any_cons] at h
    intro a ha
    cases hx : g x with
    | true => rw [hx, Bool.true_or] at h; cases h
    | false =>
      rw [hx, Bool.false_or] at h
      cases ha with
      | head => exact hx
      | tail _ hm => exact ih h a hm

/-! ## Per-mutation lockstep lemmas -/

/-- A produced/injected token keeps lockstep: `ring_add_last` appends at the
FIFO tail (RB5, `addLast_proj_self`) and `cache_add_token` appends to
exactly the extracted name's queue. -/
theorem sync_add {key : KeyOf} {s : Pool} {p : PlaceId} {q : CacheQ}
    (hwf : Pool.WF s) (hp : p < s.nplaces) (hq : Sync key s p q) (c : Colour) :
    Sync key (s.addLast p c) p (cacheAdd key q c) := by
  intro n
  rw [cacheAdd_eq, recompute_eq, Pool.addLast_proj_self hwf hp c,
    List.filter_append]
  cases hkc : (key c == some n) with
  | true =>
    rw [if_pos rfl, hq n, recompute_eq]
    congr 1
    rw [List.filter_cons, if_pos (show keyPred key n c = true from hkc),
      List.filter_nil]
  | false =>
    rw [if_neg Bool.false_ne_true, hq n, recompute_eq, List.filter_cons,
      show (keyPred key n c) = false from hkc, if_neg Bool.false_ne_true,
      List.filter_nil, List.append_nil]

/-- One `ring_remove_matching` on the name-equality predicate paired with
one `pop_front` of that name's queue keeps lockstep. The match half is RB6
(`removeMatching_some`): exactly the first predicate match is removed with
survivor order preserved, and every earlier survivor fails the predicate —
so the popped queue head is the removed token, other names' queues see
nothing. The no-match half (`removeMatching_none`) pairs an unchanged ring
with a pop of the (necessarily empty) queue. -/
theorem sync_matchedRemove_step {key : KeyOf} {m : Name} {s : Pool}
    {p : PlaceId} {q : CacheQ} (hwf : Pool.WF s) (hp : p < s.nplaces)
    (hq : Sync key s p q) :
    Sync key (s.removeMatching p (keyPred key m)).2 p (cachePop q m)
      ∧ Pool.WF (s.removeMatching p (keyPred key m)).2 := by
  cases hres : (s.removeMatching p (keyPred key m)).1 with
  | none =>
    obtain ⟨heq, hall⟩ := Pool.removeMatching_none hwf hp hres
    rw [heq]
    refine ⟨fun n => ?_, hwf⟩
    rw [cachePop_eq, recompute_eq]
    cases hb : (n == m) with
    | false => rw [if_neg Bool.false_ne_true, hq n, recompute_eq]
    | true =>
      have hn : n = m := eq_of_beq hb
      rw [if_pos rfl, hn, hq m, recompute_eq, filter_eq_nil_of_false hall]
      rfl
  | some c =>
    obtain ⟨hpredc, pre, post, hsplit, hprefail, hproj, hframe, hwf'⟩ :=
      Pool.removeMatching_some hwf hp hres
    have hkc : key c = some m := eq_of_beq hpredc
    refine ⟨fun n => ?_, hwf'⟩
    rw [cachePop_eq, recompute_eq, hproj]
    cases hb : (n == m) with
    | true =>
      have hn : n = m := eq_of_beq hb
      rw [if_pos rfl, hn, hq m, recompute_eq, hsplit, List.filter_append,
        List.filter_append, filter_eq_nil_of_false hprefail,
        List.nil_append, List.nil_append, List.filter_cons, if_pos hpredc,
        List.tail_cons]
    | false =>
      have hn : n ≠ m := fun hnm => by rw [hnm] at hb; simp at hb
      rw [if_neg Bool.false_ne_true, hq n, recompute_eq, hsplit,
        List.filter_append, List.filter_append, List.filter_cons,
        keyPred_other hkc hn, if_neg Bool.false_ne_true]

/-- `WF` survives `ring_remove_matching` (both halves of RB6). -/
theorem removeMatching_snd_wf {s : Pool} (hwf : Pool.WF s) {r : PlaceId}
    (hr : r < s.nplaces) (pred : Colour → Bool) :
    Pool.WF (s.removeMatching r pred).2 := by
  cases hres : (s.removeMatching r pred).1 with
  | none => rw [(Pool.removeMatching_none hwf hr hres).1]; exact hwf
  | some c =>
    obtain ⟨_, _, _, _, _, _, _, hwf'⟩ := Pool.removeMatching_some hwf hr hres
    exact hwf'

theorem removeMatching_snd_nplaces (s : Pool) (r : PlaceId)
    (pred : Colour → Bool) :
    (s.removeMatching r pred).2.nplaces = s.nplaces := by
  unfold Pool.removeMatching
  cases s.findMatch r pred with
  | none => rfl
  | some i =>
    dsimp only
    by_cases hside : i ≤ s.cnt r - 1 - i
    · rw [if_pos hside, Pool.headSlideAt_nplaces]
    · rw [if_neg hside, Pool.tailSlideAt_nplaces]

/-- Frame: `ring_remove_matching` at another place leaves this projection
untouched (RB6's other-place clause / identity on no match). -/
theorem removeMatching_snd_proj_other {s : Pool} (hwf : Pool.WF s)
    {r : PlaceId} (hr : r < s.nplaces) {p : PlaceId} (hp : p < s.nplaces)
    (hne : p ≠ r) (pred : Colour → Bool) :
    (s.removeMatching r pred).2.proj p = s.proj p := by
  cases hres : (s.removeMatching r pred).1 with
  | none => rw [(Pool.removeMatching_none hwf hr hres).1]
  | some c =>
    obtain ⟨_, _, _, _, _, _, hframe, _⟩ := Pool.removeMatching_some hwf hr hres
    exact hframe p hp hne

/-- The full matched consume — `ringK` ring removals paired with `ringK`
queue pops — keeps lockstep for **any** count, because each single step does
(`sync_matchedRemove_step`, including the exhausted case). Conjunct 1's
real content is therefore not this lemma but the *pairing*: only for
`One`/`Exactly` does the shipped code pop as many as it removes — see
`one_exactly_is_necessary`. -/
theorem sync_matchedRemove {key : KeyOf} {m : Name} {p : PlaceId} (k : Nat) :
    ∀ {s : Pool} {q : CacheQ}, Pool.WF s → p < s.nplaces → Sync key s p q →
      Sync key (matchedRemoveIter s p (keyPred key m) k) p (cachePopN q m k)
        ∧ Pool.WF (matchedRemoveIter s p (keyPred key m) k) := by
  induction k with
  | zero => intro s q hwf _ hq; exact ⟨hq, hwf⟩
  | succ k ih =>
    intro s q hwf hp hq
    simp only [matchedRemoveIter, cachePopN]
    obtain ⟨hs', hwf'⟩ := sync_matchedRemove_step hwf hp hq
    exact ih hwf' (by rw [removeMatching_snd_nplaces]; exact hp) hs'

/-! ## WF / frame / nplaces plumbing for whole mutations -/

theorem matchedRemoveIter_wf {p : PlaceId} (pred : Colour → Bool) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → p < s.nplaces →
      Pool.WF (matchedRemoveIter s p pred k) := by
  intro k
  induction k with
  | zero => intro s hwf _; exact hwf
  | succ k ih =>
    intro s hwf hp
    simp only [matchedRemoveIter]
    exact ih (removeMatching_snd_wf hwf hp pred)
      (by rw [removeMatching_snd_nplaces]; exact hp)

theorem matchedRemoveIter_nplaces (r : PlaceId) (pred : Colour → Bool) :
    ∀ (k : Nat) (s : Pool),
      (matchedRemoveIter s r pred k).nplaces = s.nplaces := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [matchedRemoveIter]
    rw [ih, removeMatching_snd_nplaces]

theorem matchedRemoveIter_proj_other {r p : PlaceId} (hne : p ≠ r)
    (pred : Colour → Bool) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → p < s.nplaces →
      (matchedRemoveIter s r pred k).proj p = s.proj p := by
  intro k
  induction k with
  | zero => intro s _ _ _; rfl
  | succ k ih =>
    intro s hwf hr hp
    simp only [matchedRemoveIter]
    rw [ih (removeMatching_snd_wf hwf hr pred)
        (by rw [removeMatching_snd_nplaces]; exact hr)
        (by rw [removeMatching_snd_nplaces]; exact hp),
      removeMatching_snd_proj_other hwf hr hp hne pred]

theorem drainIter_wf (r : PlaceId) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → k ≤ s.cnt r →
      Pool.WF (drainIter s r k) := by
  intro k
  induction k with
  | zero => intro s hwf _ _; exact hwf
  | succ k ih =>
    intro s hwf hr hk
    simp only [drainIter]
    have hcnt : 0 < s.cnt r := by omega
    exact ih (Pool.removeFirst_wf hwf hr hcnt)
      (by rw [Pool.removeFirst_nplaces]; exact hr)
      (by rw [Pool.removeFirst_cnt_self]; omega)

theorem drainIter_nplaces (r : PlaceId) :
    ∀ (k : Nat) (s : Pool), (drainIter s r k).nplaces = s.nplaces := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [drainIter]
    rw [ih, Pool.removeFirst_nplaces]

theorem drainIter_proj_other {r p : PlaceId} (hne : p ≠ r) :
    ∀ (k : Nat) {s : Pool}, Pool.WF s → r < s.nplaces → p < s.nplaces →
      k ≤ s.cnt r → (drainIter s r k).proj p = s.proj p := by
  intro k
  induction k with
  | zero => intro s _ _ _ _; rfl
  | succ k ih =>
    intro s hwf hr hp hk
    simp only [drainIter]
    have hcnt : 0 < s.cnt r := by omega
    rw [ih (Pool.removeFirst_wf hwf hr hcnt)
        (by rw [Pool.removeFirst_nplaces]; exact hr)
        (by rw [Pool.removeFirst_nplaces]; exact hp)
        (by rw [Pool.removeFirst_cnt_self]; omega),
      Pool.removeFirst_proj_other hwf hr hp hne]

theorem addLast_nplaces (s : Pool) (r : PlaceId) (c : Colour) :
    (s.addLast r c).nplaces = s.nplaces := by
  unfold Pool.addLast
  by_cases hfull : s.cnt r = s.cap r
  · rw [if_pos hfull, Pool.pushLast_nplaces, Pool.growRing_nplaces]
  · rw [if_neg hfull, Pool.pushLast_nplaces]

/-- Every modeled mutation preserves RB1–RB3. -/
theorem applyMutPool_wf {r : PlaceId} {s : Pool} (hwf : Pool.WF s)
    (hr : r < s.nplaces) (op : Mut) : Pool.WF (applyMutPool r s op) := by
  cases op with
  | add c => exact Pool.addLast_wf hwf hr c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_wf pred ringK hwf hr
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc]; exact Pool.removeFirst_wf hwf hr hc
    · rw [if_neg hc]; exact hwf
  | reset => exact drainIter_wf r (s.cnt r) hwf hr (Nat.le_refl _)

theorem applyMutPool_nplaces (r : PlaceId) (s : Pool) (op : Mut) :
    (applyMutPool r s op).nplaces = s.nplaces := by
  cases op with
  | add c => exact addLast_nplaces s r c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_nplaces r pred ringK s
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc, Pool.removeFirst_nplaces]
    · rw [if_neg hc]
  | reset => exact drainIter_nplaces r (s.cnt r) s

/-- Frame: any mutation addressed to another place leaves this place's
projection untouched — assembled from `Ring.lean`'s `*_proj_other` family. -/
theorem applyMutPool_proj_other {r p : PlaceId} {s : Pool} (hwf : Pool.WF s)
    (hr : r < s.nplaces) (hp : p < s.nplaces) (hne : p ≠ r) (op : Mut) :
    (applyMutPool r s op).proj p = s.proj p := by
  cases op with
  | add c => exact Pool.addLast_proj_other hwf hr hp hne c
  | matchedConsume pred m ringK cacheK =>
    exact matchedRemoveIter_proj_other hne pred ringK hwf hr hp
  | consumeFirst =>
    simp only [applyMutPool]
    by_cases hc : 0 < s.cnt r
    · rw [if_pos hc]; exact Pool.removeFirst_proj_other hwf hr hp hne
    · rw [if_neg hc]
  | reset => exact drainIter_proj_other hne (s.cnt r) hwf hr hp (Nat.le_refl _)

/-! ## The main theorem -/

/-- One step preserves lockstep: a step at the cached place must be a
permitted mutation (`LockstepMut`); a step anywhere else is pure frame. -/
theorem sync_step {key : KeyOf} {p : PlaceId} {s : Pool} {q : CacheQ}
    {r : PlaceId} {op : Mut} (hwf : Pool.WF s) (hp : p < s.nplaces)
    (hr : r < s.nplaces) (hq : Sync key s p q)
    (hop : r = p → LockstepMut key op) :
    Sync key (applyStep key p (s, q) (r, op)).1 p
        (applyStep key p (s, q) (r, op)).2
      ∧ Pool.WF (applyStep key p (s, q) (r, op)).1 := by
  by_cases hrp : r = p
  · subst hrp
    have hl := hop rfl
    simp only [applyStep]
    rw [if_pos trivial]
    cases op with
    | add c =>
      exact ⟨sync_add hwf hr hq c, Pool.addLast_wf hwf hr c⟩
    | matchedConsume pred m ringK cacheK =>
      obtain ⟨hpred, hk⟩ := hl
      subst hpred
      subst hk
      simp only [applyMutPool, applyMutCache]
      exact sync_matchedRemove _ hwf hr hq
    | consumeFirst => exact (hl : False).elim
    | reset => exact (hl : False).elim
  · simp only [applyStep]
    rw [if_neg hrp]
    refine ⟨fun n => ?_, applyMutPool_wf hwf hr op⟩
    rw [recompute_eq,
      applyMutPool_proj_other hwf hr hp (fun h => hrp h.symm) op, hq n,
      recompute_eq]

/-- **Main theorem — the cache can never desync.** Starting from a synced
state (e.g. the freshly seeded cache, `sync_seed`), after ANY finite
sequence of modeled backend mutations — arbitrary mutations at other
places, and at the cached place only what eligibility permits (token adds
plus the owning join's matched consumes; `fire_muts_lockstep` supplies that
hypothesis from `FastPathEligible`) — the cache still equals `recompute` of
the live pool, and the pool is still well-formed. This is the theorem the
`init_match_caches` doc comment promises in prose, and the invariant that
makes `can_enable`'s O(1) `cache.best()` read equivalent to the O(n)
`find_match_binding` rebuild it replaces (NU-020; the selection equality on
equal contents is NU-022's differential guarantee). -/
theorem match_cache_lockstep {key : KeyOf} {p : PlaceId}
    (steps : List (PlaceId × Mut)) :
    ∀ {s : Pool} {q : CacheQ}, Pool.WF s → p < s.nplaces → Sync key s p q →
      (∀ st ∈ steps, st.1 < s.nplaces) →
      (∀ st ∈ steps, st.1 = p → LockstepMut key st.2) →
      Sync key (runSteps key p steps (s, q)).1 p
          (runSteps key p steps (s, q)).2
        ∧ Pool.WF (runSteps key p steps (s, q)).1 := by
  induction steps with
  | nil => intro s q hwf hp hq _ _; exact ⟨hq, hwf⟩
  | cons st rest ih =>
    intro s q hwf hp hq hin helig
    obtain ⟨r, op⟩ := st
    simp only [runSteps]
    have hr : r < s.nplaces := hin (r, op) (by simp)
    obtain ⟨hs', hwf'⟩ := sync_step hwf hp hr hq (helig (r, op) (by simp))
    have hnp : (applyStep key p (s, q) (r, op)).1.nplaces = s.nplaces :=
      applyMutPool_nplaces r s op
    exact ih (s := (applyStep key p (s, q) (r, op)).1)
      (q := (applyStep key p (s, q) (r, op)).2) hwf' (by rw [hnp]; exact hp)
      hs' (fun st' hm => by rw [hnp]; exact hin st' (by simp [hm]))
      (fun st' hm => helig st' (by simp [hm]))

/-! ## The eligibility predicate, exactly as `init_match_caches` states it -/

/-- The `required` match of `init_match_caches`
(`precompiled_backend.rs:254-262`): `Some(In::One) => 1`,
`Some(In::Exactly{count}) => count`, everything else — `All`, `AtLeast`, or
no input spec at all — is ineligible (`_ => { eligible = false }`). -/
def fixedRequired : Card → Option Nat
  | .one => some 1
  | .exactly k => some k
  | .all => none
  | .atLeast _ => none

/-- Conjunct 1 for one correlated input: the spec lookup
(`t.input_specs().iter().find(...)`, `precompiled_backend.rs:250-253` —
`specAt` in `Basic.lean`) composed with `fixedRequired`. `some k` means the
input consumes a fixed `k` tokens per firing. -/
def requiredOf (t : Transition) (p : PlaceId) : Option Nat :=
  (specAt t p).bind fun sp => fixedRequired sp.card

/-- Conjunct 2's artifact: the `reset_target` boolean array of
`init_match_caches` (`precompiled_backend.rs:224-231`) — is `p` a reset
target of *any* transition (the owner included)? -/
def resetTarget (ts : List Transition) (p : PlaceId) : Bool :=
  ts.any fun u => u.resets.any fun r => r == p

/-- The Rust inner loop `for spec in t.input_specs() { if pid { push(tid) } }`
(`precompiled_backend.rs:218-223`): one entry per input spec of the
transition at index `i` that lands on `p`. -/
def specTids (i : Nat) (p : PlaceId) : List InSpec → List Nat
  | [] => []
  | sp :: rest =>
    if sp.place == p then i :: specTids i p rest else specTids i p rest

/-- Conjunct 3's artifact: the `input_consumers[pid]` vector
(`precompiled_backend.rs:217-223`) — every transition index that consumes
`p` through an input arc, in index order, with multiplicity. -/
def consumerTids : List Transition → Nat → PlaceId → List Nat
  | [], _, _ => []
  | u :: rest, i, p => specTids i p u.inputs ++ consumerTids rest (i + 1) p

def inputConsumers (ts : List Transition) (p : PlaceId) : List Nat :=
  consumerTids ts 0 p

/-- **The fast-path eligibility predicate of `init_match_caches`**
(`precompiled_backend.rs:245-268`), for the correlated input `p` of the
matched transition at index `tid`:

* `fixed_count` — the input spec on `p` is `One`/`Exactly` with consume
  count `k` (`:254-262`);
* `no_reset` — `!reset_target[pid]` (`:264`);
* `sole_consumer` — `input_consumers[pid] == [tid]` (`:264`): exactly one
  input arc in the whole net lands on `p`, and it is `tid`'s.

The code additionally requires `p` to be a compiled place id (`:246-249`);
the model's `PlaceId`s are dense, so that conjunct is absorbed (tokens for
unknown places never enter the pool or the caches — CORE-072). A matched
transition is fast-path eligible when every one of its key places satisfies
this predicate; the lockstep theorems are stated per key place. -/
structure FastPathEligible (ts : List Transition) (tid : Nat)
    (t : Transition) (p : PlaceId) (k : Nat) : Prop where
  owner : ts[tid]? = some t
  fixed_count : requiredOf t p = some k
  no_reset : resetTarget ts p = false
  sole_consumer : inputConsumers ts p = [tid]

/-! ### Static-analysis lemmas over the consumer/reset maps -/

theorem specTids_mem {i : Nat} {p : PlaceId} {l : List InSpec} :
    ∀ {x : Nat}, x ∈ specTids i p l → x = i := by
  induction l with
  | nil => intro x hx; cases hx
  | cons sp rest ih =>
    intro x hx
    simp only [specTids] at hx
    cases hpl : (sp.place == p) with
    | true =>
      rw [if_pos hpl] at hx
      cases hx with
      | head => rfl
      | tail _ h => exact ih h
    | false =>
      rw [if_neg (by simp [hpl])] at hx
      exact ih hx

theorem specTids_length {i : Nat} {p : PlaceId} :
    ∀ (l : List InSpec),
      (specTids i p l).length = l.countP fun sp => sp.place == p := by
  intro l
  induction l with
  | nil => rfl
  | cons sp rest ih =>
    simp only [specTids, List.countP_cons]
    cases hpl : (sp.place == p) with
    | true => simp [ih]
    | false => simp [ih]

theorem consumerTids_ge {p : PlaceId} {ts : List Transition} :
    ∀ {i x : Nat}, x ∈ consumerTids ts i p → i ≤ x := by
  induction ts with
  | nil => intro i x hx; cases hx
  | cons u rest ih =>
    intro i x hx
    simp only [consumerTids] at hx
    rcases List.mem_append.mp hx with h | h
    · have := specTids_mem h; omega
    · have := ih h; omega

theorem consumerTids_nil {p : PlaceId} {ts : List Transition} :
    ∀ {i : Nat}, consumerTids ts i p = [] →
      ∀ (j : Nat) (u : Transition), ts[j]? = some u →
        u.inputs.countP (fun sp => sp.place == p) = 0 := by
  induction ts with
  | nil => intro i _ j u hj; nomatch hj
  | cons u₀ rest ih =>
    intro i h j u hj
    simp only [consumerTids] at h
    obtain ⟨h1, h2⟩ := append_eq_nil' h
    cases j with
    | zero =>
      have hu : u₀ = u := Option.some.inj hj
      subst hu
      rw [← specTids_length (i := i) u₀.inputs, h1]
      rfl
    | succ j' => exact ih h2 j' u hj

/-- The load-bearing consequence of `input_consumers[pid] == [tid]`: the
transition at index `tid` has **exactly one** input spec on `p`, and every
other transition has **none**. -/
theorem consumerTids_single {p : PlaceId} {ts : List Transition} :
    ∀ {i tid : Nat}, consumerTids ts i p = [tid] →
      ∀ (j : Nat) (u : Transition), ts[j]? = some u →
        u.inputs.countP (fun sp => sp.place == p)
          = if i + j = tid then 1 else 0 := by
  induction ts with
  | nil => intro i tid _ j u hj; nomatch hj
  | cons u₀ rest ih =>
    intro i tid h j u hj
    simp only [consumerTids] at h
    cases hfm : specTids i p u₀.inputs with
    | nil =>
      rw [hfm, List.nil_append] at h
      have htid : i + 1 ≤ tid :=
        consumerTids_ge (show tid ∈ consumerTids rest (i + 1) p by
          rw [h]; exact List.Mem.head _)
      cases j with
      | zero =>
        have hu : u₀ = u := Option.some.inj hj
        subst hu
        rw [if_neg (by omega), ← specTids_length (i := i) u₀.inputs, hfm]
        rfl
      | succ j' =>
        rw [ih h j' u hj]
        by_cases hc : i + 1 + j' = tid
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
    | cons x xs =>
      rw [hfm, List.cons_append] at h
      injection h with hx htail
      obtain ⟨hxs, hrec⟩ := append_eq_nil' htail
      have hxi : x = i := specTids_mem (show x ∈ specTids i p u₀.inputs by
        rw [hfm]; exact List.Mem.head _)
      cases j with
      | zero =>
        have hu : u₀ = u := Option.some.inj hj
        subst hu
        rw [if_pos (by omega), ← specTids_length (i := i) u₀.inputs, hfm, hxs]
        rfl
      | succ j' =>
        rw [if_neg (by omega)]
        exact consumerTids_nil hrec j' u hj

theorem resetTarget_false {ts : List Transition} {p : PlaceId}
    (h : resetTarget ts p = false) :
    ∀ u ∈ ts, (u.resets.any fun r => r == p) = false := by
  induction ts with
  | nil => intro u hu; cases hu
  | cons u₀ rest ih =>
    rw [resetTarget, List.any_cons] at h
    intro u hu
    cases hx : (u₀.resets.any fun r => r == p) with
    | true => rw [hx, Bool.true_or] at h; cases h
    | false =>
      rw [hx, Bool.false_or] at h
      cases hu with
      | head => exact hx
      | tail _ hm => exact ih h u hm

/-! ## What one firing does to the cached place -/

/-- The mutations the consume phase of one firing of `u`
(`consume_for_firing`, `precompiled_backend.rs:924-1014`) performs **on the
single place `p`**, in program order: for each input spec landing on `p`, a
matched consume when `p` is one of `u`'s correlated inputs
(`key_for(...).is_some()`, `:948-953`; ring count per `:961-967` —
`One => 1`, `Exactly => count`, `All`/`AtLeast => count_matching`, the
`matchAvail` parameter — cache pops per the matcher's fixed
`requireds[i] = sp.card.required`, cf. `find_match_binding`'s
`:610-615`), else plain FIFO removals (`consumeCountAt`, opcode path,
`avail = token_counts[pid]`); then one reset drain per reset arc on `p`
(`:1005-1013`). Read arcs peek and mutate nothing (`:1003`). Steps at
other places of the same firing are separate `applyStep` targets, covered
by the frame case. -/
def consumeMutsAt (u : Transition) (p : PlaceId) (isKey : Bool)
    (pred : Colour → Bool) (chosen : Name) (avail matchAvail : Nat) :
    List Mut :=
  (u.inputs.flatMap fun sp =>
    if sp.place == p then
      if isKey then
        [Mut.matchedConsume pred chosen (consumeCountAt matchAvail sp.card)
          sp.card.required]
      else
        List.replicate (consumeCountAt avail sp.card) Mut.consumeFirst
    else [])
    ++ (u.resets.flatMap fun r => if r == p then [Mut.reset] else [])

/-- Conjuncts 2+3 isolate the place: a firing of any transition **other
than the owner** performs no mutation whatsoever on the cached place — no
input arc of it lands there (`sole_consumer`) and it never resets there
(`no_reset`). The only way tokens then enter `p` is produce/inject
(mirrored `add` steps), exactly as the `init_match_caches` comment
argues. -/
theorem foreign_fire_emits_nothing {ts : List Transition} {tid : Nat}
    {t : Transition} {p : PlaceId} {k : Nat}
    (he : FastPathEligible ts tid t p k) {j : Nat} {u : Transition}
    (hj : ts[j]? = some u) (hne : j ≠ tid) (isKey : Bool)
    (pred : Colour → Bool) (chosen : Name) (avail matchAvail : Nat) :
    consumeMutsAt u p isKey pred chosen avail matchAvail = [] := by
  have hsole : consumerTids ts 0 p = [tid] := he.sole_consumer
  have hcount := consumerTids_single hsole j u hj
  rw [if_neg (by omega : ¬(0 + j = tid))] at hcount
  unfold consumeMutsAt
  rw [flatMap_if_nil (countP_zero_all hcount),
    flatMap_if_nil (any_eq_false_all
      (resetTarget_false he.no_reset u (List.mem_of_getElem? hj))),
    List.nil_append]

/-- Conjunct 1 shapes the owner's own firing: on an eligible key place the
whole consume phase is **one** matched consume whose ring count and cache
count are both the fixed `k` — `One`/`Exactly` is precisely the fragment
where `to_consume` (`:961-967`) and the matcher's `requireds[i]` agree, and
`sole_consumer` guarantees the single spec and `no_reset` the empty reset
tail. -/
theorem owner_fire_emits_lockstep {ts : List Transition} {tid : Nat}
    {t : Transition} {p : PlaceId} {k : Nat}
    (he : FastPathEligible ts tid t p k) (key : KeyOf) (chosen : Name)
    (avail matchAvail : Nat) :
    consumeMutsAt t p true (keyPred key chosen) chosen avail matchAvail
      = [Mut.matchedConsume (keyPred key chosen) chosen k k] := by
  obtain ⟨sp₀, hfind, hfx⟩ : ∃ sp, specAt t p = some sp
      ∧ fixedRequired sp.card = some k := by
    have h := he.fixed_count
    unfold requiredOf at h
    cases hs : specAt t p with
    | none => rw [hs] at h; nomatch h
    | some sp => rw [hs] at h; exact ⟨sp, rfl, h⟩
  have hsole : consumerTids ts 0 p = [tid] := he.sole_consumer
  have hcount := consumerTids_single hsole tid t he.owner
  rw [if_pos (by omega : 0 + tid = tid)] at hcount
  unfold consumeMutsAt
  rw [flatMap_if_single hcount hfind,
    flatMap_if_nil (any_eq_false_all
      (resetTarget_false he.no_reset t (List.mem_of_getElem? he.owner))),
    List.append_nil, if_pos rfl]
  cases hcard : sp₀.card with
  | one =>
    rw [hcard] at hfx
    have hk : (1 : Nat) = k := Option.some.inj hfx
    subst hk
    rfl
  | exactly j =>
    rw [hcard] at hfx
    have hk : j = k := Option.some.inj hfx
    subst hk
    rfl
  | all => rw [hcard] at hfx; nomatch hfx
  | atLeast j => rw [hcard] at hfx; nomatch hfx

/-- **The bridge**: under the eligibility predicate, every mutation the
consume phase of ANY firing performs on the cached place satisfies
`LockstepMut` — so `match_cache_lockstep`'s hypothesis holds for every
sequence of shipped mutations (adds are `LockstepMut` by definition, and
they plus firings are the only pool mutations the backend has). `howner`
records what the shipped matched path guarantees when the owner itself
fires: `p` is one of its correlated inputs and the predicate is the
name-equality closure for the chosen binding (`:948-960`). -/
theorem fire_muts_lockstep {ts : List Transition} {tid : Nat}
    {t : Transition} {p : PlaceId} {k : Nat}
    (he : FastPathEligible ts tid t p k) {key : KeyOf} {j : Nat}
    {u : Transition} (hj : ts[j]? = some u) (isKey : Bool)
    (pred : Colour → Bool) (chosen : Name) (avail matchAvail : Nat)
    (howner : j = tid → isKey = true ∧ pred = keyPred key chosen) :
    ∀ op ∈ consumeMutsAt u p isKey pred chosen avail matchAvail,
      LockstepMut key op := by
  by_cases hjt : j = tid
  · subst hjt
    rw [he.owner] at hj
    have hu : t = u := Option.some.inj hj
    subst hu
    obtain ⟨hk1, hk2⟩ := howner rfl
    subst hk1
    subst hk2
    rw [owner_fire_emits_lockstep he key chosen avail matchAvail]
    intro op hop
    cases hop with
    | head => exact ⟨rfl, rfl⟩
    | tail _ hm => cases hm
  · rw [foreign_fire_emits_nothing he hj hjt isKey pred chosen avail
      matchAvail]
    intro op hop
    cases hop

/-! ## Necessity witnesses

House rule: every hypothesis earns a concrete counterexample. Each of the
three eligibility conjuncts is dropped in isolation on a minimal
configuration — the other two conjuncts demonstrably still hold — and a
mutation the shipped code really performs desyncs the cache. The shared
fixture: place 0 holds tokens `[5, 6]`, both extracting to name `7`
(`wKey`), and the cache starts freshly seeded (`wCache = recompute …`,
which is `Sync` by `sync_seed`). -/

/-- Key extractor for the witnesses: every token correlates to name `7`. -/
def wKey : KeyOf := fun _ => some 7

/-- Two-place demo pool: place 0 (block `[0,4)`) holds `[5, 6]`, place 1
(block `[4,8)`) is empty. -/
def wPool : Pool :=
  { pool := fun idx => if idx = 0 then some 5 else if idx = 1 then some 6 else none
    len := 8
    offset := fun q => if q = 0 then 0 else 4
    head := fun _ => 0
    tail := fun q => if q = 0 then 2 else 0
    cnt := fun q => if q = 0 then 2 else 0
    cap := fun _ => 4
    nplaces := 2 }

/-- The freshly seeded cache for place 0 (`Sync` holds by `sync_seed`). -/
def wCache : CacheQ := recompute wKey (wPool.proj 0)

/-- The eligible owner shape: a single `one()` correlated input on place 0. -/
def wJoinOne : Transition :=
  { name := "join"
    inputs := [{ place := 0, card := .one, guard := none }]
    inhibitors := [], reads := [], resets := [] }

/-- Conjunct-1 violation: the correlated input is `at_least(1)`. -/
def wJoinAtLeast : Transition :=
  { name := "join"
    inputs := [{ place := 0, card := .atLeast 1, guard := none }]
    inhibitors := [], reads := [], resets := [] }

/-- Conjunct-3 violation: a second transition also consumes place 0. -/
def wRival : Transition :=
  { name := "rival"
    inputs := [{ place := 0, card := .one, guard := none }]
    inhibitors := [], reads := [], resets := [] }

/-- Conjunct-2 violation: a transition with a reset arc on place 0 (its own
trigger input is on place 1). -/
def wSweeper : Transition :=
  { name := "sweeper"
    inputs := [{ place := 1, card := .one, guard := none }]
    inhibitors := [], reads := [], resets := [0] }

/-- Sanity: the single-`one()`-join net really is fast-path eligible with
fixed count 1 — the predicate is satisfiable, so the witnesses below drop
exactly one conjunct each. -/
theorem wJoinOne_is_fast_path : FastPathEligible [wJoinOne] 0 wJoinOne 0 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Conjunct 1 (`One`/`Exactly`) is necessary.** With `at_least(1)` the
other two conjuncts still hold, but the firing's ring side consumes
`count_matching = 2` tokens (`:964-966`) while the fixed-consume matcher's
`consume` pops only `requireds[i] = 1` (`match_engine.rs:195-201` — it has
no variable-count operation, which is the code comment's "not modellable by
the fixed-consume matcher"). The emitted mutation is exactly
`matchedConsume` with `ringK = 2 ≠ 1 = cacheK` — `LockstepMut` fails — and
applying it leaves the cache claiming a token of name `7` that the ring no
longer holds. -/
theorem one_exactly_is_necessary :
    requiredOf wJoinAtLeast 0 = none
      ∧ resetTarget [wJoinAtLeast] 0 = false
      ∧ inputConsumers [wJoinAtLeast] 0 = [0]
      ∧ consumeMutsAt wJoinAtLeast 0 true (keyPred wKey 7) 7 2 2
          = [Mut.matchedConsume (keyPred wKey 7) 7 2 1]
      ∧ ¬ Sync wKey
          (applyStep wKey 0 (wPool, wCache)
            (0, Mut.matchedConsume (keyPred wKey 7) 7 2 1)).1 0
          (applyStep wKey 0 (wPool, wCache)
            (0, Mut.matchedConsume (keyPred wKey 7) 7 2 1)).2 := by
  refine ⟨by decide, by decide, by decide, rfl, fun h => ?_⟩
  exact absurd (h 7) (by decide)

/-- **Conjunct 3 (sole consumer) is necessary.** A rival `one()` consumer of
place 0 leaves conjuncts 1 and 2 intact, but its firing is a plain
`ring_remove_first` on the opcode path — a path with **no** cache call — so
one rival firing removes the ring head while the cache still lists it. -/
theorem sole_consumer_is_necessary :
    requiredOf wJoinOne 0 = some 1
      ∧ resetTarget [wJoinOne, wRival] 0 = false
      ∧ inputConsumers [wJoinOne, wRival] 0 = [0, 1]
      ∧ consumeMutsAt wRival 0 false (keyPred wKey 7) 7 2 2
          = [Mut.consumeFirst]
      ∧ ¬ Sync wKey
          (applyStep wKey 0 (wPool, wCache) (0, Mut.consumeFirst)).1 0
          (applyStep wKey 0 (wPool, wCache) (0, Mut.consumeFirst)).2 := by
  refine ⟨by decide, by decide, by decide, rfl, fun h => ?_⟩
  exact absurd (h 7) (by decide)

/-- **Conjunct 2 (never a reset target) is necessary.** A sweeper with a
reset arc on place 0 leaves conjuncts 1 and 3 intact (its own input is on
place 1), but its firing drains the whole ring through the RESET tail —
again a path with **no** cache call — so one sweep empties the place while
the cache still claims both tokens. -/
theorem no_reset_is_necessary :
    requiredOf wJoinOne 0 = some 1
      ∧ inputConsumers [wJoinOne, wSweeper] 0 = [0]
      ∧ resetTarget [wJoinOne, wSweeper] 0 = true
      ∧ consumeMutsAt wSweeper 0 false (keyPred wKey 7) 7 0 0 = [Mut.reset]
      ∧ ¬ Sync wKey
          (applyStep wKey 0 (wPool, wCache) (0, Mut.reset)).1 0
          (applyStep wKey 0 (wPool, wCache) (0, Mut.reset)).2 := by
  refine ⟨by decide, by decide, by decide, rfl, fun h => ?_⟩
  exact absurd (h 7) (by decide)

end Libpetri
