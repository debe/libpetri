/-
# Match cache: names, keys, cache state, the mutation set

The definitions and list helpers of `MatchCache.lean`, split out of it; the
lockstep theorems stay there.
-/
import Libpetri.Compile

namespace Libpetri

/-! ## Names, keys, cache state -/

/-- A correlation name. `libpetri-core/src/name.rs` `NameId` is an interned
string; only equality matters for lockstep (NU-001 ordering matters to
selection, which is out of scope here), so `Nat` suffices. -/
abbrev Name := Nat

/-- A match key's projection: `MatchKey::extract` (`match_spec.rs:55`), as
called by `cache_add_token` and `find_match_binding`. `value → Option<NameId>`
— a token whose extraction fails is invisible to the matcher. -/
abbrev KeyOf := Colour → Option Name

/-- The ν-net name-equality test — the `pred` closure the matched consume
builds at `precompiled_backend.rs:1163-1168`:
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
`cache_add_token` (`precompiled_backend.rs:364-383`): if the key extracts a
name, push the token at the back of that name's queue; otherwise do
nothing. -/
def cacheAdd (key : KeyOf) (q : CacheQ) (c : Colour) : CacheQ :=
  fun n => if key c == some n then q n ++ [c] else q n

/-- One `q.pop_front()` on name `m`'s queue — `IncrementalMatcher::consume`
(`match_engine.rs:197-199`) calling `MinQueue::pop_front` (`:102-109`):
FIFO-within-name removal, a no-op on an empty queue. -/
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
(`precompiled_backend.rs:341-359`) and the queue-level ground truth
underlying `find_match_binding`'s `(count, min_created_at)` index
(`precompiled_backend.rs:779-793`) — the index is the image of these
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
FIFO order and `add`s every extracting token
(`precompiled_backend.rs:344-359`), which is `recompute` by construction. -/
theorem sync_seed (key : KeyOf) (s : Pool) (p : PlaceId) :
    Sync key s p (recompute key (s.proj p)) := fun _ => rfl

/-! ## The modeled mutation set

Every way the shipped backend can touch a compiled place's ring, with the
cache mirroring exactly the calls the code makes (and only those). -/

/-- The ring side of one matched consume: `to_consume` iterations of
`ring_remove_matching`, as `consume_for_firing` calls it
(`precompiled_backend.rs:1180-1188`), each removing the first
`pred`-satisfying token or nothing. -/
def matchedRemoveIter (s : Pool) (p : PlaceId) (pred : Colour → Bool) :
    Nat → Pool
  | 0 => s
  | k + 1 => matchedRemoveIter (s.removeMatching p pred).2 p pred k

/-- A reset drain: `drainable(pid, token_counts[pid])` repeated
`ring_remove_first` calls — `consume_for_firing`'s RESET tail
(`precompiled_backend.rs:1222-1230` matched, `:1265-1274` opcode). -/
def drainIter (s : Pool) (p : PlaceId) : Nat → Pool
  | 0 => s
  | k + 1 => drainIter (s.removeFirst p) p k

/-- One backend mutation addressed to one place.

* `add c` — `produce_token` / `inject_external_token`
  (`precompiled_backend.rs:1313-1327`, `:1319-1329`): `cache_add_token`
  then `ring_add_last`. The only mutations that *insert* into a ring.
  `produce_token` additionally records a same-pass deposit (EXEC-003 AC4/AC5,
  `:1292-1294`), which touches neither ring nor cache and is invisible here.
* `matchedConsume pred m ringK cacheK` — the matched branch of
  `consume_for_firing` on one correlated input: `ringK` iterations of
  `ring_remove_matching pred` (`precompiled_backend.rs:1180-1188`) plus
  `cache.consume(m)` popping `cacheK` tokens of `m`'s queue for this input
  (`:1188-1192`, `match_engine.rs:195-201`). The shipped eligible path always
  has `pred = keyPred key m` (the `precompiled_backend.rs:1163-1168` closure) and
  `ringK = cacheK = required`; the counts are carried separately precisely
  so `one_exactly_is_necessary` can exhibit why `One`/`Exactly` is
  load-bearing.
* `consumeFirst` — one foreign `ring_remove_first`
  (`precompiled_backend.rs:396-403`; the opcode
  path of `consume_for_firing` and the matched path's non-correlated
  inputs). **No cache call exists on this path.**
* `reset` — the RESET drain (`:1196-1204` / `:1265-1274`). **No cache call
  exists on this path either.** -/
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

end Libpetri
