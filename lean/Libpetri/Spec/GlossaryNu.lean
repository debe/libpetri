import Mathlib.Data.List.MinMax
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot
import Libpetri.Spec.GlossaryQueue

set_option linter.missingDocs true

/-!
# Glossary: ν-net terms (match specification, chosen name, correlated take)

The executor-side terms of the ν requirements ([NU-020], [NU-021], [NU-022], [NU-054]) on queue
markings. Each glossary term refers to its glossary entry by name, `Glossary: *Place* (spec/glossary.md)`, rather than copying it
(section "ν-nets").

* **Tokens and names.** A ν token is `Stamped V`: a value and its `createdAt` stamp ([CORE-011]).
  A key projection is partial (`KeyFn V Nm := V → Option Nm`, ruling D37 (a)): a token whose key
  yields no name has no name on that input and is never matched or consumed by it.
* **Transitions.** `NuTrans N K` wraps a `Reference.Trans N` with an optional match
  specification. It is a separate type: `Reference.Trans` keeps no match, so every CORE and IO
  block over `Reference.Trans` stays true of its reference (ruling D30, nu.md section 0). The key
  type `K` is abstract, so the build checks and the composition rewrites see only places; the
  firing instantiates `K := KeyFn V Nm`.
* **Selection** ([NU-022]). `MatchIn` is what the selection reads; `eligible`, `oldest`,
  `selKey`, `Selected` and the reference selection `refSelect` (a registered witness). Ruling D31
  (a): the stamp that orders a name is the earliest `createdAt` over every token of the name in
  the correlated inputs, consumed by the firing or not, and the name order is a parameter
  (`[LinearOrder Nm]`).
* **Firing equations.** `corrTake` (the correlated take), `nuInputs`, `nuPost`, `nuConsume`,
  `nuDelivered` and the relay check `RelayOk`: the name-filtered counterparts of RefQFire's
  `qTake`, `qInputs`, `qPostInput`, `qConsume` and `qDelivered`. On a place without a key they are
  RefQFire's.
* **Agreement predicates** for the consistency theorem: `NuRestrictsTo` (without a match a ν
  firing is a queue firing), `NuSelectsBy` (the chosen name is the selection's answer),
  `NuCovers` (every enabled matched transition with an offered outcome under the selected name
  fires) and `NuBuildExtends` (the ν builder is the plain builder until the plain builder accepts).

The reference ν firing `RefNuFire`, the builders `refNuBuild` and `refMatchBuild`, and the
definition record `NuDef` are in `Reference/Nu.lean`. Every statement over names takes
`[LinearOrder Nm]` and never `[DecidableEq Nm]` beside it, so one decidable equality is in play.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Tokens, names and match specifications -/

/-- A token with its creation stamp: the value and `createdAt`, an integer count of the
implementation's unit since the start of the epoch ([CORE-011]). The stamp is what the
[NU-020] tie-break reads; a forwarded token keeps its stamp ([IO-014]). -/
structure Stamped (V : Type) where
  /-- The token's value. -/
  val : V
  /-- The token's `createdAt`. -/
  stamp : Int
  deriving DecidableEq, Repr

/-- Glossary: *Key projection* (spec/glossary.md). -/
abbrev KeyFn (V Nm : Type) := V → Option Nm

/-- Glossary: *Match specification* (spec/glossary.md).

The key type `K` is abstract (`KeyFn V Nm` at firing), so a rewrite that maps places maps the
`N` component of keys and relays and keeps `K`. -/
structure MatchSpec (N K : Type) where
  /-- The correlated inputs with their keys, in declaration order. -/
  keys   : List (N × K)
  /-- The relay targets with their projections ([NU-054]), in declaration order. -/
  relays : List (N × K) := []

/-- A transition that may carry a match specification: a `Reference.Trans` and the match
(`none`: no match). A separate type, so `Reference.Trans` keeps no match. -/
structure NuTrans (N K : Type) where
  /-- The transition without its match: arcs, output spec, reapable bit. -/
  base  : Trans N
  /-- The match specification; `none` = no match. -/
  mspec : Option (MatchSpec N K) := none

variable {N K V Nm : Type}

/-! ## Build-time terms -/

/-- The places a match specification keys, in declaration order. -/
def MatchSpec.keyPlaces (ms : MatchSpec N K) : List N := ms.keys.map Prod.fst

/-- The relay target places, in declaration order. -/
def MatchSpec.relayPlaces (ms : MatchSpec N K) : List N := ms.relays.map Prod.fst

/-- The match keys each place at most once ([NU-020]). -/
def KeysDistinct (ms : MatchSpec N K) : Prop := ms.keyPlaces.Nodup

/-- Every place the match keys is an input place of the transition ([NU-020]). -/
def KeysOnInputs (t : NuTrans N K) (ms : MatchSpec N K) : Prop :=
  ∀ p ∈ ms.keyPlaces, p ∈ inPlaces t.base

/-- The relay targets are declared once each and each is an output place of the transition, in
some output branch ([NU-054] AC1). -/
def RelaysOK (t : NuTrans N K) (ms : MatchSpec N K) : Prop :=
  ms.relayPlaces.Nodup ∧ ∀ p ∈ ms.relayPlaces, OutputArc t.base p

/-- **A ν transition builds**: the transition builds without its match (glossary: Builds), and
its match, if any, keys distinct input places and declares its relay targets once each as output
places. The glossary entry Build-time checks lists these checks after the others. -/
def NuBuilds [DecidableEq N] (t : NuTrans N K) : Prop :=
  Builds t.base ∧ ∀ ms, t.mspec = some ms → KeysDistinct ms ∧ KeysOnInputs t ms ∧ RelaysOK t ms

section DecBuild
variable [DecidableEq N]

instance (ms : MatchSpec N K) : Decidable (KeysDistinct ms) :=
  inferInstanceAs (Decidable ms.keyPlaces.Nodup)

instance (t : NuTrans N K) (ms : MatchSpec N K) : Decidable (KeysOnInputs t ms) := by
  unfold KeysOnInputs; infer_instance

instance (t : NuTrans N K) (ms : MatchSpec N K) : Decidable (RelaysOK t ms) := by
  unfold RelaysOK; infer_instance

instance (t : NuTrans N K) : Decidable (NuBuilds t) :=
  match h : t.mspec with
  | none => decidable_of_iff (Builds t.base) (by simp [NuBuilds, h])
  | some ms => decidable_of_iff (Builds t.base ∧ KeysDistinct ms ∧ KeysOnInputs t ms ∧
      RelaysOK t ms) (by simp [NuBuilds, h])

end DecBuild

/-! ## Names and queues -/

/-- The tokens of `l` whose key `f` gives the name `n`, in queue order. -/
def named [DecidableEq Nm] (f : KeyFn V Nm) (n : Nm) (l : List (Stamped V)) : List (Stamped V) :=
  l.filter fun x => decide (f x.val = some n)

/-- `l` without its first `k` tokens of name `n`; every other token keeps its order. -/
def dropNamed [DecidableEq Nm] (f : KeyFn V Nm) (n : Nm) :
    Nat → List (Stamped V) → List (Stamped V)
  | 0, l => l
  | _, [] => []
  | k + 1, x :: xs => if f x.val = some n then dropNamed f n k xs else x :: dropNamed f n (k + 1) xs

/-- The key of correlated input `p`: the first key on `p` (a transition that builds keys `p`
at most once). `none`: `p` is not a correlated input. -/
def keyAt [DecidableEq N] (ms : MatchSpec N K) (p : N) : Option K :=
  (ms.keys.find? fun k => decide (k.1 = p)).map Prod.snd

/-- The required count of the input arc on `p` ([IO-007]); 1 without an arc. -/
def reqAt [DecidableEq N] (t : Trans N) (p : N) : Nat :=
  match nspecAt t.core p with
  | some s => s.card.required
  | none => 1

/-! ## Selection ([NU-022]) -/

/-- **What the selection reads** for one matched transition: per correlated input, in key
order, the `(name, createdAt)` of every token that has a name on that input, in queue order, and
the input's required count. -/
structure MatchIn (Nm : Type) where
  /-- Per correlated input: its named tokens' `(name, stamp)` in queue order, and its required
  count. -/
  keys : List (List (Nm × Int) × Nat)

/-- A selection function: what a matched transition joins on, `none` for no name. -/
abbrev MatchSelect (Nm : Type) := MatchIn Nm → Option Nm

/-- The stamps of the tokens of name `n` in one correlated input, in queue order. -/
def stamps [DecidableEq Nm] (q : List (Nm × Int)) (n : Nm) : List Int :=
  (q.filter fun x => decide (x.1 = n)).map Prod.snd

/-- **Eligible** ([NU-020] enablement, [NU-022]): the match has at least one key, and every
correlated input holds at least one token of name `n` and at least its required count of them. -/
def eligible [DecidableEq Nm] (I : MatchIn Nm) (n : Nm) : Bool :=
  !I.keys.isEmpty && I.keys.all fun k =>
    decide (1 ≤ (stamps k.1 n).length) && decide (k.2 ≤ (stamps k.1 n).length)

/-- The stamp that orders name `n` (ruling D31 (a)): the earliest `createdAt` over every token of
the name in every correlated input, consumed by the firing or not; `⊤` for a name with no token. -/
def oldest [DecidableEq Nm] (I : MatchIn Nm) (n : Nm) : WithTop Int :=
  (I.keys.flatMap fun k => stamps k.1 n).minimum

section Select
variable [LinearOrder Nm]

/-- The selection key: the earliest stamp of the name, then the name order ([NU-001]). -/
def selKey (I : MatchIn Nm) (n : Nm) : Lex (WithTop Int × Nm) := toLex (oldest I n, n)

/-- Glossary: *Chosen name* (spec/glossary.md).

`Selected I n`: `n` is eligible and least by `selKey` among the eligible names. At most one name
is `Selected` (`selected_unique`). -/
def Selected (I : MatchIn Nm) (n : Nm) : Prop :=
  eligible I n = true ∧ ∀ m, eligible I m = true → selKey I n ≤ selKey I m

/-- The candidate names: the names of the first correlated input that are eligible. -/
def cands (I : MatchIn Nm) : List Nm :=
  (((I.keys.head?.map Prod.fst).getD []).map Prod.fst).filter (eligible I)

/-- **The reference selection** ([NU-022], `select_match_name`): the eligible name least by
(earliest stamp, name). -/
def refSelect : MatchSelect Nm := fun I => (cands I).argmin (selKey I)

end Select

/- The reference selection is the witness model of NU-022's `holds` theorem. -/
#spec_witness refSelect

section SelectFacts
variable [LinearOrder Nm]

/-- A name is a candidate exactly when it is eligible: an eligible name has a token in the
first correlated input. -/
theorem mem_cands {I : MatchIn Nm} {n : Nm} : n ∈ cands I ↔ eligible I n = true := by
  constructor
  · intro h; exact (List.mem_filter.1 h).2
  · intro h
    refine List.mem_filter.2 ⟨?_, h⟩
    have h' := h
    unfold eligible at h'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at h'
    obtain ⟨hne, hall⟩ := h'
    cases hk : I.keys with
    | nil => simp [hk] at hne
    | cons k ks =>
      have := (hall k (by simp [hk])).1
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      have hpos : 0 < (stamps k.1 n).length := this
      obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
      unfold stamps at hx
      obtain ⟨y, hy, -⟩ := List.mem_map.1 hx
      have hy' := List.mem_filter.1 hy
      exact List.mem_map.2 ⟨y, hy'.1, by simpa using hy'.2⟩

/-- The reference selection returns exactly the `Selected` name, and returns one whenever a name
is eligible. -/
theorem refSelect_spec (I : MatchIn Nm) :
    (∀ n, refSelect I = some n → Selected I n) ∧
      ((∃ n, eligible I n = true) → (refSelect I).isSome = true) := by
  refine ⟨fun n hn => ?_, fun ⟨n, hn⟩ => ?_⟩
  · have hmem : n ∈ cands I := List.argmin_mem (by simpa [refSelect] using hn)
    exact ⟨mem_cands.1 hmem, fun m hm =>
      List.le_of_mem_argmin (mem_cands.2 hm) (by simpa [refSelect] using hn)⟩
  · cases h : refSelect I with
    | some _ => rfl
    | none =>
      have h' : (cands I).argmin (selKey I) = none := h
      have hnil : cands I = [] := List.argmin_eq_none.1 h'
      have hmem := mem_cands.2 hn
      rw [hnil] at hmem
      exact absurd hmem List.not_mem_nil

/-- At most one name is `Selected`: two selected names have equal keys, so equal names. -/
theorem selected_unique {I : MatchIn Nm} {n m : Nm} (hn : Selected I n) (hm : Selected I m) :
    n = m := by
  have := le_antisymm (hn.2 m hm.1) (hm.2 n hn.1)
  have h2 : (oldest I n, n) = (oldest I m, m) := toLex.injective this
  exact (Prod.ext_iff.1 h2).2

/-- The reference selection returns `n` exactly when `n` is `Selected`. -/
theorem refSelect_eq_some_iff {I : MatchIn Nm} {n : Nm} : refSelect I = some n ↔ Selected I n := by
  constructor
  · exact (refSelect_spec I).1 n
  · intro hs
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 ((refSelect_spec I).2 ⟨n, hs.1⟩)
    rw [hm, selected_unique ((refSelect_spec I).1 m hm) hs]

end SelectFacts

/-! ## Reading the selection input off a queue marking -/

/-- `MatchIn.ofMarking`: per correlated input `(p, f)` of the match, the `(name, stamp)` of every
token of `M p` that has a name under `f`, in queue order, and the required count of the arc on
`p`. -/
def matchIn [DecidableEq N] (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) : MatchIn Nm :=
  ⟨ms.keys.map fun k =>
    ((M k.1).filterMap fun x => (k.2 x.val).map fun n => (n, x.stamp), reqAt t.base k.1)⟩

/-! ## The firing equations -/

section Fire
variable [DecidableEq N] [DecidableEq Nm]

/-- Glossary: *Correlated take* (spec/glossary.md).

`corrTake ms t M n p`: how many tokens the firing takes from `p` for the chosen name `n`: on a
correlated input, the consumption count over the tokens of `n` (0 without an input arc); on any
other place, RefQFire's `qTake`. -/
def corrTake (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) (n : Nm) (p : N) : Nat :=
  match keyAt ms p with
  | some f => match nspecAt t.base.core p with
    | some s => consumptionCount s.card (named f n (M p)).length
    | none => 0
  | none => qTake M t.base p

/-- The tokens the firing delivers from each input place for chosen name `n`: on a correlated
input the first `corrTake` tokens of `n`, in queue order; elsewhere RefQFire's `qInputs`. -/
def nuInputs (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) (n : Nm) : N → List (Stamped V) := fun p =>
  match keyAt ms p with
  | some f => (named f n (M p)).take (corrTake ms t M n p)
  | none => qInputs M t.base p

/-- The queue marking after the inputs are taken: on a correlated input the queue without the
taken tokens of `n`, every other token in its order; elsewhere RefQFire's `qPostInput`. -/
def nuPost (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) (n : Nm) : QMarking N (Stamped V) := fun p =>
  match keyAt ms p with
  | some f => dropNamed f n (corrTake ms t M n p) (M p)
  | none => qPostInput M t.base p

/-- The queue marking after the whole consume: inputs taken, then reset places drained
([CORE-034]). -/
def nuConsume (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) (n : Nm) : QMarking N (Stamped V) := fun p =>
  if p ∈ t.base.core.resets then [] else nuPost ms t M n p

/-- What a matched firing delivers to its action: the taken input tokens, and per read arc the
head of its place after the inputs are taken ([EXEC-012]). -/
def nuDelivered (ms : MatchSpec N (KeyFn V Nm)) (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) (n : Nm) : QDelivered N (Stamped V) :=
  ⟨nuInputs ms t M n, qReadsBag (nuPost ms t M n) t.base.core.reads⟩

/-- Glossary: *Relay target* (spec/glossary.md).

`RelayOk ms n e`: every token the emission `e` puts on a relay target projects to `n` under that
target's projection. -/
def RelayOk (ms : MatchSpec N (KeyFn V Nm)) (n : Nm) (e : List (N × Stamped V)) : Prop :=
  ∀ r ∈ ms.relays, ∀ x ∈ qEmittedTo e r.1, r.2 x.val = some n

end Fire

/-! ## ν firing relations and enablement -/

/-- A ν firing relation: `R t M c δ e M'` says that `t` fires from the queue marking `M` with
chosen name `c` (`none` without a match), delivers `δ` to its action, `e` is every token the
firing deposits, from the action or the timeout outcome (places and tokens, in emission order),
and the firing leaves `M'`. -/
abbrev NuFireRel (N V Nm : Type) :=
  NuTrans N (KeyFn V Nm) → QMarking N (Stamped V) → Option Nm → QDelivered N (Stamped V) →
    List (N × Stamped V) → QMarking N (Stamped V) → Prop

/-- **ν enablement** ([NU-020]): enabled on the token counts ([CORE-022]) and, for a matched
transition, some name eligible. -/
def NuEnabled [DecidableEq N] [DecidableEq Nm] (t : NuTrans N (KeyFn V Nm))
    (M : QMarking N (Stamped V)) : Prop :=
  Enabled t.base (qCount M) ∧ ∀ ms, t.mspec = some ms → ∃ n, eligible (matchIn ms t M) n = true

/-! ## Agreement predicates of the consistency theorem -/

/-- **Without a match a ν firing is a queue firing**: for every transition without a match,
`NF` fires exactly when `QF` fires its base, with no chosen name. Through `QProjectsTo` and
`QCovers` every queue and count block then speaks of the match-free ν firings. -/
def NuRestrictsTo (NF : NuFireRel N V Nm) (QF : QFireRel N (Stamped V)) : Prop :=
  ∀ t : NuTrans N (KeyFn V Nm), t.mspec = none →
    ∀ M c δ e M', NF t M c δ e M' ↔ c = none ∧ QF t.base M δ e M'

/-- **The chosen name is the selection's answer**: every matched firing of `NF` chooses the name
`S` returns on the selection input read off the marking. -/
def NuSelectsBy [DecidableEq N] (NF : NuFireRel N V Nm) (S : MatchSelect Nm) : Prop :=
  ∀ (t : NuTrans N (KeyFn V Nm)) ms, t.mspec = some ms →
    ∀ M c δ e M', NF t M c δ e M' → c = S (matchIn ms t M)

/-- **Every enabled matched transition fires** (the anti-vacuity conjunct, under the selected
name, nu.md S8): from every marking at which a matched transition is enabled on the counts, with
`n` the `Selected` name, every emission whose places an output branch or timeout outcome offers
under the correlated takes of `n`, and which passes the relay check, is the emission of some
firing that chooses `n`. Without it the relation that never fires satisfies every ν line. The
timeout outcome is offered as ruling D24 (a) reads it, so a timeout whose output spec puts the
timeout under an `And`, such as `And(A, Timeout(d, B))`, deposits `B`; an executor that validates
the timeout outcome against the whole output spec (the Java and TypeScript behaviour RD-01
recorded) does not meet that offer. -/
def NuCovers [DecidableEq N] [LinearOrder Nm] (NF : NuFireRel N V Nm) : Prop :=
  ∀ (t : NuTrans N (KeyFn V Nm)) ms, t.mspec = some ms → ∀ M n, Selected (matchIn ms t M) n →
    Enabled t.base (qCount M) → ∀ e : List (N × Stamped V),
      (∃ ch, deposit (corrTake ms t M n) t.base.out ch = some (e.map Prod.fst)) →
      RelayOk ms n e → ∃ δ M', NF t M (some n) δ e M'

/-- **The ν builder extends the plain builder**: on a transition without a match, and on a
transition the plain builder rejects, the ν builder answers what the plain builder answers, so
the match checks run after every other build-time check and add no message of their own before
them. -/
def NuBuildExtends (NB : NuTrans N K → Option String) (Build : Trans N → Option String) : Prop :=
  ∀ t : NuTrans N K, (Build t.base ≠ none ∨ t.mspec = none) → NB t = Build t.base

/-! ## Readable facts -/

/-- On a correlated input `named` keeps exactly the tokens of the name, in order. -/
theorem named_sublist [DecidableEq Nm] (f : KeyFn V Nm) (n : Nm) (l : List (Stamped V)) :
    (named f n l).Sublist l := List.filter_sublist

/-- `dropNamed` keeps every token that is not of the name, in order. -/
theorem dropNamed_filter_other [DecidableEq Nm] (f : KeyFn V Nm) (n : Nm) :
    ∀ (k : Nat) (l : List (Stamped V)),
      (dropNamed f n k l).filter (fun x => !decide (f x.val = some n)) =
        l.filter (fun x => !decide (f x.val = some n))
  | 0, l => by simp [dropNamed]
  | _ + 1, [] => by simp [dropNamed]
  | k + 1, x :: xs => by
    by_cases h : f x.val = some n
    · simp [dropNamed, h, dropNamed_filter_other f n k xs]
    · simp [dropNamed, h, dropNamed_filter_other f n (k + 1) xs]

/-- `dropNamed` removes exactly the first `k` tokens of the name: the tokens of the name it keeps
are those after them. -/
theorem dropNamed_named [DecidableEq Nm] (f : KeyFn V Nm) (n : Nm) :
    ∀ (k : Nat) (l : List (Stamped V)), named f n (dropNamed f n k l) = (named f n l).drop k
  | 0, l => by simp [dropNamed]
  | _ + 1, [] => by simp [dropNamed, named]
  | k + 1, x :: xs => by
    by_cases h : f x.val = some n
    · have ih := dropNamed_named f n k xs
      simp only [named] at ih
      simp [dropNamed, h, named, ih]
    · have ih := dropNamed_named f n (k + 1) xs
      simp only [named] at ih
      simp [dropNamed, h, named, ih]

end Libpetri.Spec
