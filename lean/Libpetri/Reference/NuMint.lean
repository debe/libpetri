import Libpetri.Spec.Registry
import Libpetri.Novel.RouteB.Exec

set_option linter.missingDocs true

/-!
# RefMint: minting fresh names ([NU-010], [NU-011])

The mint layer of the ν reference. It has no firing semantics: the minter is per executor and is
keyed on the order of the `freshName()` calls, not on the order of firings (ruling D56 (a)), so it
needs no executor model.

* **Names.** `mintName t s n` is `<t>#<s>:<n>` ([NU-011]): transition name, scope, counter in
  decimal. `refValidScope` is the scope check made when the executor is configured: not empty,
  no `:` and no `#` (a whitespace-only scope is accepted). `mintName_inj` is the parse rule: with
  `#` banned from the scope, a name splits back into transition, scope and counter whatever the
  transition name holds. `mintName_collision` is the spec's own example of why `:` alone is not
  enough.
* **Minting systems.** `MintSys` is an abstract minter: a state type, an initial state per scope,
  a mint relation (state, transition name, minted name, next state) and a firing-boundary step.
  A run (`MintRun`) interleaves `call t` and `boundary` events, so "two calls in one firing" and
  "a counter reset per firing" are both observable (nu.md skeptic correction S2). The state type
  is abstract, so a high-water-mark minter is a `MintSys` too.
* **The reference.** `refMintSys` (a registered witness): the state is the scope and one counter
  per executor, shared by all transitions; a call mints `mintName t scope counter` and advances
  the counter; a firing boundary changes nothing. This is `fresh_name_fn` in
  `rust/libpetri-runtime/src/executor_core/executor.rs:203-221` (one `fresh_name_counter` per
  executor, starting at 0, read with `fetch_add`), and the same in Java and TypeScript.
* **Lemmas for the blocks.** Uniqueness (`refRun_nodup`), the n-th name (`refRun_names`),
  determinism (`refMintSys_functional`, `mintRun_det`), totality (`refMintSys_total`,
  `refRun_exists`), and disjointness across scopes (`refRun_disjoint`, `refRun_fresh`).
* **The mint contract** (ruling D78 (a)): a declared mint writes ONE fresh name, the same in every
  coloured place it writes (`MintContract`). `EachFresh` is the per-place reading the ruling set
  aside; `eachFresh_not_mintContract` shows the two differ. `mintContract_iff_routeB` ties
  `MintContract` to `Novel.RouteB.Contract` at `Role.mint`, the premise the Route B soundness
  theorems use.

Not modelled: the default scope (32 lowercase hexadecimal characters, at least 122 random bits) is
a statistical claim and stays with the tests; the fallback minter used without an executor, and
how a bad scope is rejected (exception or panic), differ per language.
-/

namespace Libpetri.Reference

/-! ## Names and scopes -/

/-- The name an executor mints: `<t>#<s>:<n>`, the transition name `t`, the scope `s` and the
counter `n` in decimal ([NU-011]). For example `mintName "fork" "s" 2 = "fork#s:2"`. -/
def mintName (t s : String) (n : Nat) : String := t ++ "#" ++ s ++ ":" ++ Nat.repr n

/-- A scope check: which host-supplied scopes the executor accepts when it is configured. -/
abbrev ScopeCheck := String → Bool

/-- The reference scope check ([NU-011]): a scope is accepted when it is not empty (length zero)
and holds neither `:` nor `#`. A whitespace-only scope is accepted; nothing is trimmed. This is
`validate_execution_scope` in `rust/libpetri-runtime/src/executor_core/scope.rs:63-70`. -/
def refValidScope : ScopeCheck := fun s =>
  decide (s ≠ "") && decide (':' ∉ s.toList) && decide ('#' ∉ s.toList)

#spec_witness refValidScope

/-- The reference scope check accepts exactly the scopes that are not empty and hold neither
`:` nor `#`. -/
theorem refValidScope_iff (s : String) :
    refValidScope s = true ↔ s ≠ "" ∧ ':' ∉ s.toList ∧ '#' ∉ s.toList := by
  simp [refValidScope, and_assoc]

/-- A scope the reference accepts holds no `#`. -/
theorem refValidScope_noHash {s : String} (h : refValidScope s = true) : '#' ∉ s.toList :=
  ((refValidScope_iff s).mp h).2.2

/-- Example: a blank scope `" "` is accepted, while `""`, `"a:b"` and `"a#b"` are refused. -/
theorem refValidScope_examples :
    refValidScope " " = true ∧ refValidScope "" = false ∧ refValidScope "a:b" = false ∧
      refValidScope "a#b" = false := by
  decide

/-- The characters of a minted name. -/
theorem mintName_toList (t s : String) (n : Nat) :
    (mintName t s n).toList = t.toList ++ '#' :: (s.toList ++ ':' :: (Nat.repr n).toList) := by
  simp [mintName, String.toList_append, List.append_assoc]

/-- Splitting a list at the FIRST occurrence of `c` is unique. -/
theorem mint_split_first {α : Type} {c : α} : ∀ {x x' y y' : List α}, c ∉ x → c ∉ x' →
    x ++ c :: y = x' ++ c :: y' → x = x' ∧ y = y'
  | [], [], _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], b :: x', _, _, _, hx', h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx'
  | a :: x, [], _, _, hx, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx
  | a :: x, b :: x', _, _, hx, hx', h => by
      simp only [List.cons_append, List.cons.injEq] at h
      have := mint_split_first (fun m => hx (List.mem_cons_of_mem _ m))
        (fun m => hx' (List.mem_cons_of_mem _ m)) h.2
      exact ⟨by rw [h.1, this.1], this.2⟩

/-- Splitting a list at the LAST occurrence of `c` is unique. -/
theorem mint_split_last {α : Type} {c : α} {x x' y y' : List α} (hy : c ∉ y) (hy' : c ∉ y')
    (h : x ++ c :: y = x' ++ c :: y') : x = x' ∧ y = y' := by
  have h2 := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    at h2
  have := mint_split_first (by simpa using hy) (by simpa using hy') h2
  exact ⟨List.reverse_injective this.2, List.reverse_injective this.1⟩

/-- The decimal digits of a counter hold only digits. -/
theorem mint_digit_of_mem_repr {n : Nat} {c : Char} (h : c ∈ (Nat.repr n).toList) :
    c.isDigit = true := by
  simp only [Nat.repr, String.toList_ofList] at h
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- The decimal digits of a counter hold no `:`. -/
theorem colon_not_mem_repr (n : Nat) : ':' ∉ (Nat.repr n).toList := by
  intro h; have := mint_digit_of_mem_repr h; revert this; decide

/-- The decimal digits of a counter hold no `#`. -/
theorem hash_not_mem_repr (n : Nat) : '#' ∉ (Nat.repr n).toList := by
  intro h; have := mint_digit_of_mem_repr h; revert this; decide

/-- **The parse rule of [NU-011].** When neither scope holds `#`, two minted names are equal only
if transition, scope and counter are equal, whatever the transition names hold: the last `:`
splits off the counter, and the last `#` before it splits off the scope. -/
theorem mintName_inj {t t' s s' : String} {n n' : Nat} (hs : '#' ∉ s.toList)
    (hs' : '#' ∉ s'.toList) (h : mintName t s n = mintName t' s' n') :
    t = t' ∧ s = s' ∧ n = n' := by
  have hl := congrArg String.toList h
  rw [mintName_toList, mintName_toList] at hl
  have h1 : (t.toList ++ '#' :: s.toList) ++ ':' :: (Nat.repr n).toList =
      (t'.toList ++ '#' :: s'.toList) ++ ':' :: (Nat.repr n').toList := by
    simpa [List.append_assoc] using hl
  obtain ⟨h2, hd⟩ := mint_split_last (colon_not_mem_repr n) (colon_not_mem_repr n') h1
  obtain ⟨ht, hss⟩ := mint_split_last hs hs' h2
  exact ⟨String.toList_inj.mp ht, String.toList_inj.mp hss,
    Nat.repr_inj.mp (String.toList_inj.mp hd)⟩

/-- The counter can be read back from a minted name, whatever the transition name and the scope
hold. So one executor, whose scope is fixed, never mints one name for two counter values. -/
theorem mintName_counter_inj {t t' s s' : String} {n n' : Nat}
    (h : mintName t s n = mintName t' s' n') : n = n' := by
  have hl := congrArg String.toList h
  rw [mintName_toList, mintName_toList] at hl
  have h1 : (t.toList ++ '#' :: s.toList) ++ ':' :: (Nat.repr n).toList =
      (t'.toList ++ '#' :: s'.toList) ++ ':' :: (Nat.repr n').toList := by
    simpa [List.append_assoc] using hl
  exact Nat.repr_inj.mp (String.toList_inj.mp (mint_split_last (colon_not_mem_repr n)
    (colon_not_mem_repr n') h1).2)

/-- The parse rule for two scopes the reference check accepts. -/
theorem mintName_inj_of_valid {t t' s s' : String} {n n' : Nat} (hs : refValidScope s = true)
    (hs' : refValidScope s' = true) (h : mintName t s n = mintName t' s' n') :
    t = t' ∧ s = s' ∧ n = n' :=
  mintName_inj (refValidScope_noHash hs) (refValidScope_noHash hs') h

/-- Names minted under two different scopes, neither holding `#`, are different. -/
theorem mintName_scope_ne {t t' s s' : String} {n n' : Nat} (hs : '#' ∉ s.toList)
    (hs' : '#' ∉ s'.toList) (hne : s ≠ s') : mintName t s n ≠ mintName t' s' n' :=
  fun h => hne (mintName_inj hs hs' h).2.1

/-- Why `#` is banned as well as `:` (the spec's example): transition `a` under scope `b#c`
and transition `a#b` under scope `c` both mint `a#b#c:0`. -/
theorem mintName_collision : mintName "a" "b#c" 0 = mintName "a#b" "c" 0 := by decide

/-- The name `x` was minted under scope `s`: it is `<t>#<s>:<n>` for some transition `t` and
counter `n`. -/
def MintedUnder (s x : String) : Prop := ∃ t n, x = mintName t s n

/-! ## Minting systems and their runs -/

/-- An abstract minter: a state type, the initial state of an executor whose scope is `s`, the
mint relation (`mint st t x st'`: in state `st`, a `freshName()` call by transition `t` returns
`x` and leaves state `st'`), and the step taken at a firing boundary. -/
structure MintSys where
  /-- The minter's state. -/
  St : Type
  /-- The initial state of an executor, given its scope. -/
  init : String → St
  /-- One `freshName()` call: state, calling transition, returned name, next state. -/
  mint : St → String → String → St → Prop
  /-- The step at a firing boundary. -/
  next : St → St

/-- An event a minter sees: a `freshName()` call by a transition, or a firing boundary. -/
inductive MintEv where
  /-- A `freshName()` call by transition `t`. -/
  | call (t : String)
  /-- The boundary between two firings. -/
  | boundary
  deriving DecidableEq, Repr

/-- `MintRun Sy st evs xs`: from state `st`, the events `evs` can return the names `xs`, one per
call, in call order. -/
inductive MintRun (Sy : MintSys) : Sy.St → List MintEv → List String → Prop
  /-- No events, no names. -/
  | nil (s : Sy.St) : MintRun Sy s [] []
  /-- A call returns `x` and the run goes on from the next state. -/
  | call {s s' : Sy.St} {t x : String} {evs : List MintEv} {xs : List String} :
      Sy.mint s t x s' → MintRun Sy s' evs xs → MintRun Sy s (.call t :: evs) (x :: xs)
  /-- A firing boundary returns no name and moves the state by `next`. -/
  | boundary {s : Sy.St} {evs : List MintEv} {xs : List String} :
      MintRun Sy (Sy.next s) evs xs → MintRun Sy s (.boundary :: evs) xs

/-- The transition names of the calls among `evs`, in order. -/
def calls : List MintEv → List String
  | [] => []
  | .call t :: evs => t :: calls evs
  | .boundary :: evs => calls evs

/-- The mint relation is a function: one state and one calling transition give one name and one
next state. -/
def MintFunctional (Sy : MintSys) : Prop :=
  ∀ st t x st' x' st'', Sy.mint st t x st' → Sy.mint st t x' st'' → x = x' ∧ st' = st''

/-- Every call can be answered: from every state, every transition gets some name. -/
def MintTotal (Sy : MintSys) : Prop := ∀ st t, ∃ x st', Sy.mint st t x st'

/-- For a functional minter, one start state and one event sequence give one name sequence. -/
theorem mintRun_det {Sy : MintSys} (hf : MintFunctional Sy) {st : Sy.St} {evs : List MintEv}
    {xs ys : List String} (h : MintRun Sy st evs xs) (h' : MintRun Sy st evs ys) : xs = ys := by
  induction h generalizing ys with
  | nil => cases h'; rfl
  | call hm _ ih =>
    cases h' with
    | call hm' hr' =>
      obtain ⟨rfl, rfl⟩ := hf _ _ _ _ _ _ hm hm'
      rw [ih hr']
  | boundary _ ih => cases h' with | boundary hr' => exact ih hr'

/-- For a total minter, every event sequence has a run. -/
theorem mintRun_total {Sy : MintSys} (ht : MintTotal Sy) :
    ∀ (st : Sy.St) (evs : List MintEv), ∃ xs, MintRun Sy st evs xs
  | st, [] => ⟨[], .nil st⟩
  | st, .call t :: evs => by
    obtain ⟨x, st', hm⟩ := ht st t
    obtain ⟨xs, hr⟩ := mintRun_total ht st' evs
    exact ⟨x :: xs, .call hm hr⟩
  | st, .boundary :: evs => by
    obtain ⟨xs, hr⟩ := mintRun_total ht (Sy.next st) evs
    exact ⟨xs, .boundary hr⟩

/-! ## The reference minter -/

/-- The reference minter's state: the executor's scope and its one counter. -/
structure MintSt where
  /-- The executor's scope (pinned by the host, or the default drawn once). -/
  scope : String
  /-- The counter, shared by every transition of the executor. -/
  ctr : Nat
  deriving DecidableEq, Repr

/-- One reference mint: render the name with the current counter, then advance the counter. -/
def refMint (st : MintSt) (t : String) : String × MintSt :=
  (mintName t st.scope st.ctr, { st with ctr := st.ctr + 1 })

/-- The names the reference minter returns, from state `st`, to calls by the transitions `ts`. -/
def mintSeq : MintSt → List String → List String
  | _, [] => []
  | st, t :: ts => (refMint st t).1 :: mintSeq (refMint st t).2 ts

/-- **The reference minting system.** An executor whose scope is `s` starts with counter 0; a
call by transition `t` returns `<t>#<s>:<counter>` and advances the counter; a firing boundary
changes nothing. -/
def refMintSys : MintSys where
  St := MintSt
  init s := ⟨s, 0⟩
  mint st t x st' := x = (refMint st t).1 ∧ st' = (refMint st t).2
  next := id

#spec_witness refMintSys

/-- Example: three calls under scope `s` return `fork#s:0`, `fork#s:1`, `split#s:2`. -/
theorem mintSeq_example :
    mintSeq ⟨"s", 0⟩ ["fork", "fork", "split"] = ["fork#s:0", "fork#s:1", "split#s:2"] := by
  decide

/-- The reference minter is a function of its state and the calling transition. -/
theorem refMintSys_functional : MintFunctional refMintSys := by
  rintro st t x st' x' st'' ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-- The reference minter answers every call. -/
theorem refMintSys_total : MintTotal refMintSys :=
  fun st t => ⟨(refMint st t).1, (refMint st t).2, rfl, rfl⟩

/-- The reference minter's names, written out: the `i`-th call (from 0) by transition `t`
returns `<t>#<scope>:<counter + i>`. -/
theorem mintSeq_eq_mapIdx : ∀ (st : MintSt) (ts : List String),
    mintSeq st ts = ts.mapIdx fun i t => mintName t st.scope (st.ctr + i)
  | _, [] => by simp [mintSeq]
  | st, t :: ts => by
    rw [mintSeq, mintSeq_eq_mapIdx, List.mapIdx_cons]
    simp only [refMint, Nat.add_zero, List.cons.injEq, true_and]
    congr 1
    funext i u
    rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- One name per call. -/
theorem mintSeq_length (st : MintSt) (ts : List String) : (mintSeq st ts).length = ts.length := by
  rw [mintSeq_eq_mapIdx, List.length_mapIdx]

/-- Every name the reference minter returns carries the state's scope and a counter at or above
the state's counter. -/
theorem mintSeq_counters : ∀ (st : MintSt) (ts : List String),
    ∀ x ∈ mintSeq st ts, ∃ t n, st.ctr ≤ n ∧ x = mintName t st.scope n
  | _, [] => by simp [mintSeq]
  | st, t :: ts => by
    intro x hx
    simp only [mintSeq, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨t, st.ctr, Nat.le_refl _, rfl⟩
    · obtain ⟨t', n, hn, rfl⟩ := mintSeq_counters _ ts x hx
      exact ⟨t', n, by simp [refMint] at hn; omega, rfl⟩

/-- The reference minter's names are pairwise distinct, whatever the transition names and the
scope hold. -/
theorem mintSeq_nodup : ∀ (st : MintSt) (ts : List String), (mintSeq st ts).Nodup
  | _, [] => by simp [mintSeq]
  | st, t :: ts => by
    simp only [mintSeq, List.nodup_cons]
    refine ⟨fun hmem => ?_, mintSeq_nodup _ ts⟩
    obtain ⟨t', n, hn, he⟩ := mintSeq_counters _ ts _ hmem
    have := mintName_counter_inj he
    simp [refMint] at hn this
    omega

/-- A run of the reference minter returns exactly `mintSeq` of its calls: firing boundaries do
not matter. -/
theorem refRun_eq {st : refMintSys.St} {evs : List MintEv} {xs : List String}
    (h : MintRun refMintSys st evs xs) : xs = mintSeq st (calls evs) := by
  induction h with
  | nil => rfl
  | call hm _ ih => obtain ⟨rfl, rfl⟩ := hm; simp [calls, mintSeq, ih]
  | boundary _ ih => simpa [calls, refMintSys] using ih

/-- Every event sequence has a reference run, the one returning `mintSeq` of its calls. -/
theorem refRun_exists : ∀ (st : MintSt) (evs : List MintEv),
    MintRun refMintSys st evs (mintSeq st (calls evs))
  | st, [] => (MintRun.nil (Sy := refMintSys) st : MintRun refMintSys st [] [])
  | st, .call t :: evs => .call (s' := (refMint st t).2) ⟨rfl, rfl⟩ (refRun_exists _ evs)
  | st, .boundary :: evs => .boundary (refRun_exists (refMintSys.next st) evs)

/-- The reference runs are exactly the `mintSeq` of their calls. -/
theorem refRun_iff {st : MintSt} {evs : List MintEv} {xs : List String} :
    MintRun refMintSys st evs xs ↔ xs = mintSeq st (calls evs) :=
  ⟨refRun_eq, fun h => h ▸ refRun_exists st evs⟩

/-- **The n-th name.** In a reference run of an executor whose scope is `s`, the `i`-th call
(counting from 0, across firings) by transition `t` returns `<t>#<s>:<i>`. -/
theorem refRun_names {s : String} {evs : List MintEv} {xs : List String}
    (h : MintRun refMintSys (refMintSys.init s) evs xs) :
    xs = (calls evs).mapIdx fun i t => mintName t s i := by
  rw [refRun_eq h, mintSeq_eq_mapIdx]
  simp [refMintSys]

/-- **Uniqueness.** A reference run returns pairwise distinct names, two calls in one firing
included. -/
theorem refRun_nodup {st : MintSt} {evs : List MintEv} {xs : List String}
    (h : MintRun refMintSys st evs xs) : xs.Nodup := by
  rw [refRun_eq h]; exact mintSeq_nodup _ _

/-- Every name of a reference run from scope `s` was minted under `s`. -/
theorem refRun_mintedUnder {s : String} {evs : List MintEv} {xs : List String}
    (h : MintRun refMintSys (refMintSys.init s) evs xs) : ∀ x ∈ xs, MintedUnder s x := by
  intro x hx
  rw [refRun_eq h] at hx
  obtain ⟨t, n, -, rfl⟩ := mintSeq_counters _ _ x hx
  exact ⟨t, n, rfl⟩

/-- A name minted under scope `s` is not minted under another scope `s'`, when neither holds
`#`. -/
theorem mintedUnder_unique {s s' x : String} (hs : '#' ∉ s.toList) (hs' : '#' ∉ s'.toList)
    (h : MintedUnder s x) (h' : MintedUnder s' x) : s = s' := by
  obtain ⟨t, n, rfl⟩ := h
  obtain ⟨t', n', he⟩ := h'
  exact (mintName_inj hs hs' he).2.1

/-- **Different scopes, disjoint names.** Two reference runs from two different scopes, neither
holding `#`, share no name, whatever their calls. -/
theorem refRun_disjoint {s s' : String} {evs evs' : List MintEv} {xs xs' : List String}
    (hs : '#' ∉ s.toList) (hs' : '#' ∉ s'.toList) (hne : s ≠ s')
    (h : MintRun refMintSys (refMintSys.init s) evs xs)
    (h' : MintRun refMintSys (refMintSys.init s') evs' xs') : ∀ x ∈ xs, x ∉ xs' :=
  fun x hx hx' => hne (mintedUnder_unique hs hs' (refRun_mintedUnder h x hx)
    (refRun_mintedUnder h' x hx'))

/-- **Freshness of the next name.** Take a reference run from scope `s` (no `#`) whose last call
returns `x`. If every name held somewhere was returned earlier in this run, or was minted under
another scope that holds no `#` (an earlier executor of the restore lineage), then `x` is held
nowhere. -/
theorem refRun_fresh {s x : String} {evs : List MintEv} {xs : List String}
    {held : String → Prop} (hs : '#' ∉ s.toList)
    (h : MintRun refMintSys (refMintSys.init s) evs (xs ++ [x]))
    (hheld : ∀ y, held y → y ∈ xs ∨ ∃ s', '#' ∉ s'.toList ∧ s' ≠ s ∧ MintedUnder s' y) :
    ¬ held x := by
  intro hx
  have hnd := refRun_nodup h
  have hxs : x ∉ xs := by
    intro hm
    rw [List.nodup_append] at hnd
    exact hnd.2.2 x hm x (List.mem_singleton_self x) rfl
  rcases hheld x hx with hm | ⟨s', hs', hne, hu⟩
  · exact hxs hm
  · exact hne (mintedUnder_unique hs' hs hu
      (refRun_mintedUnder h x (List.mem_append_right _ (List.mem_singleton_self x))))

/-! ## The mint contract ([NU-010], ruling D78 (a)) -/

section Contract

variable {C Nm : Type}

/-- **The mint contract.** A declared mint writes one name `f` into every coloured place it
writes (`wr c` is what it writes to coloured place `c`), and no coloured place holds `f` before
the firing (`holds c f` is false for every `c`). -/
def MintContract (holds : C → Nm → Prop) (wr : C → List Nm) : Prop :=
  ∃ f, (∀ c, ¬ holds c f) ∧ ∀ c, ∀ w ∈ wr c, w = f

/-- The per-place reading ruling D78 set aside: every written name is fresh, but two coloured
places may get two different fresh names. -/
def EachFresh (holds : C → Nm → Prop) (wr : C → List Nm) : Prop :=
  ∀ c, ∀ w ∈ wr c, ∀ c', ¬ holds c' w

/-- The contract implies the per-place reading. -/
theorem mintContract_eachFresh {holds : C → Nm → Prop} {wr : C → List Nm}
    (h : MintContract holds wr) : EachFresh holds wr := by
  obtain ⟨f, hf, hw⟩ := h
  intro c w hw' c'
  rw [hw c w hw']
  exact hf c'

/-- The per-place reading is weaker: writing fresh name 1 into place `A` and fresh name 2 into
place `B` meets it, but not the contract, and a join on `A` and `B` could then never fire. -/
theorem eachFresh_not_mintContract :
    EachFresh (fun (_ : Bool) (_ : Nat) => False) (fun b => if b then [1] else [2]) ∧
      ¬ MintContract (fun (_ : Bool) (_ : Nat) => False) (fun b => if b then [1] else [2]) := by
  refine ⟨fun _ _ _ _ h => h, ?_⟩
  rintro ⟨f, -, hw⟩
  have h1 := hw true 1 (by simp)
  have h2 := hw false 2 (by simp)
  omega

/-- The reference mint action: write the minted name `x` once into every coloured place in
`outs`, nothing elsewhere. -/
def refMintAction (outs : C → Bool) (x : Nm) : C → List Nm :=
  fun c => if outs c then [x] else []

/-- The reference mint action keeps the contract when its minted name is held nowhere. -/
theorem refMintAction_contract {holds : C → Nm → Prop} (outs : C → Bool) {x : Nm}
    (hx : ∀ c, ¬ holds c x) : MintContract holds (refMintAction outs x) := by
  refine ⟨x, hx, fun c w hw => ?_⟩
  unfold refMintAction at hw
  split at hw <;> simp_all

end Contract

/-- **Bridge to Route B.** On Route B's name layer (`M u i` tokens of name `u` at the `i`-th
coloured place), the mint contract is `Novel.RouteB.Contract` at `Role.mint`, the premise of
the Route B soundness theorems. -/
theorem mintContract_iff_routeB (co : List PlaceId) (T : Novel.RouteB.NuTrans)
    (M : Novel.RouteB.NM co) (n : Nat) (hss : List (List Nat))
    (wr : Fin co.length → List Nat) :
    MintContract (fun i u => M u i ≠ 0) wr ↔ Novel.RouteB.Contract co .mint T M n hss wr := by
  simp [MintContract, Novel.RouteB.Contract]

end Libpetri.Reference
