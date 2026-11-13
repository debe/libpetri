import Libpetri.Spec.Registry
import Libpetri.Reference.Snapshot
import Libpetri.Spec.Req.CORE_072

set_option linter.missingDocs true

/-!
# CORE-073: Marking snapshot and restore (`spec/01-core-model.md`)

Two blocks, one per part of the requirement.

**`CORE_073` (kind F)** is a predicate over three abstract functions on the snapshot form
(`QSnap String T`, `Reference/Snapshot.lean`): a snapshot `Snap` of a queue marking given with a
finite list covering its marked places (`FinQ`), a restore `Restore` from the form to a queue
marking, and the seeding `Seed` of an executor from an optional restored marking and an explicit
initial marking. Place names are strings, so the canonical order is `String.lt`, ascending
code-point order. The token type `T` is abstract: an entry is the implementation's own token, its
value and its `created_at` together. Seven lines: the round trip; the canonical form of an emitted
snapshot; restoring an entry; restoring an absent name; rejecting a restore together with an
explicit marking that holds a token; accepting a restore together with an explicit marking that
names no place; and seeding the restored marking whenever a restore is accepted alongside an
explicit marking that holds no token. The witness is (`refSnapshot`, `refRestore`, `refSeed`).

Every function triple that meets the block emits exactly the reference snapshot
(`core073_snapshot_eq`) and restores every mapping as the reference does (`core073_restore_eq`):
the form is normative, so two conforming implementations agree on it entry for entry. The spec's
other restore and snapshot sentences are derived from the lines: a restore ignores entry order
(`core073_restore_perm`), an empty entry restores like an absent one (`core073_restore_dropEmpty`),
a snapshot depends only on the marking (`core073_extensional`), and it lists exactly the marked
places (`core073_keys`). One wrong model per line is killed (a reversed queue, drained places kept
as empty entries, a restore that refuses an empty entry, a restore that keeps an old marking on an
omitted place, a seed that prefers the restore, a seed that refuses every restore, a seed that
prefers an explicit marking naming places but holding no token), and five more are forbidden
(UTF-16 code-unit order, a re-stamping restore, a snapshot that drops the name `__proto__`, a seed
that merges, a seed that re-stamps the restored tokens with the executor's epoch clock reading). Whether an explicit marking that names places but holds no token is rejected is
`undecided`: the reference accepts it, Java and TypeScript reject it; what an accepted one seeds
is not (line 7).

**`CORE_073_T` (kind T)** is a predicate over the restore and an abstract resume `Rs`, the timed
state a new executor starts from when a snapshot seeds it at the first clock reading. Two lines:
the resumed state holds the restored marking's counts on every place, and every transition of the
net that the restored marking enables holds the resumed state's own clock reading as its stamp.
The witness is (`refRestore`, `refResume`). An initialiser that meets CORE-072 meets it on the
restored counts (`core073T_of_core072`). With the reference timed step, a `Delayed` or `Window`
transition enabled by restored tokens waits its whole earliest bound from the resume, and a
`Deadline` transition is expired exactly when the time since the resume passes its bound plus the
tolerance, whatever the tokens' `created_at` (AC3 to AC5, for one delay step from the resume). The
wrong models are a resume that keeps only the places the net lists, a resume that stamps from the
tokens' `created_at`, and a resume stamped when the executor was built rather than when it runs.

`core073_joint` states the two blocks of one implementation together, over one restore at
`N := String`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## CORE-073 (F): the snapshot form, restore and seeding -/

requirement CORE_073
  id "CORE-073"
  title "Marking Snapshot and Restore"
  kind F
  scope "all implementations; line 6 binds every executor, an executor built from a restored marking alone (Rust, Python) included; lines 5 and 7 bind every executor that accepts a restored marking and an explicit initial marking together (Java, TypeScript)"
  source verbatim "spec/01-core-model.md"
  quote "*When* a snapshot of a marking is restored, the restored marking *shall* hold on every place exactly the tokens the marking held there, in the same FIFO order, each token unchanged in its value and its `created_at`."
        "A snapshot an implementation returns to the host *shall* list its places in strictly ascending code-point order of the place name and *shall not* list a place that holds no token."
        "*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold on each place the snapshot names exactly the tokens of that place's entry, in their order, whatever the place name and whether or not the receiving net declares the place."
        "*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold no token on a place the snapshot does not name."
        "*If* an executor is constructed with a restored marking together with an explicit initial marking that holds a token, *then* the construction *shall* fail with an error to the caller, and the executor *shall not* merge the two markings or keep either one."
        "*When* an executor is constructed with a restored marking together with an explicit initial marking that names no place, the executor's initial marking *shall* be the restored marking."
        "*When* an executor is constructed with a restored marking together with an explicit initial marking that holds no token and the construction succeeds, the executor's initial marking *shall* be the restored marking."
        "*When* a restored marking seeds a new executor, each restored token *shall* keep its value and its `created_at`, whatever the executor's epoch clock ([TIME-015])."
  reading "Let Snap be the snapshot (Snap F: the snapshot of the queue marking F.M, given with a finite list covering its marked places), Restore the restore (Restore s p: the queue the snapshot s restores on the place p) and Seed the seeding (Seed r E: the initial marking an executor is constructed with, token for token, from an optional restored snapshot r and an explicit initial marking E, or an error; an executor given an epoch clock has one Seed per clock reading, and the block binds each). Place names are strings."
          "For every F: Restore (Snap F) is F.M, on every place, token for token and in order."
          "For every F: Snap F is canonical (QCanon): its names are strictly ascending in String order, which is code-point order, and no entry has an empty queue."
          "For every snapshot s whose names are pairwise distinct and every entry (k, q) of s: Restore s k is q."
          "For every snapshot s whose names are pairwise distinct and every name k without an entry in s: Restore s k is empty."
          "For every snapshot s and every explicit initial marking E holding a token: Seed (some s) E is an error, for no marking M is it ok M."
          "For every snapshot s: Seed (some s) [] is ok (Restore s)."
          "For every snapshot s, every explicit initial marking E holding no token and every marking M: if Seed (some s) E is ok M, then M is Restore s."
  assumes "The model is the triple (Snap, Restore, Seed) over the snapshot form QSnap String T (Reference/Snapshot.lean): a list of (place name, queue) entries, each queue the place's tokens in FIFO order, head oldest. T is the implementation's own token, its value and its created_at together, so 'the tokens are unchanged' covers both fields; the form imposes nothing on T, which is the fourth bullet of the form (an entry is the implementation's own token representation). A queue marking is a function, so a snapshot is taken of a FinQ: the marking with a finite list covering its marked places, which may repeat a name or name an unmarked place. The witness is refSnapshot (the marked places of the list, sorted by insertionSort, deduplicated, each with its whole queue), refRestore (the queue of the first entry for a name, else empty) and refSeed (ruling D84 (a))."
          "A snapshot is a mapping (the form's second paragraph), read as QKeysNodup: lines 3 and 4 range over snapshots whose names are pairwise distinct, which every runtime container (a Java Map, a TypeScript Map, a Rust BTreeMap, a Python dict) guarantees, and their quoted sentences say so ('a snapshot whose place names are pairwise distinct'). A list naming one place twice is not a snapshot, and no line constrains its restore."
          "Lines 1 and 2 with lines 3 and 4 pin both functions down: every triple meeting the block emits refSnapshot (core073_snapshot_eq) and restores every mapping as refRestore does (core073_restore_eq). The form's MUSTs on restore and emission follow as theorems for every such triple: a restore does not depend on the order the places appear in (core073_restore_perm), an entry with an empty queue restores like an absent one (core073_restore_dropEmpty), the snapshot depends only on the marking, not on the list it came with, so a drained place and a place that never held a token snapshot identically and snapshotting twice gives one artefact (core073_extensional), and it lists exactly the marked places (core073_keys)."
          "Line 1 is the round trip (the body sentence, the first bullet of the form, the MUST NOT re-stamp sentence). Wrong models: a snapshot that reverses each queue violates it alone (CORE_073_mutant_roundTrip_killed); a restore that re-stamps every created_at (CORE_073_forbids_restampRestore, at T := value and created_at) and a snapshot written into a plain object that loses the name __proto__ (CORE_073_forbids_protoName, the reserved-name bullet) violate it too."
          "Line 2 is the emission half of the second bullet (omit a place with no token) and the canonical order paragraph (ascending code-point order of the place name), for the snapshot an implementation returns to the host: Snap is that operation. The same rule on a snapshot carried on an event (the paragraph 'The rule follows the form') is the event block's (EVT-014, W7), whose snapshot ruling D38 takes over the declared places; the rule does not reach a JSON session archive or the JSON debug protocol, which the quoted sentence therefore does not name. On String, Lean's order is lexicographic on characters, which is code-point order. A snapshot that keeps a drained place as an empty entry violates it alone (CORE_073_mutant_canonical_killed), and so does a snapshot sorted by UTF-16 code unit, on the names U+E000 and U+10000 (CORE_073_forbids_utf16)."
          "Lines 3 and 4 are the restore half of the second bullet (accept a place omitted and a place present as an empty sequence, and restore them identically), the third bullet (a name the receiving net does not declare is retained: Restore knows no net, so every name is kept) and the fifth bullet (no name is reserved: line 3 holds at every string). A restore that accepts only the emitted form and restores nothing from a snapshot with an empty entry violates line 3 alone (CORE_073_mutant_restoreEntry_killed); a restore that keeps an earlier marking on the places a hand-authored snapshot omits violates line 4 alone (CORE_073_mutant_restoreAbsent_killed)."
          "Lines 5, 6 and 7 are the paragraph 'A restore and an initial marking are two descriptions of one thing' and AC11, under ruling D84 (a): an explicit initial marking that holds a token is rejected together with a restore, an explicit initial marking that names no place is accepted and seeds the restored marking, and whenever a restore is accepted alongside an explicit marking that holds no token, the restored marking is what is seeded. A seed that silently prefers the restore violates line 5 alone (CORE_073_mutant_rejectBoth_killed), and so does a seed that merges the two (CORE_073_forbids_mergeSeed); a seed that refuses every restore, the shape the body's former 'supplying both' would force on a factory that always takes a map, violates line 6 alone (CORE_073_mutant_acceptEmpty_killed); a seed that accepts an explicit marking naming places with no token and then seeds that explicit marking, dropping every restored token (the selection written as 'initialTokens.isEmpty() ? restored : initialTokens'), violates line 7 alone (CORE_073_mutant_seedRestore_killed). Whether an explicit marking that names places but holds no token is rejected is left open (CORE_073_undecided_emptyEntries): refSeed accepts it, Java (initialTokens.isEmpty(), BitmapNetExecutor.java Builder.restore) and TypeScript (initialTokens.size > 0, bitmap-net-executor.ts) reject it, and both meet the block, line 7 included. Rust and Python construct an executor from one marking: an executor built from a restored marking alone (Marking::from_snapshot handed to the constructor, which the Python binding wraps) is Seed (some s) [], a restore with an explicit marking that names no place, so line 6 binds them; they have no second input, so lines 5 and 7 do not (the scope). Seed is the seeding over nets without two places of one name: Java's build() rejects a restore into a net that declares two same-named places (Marking.resolveSnapshot, reached from Builder.seedTokens; MOD-024, AC10), which is the unmodelled N part below, so that rejection is not a counterexample to line 6."
          "The seeding lines say nothing of a seed without a restore (Seed none E): that the explicit initial marking is the initial marking is CORE-072's line 1, on counts. An executor built from a restored marking is Seed (some s) [] in every runtime, Rust and Python included, so a seed that keeps the restored tokens only on Seed (some s) [] and re-stamps an explicit marking given without a restore is outside this block's sentences, not a counterexample to them."
          "Not modelled (N, Java only): the paragraph 'Restoring resolves names against the receiving net' (resolve each name against the net's declared places; retain an undeclared name under a placeholder place), the paragraph after it (reject, where the host asked, a snapshot or a restore over two places sharing one name; the marking-snapshot event never fails a run over it, EVT-014's) and AC10. Lean places are names, so a restore needs no net and is never ambiguous; Java's place equality over name and token type (MOD-024) forces it to take the net's places as a second input and to reject a snapshot or a restore over two same-named places, a divergence of Java's Place type, not of the form. Under ruling D21 the Kind line carries the primary kind only (F), so this N part is recorded here; a Java-scoped companion block is the integrator's call. The sixth bullet (no codec, the form is structural) and AC8 hold by type: every line is stated at every T, a function type included (core073_closure_roundTrip). The order rule's reach into events (EVT-014) and the reproducibility of JSON archives and the debug protocol (EVT-025) are the event blocks' (W7, W6), stated over the same refSnapshot. The non-normative note on the NU-022 tie-break and the SHOULD to reuse the canonical comparator are advice."
          "The VER paragraph ('A timed proof does not cross a restore') is a remark about proofs, cited by the VER blocks: the state-class graph of a resumed run starts from the initial state of CORE_073_T, every clock at zero; an untimed proof covers a restored marking taken from a real run at a moment with no work in flight (ENV-014, ruling R-CC6), not a hand-authored one."
          "AC1 (snapshot then restore round-trips each token's value and created_at) is line 1."
          "AC6 (FIFO order survives; the first firing takes A) is line 1 with the reference queue firing: CORE_073_nonvacuous restores A, B, C on a place and the reference delivery of a one-token input arc on it is A (EXEC-010)."
          "AC7 (an empty place restores identically to an omitted one; an emitted snapshot omits empty places on every executor; an undeclared name is retained) is core073_restore_dropEmpty, line 2 with core073_extensional, and line 3. 'On every executor' is the scope: every snapshot an implementation emits is one Snap."
          "AC8 (no codec) is by type, as above. AC10 (resolution against the receiving net, rejection of two same-named places) is not modelled, as above."
          "AC9 (the engine does not re-stamp) is line 1 for the snapshot pair and CORE_073_forbids_restampRestore. The quoted sentence on seeding a new executor ('each restored token shall keep its value and its created_at, whatever the executor's epoch clock') and AC9's 'including where the executor was given an injected epoch clock' are line 6 for every executor and line 7 for one that also takes an explicit marking (Java, TypeScript): Seed's result is the executor's initial marking token for token, and an accepted construction from a restore seeds Restore s itself, which by lines 1 and 3 is the snapshot's tokens with their values and created_at unchanged. An executor given an epoch clock is one Seed per clock reading, and the block binds each, so no reading can enter the seeded tokens: a seed that re-stamps the restored tokens with the reading r violates line 6 at every r (core073_restampSeed_every; the evidence CORE_073_forbids_restampSeed at r = 0, at T := value and created_at). The runtimes keep the tokens as given (rust/libpetri-runtime/src/precompiled_backend.rs, the initial-token load, clones each token; Java Builder.seedTokens returns Marking.resolveSnapshot's tokens; TypeScript restoredTokens copies the token list), so no RD entry is needed. Line 6 states the initial marking an executor is constructed with; that a run then starts from it is the executor cycle relation's start state (RefExec, xinit), which takes its initial marking as given."
          "AC11 (both is an error) is lines 5, 6 and 7, and AC12 (canonical place order: the same order twice, order-blind restore, ascending code-point order, also above U+FFFF) is line 2 with core073_extensional, core073_restore_perm and CORE_073_forbids_utf16."
          "AC2, AC3, AC4 and AC5 (the restored marking pre-populates places; the clocks start fresh at the resume) are the timed block CORE_073_T, on counts and stamps; AC2's 'exactly like any other initial marking' at the level of the tokens themselves, values and created_at, is line 6 for every executor and line 7 for Java and TypeScript."
  signoff "2026-11-13 6d172b9f8eb5b302 ai"
  statement : ∀ {T : Type}, (FinQ String T → QSnap String T) → (QSnap String T → QMarking String T) →
      (Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) → Prop :=
    fun Snap Restore Seed =>
      (∀ F, Restore (Snap F) = F.M) ∧
      (∀ F, QCanon (Snap F)) ∧
      (∀ s, QKeysNodup s → ∀ k q, (k, q) ∈ s → Restore s k = q) ∧
      (∀ s, QKeysNodup s → ∀ k, k ∉ s.map Prod.fst → Restore s k = []) ∧
      (∀ s E, HoldsToken E → ∀ M, Seed (some s) E ≠ .ok M) ∧
      (∀ s, Seed (some s) [] = .ok (Restore s)) ∧
      (∀ s E M, ¬ HoldsToken E → Seed (some s) E = .ok M → M = Restore s)

/- The pinned readable form of CORE-073: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_073 : {T : Type} →
  (FinQ String T → QSnap String T) →
    (QSnap String T → QMarking String T) →
      (Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) → Prop :=
fun {T} Snap Restore Seed =>
  (∀ (F : FinQ String T), Restore (Snap F) = F.M) ∧
    (∀ (F : FinQ String T), QCanon (Snap F)) ∧
      (∀ (s : QSnap String T), QKeysNodup s → ∀ (k : String) (q : List T), (k, q) ∈ s → Restore s k = q) ∧
        (∀ (s : QSnap String T), QKeysNodup s → ∀ k ∉ List.map Prod.fst s, Restore s k = []) ∧
          (∀ (s E : QSnap String T), HoldsToken E → ∀ (M : QMarking String T), Seed (some s) E ≠ Except.ok M) ∧
            (∀ (s : QSnap String T), Seed (some s) [] = Except.ok (Restore s)) ∧
              ∀ (s E : QSnap String T) (M : QMarking String T),
                ¬HoldsToken E → Seed (some s) E = Except.ok M → M = Restore s
-/
#guard_msgs in #print CORE_073

/-! ### The six lines, named (for the mutants) -/

section Lines

variable {T : Type}

/-- Line 1 of CORE-073: restore after snapshot is the marking. -/
def core073_line1 (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T) : Prop :=
  ∀ F, Restore (Snap F) = F.M

/-- Line 2 of CORE-073: an emitted snapshot is canonical. -/
def core073_line2 (Snap : FinQ String T → QSnap String T) : Prop := ∀ F, QCanon (Snap F)

/-- Line 3 of CORE-073: a mapping restores each entry's queue on its place. -/
def core073_line3 (Restore : QSnap String T → QMarking String T) : Prop :=
  ∀ s, QKeysNodup s → ∀ k q, (k, q) ∈ s → Restore s k = q

/-- Line 4 of CORE-073: a mapping restores nothing on a name it does not hold. -/
def core073_line4 (Restore : QSnap String T → QMarking String T) : Prop :=
  ∀ s, QKeysNodup s → ∀ k, k ∉ s.map Prod.fst → Restore s k = []

/-- Line 5 of CORE-073: a restore together with an explicit marking holding a token is rejected. -/
def core073_line5
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  ∀ s E, HoldsToken E → ∀ M, Seed (some s) E ≠ .ok M

/-- Line 6 of CORE-073: a restore together with an explicit marking naming no place seeds the
restored marking. -/
def core073_line6 (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  ∀ s, Seed (some s) [] = .ok (Restore s)

/-- Line 7 of CORE-073: a restore accepted alongside an explicit marking that holds no token seeds
the restored marking. -/
def core073_line7 (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  ∀ s E M, ¬ HoldsToken E → Seed (some s) E = .ok M → M = Restore s

/-- CORE-073 is its seven lines. -/
theorem core073_iff (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) :
    CORE_073 Snap Restore Seed ↔
      core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line3 Restore ∧
        core073_line4 Restore ∧ core073_line5 Seed ∧ core073_line6 Restore Seed ∧
          core073_line7 Restore Seed :=
  Iff.rfl

end Lines

/-! ### The reference -/

/-- An explicit initial marking that names no place holds no token. -/
theorem core073_nil_not_holds {T : Type} : ¬ HoldsToken ([] : QSnap String T) := by
  simp [HoldsToken]

/-- ✓ The reference triple satisfies CORE-073: restore after snapshot is the marking
(`restore_snapshot`), the snapshot is canonical (`snapshot_canon`), a mapping restores each entry
and nothing else (`restore_of_mem`, `restore_eq_nil_of_not_mem`), and `refSeed` rejects a restore
with an explicit marking holding a token and accepts one with an explicit marking naming no place
(`refSeed_both`, `refSeed_restore`), and seeds the restored marking whenever the explicit marking
holds no token (`refSeed_restore`). -/
@[evidence holds CORE_073]
theorem CORE_073_reference {T : Type} : CORE_073 (T := T) refSnapshot refRestore refSeed :=
  ⟨restore_snapshot, snapshot_canon, fun _ hnd _ _ hm => restore_of_mem hnd hm,
    fun _ _ _ hk => restore_eq_nil_of_not_mem hk, fun _ _ hE M => refSeed_both hE M,
    fun _ => refSeed_restore core073_nil_not_holds,
    fun _ _ _ hE hM => by rw [refSeed_restore hE] at hM; cases hM; rfl⟩

/-! ### Consequences: the form is normative -/

section Consequences

variable {T : Type} {Snap : FinQ String T → QSnap String T}
  {Restore : QSnap String T → QMarking String T}
  {Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)}

/-- Under lines 3 and 4, a restore of a mapping is the reference restore. -/
theorem core073_restore_eq (h : CORE_073 Snap Restore Seed) {s : QSnap String T}
    (hnd : QKeysNodup s) : Restore s = refRestore s := by
  funext k
  by_cases hk : k ∈ s.map Prod.fst
  · obtain ⟨⟨k', q⟩, hm, rfl⟩ := List.mem_map.mp hk
    rw [h.2.2.1 s hnd _ q hm, restore_of_mem hnd hm]
  · rw [h.2.2.2.1 s hnd k hk, restore_eq_nil_of_not_mem hk]

/-- **The form is normative**: every snapshot that meets CORE-073 is the reference snapshot, so
two conforming implementations emit the same snapshot of one marking, entry for entry. -/
theorem core073_snapshot_eq (h : CORE_073 Snap Restore Seed) (F : FinQ String T) :
    Snap F = refSnapshot F :=
  canon_ext (h.2.1 F) (snapshot_canon F) fun p => by
    rw [← core073_restore_eq h (h.2.1 F).keysNodup, h.1 F, restore_snapshot]

/-- **Extensional**: the snapshot depends only on the marking. A drained place and a place that
never held a token snapshot identically, and snapshotting one marking twice gives one artefact. -/
theorem core073_extensional (h : CORE_073 Snap Restore Seed) {F G : FinQ String T}
    (hm : F.M = G.M) : Snap F = Snap G := by
  rw [core073_snapshot_eq h, core073_snapshot_eq h]
  exact snapshot_extensional hm

/-- The snapshot lists exactly the marked places. -/
theorem core073_keys (h : CORE_073 Snap Restore Seed) (F : FinQ String T) (k : String) :
    k ∈ (Snap F).map Prod.fst ↔ F.M k ≠ [] := by
  rw [core073_snapshot_eq h]
  exact mem_snapshot_keys F k

/-- **Order-blind**: a restore of a mapping does not depend on the order of its entries. -/
theorem core073_restore_perm (h : CORE_073 Snap Restore Seed) {s s' : QSnap String T}
    (hnd : QKeysNodup s) (hp : s.Perm s') : Restore s = Restore s' := by
  have hnd' : QKeysNodup s' := (hp.map Prod.fst).nodup_iff.mp hnd
  rw [core073_restore_eq h hnd, core073_restore_eq h hnd']
  exact restore_perm hnd hp

/-- **Empty equals absent**: on a mapping, an entry with an empty queue restores like an absent
one. -/
theorem core073_restore_dropEmpty (h : CORE_073 Snap Restore Seed) {s : QSnap String T}
    (hnd : QKeysNodup s) : Restore (s.filter fun e => !e.2.isEmpty) = Restore s := by
  have hnd' : QKeysNodup (s.filter fun e => !e.2.isEmpty) :=
    List.Nodup.sublist (List.filter_sublist.map Prod.fst) hnd
  rw [core073_restore_eq h hnd, core073_restore_eq h hnd']
  exact restore_dropEmpty hnd

end Consequences

/-! ### Examples -/

/-- Place "p" holds A, B, C (the tokens 1, 2, 3); every other place is empty. -/
def core073_F : FinQ String Nat where
  M := fun k => if k = "p" then [1, 2, 3] else []
  supp := ["p"]
  hsupp := fun k hk => by
    by_cases h : k = "p"
    · simp [h]
    · simp [h] at hk

/-- Place "a" holds 1; the list also names the unmarked "b" (a drained place). -/
def core073_Fab : FinQ String Nat where
  M := fun k => if k = "a" then [1] else []
  supp := ["a", "b"]
  hsupp := fun k hk => by
    by_cases h : k = "a"
    · simp [h]
    · simp [h] at hk

/-- The transition of AC6: one input arc on "p" (one token), output "q". -/
def core073_t : Trans String :=
  { core := { name := "t", inputs := [⟨"p", .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place "q") }

/-- ✓ CORE-073 is not vacuous. A, B, C on "p" snapshot to one entry and restore in order, and the
first firing of a one-token input arc on "p" is delivered A (AC6); a list naming "a" twice and
the unmarked "b" snapshots to the marked places in order (AC7); the names U+E000 and U+10000 come
out in code-point order (AC12); a hand-authored snapshot with an empty entry, out of order,
restores like the canonical one (AC7, AC12); and a restore with an explicit marking holding a
token is an error while one with no explicit marking is not (AC11). -/
@[evidence nonvacuous CORE_073]
theorem CORE_073_nonvacuous :
    refSnapshot core073_F = [("p", [1, 2, 3])] ∧
    refRestore (refSnapshot core073_F) "p" = [1, 2, 3] ∧
    (qDelivered (refRestore (refSnapshot core073_F)) core073_t).inputs "p" = [1] ∧
    refSnapshot snapExF = [("a", [1]), ("c", [7, 8])] ∧
    (refSnapshot snapExCP).map Prod.fst = [snapNameBmp, snapNameAstral] ∧
    (["a", "b", "c"].map fun k => refRestore [("c", [7, 8]), ("b", []), ("a", [1])] k) =
      (["a", "b", "c"].map fun k => refRestore (refSnapshot snapExF) k) ∧
    (refSeed (some [("a", [1])]) [("b", [2])] : Except String (QMarking String Nat)).toBool
      = false ∧
    (refSeed (some [("a", [1])]) [] : Except String (QMarking String Nat)).toBool = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- AC8: the round trip holds at a token type no codec can encode, a function type. -/
theorem core073_closure_roundTrip (F : FinQ String (Nat → Nat)) :
    refRestore (refSnapshot F) = F.M :=
  CORE_073_reference.1 F

/-! ### Mutant: line 1, a snapshot that reverses each queue -/

section MutantRoundTrip

variable {T : Type}

/-- A snapshot that lists each marked place with its queue reversed (newest first). -/
def core073_snapRev (F : FinQ String T) : QSnap String T :=
  (refSnapshot F).map fun e => (e.1, e.2.reverse)

/-- Mutant reading of CORE-073 without line 1 (no round trip). -/
def CORE_073_mutant_roundTrip (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line2 Snap ∧ core073_line3 Restore ∧ core073_line4 Restore ∧ core073_line5 Seed ∧
    core073_line6 Restore Seed ∧ core073_line7 Restore Seed

theorem core073_snapRev_canon (F : FinQ String T) : QCanon (core073_snapRev F) := by
  obtain ⟨h1, h2⟩ := snapshot_canon F
  refine ⟨by simpa [core073_snapRev, Function.comp_def] using h1, fun e he => ?_⟩
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  simpa using h2 e' he'

end MutantRoundTrip

/-- ✗ The reversing snapshot kills the mutant: it is canonical, and the restore and the seed are
the reference, but A, B, C on "p" restore as C, B, A (line 1, AC6). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_roundTrip_killed :
    CORE_073_mutant_roundTrip (T := Nat) core073_snapRev refRestore refSeed ∧
      ¬ CORE_073 (T := Nat) core073_snapRev refRestore refSeed := by
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := CORE_073_reference (T := Nat)
  refine ⟨⟨core073_snapRev_canon, h3, h4, h5, h6, h7⟩, fun h => ?_⟩
  have := congrFun (h.1 core073_F) "p"
  revert this
  decide

/-! ### Mutant: line 2, a snapshot that keeps drained places as empty entries -/

section MutantCanonical

variable {T : Type}

/-- A snapshot that lists every place of the list it came with, sorted and deduplicated, a
drained place as an empty entry: a function of history, not of the marking. -/
def core073_snapKeep (F : FinQ String T) : QSnap String T :=
  ((F.supp.insertionSort (· ≤ ·)).dedup).map fun k => (k, F.M k)

/-- Mutant reading of CORE-073 with line 2 weakened to its order half (names strictly
ascending), without 'omit a place that holds no token'. -/
def CORE_073_mutant_canonical (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ (∀ F, ((Snap F).map Prod.fst).Pairwise (· < ·)) ∧
    core073_line3 Restore ∧ core073_line4 Restore ∧ core073_line5 Seed ∧
    core073_line6 Restore Seed ∧ core073_line7 Restore Seed

theorem core073_snapKeep_keys (F : FinQ String T) :
    (core073_snapKeep F).map Prod.fst = (F.supp.insertionSort (· ≤ ·)).dedup := by
  simp [core073_snapKeep, Function.comp_def]

theorem core073_snapKeep_lt (F : FinQ String T) :
    ((core073_snapKeep F).map Prod.fst).Pairwise (· < ·) := by
  rw [core073_snapKeep_keys]
  have hs : ((F.supp.insertionSort (· ≤ ·)).dedup).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) F.supp).sublist (List.dedup_sublist _)
  exact (hs.and (List.nodup_dedup _)).imp fun h => lt_of_le_of_ne h.1 h.2

theorem core073_snapKeep_restore (F : FinQ String T) : refRestore (core073_snapKeep F) = F.M := by
  have hnd : QKeysNodup (core073_snapKeep F) := by
    unfold QKeysNodup
    rw [core073_snapKeep_keys]
    exact List.nodup_dedup _
  funext k
  by_cases hk : k ∈ (F.supp.insertionSort (· ≤ ·)).dedup
  · exact restore_of_mem hnd (List.mem_map.mpr ⟨k, hk, rfl⟩)
  · have hns : k ∉ F.supp := fun hm =>
      hk (List.mem_dedup.mpr ((List.perm_insertionSort _ _).mem_iff.mpr hm))
    have hM : F.M k = [] := by
      by_contra hne
      exact hns (F.hsupp k hne)
    rw [hM]
    exact restore_eq_nil_of_not_mem (by rw [core073_snapKeep_keys]; exact hk)

end MutantCanonical

/-- ✗ The history-keeping snapshot kills the mutant: its names are ascending and it round-trips,
but the list ["a", "b"] with "b" drained snapshots to an entry for "b" with an empty queue, which is
not canonical (line 2, AC7). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_canonical_killed :
    CORE_073_mutant_canonical (T := Nat) core073_snapKeep refRestore refSeed ∧
      ¬ CORE_073 (T := Nat) core073_snapKeep refRestore refSeed := by
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := CORE_073_reference (T := Nat)
  refine ⟨⟨core073_snapKeep_restore, core073_snapKeep_lt, h3, h4, h5, h6, h7⟩, fun h => ?_⟩
  have := h.2.1 core073_Fab
  revert this
  decide

/-! ### Forbidden: a snapshot sorted by UTF-16 code unit -/

/-- The UTF-16 code units of a character. -/
def core073_utf16Units (c : Char) : List Nat :=
  if c.toNat < 0x10000 then [c.toNat]
  else [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400]

/-- A name as its UTF-16 code units: the key Java's `String.compareTo` and JavaScript's `<`
compare. -/
def core073_utf16 (s : String) : List Nat := s.toList.flatMap core073_utf16Units

/-- A snapshot that sorts its names by UTF-16 code unit, as a host's natural string order does. -/
def core073_snapUtf16 {T : Type} (F : FinQ String T) : QSnap String T :=
  (((F.supp.insertionSort fun a b => core073_utf16 a ≤ core073_utf16 b).dedup).filter
    fun k => !(F.M k).isEmpty).map fun k => (k, F.M k)

/-- ✗ CORE-073 forbids the UTF-16 order: U+10000 (surrogate D800) sorts before U+E000 in it, so
the snapshot of a marking holding both names is not in code-point order (line 2, AC12). -/
@[evidence forbids CORE_073]
theorem CORE_073_forbids_utf16 : ¬ CORE_073 (T := Nat) core073_snapUtf16 refRestore refSeed := by
  intro h
  have := h.2.1 snapExCP
  revert this
  decide

/-! ### Forbidden: a restore that re-stamps `created_at` -/

/-- A restore that re-stamps every token's `created_at` with the reading 0 (tokens are a value
and a `created_at`). -/
def core073_restoreRestamp : QSnap String (Nat × Nat) → QMarking String (Nat × Nat) :=
  fun s k => (refRestore s k).map fun x => (x.1, 0)

/-- ✗ CORE-073 forbids re-stamping: a token stamped 7 restores stamped 0 (line 1, AC9). -/
@[evidence forbids CORE_073]
theorem CORE_073_forbids_restampRestore :
    ¬ CORE_073 refSnapshot core073_restoreRestamp refSeed := by
  intro h
  have := h.2.2.1 [("p", [(5, 7)])] (by decide) "p" [(5, 7)] (by simp)
  revert this
  decide

/-! ### Forbidden: a snapshot that loses a name a host container reserves -/

/-- A snapshot written into a plain object, which loses the name `__proto__`. -/
def core073_snapProto {T : Type} (F : FinQ String T) : QSnap String T :=
  (refSnapshot F).filter fun e => e.1 != "__proto__"

/-- The place `__proto__` holds 1. -/
def core073_Fproto : FinQ String Nat where
  M := fun k => if k = "__proto__" then [1] else []
  supp := ["__proto__"]
  hsupp := fun k hk => by
    by_cases h : k = "__proto__"
    · simp [h]
    · simp [h] at hk

/-- ✗ CORE-073 forbids a reserved name: the marking with a token on `__proto__` does not survive
the round trip (line 1, the bullet 'no name is reserved'). -/
@[evidence forbids CORE_073]
theorem CORE_073_forbids_protoName : ¬ CORE_073 (T := Nat) core073_snapProto refRestore refSeed := by
  intro h
  have := congrFun (h.1 core073_Fproto) "__proto__"
  revert this
  decide

/-! ### Seeds built on a restore -/

section Seeds

variable {T : Type}

/-- The reference seeding shape on any restore `R`: without a restore, the explicit marking; with
one, an error when the explicit marking holds a token, else the restored marking. -/
def core073_seedOf (R : QSnap String T → QMarking String T) :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (R E)
  | some s, E =>
    if HoldsToken E then
      .error "a restored marking and a non-empty explicit initial marking both describe the initial marking"
    else .ok (R s)

/-- On the reference restore it is `refSeed`. -/
theorem core073_seedOf_ref : core073_seedOf (T := T) refRestore = refSeed := by
  funext r E
  cases r <;> rfl

theorem core073_seedOf_line5 (R : QSnap String T → QMarking String T) :
    core073_line5 (core073_seedOf R) := by
  intro s E hE M
  simp [core073_seedOf, hE]

theorem core073_seedOf_line6 (R : QSnap String T → QMarking String T) :
    core073_line6 R (core073_seedOf R) := by
  intro s
  simp [core073_seedOf, core073_nil_not_holds]

theorem core073_seedOf_line7 (R : QSnap String T → QMarking String T) :
    core073_line7 R (core073_seedOf R) := by
  intro s E M hE hM
  simp [core073_seedOf, hE] at hM
  exact hM.symm

end Seeds

/-! ### Mutant: line 3, a restore that accepts only the emitted form -/

section MutantEntry

variable {T : Type}

/-- A restore that reads only a snapshot without an empty entry, and restores nothing from a
snapshot a host wrote with one. -/
def core073_restoreStrict (s : QSnap String T) : QMarking String T :=
  if s.all (fun e => !e.2.isEmpty) then refRestore s else fun _ => []

/-- Mutant reading of CORE-073 without line 3. -/
def CORE_073_mutant_restoreEntry (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line4 Restore ∧ core073_line5 Seed ∧
    core073_line6 Restore Seed ∧ core073_line7 Restore Seed

theorem core073_restoreStrict_canon {s : QSnap String T} (hc : QCanon s) :
    core073_restoreStrict s = refRestore s := by
  have : s.all (fun e => !e.2.isEmpty) = true :=
    List.all_eq_true.mpr fun e he => by simpa [List.isEmpty_eq_false_iff] using hc.2 e he
  simp [core073_restoreStrict, this]

end MutantEntry

/-- ✗ The strict restore kills the mutant: it round-trips every emitted snapshot and restores
nothing on an absent name, but the hand-authored snapshot {a: [1], b: []} restores nothing on "a"
(line 3, AC7). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_restoreEntry_killed :
    CORE_073_mutant_restoreEntry (T := Nat) refSnapshot core073_restoreStrict
        (core073_seedOf core073_restoreStrict) ∧
      ¬ CORE_073 (T := Nat) refSnapshot core073_restoreStrict
        (core073_seedOf core073_restoreStrict) := by
  refine ⟨⟨fun F => by rw [core073_restoreStrict_canon (snapshot_canon F), restore_snapshot],
    snapshot_canon, fun s _ k hk => ?_, core073_seedOf_line5 _, core073_seedOf_line6 _,
    core073_seedOf_line7 _⟩, fun h => ?_⟩
  · unfold core073_restoreStrict
    split
    · exact restore_eq_nil_of_not_mem hk
    · rfl
  · have := h.2.2.1 [("a", [1]), ("b", [])] (by decide) "a" [1] (by simp)
    revert this
    decide

/-! ### Mutant: line 4, a restore that keeps an earlier marking on omitted places -/

/-- The marking an executor held before the restore: a token 0 on every place. -/
def core073_prev : QMarking String Nat := fun _ => [0]

/-- A restore that, for a snapshot not in canonical form (a hand-authored one), keeps the earlier
marking on the places the snapshot omits: a merge, not a replacement. -/
def core073_restoreMerge (s : QSnap String Nat) : QMarking String Nat := fun k =>
  if k ∈ s.map Prod.fst then refRestore s k else if QCanon s then [] else core073_prev k

/-- Mutant reading of CORE-073 without line 4. -/
def CORE_073_mutant_restoreAbsent {T : Type} (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line3 Restore ∧ core073_line5 Seed ∧
    core073_line6 Restore Seed ∧ core073_line7 Restore Seed

theorem core073_restoreMerge_canon {s : QSnap String Nat} (hc : QCanon s) :
    core073_restoreMerge s = refRestore s := by
  funext k
  by_cases hk : k ∈ s.map Prod.fst
  · simp only [core073_restoreMerge, if_pos hk]
  · simp only [core073_restoreMerge, if_neg hk, if_pos hc, restore_eq_nil_of_not_mem hk]

/-- ✗ The merging restore kills the mutant: it round-trips every emitted snapshot and restores
every entry, but the out-of-order snapshot {b: [1], a: [2]} restores a token on the omitted "c"
(line 4). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_restoreAbsent_killed :
    CORE_073_mutant_restoreAbsent refSnapshot core073_restoreMerge
        (core073_seedOf core073_restoreMerge) ∧
      ¬ CORE_073 refSnapshot core073_restoreMerge (core073_seedOf core073_restoreMerge) := by
  refine ⟨⟨fun F => by rw [core073_restoreMerge_canon (snapshot_canon F), restore_snapshot],
    snapshot_canon, fun s hnd k q hm => ?_, core073_seedOf_line5 _, core073_seedOf_line6 _,
    core073_seedOf_line7 _⟩, fun h => ?_⟩
  · have hk : k ∈ s.map Prod.fst := List.mem_map.mpr ⟨_, hm, rfl⟩
    simp only [core073_restoreMerge, if_pos hk]
    exact restore_of_mem hnd hm
  · have := h.2.2.2.1 [("b", [1]), ("a", [2])] (by decide) "c" (by decide)
    revert this
    decide

/-! ### Mutant: line 5, a seed that prefers the restore -/

section MutantSeeds

variable {T : Type}

/-- A seed that silently prefers the restore and discards the explicit marking. -/
def core073_seedPrefer :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (refRestore E)
  | some s, _ => .ok (refRestore s)

/-- A seed that merges the explicit marking with the restore. -/
def core073_seedMerge :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (refRestore E)
  | some s, E => .ok fun k => refRestore E k ++ refRestore s k

/-- A seed that refuses every restore, whatever the explicit marking. -/
def core073_seedRejectAll :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (refRestore E)
  | some _, _ => .error "restore and initial marking"

/-- The Java and TypeScript seed: a restore is rejected when the explicit marking has an entry,
token or not (`!initialTokens.isEmpty()`, `initialTokens.size > 0`). -/
def core073_seedMap :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (refRestore E)
  | some s, E => if E.isEmpty then .ok (refRestore s) else .error "restore and initial marking"

/-- A seed whose guard follows ruling D84 (a) but whose selection prefers the explicit marking
unless it names no place (`initialTokens.isEmpty() ? restored : initialTokens`): an explicit
marking that names a place with no token passes the guard and is seeded, and the restored tokens
are dropped. -/
def core073_seedExplicit :
    Option (QSnap String T) → QSnap String T → Except String (QMarking String T)
  | none, E => .ok (refRestore E)
  | some s, E =>
    if HoldsToken E then .error "restore and initial marking"
    else if E.isEmpty then .ok (refRestore s) else .ok (refRestore E)

/-- Mutant reading of CORE-073 without line 5. -/
def CORE_073_mutant_rejectBoth (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line3 Restore ∧
    core073_line4 Restore ∧ core073_line6 Restore Seed ∧ core073_line7 Restore Seed

/-- Mutant reading of CORE-073 without line 6. -/
def CORE_073_mutant_acceptEmpty (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line3 Restore ∧
    core073_line4 Restore ∧ core073_line5 Seed ∧ core073_line7 Restore Seed

/-- Mutant reading of CORE-073 without line 7. -/
def CORE_073_mutant_seedRestore (Snap : FinQ String T → QSnap String T)
    (Restore : QSnap String T → QMarking String T)
    (Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)) : Prop :=
  core073_line1 Snap Restore ∧ core073_line2 Snap ∧ core073_line3 Restore ∧
    core073_line4 Restore ∧ core073_line5 Seed ∧ core073_line6 Restore Seed

end MutantSeeds

/-- ✗ The preferring seed kills the mutant: it seeds the restored marking when the explicit marking
names no place, but it also accepts a restore with an explicit marking holding a token, and drops
that token (line 5, AC11). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_rejectBoth_killed :
    CORE_073_mutant_rejectBoth (T := Nat) refSnapshot refRestore core073_seedPrefer ∧
      ¬ CORE_073 (T := Nat) refSnapshot refRestore core073_seedPrefer := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := CORE_073_reference (T := Nat)
  exact ⟨⟨h1, h2, h3, h4, fun _ => rfl, fun _ _ _ _ hM => (Except.ok.inj hM).symm⟩,
    fun h => h.2.2.2.2.1 [] [("a", [1])] (by decide) _ rfl⟩

/-- ✗ CORE-073 forbids merging a restore with an explicit marking holding a token (line 5,
AC11). -/
@[evidence forbids CORE_073]
theorem CORE_073_forbids_mergeSeed :
    ¬ CORE_073 (T := Nat) refSnapshot refRestore core073_seedMerge :=
  fun h => h.2.2.2.2.1 [("b", [2])] [("a", [1])] (by decide) _ rfl

/-- A seed that, given a restore and an explicit marking holding no token, seeds the restored
tokens re-stamped with the reading `r` of the executor's epoch clock (tokens are a value and a
`created_at`); otherwise the reference. -/
def core073_seedRestampAt (r : Nat) :
    Option (QSnap String (Nat × Nat)) → QSnap String (Nat × Nat) →
      Except String (QMarking String (Nat × Nat))
  | none, E => .ok (refRestore E)
  | some s, E =>
    if HoldsToken E then .error "restore and initial marking"
    else .ok fun k => (refRestore s k).map fun x => (x.1, r)

/-- At every epoch clock reading `r`, the re-stamping seed violates CORE-073: an executor built
from a restore holding a token stamped `r + 1` on "p", and no explicit marking (the Rust and Python
construction), would seed it stamped `r` (line 6). -/
theorem core073_restampSeed_every (r : Nat) :
    ¬ CORE_073 refSnapshot refRestore (core073_seedRestampAt r) := by
  intro h
  have h6 := h.2.2.2.2.2.1 [("p", [(5, r + 1)])]
  simp only [core073_seedRestampAt, if_neg core073_nil_not_holds, Except.ok.injEq] at h6
  have := congrFun h6 "p"
  simp [refRestore] at this

/-- ✗ CORE-073 forbids re-stamping at the seed: with the epoch clock reading 0, a token stamped 1
restored and seeded with no explicit marking would come out stamped 0 (line 6, the quoted seeding
sentence, AC9); `core073_restampSeed_every` gives the same at every reading. -/
@[evidence forbids CORE_073]
theorem CORE_073_forbids_restampSeed :
    ¬ CORE_073 refSnapshot refRestore (core073_seedRestampAt 0) :=
  core073_restampSeed_every 0

/-- ✗ The refusing seed kills the mutant: it rejects every restore with an explicit marking
holding a token, but it also rejects a restore with an explicit marking that names no place, so
an executor cannot be resumed at all (line 6, AC11). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_acceptEmpty_killed :
    CORE_073_mutant_acceptEmpty (T := Nat) refSnapshot refRestore core073_seedRejectAll ∧
      ¬ CORE_073 (T := Nat) refSnapshot refRestore core073_seedRejectAll := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := CORE_073_reference (T := Nat)
  refine ⟨⟨h1, h2, h3, h4, fun _ _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he)⟩,
    fun h => ?_⟩
  have := h.2.2.2.2.2.1 []
  simp [core073_seedRejectAll] at this

/-- ✗ The explicit-preferring seed kills the mutant: it rejects a restore with an explicit marking
holding a token and seeds the restore when the explicit marking names no place, but given a
restore holding 1 on "a" with the explicit marking {b: []} it accepts and seeds that explicit
marking, so the token on "a" is silently lost (line 7, the paragraph 'A restore and an initial
marking are two descriptions of one thing', AC11). -/
@[evidence mutant CORE_073]
theorem CORE_073_mutant_seedRestore_killed :
    CORE_073_mutant_seedRestore (T := Nat) refSnapshot refRestore core073_seedExplicit ∧
      ¬ CORE_073 (T := Nat) refSnapshot refRestore core073_seedExplicit := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := CORE_073_reference (T := Nat)
  refine ⟨⟨h1, h2, h3, h4, fun s E hE M => ?_, fun s => ?_⟩, fun h => ?_⟩
  · simp [core073_seedExplicit, hE]
  · simp [core073_seedExplicit, core073_nil_not_holds]
  · have hok : (core073_seedExplicit (some [("a", [1])]) [("b", [])] :
        Except String (QMarking String Nat)) = .ok (refRestore [("b", [])]) := by
      simp [core073_seedExplicit, HoldsToken]
    have := congrFun (h.2.2.2.2.2.2 [("a", [1])] [("b", [])] _ (by decide) hok) "a"
    revert this
    decide

/-- ? Whether an explicit initial marking that names places but holds no token, given with a
restore, is rejected is not settled: the reference accepts it and the Java/TypeScript seed rejects
it, and both meet CORE-073, line 7 included (ruling D84 (a), the middle case). What an accepted one
seeds is settled by line 7. -/
@[evidence undecided CORE_073]
theorem CORE_073_undecided_emptyEntries :
    CORE_073 (T := Nat) refSnapshot refRestore refSeed ∧
      CORE_073 (T := Nat) refSnapshot refRestore core073_seedMap ∧
      (refSeed (some [("a", [1])]) [("b", [])] : Except String (QMarking String Nat)).toBool
        = true ∧
      (core073_seedMap (some [("a", [1])]) [("b", [])] :
        Except String (QMarking String Nat)).toBool = false := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := CORE_073_reference (T := Nat)
  refine ⟨CORE_073_reference, ⟨h1, h2, h3, h4, fun s E hE M => ?_, fun s => rfl,
    fun s E M _ hM => ?_⟩, by decide, by decide⟩
  · have hne : E.isEmpty = false := by
      obtain ⟨e, he, -⟩ := (holdsToken_iff E).mp hE
      cases E with
      | nil => exact absurd he List.not_mem_nil
      | cons _ _ => rfl
    simp [core073_seedMap, hne]
  · cases E with
    | nil => simp [core073_seedMap] at hM; exact hM.symm
    | cons e E => simp [core073_seedMap] at hM

/-! ## CORE-073 (T): seeding a resume -/

requirement CORE_073_T
  id "CORE-073"
  title "Marking Snapshot and Restore (resume timing)"
  kind T
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  quote "*When* a restored marking seeds a new executor, that executor's initial marking *shall* hold on every place the token count the restored marking holds there, whether or not the net declares the place ([CORE-072])."
        "*When* execution resumes from a restored marking, each transition of the net that the restored marking enables *shall* be armed with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 whatever the `created_at` of the restored tokens ([TIME-010])."
  reading "Let Restore be the restore (Restore s: the queue marking the snapshot s restores) and Rs the resume (Rs X s now0: the timed state a new executor of the timed net X starts from when the snapshot s seeds it and its firing clock first reads now0)."
          "For every timed net X, snapshot s and reading now0: the marking of Rs X s now0 is the token count of Restore s, on every place, declared or not."
          "For every timed net X, snapshot s, reading now0 and transition u of X that the counts of Restore s enable: u's stamp in Rs X s now0 is that state's own clock reading."
  assumes "The model is the pair (Restore, Rs). Restore is CORE_073's restore, at any place type. Rs is the resume: like CORE-072's initialiser (glossary: Init), but from a snapshot, whose counts are all the timed state (TSt, Phase 1) carries. The witness is refRestore and refResume, the reference initialiser TSt.init on the counts of the restored marking at the resuming reading (Reference/Snapshot.lean). Armed, Elapsed time, Enabled and Unknown place are the glossary terms; transitions are identified by name (ruling D10, InNet)."
          "Line 1 is the first quoted sentence and AC2 (a restored marking pre-populates places exactly like any other initial marking): on counts, on every place, the undeclared ones included (the third bullet of the form, CORE-072). A resume that keeps only the places the net lists violates it (CORE_073_T_mutant_marking_killed). That the restored tokens themselves, values and created_at, seed the executor unchanged whatever its epoch clock (AC9's executor side, the quoted sentence before this block's first quote) is the F block's line 6 for every executor, with its lines 1 and 3 (CORE_073_forbids_restampSeed); this block's timed state carries counts only."
          "Line 2 is the second quoted sentence, the paragraph 'The preserved created_at is token metadata' and the first sentence of the frequency paragraph ('Every restore restarts every clock', TIME-011): an enabled transition is stamped with the resumed state's own clock reading, so its elapsed time is 0 (core073T_elapsed) whatever the stamps of the restored tokens. With line 1 it is CORE-072's InitArms on the restored counts (core073T_initArms), and an initialiser that meets CORE-072 gives a resume that meets this block (core073T_of_core072). A resume that stamps from the tokens' created_at violates it (CORE_073_T_mutant_stamp_killed, at T := value and created_at), and so does a resume stamped when the executor was built, before the run starts (CORE_073_T_forbids_constructorStamp). As in CORE-072, the line fixes the stamp relative to the clock, not the clock reading itself: now0 is not constrained, so a resume that restarts its firing clock at 0 and stamps 0 meets the block, and is observationally equal under the reference timed step since elapsed time is a difference. How an injected epoch clock relates to the restored created_at (the NU-022 note) is TIME-015's. The line does not cover a terminal place marked by the restored marking (EXEC-042, RefExec)."
          "AC3 (a Delayed or Window transition enabled by restored tokens waits its full interval from the resuming executor's enablement) is core073T_not_ready_after: after a delay shorter than the earliest bound from the resume, the transition is not ready under the reference timed step (TIME-010, TIME-004, TIME-005), and core073T_no_fire: it does not fire there. Both are shown for one delay step taken directly from the resumed state; several delay steps in a row, or firings of other transitions between the resume and the decision, are the reference timed step's own lines (TIME-010), which this block feeds with the resuming stamp."
          "AC4 (a Deadline(d) transition enabled by restored tokens is reaped once its elapsed time from the resuming stamp is strictly greater than d plus the deadline tolerance, ruling D4 and the AC4 rewording R-CC5) is core073T_expired_after: after one delay step from the resume, a reapable transition still enabled is expired exactly when the delay exceeds its latest bound plus the tolerance (TIME-003); that an expired transition is then reaped is TIME-013's step, not this block's. No TransitionTimedOut for the original budget is the event model's (EVT-009, W7); in this model no stamp survives the resume, so no original budget exists."
          "AC5 (restoring at an interval shorter than d never fires a Delayed(d) transition) is core073T_no_fire for one segment: each restore is a resume, and between two resumes less than d apart the clock advances by less than d, so the gate of TIME-010 is never passed. Restoring repeatedly is a sequence of such segments, each starting from a fresh resume; the block shows the segment, and the sequence is the host's loop, not a further line. The paragraph 'The fresh clock is safe for lower bounds and unsafe for upper bounds', its MUST NOT on the host, and the SHOULD to state the frequency bound are advice to hosts and implementations about the contract, not checkable lines."
  signoff "2026-11-13 780f44c3d032f165 ai"
  statement : ∀ {N T : Type} [DecidableEq N], (QSnap N T → QMarking N T) →
      (TimedNet N → QSnap N T → Nat → TSt N) → Prop :=
    fun Restore Rs =>
      (∀ X s now0, (Rs X s now0).m = qCount (Restore s)) ∧
      (∀ X s now0 u, InNet X u → Enabled u (qCount (Restore s)) →
        (Rs X s now0).stamp u.core.name = some (ClockReading (Rs X s now0)))

/- The pinned readable form of CORE-073 (T): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_073_T : {N T : Type} →
  [DecidableEq N] → (QSnap N T → QMarking N T) → (TimedNet N → QSnap N T → ℕ → TSt N) → Prop :=
fun {N T} [DecidableEq N] Restore Rs =>
  (∀ (X : TimedNet N) (s : QSnap N T) (now0 : ℕ), (Rs X s now0).m = qCount (Restore s)) ∧
    ∀ (X : TimedNet N) (s : QSnap N T) (now0 : ℕ) (u : Reference.Trans N),
      InNet X u → Enabled u (qCount (Restore s)) → (Rs X s now0).stamp u.core.name = some (ClockReading (Rs X s now0))
-/
#guard_msgs in #print CORE_073_T

/-! ### The reference -/

/-- ✓ The reference pair satisfies CORE-073 (T): the resume holds the restored counts
(`resume_marking`) and stamps every enabled transition of the net with the resuming reading
(`resume_initArms`). -/
@[evidence holds CORE_073_T]
theorem CORE_073_T_reference {N T : Type} [DecidableEq N] :
    CORE_073_T (N := N) (T := T) refRestore refResume :=
  ⟨resume_marking, fun X s now0 _ hu he => (resume_initArms X s now0 hu).2 he⟩

/-! ### Consequences -/

section TConsequences

variable {N T : Type} [DecidableEq N] {Restore : QSnap N T → QMarking N T}
  {Rs : TimedNet N → QSnap N T → Nat → TSt N}

/-- An initialiser that meets CORE-072 meets CORE-073 (T) on the restored counts: seeding a
restore is initialising with the restored marking ([CORE-072], AC2). -/
theorem core073T_of_core072 {I : Init N} {R : TRel N} {Q : QFireRel N T}
    (h : CORE_072 I R Q) (Restore : QSnap N T → QMarking N T) :
    CORE_073_T Restore (fun X s now0 => I X (qCount (Restore s)) now0) :=
  ⟨fun X _ now0 => h.1 X _ now0, fun X _ now0 u hu he => h.2.1 X _ now0 u hu he⟩

/-- **Every restore restarts every clock**: a transition of the net is armed in the resumed
state exactly when the restored marking enables it, with the resumed state's reading as its
stamp (CORE-072's `InitArms`, on the restored counts). -/
@[evidence cites "TIME-011" "a restore restarts every clock (CORE-073): under CORE-073 (T), every transition of the net that the restored marking enables is armed in the resumed state with that state's own clock reading as its stamp, so no stamp from before the restore survives"]
theorem core073T_initArms (h : CORE_073_T Restore Rs) (X : TimedNet N) (s : QSnap N T)
    (now0 : Nat) {u : Trans N} (hu : InNet X u) :
    (Armed (Rs X s now0) u ↔ Enabled u (qCount (Restore s))) ∧
      (Enabled u (qCount (Restore s)) →
        (Rs X s now0).stamp u.core.name = some (ClockReading (Rs X s now0))) := by
  refine ⟨⟨fun ha => ?_, fun he => ⟨?_, ?_⟩⟩, h.2 X s now0 u hu⟩
  · have := ha.1
    rwa [show (Rs X s now0).m = qCount (Restore s) from h.1 X s now0] at this
  · show Enabled u (Rs X s now0).m
    rw [h.1 X s now0]; exact he
  · rw [h.2 X s now0 u hu he]; rfl

/-- A transition of the net enabled by the restored marking starts with elapsed time 0. -/
theorem core073T_elapsed (h : CORE_073_T Restore Rs) {X : TimedNet N} {s : QSnap N T}
    {now0 : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u (qCount (Restore s))) :
    Elapsed (Rs X s now0) u = 0 := by
  simp [Elapsed, h.2 X s now0 u hu he]

/-- After the clock advances by `δ` from the resume (the reference timed step), a transition of
the net enabled by the restored marking is armed with elapsed time exactly `δ`. -/
theorem core073T_after_delay (h : CORE_073_T Restore Rs) {X : TimedNet N} {s : QSnap N T}
    {now0 δ : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u (qCount (Restore s)))
    {s' : TSt N} (hst : RefTStep X (Rs X s now0) (.delay δ) s') :
    Armed s' u ∧ Elapsed s' u = δ := by
  cases hst
  have hst := h.2 X s now0 u hu he
  have ha := ((core073T_initArms h X s now0 hu).1).mpr he
  refine ⟨⟨ha.1, by simp [hst]⟩, ?_⟩
  simp [Elapsed, hst, ClockReading]

/-- **AC3**: after a delay shorter than its earliest bound from the resume, a transition enabled
by the restored marking is not ready, whatever the `created_at` of the restored tokens. -/
theorem core073T_not_ready_after (h : CORE_073_T Restore Rs) {X : TimedNet N} {s : QSnap N T}
    {now0 δ : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u (qCount (Restore s)))
    {s' : TSt N} (hst : RefTStep X (Rs X s now0) (.delay δ) s')
    (hδ : δ < (TimingOf X u).earliest) : ¬ Ready X s' u := by
  rintro ⟨-, hg, -⟩
  rw [(core073T_after_delay h hu he hst).2] at hg
  omega

/-- **AC3, AC5**: from the state a delay shorter than its earliest bound after the resume, the
transition does not fire under the reference timed step. Between two restores less than `d`
apart, a `Delayed(d)` transition therefore never fires. -/
theorem core073T_no_fire (h : CORE_073_T Restore Rs) {X : TimedNet N} {s : QSnap N T}
    {now0 δ : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u (qCount (Restore s)))
    {s' : TSt N} (hst : RefTStep X (Rs X s now0) (.delay δ) s')
    (hδ : δ < (TimingOf X u).earliest) {d : List N} {s'' : TSt N} :
    ¬ RefTStep X s' (.fire u d) s'' := by
  intro hf
  exact core073T_not_ready_after h hu he hst hδ (refTStep_fire_inv hf).2.2.1

/-- **AC4**: after a delay of `δ` from the resume, a reapable transition enabled by the restored
marking is expired exactly when `δ` exceeds its latest bound plus the deadline tolerance: the
bound is measured from the resuming stamp, never from the original enablement. -/
theorem core073T_expired_after (h : CORE_073_T Restore Rs) {X : TimedNet N} {s : QSnap N T}
    {now0 δ : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u (qCount (Restore s)))
    (hr : Reapable X u) {s' : TSt N} (hst : RefTStep X (Rs X s now0) (.delay δ) s') :
    Expired X s' u ↔ (TimingOf X u).latest + Tolerance X < δ := by
  obtain ⟨ha, hel⟩ := core073T_after_delay h hu he hst
  simp only [Expired, hel]
  exact ⟨fun hx => hx.2.2, fun hx => ⟨hr, ha, hx⟩⟩

end TConsequences

/-! ### Examples -/

/-- `u`: one input arc on place 1, output place 2. -/
def core073T_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The timed net: `u` alone, `Delayed(5)`, tolerance 0; it lists places 1 and 2. -/
def core073T_X : TimedNet Nat :=
  { net := { places := [1, 2], transitions := [core073T_u] },
    timing := fun _ => .delayed 5, tol := 0 }

/-- A snapshot holding one token on place 1, value 10 stamped 0 (an old token), and one token on
the undeclared place 9. -/
def core073T_s : QSnap Nat (Nat × Nat) := [(1, [(10, 0)]), (9, [(90, 0)])]

theorem core073T_u_inX : InNet core073T_X core073T_u := rfl

theorem core073T_u_enabled : Enabled core073T_u (qCount (refRestore core073T_s)) := by decide

/-- ✓ CORE-073 (T) is not vacuous. Resumed at reading 100 from a snapshot whose token on place 1
was stamped 0, the reference arms `u` with the stamp 100 and elapsed time 0, so its `Delayed(5)`
is not passed; the undeclared place 9 keeps its token; and after a delay of 5 the transition is
ready. -/
@[evidence nonvacuous CORE_073_T]
theorem CORE_073_T_nonvacuous :
    Armed (refResume core073T_X core073T_s 100) core073T_u ∧
    (refResume core073T_X core073T_s 100).stamp "u" = some 100 ∧
    Elapsed (refResume core073T_X core073T_s 100) core073T_u = 0 ∧
    ¬ Ready core073T_X (refResume core073T_X core073T_s 100) core073T_u ∧
    (refResume core073T_X core073T_s 100).m 9 = 1 ∧
    Ready core073T_X { refResume core073T_X core073T_s 100 with now := 105 } core073T_u := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Mutant: line 1, a resume that keeps only the places the net lists -/

section TMutants

variable {N T : Type} [DecidableEq N]

/-- A resume whose store keeps only the places the net lists: a token restored on an undeclared
place is dropped. -/
def core073T_declaredOnly (X : TimedNet N) (s : QSnap N T) (now0 : Nat) : TSt N :=
  { refResume X s now0 with
    m := fun p => if p ∈ X.net.places then qCount (refRestore s) p else 0 }

/-- Mutant reading of CORE-073 (T) with line 1 on the places the net lists only. -/
def CORE_073_T_mutant_marking (Restore : QSnap N T → QMarking N T)
    (Rs : TimedNet N → QSnap N T → Nat → TSt N) : Prop :=
  (∀ X s now0 p, p ∈ X.net.places → (Rs X s now0).m p = qCount (Restore s) p) ∧
  (∀ X s now0 u, InNet X u → Enabled u (qCount (Restore s)) →
    (Rs X s now0).stamp u.core.name = some (ClockReading (Rs X s now0)))

/-- Mutant reading of CORE-073 (T) with line 2 as arming only: an enabled transition holds some
stamp, not necessarily the resuming reading. -/
def CORE_073_T_mutant_stamp (Restore : QSnap N T → QMarking N T)
    (Rs : TimedNet N → QSnap N T → Nat → TSt N) : Prop :=
  (∀ X s now0, (Rs X s now0).m = qCount (Restore s)) ∧
  (∀ X s now0 u, InNet X u → Enabled u (qCount (Restore s)) →
    ((Rs X s now0).stamp u.core.name).isSome)

end TMutants

/-- ✗ The declared-only resume kills the mutant: it holds the restored counts on every place the
net lists and stamps like the reference, but the token restored on the undeclared place 9 is
gone (line 1, AC2, AC7). -/
@[evidence mutant CORE_073_T]
theorem CORE_073_T_mutant_marking_killed :
    CORE_073_T_mutant_marking (N := Nat) (T := Nat × Nat) refRestore core073T_declaredOnly ∧
      ¬ CORE_073_T (N := Nat) (T := Nat × Nat) refRestore core073T_declaredOnly := by
  refine ⟨⟨fun X s now0 p hp => by simp [core073T_declaredOnly, hp],
    fun X s now0 u hu he => (resume_initArms X s now0 hu).2 he⟩, fun h => ?_⟩
  have := congrFun (h.1 core073T_X core073T_s 100) 9
  revert this
  decide

/-- The oldest `created_at` among a snapshot's tokens, or the reading `now0` without a token. -/
def core073T_oldest {N : Type} (s : QSnap N (Nat × Nat)) (now0 : Nat) : Nat :=
  (s.flatMap (·.2)).foldr (fun x acc => min x.2 acc) now0

/-- A resume that stamps every armed transition with the oldest `created_at` of the restored
tokens, as if the original enablement carried over. -/
def core073T_staleResume {N : Type} [DecidableEq N] (X : TimedNet N) (s : QSnap N (Nat × Nat))
    (now0 : Nat) : TSt N :=
  { refResume X s now0 with
    stamp := fun n => ((refResume X s now0).stamp n).map fun _ => core073T_oldest s now0 }

/-- ✗ The stale-stamp resume kills the mutant: it holds the restored counts and arms every
enabled transition, but resumed at reading 100 it stamps `u` with the token's `created_at` 0, so
`u` passes its `Delayed(5)` at once (line 2, AC3). -/
@[evidence mutant CORE_073_T]
theorem CORE_073_T_mutant_stamp_killed :
    CORE_073_T_mutant_stamp (N := Nat) refRestore core073T_staleResume ∧
      ¬ CORE_073_T (N := Nat) refRestore core073T_staleResume := by
  refine ⟨⟨fun X s now0 => rfl, fun X s now0 u hu he => ?_⟩, fun h => ?_⟩
  · simp [core073T_staleResume, (resume_initArms X s now0 hu).2 he]
  · have := h.2 core073T_X core073T_s 100 core073T_u core073T_u_inX core073T_u_enabled
    revert this
    decide

/-! ### Forbidden: a resume stamped when the executor was built -/

/-- A resume stamped at the reading the clock had when the executor was constructed from the
snapshot, `lag` before the run, and so the resume, starts at `now0`: the reference, with every
stamp taken at `now0 - lag`. -/
def core073T_constructorStamp (lag : Nat) {N T : Type} [DecidableEq N] (X : TimedNet N)
    (s : QSnap N T) (now0 : Nat) : TSt N :=
  { refResume X s now0 with
    stamp := fun n => ((refResume X s now0).stamp n).map fun _ => now0 - lag }

/-- ✗ CORE-073 (T) forbids stamping at construction: built 5 before the run starts at 100, `u` is
stamped 95, so its `Delayed(5)` is passed the moment the run starts (line 2, AC3). -/
@[evidence forbids CORE_073_T]
theorem CORE_073_T_forbids_constructorStamp :
    ¬ CORE_073_T (N := Nat) (T := Nat × Nat) refRestore (core073T_constructorStamp 5) := by
  intro h
  have := h.2 core073T_X core073T_s 100 core073T_u core073T_u_inX core073T_u_enabled
  revert this
  decide

/-- The constructor-stamped resume makes `u` ready at once. -/
theorem core073T_constructorStamp_ready :
    Ready core073T_X (core073T_constructorStamp 5 core073T_X core073T_s 100) core073T_u := by
  decide

/-! ## The two blocks together -/

/-- The reference meets both blocks with one restore at `N := String`. -/
theorem core073_joint :
    CORE_073 (T := Nat) refSnapshot refRestore refSeed ∧
      CORE_073_T (N := String) (T := Nat) refRestore refResume :=
  ⟨CORE_073_reference, CORE_073_T_reference⟩

/-- Over one restore, the two blocks fix the resumed counts of every snapshot whose names are
pairwise distinct: they are the reference resume's, since every restore that meets the F block
is `refRestore` on such a snapshot (`core073_restore_eq`). -/
theorem core073_joint_counts {T : Type} {Snap : FinQ String T → QSnap String T}
    {Restore : QSnap String T → QMarking String T}
    {Seed : Option (QSnap String T) → QSnap String T → Except String (QMarking String T)}
    {Rs : TimedNet String → QSnap String T → Nat → TSt String}
    (hF : CORE_073 Snap Restore Seed) (hT : CORE_073_T Restore Rs) (X : TimedNet String)
    {s : QSnap String T} (hnd : QKeysNodup s) (now0 : Nat) :
    (Rs X s now0).m = (refResume X s now0).m := by
  rw [hT.1 X s now0, core073_restore_eq hF hnd, resume_marking]

end Libpetri.Spec
