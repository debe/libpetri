import Mathlib.Data.List.Lex
import Libpetri.Spec.ConsistencyNu
import Libpetri.Spec.Req.NU_040
import Libpetri.Spec.Req.NU_050
import Libpetri.Spec.Req.CORE_013
import Libpetri.Spec.Req.IO_003
import Libpetri.Spec.Req.NU_052
import Libpetri.Novel.RouteA.Retrodict
import Libpetri.Novel.RouteB.Decide

set_option linter.missingDocs true

/-!
# The ν clashes (NU-001 to NU-060), after the rulings

The confirmed clashes of plan section 6 that touch a ν requirement and have a block to speak
of in wave W9, stated over the reference ν firing `RefNuFire`, the reference selection
`refSelect`, the reference builders `refMatchBuild` and `refNuBuild` (`Reference/Nu.lean`) and the
Route A and Route B models of `Novel/`. Every ruling is decided (plan section 5, accepted
2026-11-10); each theorem below records the evidence for the decided reading, never a reading the
user rejected.

Where every block the clash names exists, the evidence is `consistent`: one reference meets those
blocks together, and a small marking decided on it shows the case the clash was about, read the
way the ruled text says. Where the clash is about a sentence that has no block (NU-052's demand,
VER-012's exactness, the Route A fragment of NU-053's slot bound), the candidate readings are
plain definitions here and the evidence is a citation of the spec ID (as in `ClashesExec.lean`):
the registry's `conflict` and `ambiguity` roles name requirement blocks only.

| Clash | Ruling | Evidence here |
|---|---|---|
| nu-a#1, conc-b#2, core-a#7 (count-level sentences against the ν take) | D30 (a), ruled D16 | `clashNu_countLevel`: the queue and count blocks hold of the match-free firings, and the ν firing on AC1 takes a token that is not a prefix of its queue, and on AC3 leaves a token in a correlated `All` place |
| nu-a#2, nu-b#4, core-a#8 ('oldest matched token') | D31 (a) | `clashNu_oldest`: a name whose earliest token sits behind a newer one; the selection reads the earliest `createdAt` over every token, the firing takes the queue's first token of the name, and the consumed-only reading picks the other name |
| nu-a#3, nu-b#5 (identical firing across languages) | D31 (a) | `clashNu_nameOrder`: code-point and UTF-16 names both meet NU-001 and NU-022, agree on BMP names, and pick different names on a tie between U+FFFF and U+10000 |
| nu-a#4, nu-a#5 (fewer than two keys, a key with no name) | D37 (a) | `clashNu_keys`: the match builder rejects one key, a raw one-key match builds and fires by name, and a token with no name is skipped and stays |
| nu-a#8 (one fresh name per firing or per place) | D78 (a) | `clashNu_mintOneFresh`: NU-010's contract block holds of a fork that writes its one minted name into two places; its contract `MintContract` is Route B's mint contract, and a write of two different fresh names meets the per-place reading only |
| nu-b#1 (Violated or Unknown on a truncated graph) | D59 (a) | `clashNu_prefix`: NU-050's verdict block holds of the shipped verdict; an unclosed graph with a violating stored class answers Violated, one without answers Unknown, Proven needs a closed graph, and a safety Violated names a reachable bad class |
| nu-b#2 (the Route A fragment: budget or slot bound) | D59 (a) | `clashNu_budgetCount`: the budget count as colour bound proves a false bound on a net that reaches two live names, and the colour-slot plan refuses that net |
| nu-b#3, ver-d#1 ('exact' for a closed Route B graph) | D59 (a) | `clashNu_freeChoice`: two names are eligible at AC1's join, so the graph may join on either, while every reference firing joins on the selected one |
| nu-b#8 (count quiescence on a matched net) | D20 | `clashNu_countRest`: NU-040's joined-or-dead-lettered block holds of the reference predicate; a join enabled on its counts with no name in both branches is not ν-enabled, the net rests with the join not reapable, and the pending token there is a violation |
| nu-c#3 (a demand: required count or tokens consumed) | D97 (a) | `clashNu_demand`: two `All` arcs on a place with two tokens compete under the tokens-consumed reading and not under the required count; the required count never prunes where the other reading does not |

Not here:

* Editorial clashes with no change of behaviour (D20): nu-a#9 (the glossary entry Build-time
  checks; its evidence is `NuBuildExtends` in `ConsistencyNu.lean`), nu-a#10, nu-b#6, nu-b#9,
  nu-c#1, nu-c#7, nu-c#9 and nu-c#10. nu S3 (NU-010 AC6) is a pipeline
  line of NU-010 (P2).
* Clashes carried by the lines of a block of this wave: nu-a#6, nu-a#7 and nu S9 (ruling D56)
  by `NU_010_unique`, `NU_010_replay`, `NU_011_format`, `NU_011_lineage` and `NU_011_host` over the
  mint system (the replay exception of nu-a#7 is `NU_011_host`'s formula); nu-b#7 and composition
  S7 (ruling D81) by `NU_060`'s second line; core-a#13 (ruling D64) by NU-054's blocks and
  CORE-012.
* Clashes whose evidence is a line of a block of a later wave: nu-c#8 (ruling D24) to
  `NU_054_fail` on RefExec (W11; the executor half is `clashExec_timeoutValidated_conflict`);
  evt-a#5 (ruling D98) to EVT-002 (W7) and NU-011; nu-b#10 (D20, D5, D7) to the TIME-012 ν-join
  line on RefExec with the ν kernel (W11); ver-a#11 (ruling D40) to VER-003 (W10).
* Clashes already carried by an existing block: nu-c#4 (NU_052's assumes, ruling D97), nu-c#5
  and nu-c#6 (NU_053, ruling D80), nu-c#2 (the carrier line of NU-051, ruling D95, wave W10).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

namespace ClashNu

/-! ## Candidate readings and small markings -/

/-- CORE-013 and CONC-022 AC2 read for every ν firing: every input place delivers a prefix of
its queue, oldest first. -/
def LiteralOldestFirst {N V Nm : Type} [DecidableEq N] (NF : NuFireRel N V Nm) : Prop :=
  ∀ t M c δ e M' p, NF t M c δ e M' → p ∈ inPlaces t.base → ∃ k, δ.inputs p = OldestFirst M p k

/-- IO-003 read for every ν firing: an `All` input place that is not an output place ends
empty. -/
def LiteralAllDrains {N V Nm : Type} [DecidableEq N] (NF : NuFireRel N V Nm) : Prop :=
  ∀ t M c δ e M' p, NF t M c δ e M' → InputArc t.base p .all → ¬ OutputArc t.base p → M' p = []

/-- A marking of AC1's join: place 0 holds X stamped 5, X stamped 3 (a token forwarded with its
old stamp, IO-014) and Y stamped 4; place 1 holds Y stamped 6 and X stamped 7 (X = 1, Y = 2). -/
def clashNuStale : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 1 5, nu020_tok 1 3, nu020_tok 2 4]
  else if p = 1 then [nu020_tok 2 6, nu020_tok 1 7] else []

/-- A name as Java and TypeScript hold it: a string ordered by its UTF-16 code units. -/
structure Utf16Name where
  /-- The string value of the name. -/
  s : String

instance : LinearOrder Utf16Name :=
  LinearOrder.lift' (fun x => nu001Utf16 x.s)
    (fun a b h => by cases a; cases b; exact congrArg _ (nu001Utf16_inj h))

/-- One correlated input holding U+FFFF and U+10000, both stamped 4, code-point names. -/
def clashNuTieS : MatchIn String := ⟨[([("￿", 4), ("𐀀", 4)], 1)]⟩

/-- The same input with UTF-16 names. -/
def clashNuTieU : MatchIn Utf16Name := ⟨[([(⟨"￿"⟩, 4), (⟨"𐀀"⟩, 4)], 1)]⟩

/-- A match with one key, on place 0, of a transition with the one input place 0. -/
def clashNuOneKey {K : Type} (k : K) : NuTrans Nat K :=
  { base := { core := { name := "one", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := none }
    mspec := some { keys := [(0, k)] } }

/-- Place 0 holds Y stamped 1, then X stamped 0. -/
def clashNuOneM : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu020_tok 2 1, nu020_tok 1 0] else []

/-- An explorer over numbered classes with no successor. -/
def clashNuE : Explorer ℕ ℕ String := ⟨id, fun _ => 0, fun _ _ => []⟩

/-- A build that stored classes 0 and 1, expanded class 0, did not close and did not stop. -/
def clashNuCut : Novel.RouteB.Decide.Out ℕ := ⟨[0, 1], 1, false, false, false⟩

/-- NU-050 AC2 read literally: a graph that does not close answers Unknown. -/
def UnknownWhenOpen {S K L : Type} (E : Explorer S K L) : Prop :=
  ∀ (o : Novel.RouteB.Decide.Out S) p, o.complete = false →
    Novel.RouteB.Decide.verdict E o p = .unknown

/-- The demand of `t` on `p` read as the tokens one firing consumes at the count marking `a`:
all of them for `All` and `AtLeast`, the required count otherwise. -/
def consumedDemandOn (a : AMarking) (t : Transition) (p : PlaceId) : ℕ :=
  ((t.inputs.filter fun s => s.place == p).map fun s =>
    if s.card.consumesAll then a p else s.card.required).sum

/-- Competition with the demand read as the tokens consumed. -/
def consumedCompete : Compete := fun a H L =>
  H.inputs.any fun sh =>
    L.inputs.any (fun sl => sl.place == sh.place)
      && decide (a sh.place < consumedDemandOn a H sh.place + consumedDemandOn a L sh.place)

/-- A transition draining place 0 at priority 10. -/
def clashNuAllH : Transition := nu052_tr "hi" 10 [⟨0, .all, none⟩]

/-- A transition draining place 0 at priority 0. -/
def clashNuAllL : Transition := nu052_tr "lo" 0 [⟨0, .all, none⟩]

/-- Under the premise that every draining arc's place holds its required count, the required
count is at most the tokens consumed. -/
theorem demandOn_le_consumed {a : AMarking} {t : Transition} {p : PlaceId}
    (h : ∀ s ∈ t.inputs, s.place = p → s.card.consumesAll = true → s.card.required ≤ a p) :
    Novel.RouteB.demandOn t p ≤ consumedDemandOn a t p := by
  unfold Novel.RouteB.demandOn consumedDemandOn
  apply List.sum_le_sum
  intro s hs
  have hs' := List.mem_filter.1 hs
  have hp : s.place = p := by simpa using hs'.2
  by_cases hc : s.card.consumesAll = true
  · simp only [hc, if_true]; exact h s hs'.1 hp hc
  · simp [hc]

end ClashNu

open ClashNu

/-! ## nu-a#1, conc-b#2, core-a#7: the count-level sentences (ruling D30 (a), ruled D16) -/

/-- On AC1's marking the reference join takes X stamped 1 from place 1, whose queue starts with Y:
not a prefix of the queue. -/
theorem clashNu_ac1_notPrefix :
    ¬ LiteralOldestFirst (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) := by
  intro h
  obtain ⟨k, hk⟩ := h _ _ _ _ _ _ 1 NU_020_enable_nonvacuous.1 (by decide)
  have h1 : (nuDelivered nu020_ms (nu020_join .one .one) nu020_ac1 1).inputs 1 =
      [nu020_tok 1 1] := by decide
  rw [h1] at hk
  unfold OldestFirst at hk
  rcases k with _ | _ | k <;> simp [nu020_ac1, nu020_tok] at hk

/-- On AC3's marking the reference join with a correlated `All` on place 0 leaves Y in place 0. -/
theorem clashNu_ac3_notDrained :
    ¬ LiteralAllDrains (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) := by
  intro h
  have := h _ _ _ _ _ _ 0 NU_020_ac3.1 ⟨⟨0, .all⟩, rfl, rfl⟩
    (by rintro ⟨o, ho, -⟩; cases ho)
  exact absurd this (by decide)

/-- ✓ **nu-a#1, conc-b#2, core-a#7, ruling D30 (a).** The count-level sentences (CORE-013's
oldest first, IO-003's `All` drains, CONC-022 AC2) hold of every firing without a match, and not of
a matched one. Worked example: on AC1's marking (A = X, Y; B = Y, X) the join takes X from B
although B's queue starts with Y, and on AC3's marking a correlated `All` on A = X, Y, X takes both
X and leaves Y. The queue blocks CORE-013 and EXEC-010 and the count block IO-003 hold of the
reference queue firing, which is the reference ν firing on every transition without a match, and
NU-020's take and frame blocks hold of the ν firing. So the exclusion of correlated inputs that
ruling D30 adds to those sentences makes them consistent with NU-020. -/
@[evidence consistent CORE_013 EXEC_010 IO_003 NU_020_take NU_020_frame]
theorem clashNu_countLevel :
    CORE_013 (RefQFire (N := Nat) (T := Stamped Nat)) ∧
      EXEC_010 (RefQFire (N := Nat) (T := Stamped Nat)) ∧ IO_003 (RefFire (N := Nat)) ∧
      QProjectsTo (RefQFire (N := Nat) (T := Stamped Nat)) RefFire ∧
      NU_020_take (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      NU_020_frame (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      NuRestrictsTo (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) RefQFire ∧
      ¬ LiteralOldestFirst (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      ¬ LiteralAllDrains (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) :=
  ⟨CORE_013_reference, EXEC_010_reference, IO_003_reference, refQFire_projectsTo,
    NU_020_take_reference, NU_020_frame_reference, refNuFire_restrictsTo,
    clashNu_ac1_notPrefix, clashNu_ac3_notDrained⟩

/-! ## nu-a#2, nu-b#4, core-a#8: which tokens make a name 'oldest' (ruling D31 (a)) -/

/-- ✓ **nu-a#2, nu-b#4, core-a#8, ruling D31 (a).** Worked example: place 0 holds X@5, X@3, Y@4
and place 1 holds Y@6, X@7 (X@3 was forwarded with its old stamp). X's earliest `createdAt` over
all its tokens is 3 and Y's is 4, so the selection joins on X. The firing then takes from place 0
the first X in the queue, X@5, which is also the head of the queue: the 'oldest token' of CORE-013
(first added) is not the token with the earliest `createdAt` that ranks the name. Counting only the
tokens a firing would consume, X ranks at 5 and Y at 4, so that reading picks Y; it breaks NU-022
while the reference meets NU-022 and NU-020's enablement and take blocks. -/
@[evidence consistent NU_020_enable NU_020_take NU_022]
theorem clashNu_oldest :
    NU_020_enable (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      NU_020_take (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      NU_022 (refSelect (Nm := Nat)) ∧
      NuSelectsBy (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) refSelect ∧
      ¬ NU_022 nu022_consumedOnly ∧
      oldest (matchIn nu020_ms (nu020_join .one .one) clashNuStale) 1 = (3 : Int) ∧
      oldest (matchIn nu020_ms (nu020_join .one .one) clashNuStale) 2 = (4 : Int) ∧
      RefNuFire (nu020_join .one .one) clashNuStale (some 1)
        (nuDelivered nu020_ms (nu020_join .one .one) clashNuStale 1) []
        (qAppend (nuConsume nu020_ms (nu020_join .one .one) clashNuStale 1) []) ∧
      (clashNuStale 0).head? = some (nu020_tok 1 5) ∧
      nuInputs nu020_ms (nu020_join .one .one) clashNuStale 1 0 = [nu020_tok 1 5] ∧
      nu022_consumedOnly (matchIn nu020_ms (nu020_join .one .one) clashNuStale) = some 2 :=
  ⟨NU_020_enable_reference, NU_020_take_reference, NU_022_reference, refNuFire_selectsBy,
    NU_022_forbids_consumedOnly, by decide, by decide,
    ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_ms] at hr, rfl, rfl⟩,
    by decide, by decide, by decide⟩

/-! ## nu-a#3, nu-b#5: identical firing across languages (ruling D31 (a)) -/

/-- ✓ **nu-a#3, nu-b#5, ruling D31 (a).** Identical selection across languages is claimed for BMP
names only, because the name order is a parameter. Worked example: Rust orders names by code
point, Java and TypeScript by UTF-16 code unit. Both meet NU-001, the selection meets NU-022 at
either order, and the two orders agree on every pair of BMP names. One correlated input holds
U+FFFF and U+10000, both stamped 4: the code-point selection joins on U+FFFF, the UTF-16 one on
U+10000 (whose surrogate pair D800 DC00 precedes FFFF). -/
@[evidence consistent NU_001 NU_022]
theorem clashNu_nameOrder :
    NU_001 refNameImpl ∧ NU_001 utf16NameImpl ∧
      NU_022 (refSelect (Nm := String)) ∧ NU_022 (refSelect (Nm := Utf16Name)) ∧
      (∀ a b : String, (⟨a⟩ : Utf16Name) < ⟨b⟩ ↔ utf16NameImpl.lt a b) ∧
      (∀ a b : String, (∀ c ∈ a.toList, c.toNat < 0x10000) → (∀ c ∈ b.toList, c.toNat < 0x10000) →
        ((⟨a⟩ : Utf16Name) < ⟨b⟩ ↔ a < b)) ∧
      refSelect clashNuTieS = some "￿" ∧ refSelect clashNuTieU = some ⟨"𐀀"⟩ :=
  ⟨NU_001_reference, NU_001_allows_utf16.1, NU_022_reference, NU_022_reference,
    fun _ _ => Iff.rfl, fun a b ha hb => NU_001_utf16_bmp_agree a b ha hb, by decide, by decide⟩

/-! ## nu-a#4, nu-a#5: fewer than two keys, a key with no name (ruling D37 (a)) -/

/-- ✓ **nu-a#4, nu-a#5, ruling D37 (a).** Worked example: the match builder rejects a single key,
but a transition built on a raw path with one key on place 0 builds, and on place 0 = Y@1, X@0 it
joins on X (the earlier stamp) and takes X@0 although Y is first in the queue. With a partial key,
on place 0 = (no name)@0, X@1 and place 1 = X@2, the join fires on X, takes X@1 from place 0 and
leaves the token without a name there. NU-020's build, enablement and take blocks hold of the
references that do this. -/
@[evidence consistent NU_020_build NU_020_enable NU_020_take]
theorem clashNu_keys :
    NU_020_build (refMatchBuild (N := Nat) (K := Unit)) refNuBuild ∧
      NU_020_enable (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      NU_020_take (RefNuFire (N := Nat) (V := Nat) (Nm := Nat)) ∧
      refMatchBuild ([(0, ())] : List (Nat × Unit)) ≠ none ∧
      refNuBuild (clashNuOneKey ()) = none ∧
      RefNuFire (clashNuOneKey nu020_key) clashNuOneM (some 1)
        (nuDelivered { keys := [(0, nu020_key)] } (clashNuOneKey nu020_key) clashNuOneM 1) []
        (qAppend (nuConsume { keys := [(0, nu020_key)] } (clashNuOneKey nu020_key) clashNuOneM 1)
          []) ∧
      nuInputs { keys := [(0, nu020_key)] } (clashNuOneKey nu020_key) clashNuOneM 1 0 =
        [nu020_tok 1 0] ∧
      RefNuFire nu020_partialJoin nu020_noName (some 1)
        (nuDelivered nu020_partialMs nu020_partialJoin nu020_noName 1) []
        (qAppend (nuConsume nu020_partialMs nu020_partialJoin nu020_noName 1) []) ∧
      nuInputs nu020_partialMs nu020_partialJoin nu020_noName 1 0 = [nu020_tok 1 1] ∧
      qAppend (nuConsume nu020_partialMs nu020_partialJoin nu020_noName 1) [] 0 =
        [nu020_tok 0 0] :=
  ⟨NU_020_build_reference, NU_020_enable_reference, NU_020_take_reference, by decide, by decide,
    ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩, fun r hr => by simp at hr, rfl, rfl⟩,
    by decide,
    ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
      fun r hr => by simp [nu020_partialMs] at hr, rfl, rfl⟩,
    by decide, by decide⟩

/-! ## nu-a#8: one fresh name per firing (ruling D78 (a)) -/

/-- ✓ **nu-a#8, ruling D78 (a).** A declared mint writes one fresh name per firing, the same in
every coloured place it writes. Worked example: a fork that mints `fork#s:0` and writes it into
two coloured places keeps NU-010's contract block. The contract the analyses assume is
`MintContract` (one name, fresh at the marking, in every coloured place), which is Route B's
`Contract .mint` exactly and implies the per-place reading `EachFresh` (every written name is
fresh). A mint that writes name 1 into one coloured place and name 2 into another, both fresh,
meets the per-place reading and not the contract, and a join on the two places could then never
fire. -/
@[evidence consistent NU_010_contract]
theorem clashNu_mintOneFresh :
    NU_010_contract ["fork#s:0"] (fun (_ : Bool) => ["fork#s:0"]) ∧
      (∀ (co : List PlaceId) (T : Novel.RouteB.NuTrans) (M : Novel.RouteB.NM co) n hss wr,
        MintContract (fun i u => M u i ≠ 0) wr ↔ Novel.RouteB.Contract co .mint T M n hss wr) ∧
      (∀ (holds : Bool → ℕ → Prop) (wr : Bool → List ℕ),
        MintContract holds wr → Reference.EachFresh holds wr) ∧
      Reference.EachFresh (fun (_ : Bool) (_ : Nat) => False) (fun b => if b then [1] else [2]) ∧
      ¬ MintContract (fun (_ : Bool) (_ : Nat) => False) (fun b => if b then [1] else [2]) :=
  ⟨⟨fun _ _ hw => hw, fun _ _ _ hw _ hw' => by
      simp only [List.mem_singleton] at hw hw'
      rw [hw, hw']⟩,
    mintContract_iff_routeB, fun _ _ h => mintContract_eachFresh h,
    eachFresh_not_mintContract.1, eachFresh_not_mintContract.2⟩

/-! ## nu-b#1, nu-b#2, nu-b#3, ver-d#1: what a ν verdict claims (ruling D59 (a)) -/

/-- ✓ **nu-b#1, ruling D59 (a): the prefix rule.** A graph that does not close may answer
Violated, and NU-050's verdict block holds of the shipped verdict that does so. Worked example: a build stored classes 0 and 1 and did not close. For the safety
property 'class 1 is bad' Route B answers Violated at class 1; for 'class 2 is bad', which no
stored class is, it answers Unknown. So the literal reading 'an unclosed graph answers Unknown'
fails. Proven needs a closed build that did not stop, and a safety Violated off any build names
a stored class that is reachable and bad. -/
@[evidence consistent NU_050_prefix]
theorem clashNu_prefix :
    NU_050_prefix refClassVerdict ∧
    Novel.RouteB.Decide.verdict clashNuE clashNuCut (.safety fun x => x == 1) = .violated 1 ∧
      Novel.RouteB.Decide.verdict clashNuE clashNuCut (.safety fun x => x == 2) = .unknown ∧
      ¬ UnknownWhenOpen clashNuE ∧
      (∀ {S K L : Type} (E : Explorer S K L) (o : Novel.RouteB.Decide.Out S) p,
        Novel.RouteB.Decide.verdict E o p = .proven → o.complete = true ∧ o.stopped = false) ∧
      (∀ {S K L : Type} (E : Explorer S K L) {maxClasses : ℕ} {cut : ℕ → Bool}
        {stopBad bad : S → Bool} {stopAt : Bool} {fuel : ℕ} {x0 : S} {i : ℕ},
        Novel.RouteB.Decide.verdict E
            (Novel.RouteB.Decide.build E maxClasses cut stopBad stopAt fuel x0) (.safety bad) =
          .violated i →
        ∃ x, (Novel.RouteB.Decide.build E maxClasses cut stopBad stopAt fuel x0).cls[i]? = some x ∧
          Explorer.Reach E x0 x ∧ bad x = true) := by
  refine ⟨NU_050_prefix_reference, by decide, by decide, fun h => ?_, fun E o p h =>
    Novel.RouteB.Decide.truncated_never_proven E o p h,
    fun E _ _ _ _ _ _ _ _ h => Novel.RouteB.Decide.prefix_safety_sound (E := E) h⟩
  have := h clashNuCut (.safety fun x => x == 1) rfl
  exact absurd this (by decide)

open Libpetri.Novel.RouteA Libpetri.Novel.RouteA.Retro in
/-- ✓ **nu-b#2, ruling D59 (a): the Route A fragment is 'a colour-slot bound exists'.** Worked
example: on a net where two mints feed one join through a budget, the real net reaches a marking
with two live names in place `a`, but the one-slot encoding the budget count gives proves at most
one. No covering weighting exists for that net, so the colour-slot plan refuses it whatever the
simplex answers. So bounding the colours by the initial budget is unsound, and the fragment is
the one NU-053's slot bound certifies. -/
@[evidence cites "NU-050" "the Route A fragment is 'a colour-slot bound exists' ([NU-053]), not budget conservation (ruling D59 (a)): bounding the colours by the budget count proves a false bound on a net that reaches two live names, and the slot-bound plan refuses that net"]
theorem clashNu_budgetCount :
    (ReachNu CB rowsB m0B m4B ∧ alpha m4B 2 = 2 ∧
        ∀ invs e, ReachE (encB invs) e → agg CB 1 e 2 ≤ 1) ∧
      ∀ ans, colourSlotBoundLP 4 CB (rowsB.map CRow.flat) (alpha m0B) ans = none :=
  ⟨budget_k_false_proven, inflating_net_refused⟩

/-- ✓ **nu-b#3, ver-d#1, ruling D59 (a): 'exact' means sound against the executor and complete
against the free-choice graph.** Worked example: at AC1's join (A = X, Y; B = Y, X) both X and Y
are in both branches, so the Route B graph may join on either name. The reference executor joins
on X only: every firing of the join from that marking chooses X, and one does. -/
@[evidence cites "VER-012" "a closed Route B graph's verdict is sound against the executor and complete against the free-choice graph (ruling D59 (a)): at AC1's join two names are eligible, the graph may join on either, and every reference firing joins on the selected one"]
theorem clashNu_freeChoice :
    eligible (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 1 = true ∧
      eligible (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 2 = true ∧
      (∃ δ e M', RefNuFire (nu020_join .one .one) nu020_ac1 (some 1) δ e M') ∧
      ∀ c δ e M', RefNuFire (nu020_join .one .one) nu020_ac1 c δ e M' → c = some 1 := by
  refine ⟨by decide, by decide, ⟨_, _, _, NU_020_enable_nonvacuous.1⟩, fun c δ e M' hf => ?_⟩
  obtain ⟨n, rfl, hs⟩ := refNuFire_selected (ms := nu020_ms) rfl hf
  have h1 : Selected (matchIn nu020_ms (nu020_join .one .one) nu020_ac1) 1 :=
    refSelect_eq_some_iff.1 (by decide)
  rw [selected_unique hs h1]

/-! ## nu-b#8: count quiescence on a matched net (D20) -/

/-- ✓ **nu-b#8 (D20): quiescence reads enablement name-aware.** Worked example: AC2's marking
holds X in branch A and Y in branch B. The join is enabled on its counts (both places are
marked), but no name is in both branches, so it is not ν-enabled, and the net of that one join
rests there although the join is not reapable. With branch A as the pending place, the token X
waits there while the net rests: NU-040's joined-or-dead-lettered predicate, which reads the
name-aware rest and holds of the reference, calls the marking a violation. The count reading
would call the join enabled and the marking not quiescent. -/
@[evidence consistent NU_040_jodl]
theorem clashNu_countRest :
    NU_040_jodl (refJodl (N := Nat) (V := Nat) (Nm := Nat)) ∧
      Enabled (nu020_join .one .one).base (qCount nu020_ac2) ∧
      ¬ NuEnabled (nu020_join .one .one) nu020_ac2 ∧
      (nu020_join .one .one).base.reapable = false ∧
      NuRests [nu020_join .one .one] nu020_ac2 ∧
      refJodl [nu020_join .one .one] [] 0 nu020_ac2 := by
  have hn : ¬ NuEnabled (nu020_join .one .one) nu020_ac2 := by
    rintro ⟨-, h⟩
    have hs := (refSelect_spec (matchIn nu020_ms (nu020_join .one .one) nu020_ac2)).2 (h _ rfl)
    exact absurd hs (by decide)
  have hr : NuRests [nu020_join .one .one] nu020_ac2 := fun t ht he => by
    simp only [List.mem_singleton] at ht
    subst ht
    exact absurd he hn
  exact ⟨NU_040_jodl_reference, by decide, hn, rfl, hr, hr, by decide⟩

/-! ## nu-c#3: what a demand counts (ruling D97 (a)) -/

/-- ✓ **nu-c#3, ruling D97 (a): a demand is the required count.** Worked example: two transitions
drain place 0 with `All` arcs, and place 0 holds two tokens. With the required count (1 each) the
two need 2, which the place holds, so they do not compete and the lower one is not pruned. Read as
the tokens each firing consumes (2 each) they would need 4 and compete. On One and Exactly arcs
the two readings agree, and wherever the draining arcs' places hold their required counts the
required count competes only where the tokens-consumed reading does, so the runtimes prune a
subset of what the text allows and stay sound. -/
@[evidence cites "NU-052" "a transition's demand on a place is the required count of its input arcs there, not the tokens one firing consumes (ruling D97 (a)): two All arcs on a place with two tokens compete under the tokens-consumed reading and not under the required count, and the required count never competes where the other reading does not"]
theorem clashNu_demand :
    refCompete (nu052_a 2) clashNuAllH clashNuAllL = false ∧
      consumedCompete (nu052_a 2) clashNuAllH clashNuAllL = true ∧
      refCompete (nu052_a 1) nu052_hi.base nu052_lo.base =
        consumedCompete (nu052_a 1) nu052_hi.base nu052_lo.base ∧
      ∀ (a : AMarking) (H L : Transition),
        (∀ s ∈ H.inputs ++ L.inputs, s.card.consumesAll = true → s.card.required ≤ a s.place) →
        refCompete a H L = true → consumedCompete a H L = true := by
  refine ⟨by decide, by decide, by decide, fun a H L hreq h => ?_⟩
  simp only [refCompete, Novel.RouteB.sharesConsumed, consumedCompete, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨sh, hsh, hl, hlt⟩ := h
  refine ⟨sh, hsh, hl, ?_⟩
  have hH := demandOn_le_consumed (a := a) (t := H) (p := sh.place)
    (fun s hs hp hc => hp ▸ hreq s (List.mem_append_left _ hs) hc)
  have hL := demandOn_le_consumed (a := a) (t := L) (p := sh.place)
    (fun s hs hp hc => hp ▸ hreq s (List.mem_append_right _ hs) hc)
  omega

end Libpetri.Spec
