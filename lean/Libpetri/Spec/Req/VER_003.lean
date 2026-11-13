import Libpetri.Spec.Verifier.Result
import Libpetri.Spec.Req.VER_001
import Libpetri.Spec.Req.CORE_022
import Libpetri.Spec.Text.VER_003

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-003: Verification Result (`spec/07-verification.md`)

What a verdict promises. The requirement is a predicate over four variables:

* `F : FireRel K`, the firing relation the CORE and IO blocks constrain; firing sequences and
  reachability of the verified net are read through it (`RunF F`, `ReachF F`);
* `V : SafetyViolRel K`, the violation reading of [VER-002] (the same variable VER-002's
  statement fixes), at the option `assumeNoReaping`;
* `abs : Abs K`, the verified-net function (VER-001 inert places, VER-006 Arrivals closure,
  VER-004 in-flight split, EXEC-042 terminal rewrite), or the reason it cannot be built;
* `D : Decider K`, a verifier entry point.

The lines: an `Unknown` has a reason and a `Proven` a method; a property that names a place the
net does not declare, the initial marking does not mark and no rewrite of the verified net adds
is `Unknown`, and so is a verified net that cannot be built; a confirmed `Violated` carries a
firing sequence of the verified net to a violating marking; an initial violation is the empty
trace, not marked unconfirmed, and confirmed off Route B; a `Proven` holds on every reachable
marking; every reported P-invariant is conserved on the reachable markings;
`counterexampleTiming` is present exactly with `Violated`, `UNTIMED_NET` exactly on an untimed
net, and on a timed net `TIMED_EXACT` from Route B and `UNTIMED_ABSTRACTION` from another route
while the timed check is off; a decided verdict names a route other than `Unavailable`.

The witness is `refVerify abs` at `F = RefFire` and `V = refSafetyViol`, for every `abs`
(`VER_003_reference`). Wrong deciders are killed one per line, on the [VER-002] AC11 net
`p0 → t → p1` with `t` at `window(3, 5)`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.Seam Libpetri.Spec.Verifier

/-! ## The verified-net function of VER-001 alone -/

/-- The verified-net function that adds VER-001's inert places and nothing else: the user's
timed net with every undeclared marked place appended (`refVerifiedNet`), the property and the
marking unchanged. -/
def inertAbs {K : Type} [DecidableEq K] : Abs K := fun _ X φ m0 =>
  .ok ⟨{ X with net := refVerifiedNet X.net m0 }, φ, m0⟩

/-! ## VER-003 (B): the verdict contract -/

requirement VER_003
  id "VER-003"
  title "Verification Result"
  kind B
  scope "every verifier entry point and every route, all implementations (SHOULD; the shall sentences bind an implementation that offers verification)"
  source verbatim "spec/07-verification.md"
  covers VER_003.s1, VER_003.s2, VER_003.s3, VER_003.s4, VER_003.s5, VER_003.s6, VER_003.s7,
        VER_003.s8, VER_003.s9, VER_003.s10, VER_003.s11
  reading "For every firing relation F, violation reading V, verified-net function abs and decider D, and all options o, timed nets X, properties φ and initial markings m0, with r the result D o X φ m0:"
          "if r is Unknown, its reason is not the empty string;"
          "if r is Proven, its method is not the empty string;"
          "if some place φ names (propPlaces: places and waivers, never sinks) is neither a declared place of X nor marked by m0, and every verified query abs returns lacks some place φ names, r is Unknown;"
          "if abs refuses (returns an error), r is Unknown;"
          "for every verified query q that abs returns: if r is Violated with counterexampleConfirmed true, its trace is a firing sequence under F of the verified net from q's initial marking to a marking that violates q's property under V at the option assumeNoReaping;"
          "for that q: if q's initial marking violates q's property and r is Violated, its trace is empty, counterexampleConfirmed is not false, and it is true unless r's route is Route B (nuScg);"
          "for that q: if r is Proven, no marking reachable under F from q's initial marking violates q's property;"
          "for that q: every P-invariant r reports has a weighted token sum equal to its constant on every marking reachable under F from q's initial marking;"
          "if r is not Violated, it has no counterexampleTiming;"
          "if r is Violated, it has a counterexampleTiming, it is UNTIMED_NET exactly when every transition of X has timing immediate, and, when some transition of X is timed, it is TIMED_EXACT if r's route is Route B (nuScg) and UNTIMED_ABSTRACTION if r's route is another and the timed check is off;"
          "if r is Violated or Proven, its route is not Unavailable."
  assumes "The verified net is the value of the verified-net function abs, a parameter: VER-001's inert places, VER-006's Arrivals closure, VER-004's in-flight split and EXEC-042's terminal rewrite are its parts, each that requirement's subject. The block holds of the reference for every abs (VER_003_reference), so it does not wait for those functions; the property in the lines is the one abs returns, which the terminal rewrite may extend with sinks and markers. A confirmed trace names transitions of the net abs returns: the runtimes label a row of VER-001's expansion t_b1 and an injection step of VER-006 inject(p) (the successor labels of replay in abstract_replay.rs), so for them abs is the row expansion with one injection transition per injected place, while the examples here use inertAbs, which adds VER-001's places and nothing else."
          "Reachability and firing sequences are those of the firing relation F the CORE and IO blocks constrain (ReachF F, RunF F); at F = RefFire they are Reference.Reach and Reference.Run (reachF_ref, runF_ref), the untimed abstraction of VER-004, in which each firing is atomic. Violation is the reading V of VER-002 at the option assumeNoReaping, the same variable VER-002's statement fixes, so the two blocks hold together of one V (VER_003_joint). Place names carry an order (LinearOrder K), as strings do by code point; the reference enumeration stores markings sorted by it. The nets are those Reference.TimedNet expresses, which have no match transition: on a ν-net the verdict contract of Route B and of the name-coloured encoding is NU-055's, VER-012's and NU-053's, and the name-blind replay behind counterexampleConfirmed there is NU-050's. Unreachable([]) is out of scope (ruling D88 (a)): VER-002 fixes V only on a non-empty list."
          "Ruling D22 (a): VER-003 is SHOULD, and its shall sentences bind an implementation that offers verification. Ruling D40 (a): a trace is promised only with counterexampleConfirmed true; an unconfirmed Violated (the fixpoint replay off or inconclusive, where Rust reports an empty trace and Java the decoded states) promises nothing about its trace, and Route B leaves the field absent, as Rust, Java and TypeScript do on the name-coloured encoding of NU-053, an initial violation included, which is why the initial-violation line says not false, and true only off Route B; the name-coloured encoding is outside the nets of this block (no match transition), so off Route B the line asks true. Reporting counterexampleConfirmed false on that encoding is the Java behaviour RD-26 recorded. The per-language content of an unconfirmed trace is kind N."
          "The unresolved check reads the places and waivers a property names and never its sinks or conditional declarations, as all three runtimes do (property_place_names in smt_verifier.rs; Java propertyPlaces; TypeScript propertyPlaces); a check that reads the sinks and not the waivers is killed (VER_003_forbids_sinksNotWaivers). 'Before any route runs' and 'It MUST precede the ν route, the structural routes and the encoders alike' are the line itself: the verdict is Unknown whatever a route would answer, and a refusal placed inside a route, after a route that proves the property vacuously, is killed (VER_003_forbids_noGuard). The ν properties NameAligned and QuiescentNameAligned also name places; they are NU-055's. Line 3 reads both nets the quoted sentence names: the place is neither declared by the user's net nor marked by the initial marking (Unresolved, which is not being a place of VER-001's verified net, VER_003_unresolved_verified), and the verified net abs returns lacks some place the property names. The runtimes run the check after all their rewrites (unresolved_property_place_in_net, called inside verify_net in smt_verifier.rs), so a property naming a place a rewrite adds, an in-flight place inflight:t of VER-004 or an arrival source of VER-006, resolves where that rewrite applies and is decided: PlaceBound(inflight:t, 1) is how the single start of CONC-002 is checked. The second premise is what lets such a property be decided; on VER-001's verified net alone it adds nothing (inertAbs_lacks). The lines ask for Unknown and never forbid it, so a decider that also refuses a mistyped sink meets them: the second quoted sentence fixes what line 3 is triggered by, and that the reference decides a property whose sink is mistyped is the nonvacuous example, not a line."
          "A configuration error is not a verified net that cannot be built: a name that the Arrivals closure of VER-006 would add and that the net already declares, or an ArrivalsBetween mode with max < min, is rejected with an exception before any route runs, in Rust a panic (open_net/closure.rs, the clash check of the closure; smt_verifier.rs, with_arrivals), in Java and TypeScript a thrown error (OpenNetClosure.java, open-net/closure.ts), as the markdown says. The decider D is a total function, so such a call is not among its arguments; line 4 is about the refusals that are verdicts, the in-flight split's (VER-004) and the Bounded(k) premise check's (VER-006), which the runtimes return as Unknown with route Unavailable."
          "AC1 (Proven includes the proof method) and AC3 (Unknown includes a reason) are lines 2 and 1; a blank method and a blank reason are killed (VER_003_forbids_blankMethod, VER_003_forbids_blankUnknown)."
          "AC2 (Violated includes a counterexample trace) is line 5 under ruling D40 (a), the trace being a firing sequence of the verified net when counterexampleConfirmed is true; a confirmed trace carrying the labels of the in-flight split net against a verified net without the split is killed (VER_003_forbids_splitLabels). That the trace lists markings as well as transitions is the result record's shape (kind N)."
          "AC4 (the result names the deciding route; a non-empty invariant list is valid on every route) is line 11 for the route and line 8 for the invariants; a decided verdict with route Unavailable and an unconserved invariant are killed (VER_003_forbids_noRoute, VER_003_forbids_unconserved). That an empty list off the SMT route means 'not computed' is the reading of the record, not a line: the route field is what lets a consumer tell the two apart. The reference reports the invariants of the places no transition touches (inertInvariants), VER-001's 'its own trivial P-invariant'; whether a route computes invariants at all is VER-005's subject."
          "AC5 (an unresolved property place gives Unknown before any route runs; a place a rewrite adds resolves) is line 3; the second quoted sentence says which places a property names. The reference refuses before it builds the verified query (refVerify), and VER_003_nonvacuous checks it on PlaceBound(7, 0)."
          "AC6 (counterexampleTiming absent for Proven and Unknown; for Violated, UNTIMED_NET on an all-immediate net whatever the route, TIMED_EXACT for a Route B verdict on a timed net, UNTIMED_ABSTRACTION for any other route on a timed net while the timed check is off) is lines 9 and 10; a timing label on a Proven, UNTIMED_NET on a timed net, TIMED_EXACT on an enumeration verdict and UNTIMED_ABSTRACTION on a Route B verdict are killed (VER_003_forbids_timingOnProven, VER_003_forbids_untimedEverywhere, VER_003_forbids_timedExactEnum, VER_003_forbids_routeBAbstraction). The reference has no Route B and no timed check, and labels every timed Violated UNTIMED_ABSTRACTION (VER_003_nonvacuous). With the timed check on, a route other than Route B may carry another label; which one, and the meaning of TIMED_CONFIRMED, SPURIOUS_UNDER_TIMING and TIMED_UNDECIDED, is the label table of VER-023, and that Route B's trace is a path of the graph it explored is VER-012's."
          "AC7 (the two UNTIMED warning lines of a fixpoint Violated) is report text, kind Q."
          "AC8 (an initial violation is the empty firing sequence, with counterexampleConfirmed true, absent on Route B and on the name-coloured encoding) is line 6; a decider that reports a non-empty trace for an initial violation, and one that leaves it unconfirmed on the enumeration route, are killed (VER_003_forbids_nonEmptyInit, VER_003_forbids_initUnconfirmed), and VER_003_nonvacuous checks the reference on the AC11 net, whose initial marking is a reap-aware DeadlockFree violation. The report line 'Counterexample: the initial marking violates the property (empty firing sequence)' is kind Q; 'At an initial violation, a Violated with no trace at all is not conforming' is line 6 read on the record, where an empty label list is the empty firing sequence."
          "The result fields Statistics, the enum spellings of the Implementation notes and the report wording are kind N or Q. A Violated, under the opt-in timed check of VER-023, may have its trace replaced; that is VER-023's line, and the replacement is a run of the verified net, which line 5 already asks of a confirmed trace."
  signoff "2026-11-13 752f8f0f680517ec ai"
  statement : ∀ {K : Type} [LinearOrder K], FireRel K → SafetyViolRel K → Abs K → Decider K → Prop :=
    fun F V abs D =>
      ∀ o X φ m0,
        (∀ why, (D o X φ m0).verdict = .unknown why → why ≠ "") ∧
        (∀ meth, (D o X φ m0).verdict = .proven meth → meth ≠ "") ∧
        (Unresolved X φ m0 ∧
            (∀ q, abs o X φ m0 = .ok q → ∃ p ∈ propPlaces φ, p ∉ q.net.net.places) →
          ∃ why, (D o X φ m0).verdict = .unknown why) ∧
        (∀ e, abs o X φ m0 = .error e → ∃ why, (D o X φ m0).verdict = .unknown why) ∧
        (∀ q, abs o X φ m0 = .ok q →
          ((D o X φ m0).verdict = .violated → (D o X φ m0).confirmed = some true →
            ∃ f, RunF F q.net.net (D o X φ m0).trace q.init f ∧
              V o.assumeNoReaping q.net q.prop f) ∧
          (V o.assumeNoReaping q.net q.prop q.init → (D o X φ m0).verdict = .violated →
            (D o X φ m0).trace = [] ∧ (D o X φ m0).confirmed ≠ some false ∧
              ((D o X φ m0).route ≠ .nuScg → (D o X φ m0).confirmed = some true)) ∧
          (∀ meth, (D o X φ m0).verdict = .proven meth →
            ∀ f, ReachF F q.net.net q.init f → ¬ V o.assumeNoReaping q.net q.prop f) ∧
          (∀ i ∈ (D o X φ m0).invariants, ∀ f, ReachF F q.net.net q.init f →
            i.dot f = i.const)) ∧
        ((D o X φ m0).verdict ≠ .violated → (D o X φ m0).timing = none) ∧
        ((D o X φ m0).verdict = .violated →
          (D o X φ m0).timing ≠ none ∧ ((D o X φ m0).timing = some .untimedNet ↔ Untimed X) ∧
          (¬ Untimed X →
            ((D o X φ m0).route = .nuScg → (D o X φ m0).timing = some .timedExact) ∧
            ((D o X φ m0).route ≠ .nuScg → o.timedCheck = false →
              (D o X φ m0).timing = some .untimedAbstraction))) ∧
        (((D o X φ m0).verdict = .violated ∨ ∃ meth, (D o X φ m0).verdict = .proven meth) →
          (D o X φ m0).route ≠ .unavailable)

/- The pinned readable form of VER-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_003 : {K : Type} → [LinearOrder K] → FireRel K → SafetyViolRel K → Abs K → Decider K → Prop :=
fun {K} [LinearOrder K] F V abs D =>
  ∀ (o : Options) (X : Reference.TimedNet K) (φ : VerProp K) (m0 : NMarking K),
    (∀ (why : String), (D o X φ m0).verdict = Verdict.unknown why → why ≠ "") ∧
      (∀ (meth : String), (D o X φ m0).verdict = Verdict.proven meth → meth ≠ "") ∧
        ((Unresolved X φ m0 ∧ ∀ (q : Query K), abs o X φ m0 = Except.ok q → ∃ p ∈ propPlaces φ, p ∉ q.net.net.places) →
            ∃ why, (D o X φ m0).verdict = Verdict.unknown why) ∧
          (∀ (e : String), abs o X φ m0 = Except.error e → ∃ why, (D o X φ m0).verdict = Verdict.unknown why) ∧
            (∀ (q : Query K),
                abs o X φ m0 = Except.ok q →
                  ((D o X φ m0).verdict = Verdict.violated →
                      (D o X φ m0).confirmed = some true →
                        ∃ f, RunF F q.net.net (D o X φ m0).trace q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
                    (V o.assumeNoReaping q.net q.prop q.init →
                        (D o X φ m0).verdict = Verdict.violated →
                          (D o X φ m0).trace = [] ∧
                            (D o X φ m0).confirmed ≠ some false ∧
                              ((D o X φ m0).route ≠ Route.nuScg → (D o X φ m0).confirmed = some true)) ∧
                      (∀ (meth : String),
                          (D o X φ m0).verdict = Verdict.proven meth →
                            ∀ (f : K → ℕ), ReachF F q.net.net q.init f → ¬V o.assumeNoReaping q.net q.prop f) ∧
                        ∀ i ∈ (D o X φ m0).invariants, ∀ (f : K → ℕ), ReachF F q.net.net q.init f → i.dot f = i.const) ∧
              ((D o X φ m0).verdict ≠ Verdict.violated → (D o X φ m0).timing = none) ∧
                ((D o X φ m0).verdict = Verdict.violated →
                    (D o X φ m0).timing ≠ none ∧
                      ((D o X φ m0).timing = some CexTiming.untimedNet ↔ Untimed X) ∧
                        (¬Untimed X →
                          ((D o X φ m0).route = Route.nuScg → (D o X φ m0).timing = some CexTiming.timedExact) ∧
                            ((D o X φ m0).route ≠ Route.nuScg →
                              o.timedCheck = false → (D o X φ m0).timing = some CexTiming.untimedAbstraction))) ∧
                  (((D o X φ m0).verdict = Verdict.violated ∨ ∃ meth, (D o X φ m0).verdict = Verdict.proven meth) →
                    (D o X φ m0).route ≠ Route.unavailable)
-/
#guard_msgs in #print VER_003

/-! ## The reference -/

/-- ✓ **The reference decider meets the verdict contract**, for every verified-net function.
Example: on the net `p0 → t → p1` from `{p0: 1}`, `refVerify` either refuses (an unresolved
place, a verified net that cannot be built), or answers through the initial marking, the dead
initial marking or the reference enumeration, whose `Proven` holds on every reachable marking and
whose `Violated` replays; it reports the route `enumeration` and `UNTIMED_ABSTRACTION` for the
timed `window(3, 5)`. -/
@[evidence holds VER_003]
theorem VER_003_reference {K : Type} [LinearOrder K] [Hashable K] (abs : Abs K) :
    VER_003 RefFire refSafetyViol abs (refVerify abs) := by
  intro o X φ m0
  by_cases hu : Unresolved X φ m0
  · simp [refVerify, hu]
  · cases ha : abs o X φ m0 with
    | error e => simp [refVerify, refDispatch, hu, ha]
    | ok q =>
      have hinv := inertInvariants_conserved q
      cases hd : firstDecided refSteps o q with
      | none =>
        simp only [refVerify, refDispatch, hu, ha, hd, if_false]
        refine ⟨by simp, by simp, fun h => h.1.elim, by simp, ?_, by simp, by simp, by simp⟩
        intro q' hq'
        obtain rfl : q = q' := by simpa using hq'
        exact ⟨by simp, by simp, by simp, hinv⟩
      | some ro =>
        obtain ⟨r, out⟩ := ro
        obtain rfl := refSteps_route hd
        obtain ⟨hp, hv, hk⟩ := firstDecided_sound refSteps_sound hd
        obtain ⟨-, -, -, -, hna⟩ := firstDecided_step hd
        cases out with
        | aside n => exact absurd rfl (hna n)
        | decided v tr c =>
          simp only [refVerify, refDispatch, hu, ha, hd, if_false]
          refine ⟨?_, ?_, fun h => h.1.elim, by simp, ?_, ?_, ?_, by simp⟩
          · intro why hw
            subst hw
            exact hk why tr c rfl
          · intro meth hm
            subst hm
            exact (hp meth tr c rfl).1
          · intro q' hq'
            obtain rfl : q = q' := by simpa using hq'
            refine ⟨?_, ?_, ?_, hinv⟩
            · intro hvi hc
              subst hvi hc
              obtain ⟨f, hr, hvf⟩ := hv tr rfl
              exact ⟨f, runF_ref.mpr hr, hvf⟩
            · intro hi hvi
              subst hvi
              rcases refSteps_initial hi with h0 | h0
              · rw [hd] at h0; exact absurd h0 (by simp)
              · rw [hd] at h0
                simp only [Option.some.injEq, Prod.mk.injEq, PhaseOut.decided.injEq] at h0
                obtain ⟨-, -, rfl, rfl⟩ := h0
                exact ⟨rfl, by simp, fun _ => rfl⟩
            · intro meth hm f hf
              subst hm
              exact (hp meth tr c rfl).2 f ((reachF_ref _ _ _).mp hf)
          · intro hvi
            simp [hvi]
          · intro hvi
            subst hvi
            by_cases hT : Untimed X <;> simp [hT]

/-! ## Consistency with CORE-022, VER-001, VER-002 and VER-014 -/

/-- **Line 3 reads VER-001's verified net.** For every verified-net function that meets VER-001,
a property place is unresolved exactly when it is not a place of the verified net. Example: on
the AC11 net with a stray token on place 2, VER-001 adds place 2, so `PlaceBound(2, 0)` resolves
and `PlaceBound(7, 0)` does not. -/
theorem VER_003_unresolved_verified {K : Type} [DecidableEq K] {VN : VerifiedNetFn K}
    {Xp : ExpandFn K} (h : VER_001 VN Xp) (X : Reference.TimedNet K) (φ : VerProp K)
    (m0 : NMarking K) :
    Unresolved X φ m0 ↔ ∃ p ∈ propPlaces φ, p ∉ (VN X.net m0).places := by
  rw [h.1 X.net m0]
  simp only [Unresolved, List.mem_append, List.mem_filter, decide_eq_true_eq, not_or, not_and,
    not_not]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, h1, fun h3 => absurd h3 h2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, h1, fun h3 => h1 (h2 h3)⟩

/-- **On VER-001's verified net the second premise of line 3 adds nothing.** Example: on the AC11
net, `PlaceBound(7, 0)` names place 7, which the user's net does not declare and `{p0: 1}` does not
mark, so the verified net `inertAbs` builds lacks it too. -/
theorem inertAbs_lacks {K : Type} [DecidableEq K] {o : Options} {X : Reference.TimedNet K}
    {φ : VerProp K} {m0 : NMarking K} (h : Unresolved X φ m0) :
    ∀ q, inertAbs o X φ m0 = .ok q → ∃ p ∈ propPlaces φ, p ∉ q.net.net.places := by
  intro q hq
  simp only [inertAbs, Except.ok.injEq] at hq
  subst hq
  exact (VER_003_unresolved_verified VER_001_reference X φ m0).mp h

/-- ✓ **One firing relation, one violation reading and one verified net for CORE-022, VER-001,
VER-002, VER-014 and VER-003.** Example: the reference firing `RefFire`, VER-014's rest set with
VER-002's reference violations, VER-001's reference verified net (declared places plus the
marked ones), the verified-net function that builds exactly that net, and `refVerify` over it,
satisfy all five blocks at once. -/
@[evidence consistent CORE_022 VER_001 VER_002 VER_003 VER_014]
theorem VER_003_joint {K : Type} [LinearOrder K] [Hashable K] :
    ∃ (F : FireRel K) (S : StrandRel K) (Vr : RestViolRel K) (V : SafetyViolRel K)
      (VN : VerifiedNetFn K) (Xp : ExpandFn K) (abs : Abs K) (D : Decider K),
      CORE_022 F ∧ VER_014 S Vr ∧ VER_002 S V ∧ VER_001 VN Xp ∧
      (∀ o X φ m0, abs o X φ m0 = .ok ⟨{ X with net := VN X.net m0 }, φ, m0⟩) ∧
      VER_003 F V abs D :=
  ⟨RefFire, refStrand, refRestViol, refSafetyViol, refVerifiedNet, refVirtual, inertAbs,
    refVerify inertAbs, CORE_022_reference, VER_014_reference, VER_002_reference,
    VER_001_reference, fun _ _ _ _ => rfl, VER_003_reference inertAbs⟩

/-! ## The AC11 net -/

/-- `t : p0 → p1`, the transition of the [VER-002] AC11 net. -/
def ver003T : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1), reapable := true }

/-- The AC11 net `p0 → t → p1`. -/
def ver003Net : Reference.Net Nat := { places := [0, 1], transitions := [ver003T] }

/-- The AC11 net with `t` at `window(3, 5)`. -/
def ver003X : Reference.TimedNet Nat := { net := ver003Net, timing := fun _ => .window 3 5, tol := 0 }

/-- The marking `{p0: 1}`. -/
def ver003P0 : NMarking Nat := ⟨[(0, 1)], by decide, by decide⟩

/-- The marking `{p1: 1}`, which enables nothing. -/
def ver003P1 : NMarking Nat := ⟨[(1, 1)], by decide, by decide⟩

/-- A stray token on the undeclared place 2 ([VER-001] AC3). -/
def ver003Stray : NMarking Nat := ⟨[(2, 1)], by decide, by decide⟩

/-- ✓ **The reference on the AC11 net.** Example: from `{p0: 1}`, `t` at `window(3, 5)` is
enabled and reapable, so the initial marking is a reap-aware rest that strands a token outside
the sink `p1`: `DeadlockFree([p1])` is `Violated` at once, with the empty trace, confirmed, route
`enumeration` and timing `UNTIMED_ABSTRACTION` (the net is timed). From `{p1: 1}` nothing is
enabled and the token rests in the sink, so the same property is `Proven` by `enumeration`.
With a stray token on the undeclared place 2, VER-001 adds the place, the token is stranded
(`Violated`), and the reference reports the place's trivial invariant `p2 = 1`.
`PlaceBound(7, 0)` names a place that is neither declared nor marked: `Unknown`. A mistyped sink
is not refused: `DeadlockFree([9])` from `{p1: 1}` is decided, `Violated`. -/
@[evidence nonvacuous VER_003]
theorem VER_003_nonvacuous :
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P0).verdict = .violated ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P0).trace = [] ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P0).confirmed = some true ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P0).route = .enumeration ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P0).timing =
      some .untimedAbstraction ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003P1).verdict =
      .proven "enumeration" ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003Stray).verdict = .violated ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [1] []) ver003Stray).invariants =
      [⟨[(2, 1)], 1⟩] ∧
    (refVerify inertAbs {} ver003X (.placeBound 7 0) ver003P0).verdict =
      .unknown "the property names a place that the net does not declare and the initial marking does not mark" ∧
    (refVerify inertAbs {} ver003X (.deadlockFree [9] []) ver003P1).verdict = .violated := by
  decide

/-! ## Wrong deciders, one per line -/

/-- `PlaceBound(p0, 0)` holds at `{p0: 1}` as a violation. -/
theorem ver003_init_violates :
    refSafetyViol false ver003X (.placeBound 0 0) ver003P0.count := by
  show 0 < ver003P0.count 0
  decide

/-- Mutant: an `Unknown` with the empty reason. -/
def ver003_blankUnknown : Decider Nat := fun _ _ _ _ => { verdict := .unknown "" }

/-- ✗ **A blank reason is not a reason** (line 1). Example: a decider that answers `Unknown("")`
on any query breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_blankUnknown :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_blankUnknown := by
  intro h
  exact (h {} ver003X (.placeBound 0 0) ver003P0).1 "" rfl rfl

/-- Mutant: a `Proven` with the empty method. -/
def ver003_blankMethod : Decider Nat := fun _ _ _ _ =>
  { verdict := .proven "", route := .enumeration }

/-- ✗ **A Proven names its method** (line 2). Example: `Proven("")` for `PlaceBound(p1, 1)` from
`{p1: 1}`, which does hold, still breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_blankMethod :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_blankMethod := by
  intro h
  exact (h {} ver003X (.placeBound 1 1) ver003P1).2.1 "" rfl rfl

/-- ✗ **A refusal inside a route is no refusal** (line 3). Example: the reference without its
first check answers `PlaceBound(7, 0)` from `{p1: 1}` with the dead initial marking: place 7 is
never marked, so it is `Proven`, although the net has no place 7. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_noGuard :
    ¬ VER_003 (K := Nat) RefFire refSafetyViol inertAbs (refDispatch inertAbs) := by
  intro h
  have hu : Unresolved ver003X (.placeBound 7 0) ver003P1 := by decide
  have hv : (refDispatch inertAbs {} ver003X (.placeBound 7 0) ver003P1).verdict =
      .proven "enumeration" := by decide
  obtain ⟨why, hw⟩ := (h {} ver003X (.placeBound 7 0) ver003P1).2.2.1 ⟨hu, inertAbs_lacks hu⟩
  rw [hv] at hw
  exact Verdict.noConfusion hw

/-- The places the first design spike read: the sinks, and not the waivers. -/
def ver003_spikePlaces : VerProp Nat → List Nat
  | .deadlockFree s _ | .terminatesAtSink s => s
  | .mutualExclusion ps | .unreachable ps => ps
  | .placeBound p _ => [p]
  | .quiescentCount ps _ _ _ => ps

/-- Mutant: an unresolved check over the sinks and not the waivers, which then reports the lower
bound of a `QuiescentCount` whose waiver is mistyped as violated at the initial marking. -/
def ver003_sinksNotWaivers : Decider Nat := fun _ X φ m0 =>
  if (ver003_spikePlaces φ).any (fun p => !decide (p ∈ X.net.places) && !decide (p ∈ m0.places))
  then { verdict := .unknown "unresolved" }
  else { verdict := .violated, route := .enumeration, trace := [], confirmed := some true,
         timing := some .untimedAbstraction }

/-- ✗ **The waivers are read** (line 3). Example: `QuiescentCount([p1], 2, ∞, waivedBy [7])` from
`{p1: 1}` names the waiver 7, which the net does not have; a check that reads only the counted
places proceeds and reports the lower bound as violated, as if the waiver were always empty. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_sinksNotWaivers :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_sinksNotWaivers := by
  intro h
  have hu : Unresolved ver003X (.quiescentCount [1] 2 none [7]) ver003P1 := by decide
  obtain ⟨why, hw⟩ :=
    (h {} ver003X (.quiescentCount [1] 2 none [7]) ver003P1).2.2.1 ⟨hu, inertAbs_lacks hu⟩
  have hv : (ver003_sinksNotWaivers {} ver003X (.quiescentCount [1] 2 none [7]) ver003P1).verdict =
      .violated := by decide
  rw [hv] at hw
  exact Verdict.noConfusion hw

/-- The verified-net function that cannot build any net. -/
def ver003_refuseAll : Abs Nat := fun _ _ _ _ => .error "refused"

/-- ✗ **A refused verified net gives Unknown** (line 4). Example: when the verified net cannot be
built, a decider that verifies the user's net instead reports `PlaceBound(p0, 0)` from
`{p0: 1}` as `Violated`. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_ignoreRefusal :
    ¬ VER_003 RefFire refSafetyViol ver003_refuseAll (refVerify inertAbs) := by
  intro h
  obtain ⟨why, hw⟩ := (h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.1 "refused" rfl
  have hv : (refVerify inertAbs {} ver003X (.placeBound 0 0) ver003P0).verdict = .violated := by
    decide
  rw [hv] at hw
  exact Verdict.noConfusion hw

/-- Mutant: a confirmed trace with the labels of the in-flight split net ([VER-004]). -/
def ver003_splitLabels : Decider Nat := fun _ _ _ _ =>
  { verdict := .violated, route := .enumeration, trace := ["complete:t"], confirmed := some true,
    timing := some .untimedAbstraction }

/-- ✗ **A confirmed trace is a run of the verified net** (line 5). Example: on the AC11 net, whose
verified net has no split, a confirmed trace `complete:t` names no transition of the net, so no
firing sequence carries it. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_splitLabels :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_splitLabels := by
  intro h
  obtain ⟨f, ⟨m1, ⟨t, ht, hn, -⟩, -⟩, -⟩ :=
    ((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.1 _ rfl).1 rfl rfl
  have ht' : t = ver003T := by
    simpa [inertAbs, refVerifiedNet, ver003X, ver003Net, ver003P0, NMarking.places] using ht
  subst ht'
  simp [ver003T] at hn

/-- Mutant: an initial violation reported with a one-step trace. -/
def ver003_nonEmptyInit : Decider Nat := fun _ _ _ _ =>
  { verdict := .violated, route := .enumeration, trace := ["t"],
    timing := some .untimedAbstraction }

/-- ✗ **An initial violation is the empty trace** (line 6). Example: `PlaceBound(p0, 0)` is
violated at `{p0: 1}` itself; a `Violated` that reports the trace `t` breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_nonEmptyInit :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_nonEmptyInit := by
  intro h
  have := (((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.1 _ rfl).2.1
    ver003_init_violates rfl).1
  simp [ver003_nonEmptyInit] at this

/-- Mutant: an initial violation reported with the empty trace but not confirmed. -/
def ver003_initUnconfirmed : Decider Nat := fun _ _ _ _ =>
  { verdict := .violated, route := .enumeration, trace := [],
    timing := some .untimedAbstraction }

/-- ✗ **Off Route B an initial violation is confirmed** (line 6). Example: `PlaceBound(p0, 0)` is
violated at `{p0: 1}` itself; the enumeration route that reports the empty trace but leaves
`counterexampleConfirmed` absent breaks the contract, since only Route B may leave it absent. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_initUnconfirmed :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_initUnconfirmed := by
  intro h
  have := (((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.1 _ rfl).2.1
    ver003_init_violates rfl).2.2 (by simp [ver003_initUnconfirmed])
  simp [ver003_initUnconfirmed] at this

/-- Mutant: always `Proven`. -/
def ver003_alwaysProven : Decider Nat := fun _ _ _ _ =>
  { verdict := .proven "enumeration", route := .enumeration }

/-- ✗ **A Proven holds on every reachable marking** (line 7). Example: `PlaceBound(p0, 0)` is
violated at `{p0: 1}`, the initial marking itself, so `Proven` there is false. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_alwaysProven :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_alwaysProven := by
  intro h
  exact ((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.1 _ rfl).2.2.1 "enumeration" rfl _
    Relation.ReflTransGen.refl ver003_init_violates

/-- Mutant: the reference with the invariant `p0 = 1` added. -/
def ver003_unconserved : Decider Nat := fun o X φ m0 =>
  { refVerify inertAbs o X φ m0 with invariants := [⟨[(0, 1)], 1⟩] }

/-- ✗ **A reported invariant is conserved** (line 8). Example: `p0 = 1` holds at `{p0: 1}` but not
after `t` fires and moves the token to `p1`, so reporting it breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_unconserved :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_unconserved := by
  intro h
  have hl := ((h {} ver003X (.placeBound 1 1) ver003P0).2.2.2.2.1 _ rfl).2.2.2
  have hf : Reference.Fires ver003T ver003P0.count [1]
      (fireNC ver003P0.count ver003T.core (depProd [1])) :=
    ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
  have hr : ReachF RefFire ver003Net ver003P0.count
      (fireNC ver003P0.count ver003T.core (depProd [1])) :=
    Relation.ReflTransGen.single ⟨"t", ver003T, by simp [ver003Net], rfl, [1], hf⟩
  have := hl ⟨[(0, 1)], 1⟩ (by simp [ver003_unconserved]) _ hr
  revert this
  decide

/-- Mutant: a timing label on a `Proven`. -/
def ver003_timingOnProven : Decider Nat := fun _ _ _ _ =>
  { verdict := .proven "enumeration", route := .enumeration, timing := some .untimedAbstraction }

/-- ✗ **No counterexampleTiming without Violated** (line 9). Example: `PlaceBound(p1, 1)` from
`{p1: 1}` holds, but a `Proven` that carries `UNTIMED_ABSTRACTION` breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_timingOnProven :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_timingOnProven := by
  intro h
  have := (h {} ver003X (.placeBound 1 1) ver003P1).2.2.2.2.2.1 (by simp [ver003_timingOnProven])
  simp [ver003_timingOnProven] at this

/-- Mutant: the reference that labels every `Violated` `UNTIMED_NET`. -/
def ver003_untimedEverywhere : Decider Nat := fun o X φ m0 =>
  { refVerify inertAbs o X φ m0 with
    timing := if (refVerify inertAbs o X φ m0).verdict = .violated then some .untimedNet else none }

/-- ✗ **UNTIMED_NET only on an untimed net** (line 10). Example: the AC11 net has `t` at
`window(3, 5)`, so a `Violated` labelled `UNTIMED_NET` breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_untimedEverywhere :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_untimedEverywhere := by
  intro h
  have hv : (ver003_untimedEverywhere {} ver003X (.placeBound 0 0) ver003P0).verdict = .violated := by
    decide
  have ht : (ver003_untimedEverywhere {} ver003X (.placeBound 0 0) ver003P0).timing =
      some .untimedNet := by decide
  have hnt : ¬ Untimed ver003X := by decide
  exact hnt (((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.2.2.1 hv).2.1.mp ht)

/-- Mutant: the reference that labels every `Violated` `TIMED_EXACT`, as if the enumeration had
explored timed behaviour. -/
def ver003_timedExactEnum : Decider Nat := fun o X φ m0 =>
  { refVerify inertAbs o X φ m0 with
    timing := if (refVerify inertAbs o X φ m0).verdict = .violated then some .timedExact else none }

/-- ✗ **Only Route B's verdict is TIMED_EXACT** (line 10). Example: on the AC11 net, timed at
`window(3, 5)`, `PlaceBound(p0, 0)` is `Violated` at `{p0: 1}` on the enumeration route, an untimed
abstraction; with the timed check off it must be labelled `UNTIMED_ABSTRACTION`, not
`TIMED_EXACT`. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_timedExactEnum :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_timedExactEnum := by
  intro h
  have hv : (ver003_timedExactEnum {} ver003X (.placeBound 0 0) ver003P0).verdict = .violated := by
    decide
  have hr : (ver003_timedExactEnum {} ver003X (.placeBound 0 0) ver003P0).route ≠ .nuScg := by
    decide
  have ht : (ver003_timedExactEnum {} ver003X (.placeBound 0 0) ver003P0).timing =
      some .timedExact := by decide
  have hnt : ¬ Untimed ver003X := by decide
  have := (((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.2.2.1 hv).2.2 hnt).2 hr rfl
  rw [ht] at this
  exact absurd this (by decide)

/-- Mutant: a Route B verdict on a timed net labelled `UNTIMED_ABSTRACTION`. -/
def ver003_routeBAbstraction : Decider Nat := fun _ _ _ _ =>
  { verdict := .violated, route := .nuScg, trace := [], timing := some .untimedAbstraction }

/-- ✗ **Route B's verdict on a timed net is TIMED_EXACT** (line 10). Example: Route B explores the
timed behaviour of the AC11 net, so a `Violated` it decides there, labelled
`UNTIMED_ABSTRACTION`, breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_routeBAbstraction :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_routeBAbstraction := by
  intro h
  have hnt : ¬ Untimed ver003X := by decide
  have := (((h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.2.2.1 rfl).2.2 hnt).1 rfl
  simp [ver003_routeBAbstraction] at this

/-- Mutant: the reference that reports the route `Unavailable`. -/
def ver003_noRoute : Decider Nat := fun o X φ m0 =>
  { refVerify inertAbs o X φ m0 with route := .unavailable }

/-- ✗ **A decided verdict names its route** (line 11). Example: `PlaceBound(p0, 0)` is `Violated`
at `{p0: 1}`; reporting it with the route `Unavailable` breaks the contract. -/
@[evidence forbids VER_003]
theorem VER_003_forbids_noRoute :
    ¬ VER_003 RefFire refSafetyViol inertAbs ver003_noRoute := by
  intro h
  have hv : (ver003_noRoute {} ver003X (.placeBound 0 0) ver003P0).verdict = .violated := by
    decide
  exact (h {} ver003X (.placeBound 0 0) ver003P0).2.2.2.2.2.2.2 (Or.inl hv) rfl

end Libpetri.Spec
