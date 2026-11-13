import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010
import Libpetri.Spec.Text.TIME_013

set_option linter.missingDocs true

/-!
# TIME-013: Deadline enforcement (`spec/03-timing.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`). The evidence theorems check it against the timed reference step
(`RefTStep`), against a reap that consumes the tokens of the reaped transition, a delay that
disarms an expired transition without reaping it, and a reap or a firing of a label outside the
net under a net transition's name, a firing of an expired transition, a firing of a reaped
transition and a step that never arms a reaped transition again, and against five mutant
readings: a reap at the bound plus the tolerance instead of strictly past it, a reap with no
tolerance, a reap of an `Exact` transition, a firing that re-arms a reaped transition whatever it
writes, and an executor that never reaps.

The reap sentence is encoded as far as one atomic step can state it: a reap is taken only from
an expired transition (line 1), and every expired transition of the net has a reap (line 9).
That an expired transition is reaped before the firing pass of its cycle is the Phase 2 cycle
relation's obligation ([EXEC-001] step 4); `clash013_refresh_rescue` in `ClashesTime.lean`
shows what the atomic relation still allows.

The lines on a reaped transition being armed again are TIME-010's lines 1 and 3 read for a
reaped transition, with the stamp of line 1; their proofs reuse TIME-010's policy-generic lemmas
(`time010_newly`, `time010_arms`, `time010_armed`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## TIME-013: Deadline enforcement -/

requirement TIME_013
  id "TIME-013"
  title "Deadline Enforcement"
  kind T
  scope "all executors"
  source verbatim "spec/03-timing.md"
  covers TIME_013.s1, TIME_013.s2, TIME_013.s3, TIME_013.s5, TIME_013.s6, TIME_013.s8, TIME_013.s4,
        TIME_013.s9, TIME_013.s11, TIME_013.s12
  reading "For every timed net X:"
          "a reap of u is of a transition of the net, is taken only from a state in which u is expired, and leaves u reaped, the marking, the reading of the firing clock and the stamp of every other name as they were;"
          "no transition fires from a state in which it is reapable and its elapsed time is greater than its latest bound plus the tolerance;"
          "no transition is reaped from a state in which it is not reapable;"
          "no transition fires from a state in which it is reaped;"
          "a step that leaves the net's transition u reaped, from a state in which u is armed, is a reap of a transition of u's name;"
          "a step that leaves the net's transition u armed, from a state in which u is reaped, is a firing that writes one of u's arc places;"
          "a firing that writes an arc place of the net's transition u, from a state in which u is reaped, leaves u armed with the reading of the firing clock if u is enabled after it;"
          "a firing is of a transition of the net;"
          "from every state in which a transition of the net is expired, the step relation has a reap of it."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic. Reapable, Expired, Reaped, Armed, Elapsed time, Arc place and Write are the glossary terms (GlossaryTime.lean); Reaped is the state reading, enabled at the marking and not armed."
          "Line 1 reads the section's first paragraph as the definition of a reap step: it is taken only from an expired transition (reapable, armed, elapsed time strictly greater than its latest bound plus the tolerance, ruling D4), so the tolerance is applied, and it disarms that transition and nothing else, without firing it: the marking (\"keeps its input tokens\"), the clock reading and every other stamp stay. Several reaps in one deadline step are several reap steps."
          "Line 9 is the 'shall' sentence on reaping, and the first quoted sentence's 'the executor reaps it', as far as one atomic step can state them: from every state in which a transition of the net is expired, a reap of it is a step (the same condition as CoversReap, for this block; TIME-003 and TIME-005 state it for their timings). The step relation has no cycles and no events, so that the reap is taken, in the deadline step of the very cycle ([EXEC-001] step 4), and emits TransitionTimedOut ([EVT-009]) are deferred to Phase 2 and EVT. The atomic relation also lets another transition fire while u is expired (RefTStep does), and that firing may restart u's clock under [TIME-012], which a real cycle cannot do because its deadline step reaps before its firing pass; ClashesTime records this as a Phase 2 obligation (clash013_refresh_rescue)."
          "The tolerance is the field TimedNet.tol, any natural number of milliseconds; the statement holds for every tolerance. Its default of 5 ms, the value 0 for strict enforcement and its exposure as a per-executor option (AC2) are configuration (kind N) and are not encoded."
          "Line 5 ties the state reading Reaped to the act of reaping: an armed transition becomes enabled and unarmed only by a reap of it, so a delay or a firing that silently drops the clock of an enabled transition is not a reap. Transitions are identified by name (ruling D10, InNet): the section assumes pairwise distinct names (NamesDistinct), and the reap of line 5 is of a transition of u's name."
          "Lines 1 and 8 make the transition of a reap or a firing label one of the net's. Without them a label outside the net that shares a name with a net transition but has another timing could reap or fire under that name, and lines 1 to 4 would check the label's timing, not the net's. Under distinct names a label of the net with u's name is u itself (time013_label_eq), so lines 1 to 5 speak of the net's transition (TIME_013_reap_is_of_u). Nets with two transitions of one name are outside ruling D10: the reference step itself then shares one stamp between them, so the statement does not speak to them."
          "Line 3 follows from line 1, as Expired includes Reapable (time013_line3_of_line1); it is kept so the quoted sentence on not reaping a non-reapable transition maps to one line."
          "Lines 6 and 7 are TIME-010's lines 1 and 3 read for a reaped transition (with line 1's fresh stamp in line 7), and are proven from the same policy-generic lemmas. A write is the glossary's Write (ruling D6): any arc place, not only an input place, and draining an empty reset place counts. The injected-token case of the last quoted 'shall' sentence is outside the step relation: injection is not a step of the Phase 1 relation, which has no environment places."
          "AC1 (a Deadline(5s) transition still armed past 5 s plus the tolerance does not fire after that bound; if it is still armed on the first cycle whose elapsed time is strictly greater than the bound, it is reaped in that cycle and TransitionTimedOut is emitted) is the nonvacuous example TIME_013_nonvacuous in milliseconds with tolerance 5: not reaped at elapsed 5005, reaped at 5006, and not fireable then. That the reap falls in the first such cycle is the cycle loop of Phase 2 (RefExec, [EXEC-001] step 4), and the TransitionTimedOut event is [EVT-009], deferred with it. AC3 (an Exact transition past its target is not disabled) is the same example: the Exact(3) transition, at elapsed 5006, cannot be reaped and fires. AC4 (a reaped transition does not fire until an arc place is written, then is armed again with a fresh clock and may fire) is the same example after the reap, ending with a firing of the re-armed transition; the backends (Bitmap, Precompiled) are Phase 2."
          "The paragraph on verification (quiescence reads a marking whose enabled transitions are all reapable as quiescent, Route B drops the latest bounds, assumeNoReaping) belongs to [VER-002], [VER-004] and [VER-012]; it is cited by ReapAware.rest_sound, not encoded here."
  signoff "2026-11-13 cf60477e972fe310 ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
          Expired X s u ∧ Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
          ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
      (∀ u, while (fun s => Reapable X u ∧ (TimingOf X u).latest + Tolerance X < Elapsed s u),
          never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ u, while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s')) ∧
      (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
          Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
          Armed s' u → ∃ t d, l = .fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
      (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
          Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
            Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
      (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions)) ∧
      (∀ u s, u ∈ X.net.transitions → Expired X s u → ∃ s', R X s (.reap u) s')

/- The pinned readable form of TIME-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.TIME_013 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (u : Reference.Trans N),
        on fun s s' => R X s (TLbl.reap u) s', shall fun s s' =>
          u ∈ X.net.transitions ∧
            Expired X s u ∧
              Reaped s' u ∧
                s'.m = s.m ∧
                  ClockReading s' = ClockReading s ∧ ∀ (n : String), n ≠ u.core.name → s'.stamp n = s.stamp n) ∧
      (∀ (u : Reference.Trans N),
          while fun s => Reapable X u ∧ (TimingOf X u).latest + Tolerance X < Elapsed s u, never fun s s' =>
            ∃ d, R X s (TLbl.fire u d) s') ∧
        (∀ (u : Reference.Trans N), while fun x => ¬Reapable X u, never fun s s' => R X s (TLbl.reap u) s') ∧
          (∀ (u : Reference.Trans N), while fun s => Reaped s u, never fun s s' => ∃ d, R X s (TLbl.fire u d) s') ∧
            (∀ (l : TLbl N) (u : Reference.Trans N),
                InNet X u →
                  on fun s s' => R X s l s', shall fun s s' =>
                    Armed s u → Reaped s' u → ∃ v, l = TLbl.reap v ∧ v.core.name = u.core.name) ∧
              (∀ (l : TLbl N) (u : Reference.Trans N),
                  InNet X u →
                    on fun s s' => R X s l s', shall fun s s' =>
                      Reaped s u → Armed s' u → ∃ t d, l = TLbl.fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p) ∧
                (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
                    InNet X u →
                      on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
                        Reaped s u →
                          (∃ p, ArcPlace u p ∧ Writes t d p) →
                            Enabled u s'.m → Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s')) ∧
                  (∀ (t : Reference.Trans N) (d : List N),
                      on fun s s' => R X s (TLbl.fire t d) s', shall fun x x_1 => t ∈ X.net.transitions) ∧
                    ∀ (u : Reference.Trans N) (s : TSt N),
                      u ∈ X.net.transitions → Expired X s u → ∃ s', R X s (TLbl.reap u) s'
-/
#guard_msgs in #print TIME_013

/-! ### The lines, for any policy -/

section Lines

variable {N : Type} [DecidableEq N]

/-- Inversion of a reap step, under any policy: the reaped transition is the net's, the policy
calls it expired, and the step drops its stamp and nothing else. -/
theorem time013_reap_inv {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    (h : RefTStepW P X s (.reap u) s') :
    u ∈ X.net.transitions ∧ P.expired X s u = true ∧
      s' = { s with stamp := fun n => if n = u.core.name then none else s.stamp n } := by
  match h with
  | .reap _ _ _ ht hx => exact ⟨ht, hx, rfl⟩

/-- The effect half of line 1, for any policy: a reap of an armed transition leaves it reaped,
and the marking, the clock reading and every other stamp as they were. -/
theorem time013_reap_effect {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    (h : RefTStepW P X s (.reap u) s') (ha : Armed s u) :
    Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
      ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n := by
  obtain ⟨-, -, rfl⟩ := time013_reap_inv h
  refine ⟨⟨ha.1, fun h' => ?_⟩, rfl, rfl, fun n hn => by simp [hn]⟩
  have := h'.2
  simp at this

/-- A policy whose expiry asks for an armed transition reaps only armed transitions. -/
theorem time013_reap_armed {P : Policy N}
    (hx : ∀ X s t, P.expired X s t = true → s.armed t = true) {X : TimedNet N} {s s' : TSt N}
    {u : Trans N} (h : RefTStepW P X s (.reap u) s') : Armed s u :=
  (armed_iff s u).2 (hx _ _ _ (time013_reap_inv h).2.1)

/-- A firing, under any policy, is of an armed transition the policy does not call expired. -/
theorem time013_fire_live {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    {d : List N} (h : RefTStepW P X s (.fire u d) s') :
    Armed s u ∧ P.expired X s u = false := by
  obtain ⟨-, -, ha, -, hx, -⟩ := refTStepW_fire_inv h
  exact ⟨(armed_iff s u).2 ha, hx⟩

/-- Line 4 for any policy: a reaped transition does not fire, as it is not armed. -/
theorem time013_reaped_noFire {P : Policy N} {X : TimedNet N} {s s' : TSt N} {u : Trans N}
    {d : List N} (h : RefTStepW P X s (.fire u d) s') : ¬ Reaped s u :=
  fun hr => hr.2 (time010_armed h)

/-- Line 5 for any policy whose `keep` keeps only a stamp there is and whose `rearm` arms again
every transition that was armed and is enabled after the firing: an armed transition is left
reaped only by a reap of its name. -/
theorem time013_onlyReap {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → (s.stamp u.core.name).isSome = true)
    (hr : ∀ X s t d m' u, s.armed u = true → enabledNA m' u.core = true →
      P.rearm X s t d m' u = true)
    {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (ha : Armed s u) (hrp : Reaped s' u) :
    ∃ v, l = .reap v ∧ v.core.name = u.core.name := by
  cases h with
  | delay => exact absurd ha hrp.2
  | reap t _ _ =>
    by_cases hn : t.core.name = u.core.name
    · exact ⟨t, rfl, hn⟩
    · refine absurd ⟨hrp.1, ?_⟩ hrp.2
      have := ha.2
      simpa [Ne.symm hn] using this
  | fire t d m' _ _ _ _ _ =>
    refine absurd ⟨hrp.1, ?_⟩ hrp.2
    show (restampAll P X s t d m' u.core.name).isSome = true
    rw [restampAll_inNet hu]
    unfold restampW
    by_cases h1 : P.keep X s t d m' u = true
    · rw [if_pos h1]; exact hk _ _ _ _ _ _ h1
    · rw [if_neg h1, if_pos (hr _ _ _ _ _ _ ((armed_iff s u).1 ha) hrp.1)]; rfl

/-- Line 6 for any policy whose `keep` asks for an armed transition, from TIME-010's
`time010_newly`: a reaped transition of the net armed after a step was armed by a firing
through `rearm`. -/
theorem time013_rearmed_by {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → s.armed u = true)
    {X : TimedNet N} {u : Trans N} (hu : InNet X u) {s s' : TSt N} {l : TLbl N}
    (h : RefTStepW P X s l s') (hrp : Reaped s u) (ha : Armed s' u) :
    ∃ t d, l = .fire t d ∧ P.rearm X s t d s'.m u = true ∧
      s'.stamp u.core.name = some (P.fresh s) ∧ ClockReading s' = ClockReading s :=
  time010_newly hk hu h hrp.2 ha

/-- Line 7 for any policy with the spec's `keep`, a `rearm` that arms an unarmed transition
whose arc place the firing writes, and the spec's fresh reading, from TIME-010's `time010_arms`
and `time010_newly`. -/
theorem time013_rearm_fresh {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → s.armed u = true)
    (hr : ∀ X s t d m' u, s.armed u = false → writesArc t d u = true →
      enabledNA m' u.core = true → P.rearm X s t d m' u = true)
    (hf : ∀ s, P.fresh s = s.now)
    {X : TimedNet N} {t : Trans N} {d : List N} {u : Trans N} (hu : InNet X u) {s s' : TSt N}
    (h : RefTStepW P X s (.fire t d) s') (hrp : Reaped s u)
    (hw : ∃ p, ArcPlace u p ∧ Writes t d p) (hen : Enabled u s'.m) :
    Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s') := by
  have hk' : ∀ X s t d m' u, P.keep X s t d m' u = true → (s.stamp u.core.name).isSome = true :=
    fun X s t d m' u h1 => by
      have := hk X s t d m' u h1
      simp only [TSt.armed, Bool.and_eq_true] at this
      exact this.2
  have ha := time010_arms hk' hr hu h hrp.2 hw hen
  obtain ⟨_, _, -, -, e, hn⟩ := time013_rearmed_by hk hu h hrp ha
  exact ⟨ha, by rw [e, hn, hf]⟩

/-- Line 8 for any policy: a firing is of a transition of the net. -/
theorem time013_fire_mem {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    {d : List N} (h : RefTStepW P X s (.fire t d) s') : t ∈ X.net.transitions :=
  (refTStepW_fire_inv h).1

omit [DecidableEq N] in
/-- Under distinct names (ruling D10), a transition of the net with the name of the net's
transition `u` is `u`. -/
theorem time013_label_eq {X : TimedNet N} (hX : NamesDistinct X) {u v : Trans N}
    (hu : InNet X u) (hv : v ∈ X.net.transitions) (hn : v.core.name = u.core.name) : v = u :=
  List.inj_on_of_nodup_map hX hv (inNet_mem hu) hn

end Lines

/-! ### What the lines give together -/

/-- Line 3 follows from line 1: a reap is taken only from an expired transition, and an expired
transition is reapable. Line 3 stays so the quoted sentence maps to one line. -/
theorem time013_line3_of_line1 {N : Type} [DecidableEq N] {R : TRel N} (h : TIME_013 R)
    (X : TimedNet N) (u : Trans N) :
    while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s') :=
  fun s s' hs hnr => hnr ((h X).1 u s s' hs).2.1.1

/-- Under distinct names, line 5 with line 1 makes the step that leaves the net's armed `u`
reaped a reap of `u` itself, not of another transition of `u`'s name. -/
theorem TIME_013_reap_is_of_u {N : Type} [DecidableEq N] {R : TRel N} (h : TIME_013 R)
    {X : TimedNet N} (hX : NamesDistinct X) {u : Trans N} (hu : InNet X u) {s s' : TSt N}
    {l : TLbl N} (hs : R X s l s') (ha : Armed s u) (hr : Reaped s' u) : l = .reap u := by
  obtain ⟨v, rfl, hn⟩ := (h X).2.2.2.2.1 l u hu s s' hs ha hr
  rw [time013_label_eq hX hu ((h X).1 v s s' hs).1 hn]

/-- Under distinct names, line 8 makes a firing of a label with the name of the net's `u` a
firing of `u` itself, so lines 2 and 4 read for `u` forbid every firing under `u`'s name. -/
theorem TIME_013_fire_is_of_u {N : Type} [DecidableEq N] {R : TRel N} (h : TIME_013 R)
    {X : TimedNet N} (hX : NamesDistinct X) {u v : Trans N} (hu : InNet X u) {d : List N}
    {s s' : TSt N} (hs : R X s (.fire v d) s') (hn : v.core.name = u.core.name) : v = u :=
  time013_label_eq hX hu ((h X).2.2.2.2.2.2.2.1 v d s s' hs) hn

/-- The timed reference step satisfies TIME-013: `refPolicy` reaps only an expired transition
(`tExpired`, which asks for a reapable timing, an armed transition and an elapsed time strictly
past the latest bound plus the tolerance), and the reap drops that stamp alone (lines 1 and 3);
a firing needs its transition armed and not expired (lines 2 and 4); a firing keeps or restarts
the clock of every armed transition enabled after it (line 5); and a reaped transition is armed
again only through `rearm`, which asks for a written arc place, with the current reading
(lines 6 and 7); a firing is of a transition of the net (line 8); and an expired transition of
the net has a reap (line 9). -/
@[evidence holds TIME_013]
theorem TIME_013_reference {N : Type} [DecidableEq N] : TIME_013 (RefTStep (N := N)) := by
  intro X
  refine ⟨fun u s s' h => ?_, fun u s s' ⟨d, h⟩ ⟨hr, hlt⟩ => ?_, fun u s s' h hnr => ?_,
    fun u s s' ⟨d, h⟩ => time013_reaped_noFire h,
    fun l u hu s s' h => time013_onlyReap refPolicy_keep_stamp
      (fun _ _ _ _ _ _ ha hen => by simp [refPolicy, ha, hen]) hu h,
    fun l u hu s s' h hrp ha => ?_,
    fun t d u hu s s' h => time013_rearm_fresh refPolicy_keep_armed refPolicy_rearm_writes
      (fun _ => rfl) hu h, fun t d s s' h => time013_fire_mem h,
    fun u s hu hx => ⟨_, RefTStepW.reap X s u hu ((expired_iff X s u).1 hx)⟩⟩
  · have hx := (time013_reap_inv h).2.1
    have hex : Expired X s u := (expired_iff X s u).2 hx
    exact ⟨(time013_reap_inv h).1, hex, time013_reap_effect h hex.2.1⟩
  · obtain ⟨ha, hx⟩ := time013_fire_live h
    have : tExpired X s u = true := (expired_iff X s u).1 ⟨hr, ha, hlt⟩
    exact Bool.noConfusion (this.symm.trans hx)
  · have hx : tExpired X s u = true := (time013_reap_inv h).2.1
    simp only [tExpired, Bool.and_eq_true] at hx
    exact hnr hx.1.1
  · obtain ⟨t, d, rfl, hrm, -⟩ := time013_rearmed_by refPolicy_keep_armed hu h hrp ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hrp.2
    simp only [refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hrm
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hrm.2⟩

/-! ### Examples (AC1, AC3, AC4) -/

/-- The source of the examples: no arcs but one output on place `0`. -/
def time013_src : Trans Nat :=
  { core := { name := "src", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The transition of AC1: one input arc on place `0`, no output spec, `Deadline(5000)`. -/
def time013_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The transition of AC3: no arcs and no output spec, `Exact(3)`; its firing writes no place. -/
def time013_w : Trans Nat :=
  { core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The timing of the examples, in milliseconds: `u` is `Deadline(5000)` (AC1's 5 s), `w` is
`Exact(3)`, the source `Immediate`. -/
def time013_timing (t : Trans Nat) : Timing :=
  if t.core.name = "u" then .deadline 5000 else if t.core.name = "w" then .exact 3
  else .immediate

/-- The timed net of the examples, with the default tolerance of 5 ms. -/
def time013_X : TimedNet Nat :=
  { net := { places := [0], transitions := [time013_src, time013_u, time013_w] },
    timing := time013_timing, tol := 5 }

theorem time013_u_inX : InNet time013_X time013_u := rfl

/-- The state at reading `now`: one token in place `0`, every transition armed since `0`. -/
def time013_s (now : Nat) : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := now, stamp := fun _ => some 0 }

/-- The state after `u` is reaped at `T = 5006`: `u` holds no clock, the others hold theirs. -/
def time013_r : TSt Nat :=
  { time013_s 5006 with
    stamp := fun n => if n = time013_u.core.name then none else (time013_s 5006).stamp n }

/-- The reap of `u` at `T = 5006`, past `5000 + 5`, under every policy whose expiry is the
spec's. -/
theorem time013_u_reaped {P : Policy Nat} (hx : P.expired = refPolicy.expired) :
    RefTStepW P time013_X (time013_s 5006) (.reap time013_u) time013_r :=
  RefTStepW.reap _ _ _ (by simp [time013_X]) (by rw [hx]; decide)

/-- The state after a firing of `t` with deposit `d` from the reaped state, under policy `P`. -/
def time013_rAfter (P : Policy Nat) (t : Trans Nat) (d : List Nat) : TSt Nat :=
  { m := fireNC time013_r.m t.core (depProd d), now := 5006,
    stamp := restampAll P time013_X time013_r t d (fireNC time013_r.m t.core (depProd d)) }

/-- `w` fires from the reaped state under every policy whose gate and expiry are the spec's. -/
theorem time013_w_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time013_X time013_r (.fire time013_w []) (time013_rAfter P time013_w []) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-! ### Violations: a reap that consumes, a delay that reaps silently -/

/-- A relation whose reap consumes the reaped transition's inputs and drains its reset places
(the intermediate marking `mid`) and otherwise is the reference step. -/
def time013_consumingReap : TRel Nat := fun X s l s' =>
  match l with
  | .reap t => tExpired X s t = true ∧
      s' = { m := mid t s.m, now := s.now,
             stamp := fun n => if n = t.core.name then none else s.stamp n }
  | _ => RefTStep X s l s'

/-- ✗ A reap that consumes tokens violates TIME-013 (line 1): reaping `u` at `T = 5006` takes
the token of its input place, so `u` is no longer enabled, not reaped. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_consumingReap : ¬ TIME_013 time013_consumingReap := by
  intro h
  have hstep : time013_consumingReap time013_X (time013_s 5006) (.reap time013_u)
      { m := mid time013_u (time013_s 5006).m, now := 5006,
        stamp := fun n => if n = time013_u.core.name then none else (time013_s 5006).stamp n } :=
    ⟨by decide, rfl⟩
  exact absurd ((h time013_X).1 time013_u _ _ hstep).2.2.1 (by decide)

/-- The stamps after a delay of `δ` that drops the clock of every transition of the net expired
at the new reading. -/
def time013_dropExpired (X : TimedNet Nat) (s : TSt Nat) (δ : Nat) : String → Option Nat :=
  fun n => match X.net.transitions.find? (·.core.name == n) with
    | some v => if tExpired X { s with now := s.now + δ } v then none else s.stamp n
    | none => s.stamp n

/-- A relation whose delay drops the clock of every transition of the net expired at the new
reading, without a reap step (a silent reap, no `TransitionTimedOut`), and otherwise is the
reference step. -/
def time013_silentReap : TRel Nat := fun X s l s' =>
  match l with
  | .delay δ => s' = { m := s.m, now := s.now + δ, stamp := time013_dropExpired X s δ }
  | _ => RefTStep X s l s'

/-- ✗ A delay that reaps silently violates TIME-013 (line 5): the delay from `T = 5005` to
`5006` leaves `u`, armed before it, reaped, and a delay is not a reap. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_silentReap : ¬ TIME_013 time013_silentReap := by
  intro h
  have hstep : time013_silentReap time013_X (time013_s 5005) (.delay 1)
      { m := (time013_s 5005).m, now := 5006,
        stamp := time013_dropExpired time013_X (time013_s 5005) 1 } := rfl
  obtain ⟨v, e, -⟩ := (h time013_X).2.2.2.2.1 _ time013_u time013_u_inX _ _ hstep
    (by decide) (by decide)
  cases e

/-! ### Violations: a label outside the net reaps or fires under a net transition's name -/

/-- A transition outside the net of the examples, named like `w` but with an input arc on
place `0`. -/
def time013_ghostW : Trans Nat :=
  { core := { name := "w", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The net of the examples with a timing table that gives a transition named `w` with an input
arc (`time013_ghostW`) `Deadline(1)`; every transition of the net keeps its timing. -/
def time013_ghostX : TimedNet Nat :=
  { time013_X with
    timing := fun t =>
      if t.core.name = "w" ∧ t.core.inputs.length = 1 then .deadline 1 else time013_timing t }

/-- A relation that is the reference step, and in addition reaps every expired transition,
whether the net holds it or not (the reference reap without its membership premise). -/
def time013_phantomReap : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ v, l = .reap v ∧ tExpired X s v = true ∧
    s' = { s with stamp := fun n => if n = v.core.name then none else s.stamp n }

/-- ✗ A reap of a label outside the net violates TIME-013 (line 1). At `T = 5006` the expired
ghost of `w` is reaped, which drops the stamp of the name `w` and so leaves the net's `Exact(3)`
transition `w`, not reapable, reaped. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_phantomReap : ¬ TIME_013 time013_phantomReap := by
  intro h
  have hstep : time013_phantomReap time013_ghostX (time013_s 5006) (.reap time013_ghostW)
      { time013_s 5006 with
        stamp := fun n => if n = time013_ghostW.core.name then none else (time013_s 5006).stamp n } :=
    Or.inr ⟨_, rfl, by decide, rfl⟩
  exact absurd ((h time013_ghostX).1 time013_ghostW _ _ hstep).1
    (by simp [time013_ghostX, time013_X, time013_ghostW, time013_src, time013_u, time013_w])

/-- A transition outside the net of the examples with the core of `u` and an output on place
`0`. -/
def time013_ghostU : Trans Nat := { time013_u with out := some (.place 0) }

/-- A relation that is the reference step, and in addition fires a label outside the net
whenever a net transition with the same core takes that firing: the label's own timing, not the
net transition's, is then what lines 2 and 4 would check. -/
def time013_phantomFire : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ t d, l = .fire t d ∧ t ∉ X.net.transitions ∧
    ∃ v ∈ X.net.transitions, v.core = t.core ∧ RefTStep X s (.fire v d) s'

/-- ✗ A firing of a label outside the net violates TIME-013 (line 8): at `T = 0` the net's `u`
fires, and the same firing is taken under the label `time013_ghostU`. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_phantomFire : ¬ TIME_013 time013_phantomFire := by
  intro h
  have hu : RefTStep time013_X (time013_s 0) (.fire time013_u [])
      { m := fireNC (time013_s 0).m time013_u.core (depProd []), now := 0,
        stamp := restampAll refPolicy time013_X (time013_s 0) time013_u []
          (fireNC (time013_s 0).m time013_u.core (depProd [])) } :=
    RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have hstep : time013_phantomFire time013_X (time013_s 0) (.fire time013_ghostU []) _ :=
    Or.inr ⟨_, _, rfl, by simp [time013_X, time013_ghostU, time013_src, time013_u, time013_w],
      time013_u, by simp [time013_X], rfl, hu⟩
  exact absurd ((h time013_X).2.2.2.2.2.2.2.1 _ _ _ _ hstep)
    (by simp [time013_X, time013_ghostU, time013_src, time013_u, time013_w])

/-! ### Mutant: reap at the bound plus the tolerance -/

/-- The policy that calls a reapable armed transition expired once its elapsed time reaches its
latest bound plus the tolerance (`≥` instead of `>`), and decides everything else as the spec
does. -/
def time013_reapAtPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      ((X.timing t).reapable && s.armed t && decide ((X.timing t).latest + X.tol ≤ s.elapsed t)) }

/-- Mutant reading of TIME-013 that reaps at the latest bound plus the tolerance: lines 1 and 2
read "at least" where TIME-013 reads "strictly greater than". The other lines are as in
TIME-013, without its last line (the reap being available). -/
def TIME_013_mutant_reapAt {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
        (Reapable X u ∧ Armed s u ∧ (TimingOf X u).latest + Tolerance X ≤ Elapsed s u) ∧
        Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
        ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
    (∀ u, while (fun s => Reapable X u ∧ (TimingOf X u).latest + Tolerance X ≤ Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s')) ∧
    (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
        Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
          Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions))

/-- The step that reaps at the bound kills the mutant: it satisfies the mutant reading, but not
TIME-013. At `T = 5005` the elapsed time of `u` is `5000 + 5`, not past it, and `u` is
reaped. -/
@[evidence mutant TIME_013]
theorem TIME_013_mutant_reapAt_killed :
    TIME_013_mutant_reapAt (RefTStepW time013_reapAtPolicy) ∧
      ¬ TIME_013 (RefTStepW time013_reapAtPolicy) := by
  have hxa : ∀ X s t, time013_reapAtPolicy.expired X s t = true → s.armed t = true :=
    fun X s t h => by
      simp only [time013_reapAtPolicy, Bool.and_eq_true] at h
      exact h.1.2
  refine ⟨fun X => ⟨fun u s s' h => ?_, fun u s s' ⟨d, h⟩ ⟨hr, hle⟩ => ?_,
      fun u s s' h hnr => ?_, fun u s s' ⟨d, h⟩ => time013_reaped_noFire h,
      fun l u hu s s' h => time013_onlyReap (P := time013_reapAtPolicy) refPolicy_keep_stamp
        (fun _ _ _ _ _ _ ha hen => by simp [time013_reapAtPolicy, refPolicy, ha, hen]) hu h,
      fun l u hu s s' h hrp ha => ?_,
      fun t d u hu s s' h => time013_rearm_fresh (P := time013_reapAtPolicy)
        refPolicy_keep_armed refPolicy_rearm_writes (fun _ => rfl) hu h,
      fun t d s s' h => time013_fire_mem h⟩, fun h => ?_⟩
  · have hx := (time013_reap_inv h).2.1
    have ha := time013_reap_armed hxa h
    simp only [time013_reapAtPolicy, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨(time013_reap_inv h).1, ⟨hx.1.1, ha, by simpa [elapsed_eq] using hx.2⟩,
      time013_reap_effect h ha⟩
  · obtain ⟨ha, hx⟩ := time013_fire_live h
    have ha' := (armed_iff s u).1 ha
    have hr' : (X.timing u).reapable = true := hr
    simp [time013_reapAtPolicy, ha', hr', ← elapsed_eq] at hx
    exact absurd hle (Nat.not_le.2 hx)
  · have hx := (time013_reap_inv h).2.1
    simp only [time013_reapAtPolicy, Bool.and_eq_true] at hx
    exact hnr hx.1.1
  · obtain ⟨t, d, rfl, hrm, -⟩ :=
      time013_rearmed_by (P := time013_reapAtPolicy) refPolicy_keep_armed hu h hrp ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hrp.2
    simp only [time013_reapAtPolicy, refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hrm
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hrm.2⟩
  · have hstep : RefTStepW time013_reapAtPolicy time013_X (time013_s 5005) (.reap time013_u)
        { time013_s 5005 with
          stamp := fun n => if n = time013_u.core.name then none else (time013_s 5005).stamp n } :=
      RefTStepW.reap _ _ _ (by simp [time013_X]) (by decide)
    exact absurd ((h time013_X).1 time013_u _ _ hstep).2.1 (by decide)

/-! ### Mutant: an `Exact` transition is reaped -/

/-- The policy that reaps every transition with a deadline in the sense of `hasDeadline`
(`Deadline`, `Window` and `Exact`), and decides everything else as the spec does. -/
def time013_reapExactPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      ((X.timing t).hasDeadline && s.armed t && decide ((X.timing t).latest + X.tol < s.elapsed t)) }

/-- Mutant reading of TIME-013 that reaps every transition with a deadline (`hasDeadline`,
which `Exact` has, [TIME-001]) instead of every reapable one: lines 1, 2 and 3 read
`hasDeadline` where TIME-013 reads `Reapable`. The other lines are as in TIME-013, without its last line (the reap being available). -/
def TIME_013_mutant_reapExact {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
        ((TimingOf X u).hasDeadline = true ∧ Armed s u ∧
          (TimingOf X u).latest + Tolerance X < Elapsed s u) ∧
        Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
        ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
    (∀ u, while (fun s => (TimingOf X u).hasDeadline = true ∧
          (TimingOf X u).latest + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun _ => ¬ (TimingOf X u).hasDeadline = true),
        never (fun s s' => R X s (.reap u) s')) ∧
    (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
        Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
          Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions))

/-- The step that reaps an `Exact` transition kills the mutant: it satisfies the mutant reading,
but not TIME-013. At `T = 5006` the `Exact(3)` transition `w` is past its target plus the
tolerance and is reaped (AC3 says it is not). -/
@[evidence mutant TIME_013]
theorem TIME_013_mutant_reapExact_killed :
    TIME_013_mutant_reapExact (RefTStepW time013_reapExactPolicy) ∧
      ¬ TIME_013 (RefTStepW time013_reapExactPolicy) := by
  have hxa : ∀ X s t, time013_reapExactPolicy.expired X s t = true → s.armed t = true :=
    fun X s t h => by
      simp only [time013_reapExactPolicy, Bool.and_eq_true] at h
      exact h.1.2
  refine ⟨fun X => ⟨fun u s s' h => ?_, fun u s s' ⟨d, h⟩ ⟨hr, hlt⟩ => ?_,
      fun u s s' h hnr => ?_, fun u s s' ⟨d, h⟩ => time013_reaped_noFire h,
      fun l u hu s s' h => time013_onlyReap (P := time013_reapExactPolicy) refPolicy_keep_stamp
        (fun _ _ _ _ _ _ ha hen => by simp [time013_reapExactPolicy, refPolicy, ha, hen]) hu h,
      fun l u hu s s' h hrp ha => ?_,
      fun t d u hu s s' h => time013_rearm_fresh (P := time013_reapExactPolicy)
        refPolicy_keep_armed refPolicy_rearm_writes (fun _ => rfl) hu h,
      fun t d s s' h => time013_fire_mem h⟩, fun h => ?_⟩
  · have hx := (time013_reap_inv h).2.1
    have ha := time013_reap_armed hxa h
    simp only [time013_reapExactPolicy, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨(time013_reap_inv h).1, ⟨hx.1.1, ha, by simpa [elapsed_eq] using hx.2⟩,
      time013_reap_effect h ha⟩
  · obtain ⟨ha, hx⟩ := time013_fire_live h
    have ha' := (armed_iff s u).1 ha
    have hr' : (X.timing u).hasDeadline = true := hr
    simp [time013_reapExactPolicy, ha', hr'] at hx
    exact absurd hlt (Nat.not_lt.2 hx)
  · have hx := (time013_reap_inv h).2.1
    simp only [time013_reapExactPolicy, Bool.and_eq_true] at hx
    exact hnr hx.1.1
  · obtain ⟨t, d, rfl, hrm, -⟩ :=
      time013_rearmed_by (P := time013_reapExactPolicy) refPolicy_keep_armed hu h hrp ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hrp.2
    simp only [time013_reapExactPolicy, refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hrm
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hrm.2⟩
  · have hstep : RefTStepW time013_reapExactPolicy time013_X (time013_s 5006) (.reap time013_w)
        { time013_s 5006 with
          stamp := fun n => if n = time013_w.core.name then none else (time013_s 5006).stamp n } :=
      RefTStepW.reap _ _ _ (by simp [time013_X]) (by decide)
    exact (h time013_X).2.2.1 time013_w _ _ hstep (by decide)

/-! ### Mutant: a firing re-arms a reaped transition whatever it writes -/

/-- Mutant reading of TIME-013 in which any firing may arm a reaped transition again: line 6
does not ask for a written arc place. The other lines are as in TIME-013, without its last line (the reap being available). -/
def TIME_013_mutant_rearmAny {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
        Expired X s u ∧ Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
        ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
    (∀ u, while (fun s => Reapable X u ∧ (TimingOf X u).latest + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s')) ∧
    (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
        Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
        Armed s' u → ∃ t d, l = .fire t d)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
          Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions))

/-- The step that re-arms on any firing (TIME-010's `time010_rearmAnyPolicy`, the pre-ruling
precompiled behaviour of `deadline_reap_dirty_diverges`) kills the mutant: it satisfies the
mutant reading, but not TIME-013. After `u` is reaped at `T = 5006`, `w` fires and writes no
place, and `u` is armed again. -/
@[evidence mutant TIME_013]
theorem TIME_013_mutant_rearmAny_killed :
    TIME_013_mutant_rearmAny (RefTStepW time010_rearmAnyPolicy) ∧
      ¬ TIME_013 (RefTStepW time010_rearmAnyPolicy) := by
  refine ⟨fun X => ⟨fun u s s' h => ?_, fun u s s' ⟨d, h⟩ ⟨hr, hlt⟩ => ?_,
      fun u s s' h hnr => ?_, fun u s s' ⟨d, h⟩ => time013_reaped_noFire h,
      fun l u hu s s' h => time013_onlyReap (P := time010_rearmAnyPolicy) refPolicy_keep_stamp
        (fun _ _ _ _ _ _ _ hen => hen) hu h,
      fun l u hu s s' h hrp ha => ?_,
      fun t d u hu s s' h => time013_rearm_fresh (P := time010_rearmAnyPolicy)
        refPolicy_keep_armed (fun _ _ _ _ _ _ _ _ hen => hen) (fun _ => rfl) hu h,
      fun t d s s' h => time013_fire_mem h⟩, fun h => ?_⟩
  · have hx := (time013_reap_inv h).2.1
    have hex : Expired X s u := (expired_iff X s u).2 hx
    exact ⟨(time013_reap_inv h).1, hex, time013_reap_effect h hex.2.1⟩
  · obtain ⟨ha, hx⟩ := time013_fire_live h
    have : tExpired X s u = true := (expired_iff X s u).1 ⟨hr, ha, hlt⟩
    exact Bool.noConfusion (this.symm.trans hx)
  · have hx : tExpired X s u = true := (time013_reap_inv h).2.1
    simp only [tExpired, Bool.and_eq_true] at hx
    exact hnr hx.1.1
  · obtain ⟨t, d, rfl, -⟩ :=
      time013_rearmed_by (P := time010_rearmAnyPolicy) refPolicy_keep_armed hu h hrp ha
    exact ⟨t, d, rfl⟩
  · obtain ⟨t, d, e, p, -, hw⟩ := (h time013_X).2.2.2.2.2.1 _ time013_u time013_u_inX _ _
      (time013_w_fires (P := time010_rearmAnyPolicy) rfl rfl) (by decide) (by decide)
    cases e
    simp [Writes, inPlaces, ResetArc, Produced, time013_w] at hw

/-! ### Mutant: no tolerance -/

/-- The policy that calls a reapable armed transition expired once its elapsed time is past its
latest bound, with no tolerance, and decides everything else as the spec does. -/
def time013_noTolPolicy : Policy Nat :=
  { refPolicy with expired := fun X s t =>
      ((X.timing t).reapable && s.armed t && decide ((X.timing t).latest < s.elapsed t)) }

/-- Mutant reading of TIME-013 that applies no deadline tolerance: lines 1 and 2 read "greater
than its latest bound" where TIME-013 reads "greater than its latest bound plus the tolerance".
The other lines are as in TIME-013, without its last line (the reap being available). -/
def TIME_013_mutant_noTolerance {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
        (Reapable X u ∧ Armed s u ∧ (TimingOf X u).latest < Elapsed s u) ∧
        Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
        ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
    (∀ u, while (fun s => Reapable X u ∧ (TimingOf X u).latest < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s')) ∧
    (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
        Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
          Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions))

/-- The step that reaps with no tolerance kills the mutant: it satisfies the mutant reading, but
not TIME-013. At `T = 5001` the elapsed time of `u` is past `5000` but not past `5000 + 5`, and
`u` is reaped. -/
@[evidence mutant TIME_013]
theorem TIME_013_mutant_noTolerance_killed :
    TIME_013_mutant_noTolerance (RefTStepW time013_noTolPolicy) ∧
      ¬ TIME_013 (RefTStepW time013_noTolPolicy) := by
  have hxa : ∀ X s t, time013_noTolPolicy.expired X s t = true → s.armed t = true :=
    fun X s t h => by
      simp only [time013_noTolPolicy, Bool.and_eq_true] at h
      exact h.1.2
  refine ⟨fun X => ⟨fun u s s' h => ?_, fun u s s' ⟨d, h⟩ ⟨hr, hlt⟩ => ?_,
      fun u s s' h hnr => ?_, fun u s s' ⟨d, h⟩ => time013_reaped_noFire h,
      fun l u hu s s' h => time013_onlyReap (P := time013_noTolPolicy) refPolicy_keep_stamp
        (fun _ _ _ _ _ _ ha hen => by simp [time013_noTolPolicy, refPolicy, ha, hen]) hu h,
      fun l u hu s s' h hrp ha => ?_,
      fun t d u hu s s' h => time013_rearm_fresh (P := time013_noTolPolicy)
        refPolicy_keep_armed refPolicy_rearm_writes (fun _ => rfl) hu h,
      fun t d s s' h => time013_fire_mem h⟩, fun h => ?_⟩
  · have hx := (time013_reap_inv h).2.1
    have ha := time013_reap_armed hxa h
    simp only [time013_noTolPolicy, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨(time013_reap_inv h).1, ⟨hx.1.1, ha, by simpa [elapsed_eq] using hx.2⟩,
      time013_reap_effect h ha⟩
  · obtain ⟨ha, hx⟩ := time013_fire_live h
    have ha' := (armed_iff s u).1 ha
    have hr' : (X.timing u).reapable = true := hr
    simp [time013_noTolPolicy, ha', hr', ← elapsed_eq] at hx
    exact absurd hlt (Nat.not_lt.2 hx)
  · have hx := (time013_reap_inv h).2.1
    simp only [time013_noTolPolicy, Bool.and_eq_true] at hx
    exact hnr hx.1.1
  · obtain ⟨t, d, rfl, hrm, -⟩ :=
      time013_rearmed_by (P := time013_noTolPolicy) refPolicy_keep_armed hu h hrp ha
    have hna' : s.armed u = false := by simpa [armed_iff] using hrp.2
    simp only [time013_noTolPolicy, refPolicy, hna', Bool.false_or, Bool.and_eq_true] at hrm
    exact ⟨t, d, rfl, (writesArc_iff t d u).1 hrm.2⟩
  · have hstep : RefTStepW time013_noTolPolicy time013_X (time013_s 5001) (.reap time013_u)
        { time013_s 5001 with
          stamp := fun n => if n = time013_u.core.name then none else (time013_s 5001).stamp n } :=
      RefTStepW.reap _ _ _ (by simp [time013_X]) (by decide)
    exact absurd ((h time013_X).1 time013_u _ _ hstep).2.1 (by decide)

/-! ### Violations: a firing that ignores expiry, a firing while reaped, no re-arming -/

/-- The reference policy with an expiry test that is always false: its firing gate does not
check expiry. -/
def time013_noExpPolicy : Policy Nat := { refPolicy with expired := fun _ _ _ => false }

/-- A relation that reaps as the reference does, and whose firings are the reference's together
with the firings of `time013_noExpPolicy`: a firing pass that judges readiness without the
deadline check, so an expired transition can still fire. -/
def time013_fireExpired : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ (∃ t d, l = .fire t d ∧ RefTStepW time013_noExpPolicy X s l s')

/-- ✗ A firing that ignores expiry violates TIME-013 (line 2): at `T = 5006` the `Deadline(5000)`
transition `u` is past `5000 + 5` and still fires. Its reaps are the reference's, so lines 1, 3
and 9 hold of it. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_fireExpired : ¬ TIME_013 time013_fireExpired := by
  intro h
  have hstep : RefTStepW time013_noExpPolicy time013_X (time013_s 5006) (.fire time013_u [])
      { m := fireNC (time013_s 5006).m time013_u.core (depProd []), now := 5006,
        stamp := restampAll time013_noExpPolicy time013_X (time013_s 5006) time013_u []
          (fireNC (time013_s 5006).m time013_u.core (depProd [])) } :=
    RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  exact (h time013_X).2.1 time013_u _ _ ⟨[], Or.inr ⟨_, _, rfl, hstep⟩⟩ ⟨by decide, by decide⟩

/-- A relation that is the reference step, and in addition fires a transition of the net that is
reaped (enabled and holding no clock), with the reference's marking effect and restamping. -/
def time013_fireReaped : TRel Nat := fun X s l s' =>
  RefTStep X s l s' ∨ ∃ t d, l = .fire t d ∧ t ∈ X.net.transitions ∧ Reaped s t ∧
    s' = { m := fireNC s.m t.core (depProd d), now := s.now,
           stamp := restampAll refPolicy X s t d (fireNC s.m t.core (depProd d)) }

/-- ✗ A firing of a reaped transition violates TIME-013 (line 4): after `u` is reaped at
`T = 5006` it still holds its input token, and it fires. Its elapsed time without a stamp is
`0`, so line 2 does not reject that firing. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_fireReaped : ¬ TIME_013 time013_fireReaped := by
  intro h
  have hr : Reaped time013_r time013_u := by decide
  exact (h time013_X).2.2.2.1 time013_u time013_r _
    ⟨[], Or.inr ⟨_, _, rfl, by simp [time013_X], hr, rfl⟩⟩ hr

/-- The reference policy that never arms a transition again once it holds no clock: `rearm` asks
for the transition to be armed before the firing (the restart of [TIME-012]), not for a written
arc place. -/
def time013_noRearmPolicy : Policy Nat :=
  { refPolicy with rearm := fun _ s _ _ m' u => s.armed u && enabledNA m' u.core }

/-- ✗ A step that keeps a reaped transition reaped for ever violates TIME-013 (line 7): after `u`
is reaped at `T = 5006`, the source fires and deposits into `u`'s input place, `u` is enabled
after the firing, and it is still not armed. -/
@[evidence forbids TIME_013]
theorem TIME_013_forbids_noRearm : ¬ TIME_013 (RefTStepW time013_noRearmPolicy) := by
  intro h
  have hstep : RefTStepW time013_noRearmPolicy time013_X time013_r (.fire time013_src [0])
      (time013_rAfter time013_noRearmPolicy time013_src [0]) :=
    RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)
  have := ((h time013_X).2.2.2.2.2.2.1 time013_src [0] time013_u time013_u_inX _ _ hstep
    (by decide) ((writesArc_iff _ _ _).1 (by decide)) (by decide)).1
  revert this
  decide

/-! ### Mutant: an executor that never reaps -/

/-- The reference step without its reap steps: an executor that never enforces deadlines. -/
def time013_neverReap : TRel Nat := fun X s l s' => RefTStep X s l s' ∧ ∀ v, l ≠ .reap v

/-- Mutant reading of TIME-013 without its last line: nothing asks that an expired transition of
the net have a reap. The other lines are as in TIME-013. -/
def TIME_013_mutant_noReap {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ u, on (fun s s' => R X s (.reap u) s'), shall (fun s s' => u ∈ X.net.transitions ∧
        Expired X s u ∧ Reaped s' u ∧ s'.m = s.m ∧ ClockReading s' = ClockReading s ∧
        ∀ n, n ≠ u.core.name → s'.stamp n = s.stamp n)) ∧
    (∀ u, while (fun s => Reapable X u ∧ (TimingOf X u).latest + Tolerance X < Elapsed s u),
        never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ u, while (fun _ => ¬ Reapable X u), never (fun s s' => R X s (.reap u) s')) ∧
    (∀ u, while (fun s => Reaped s u), never (fun s s' => ∃ d, R X s (.fire u d) s')) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Armed s u →
        Reaped s' u → ∃ v, l = .reap v ∧ v.core.name = u.core.name)) ∧
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => Reaped s u →
        Armed s' u → ∃ t d, l = .fire t d ∧ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        Reaped s u → (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m →
          Armed s' u ∧ s'.stamp u.core.name = some (ClockReading s'))) ∧
    (∀ t d, on (fun s s' => R X s (.fire t d) s'), shall (fun _ _ => t ∈ X.net.transitions))

/-- The executor that never reaps kills the mutant: every step it takes is a reference step, so
it meets lines 1 to 8, but at `T = 5006` the expired `u` has no reap (line 9). -/
@[evidence mutant TIME_013]
theorem TIME_013_mutant_noReap_killed :
    TIME_013_mutant_noReap time013_neverReap ∧ ¬ TIME_013 time013_neverReap := by
  refine ⟨fun X => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := TIME_013_reference (N := Nat) X
    exact ⟨fun u s s' hs => h1 u s s' hs.1, fun u s s' ⟨d, hs⟩ => h2 u s s' ⟨d, hs.1⟩,
      fun u s s' hs => h3 u s s' hs.1, fun u s s' ⟨d, hs⟩ => h4 u s s' ⟨d, hs.1⟩,
      fun l u hu s s' hs => h5 l u hu s s' hs.1, fun l u hu s s' hs => h6 l u hu s s' hs.1,
      fun t d u hu s s' hs => h7 t d u hu s s' hs.1, fun t d s s' hs => h8 t d s s' hs.1⟩
  · obtain ⟨s', -, hne⟩ := (h time013_X).2.2.2.2.2.2.2.2 time013_u (time013_s 5006)
      (by simp [time013_X]) (by decide)
    exact hne time013_u rfl

/-! ### Every line exercised -/

/-- Every line of TIME-013 is exercised by the reference step, in milliseconds with tolerance 5.
AC1: at `T = 5005` the `Deadline(5000)` transition `u` is armed since `0` and cannot be reaped
(line 1, the tolerance band); a delay of 1 makes it expired, and it cannot fire (line 2). AC3:
the `Exact(3)` transition `w`, past its target plus the tolerance, is not reapable, cannot be
reaped (line 3) and fires. The reap of `u` leaves it reaped (lines 1 and 5). AC4: the reaped
`u` cannot fire (line 4); `w` fires and writes none of its arc places, and `u` stays reaped
(line 6); the source fires and writes its input place, and `u` is armed again with the stamp
`5006` (lines 6 and 7), and then fires (AC4's "may fire"). Every firing is of the net (line 8). -/
@[evidence nonvacuous TIME_013]
theorem TIME_013_nonvacuous :
    (∀ s', ¬ RefTStep time013_X (time013_s 5005) (.reap time013_u) s') ∧
      RefTStep time013_X (time013_s 5005) (.delay 1) (time013_s 5006) ∧
      Expired time013_X (time013_s 5006) time013_u ∧
      (∀ d s', ¬ RefTStep time013_X (time013_s 5006) (.fire time013_u d) s') ∧
      ¬ Reapable time013_X time013_w ∧
      (∀ s', ¬ RefTStep time013_X (time013_s 5006) (.reap time013_w) s') ∧
      (∃ s', RefTStep time013_X (time013_s 5006) (.fire time013_w []) s') ∧
      RefTStep time013_X (time013_s 5006) (.reap time013_u) time013_r ∧
      Armed (time013_s 5006) time013_u ∧ Reaped time013_r time013_u ∧
      (∀ d s', ¬ RefTStep time013_X time013_r (.fire time013_u d) s') ∧
      RefTStep time013_X time013_r (.fire time013_w []) (time013_rAfter refPolicy time013_w []) ∧
      Reaped (time013_rAfter refPolicy time013_w []) time013_u ∧
      RefTStep time013_X time013_r (.fire time013_src [0])
        (time013_rAfter refPolicy time013_src [0]) ∧
      Armed (time013_rAfter refPolicy time013_src [0]) time013_u ∧
      (time013_rAfter refPolicy time013_src [0]).stamp "u" = some 5006 ∧
      (∃ s', RefTStep time013_X (time013_rAfter refPolicy time013_src [0]) (.fire time013_u []) s') := by
  refine ⟨fun s' h => ?_, RefTStepW.delay _ _ 1, by decide, fun d s' h => ?_, by decide,
    fun s' h => ?_,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)⟩,
    time013_u_reaped rfl, by decide, by decide, fun d s' h => time013_reaped_noFire h (by decide),
    time013_w_fires rfl rfl, by decide,
    RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide), by decide, by decide,
    ⟨_, RefTStepW.fire _ _ _ _ _ (by simp [time013_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
      (by decide) (by decide) (by decide)⟩⟩
  · have := (time013_reap_inv h).2.1
    revert this
    decide
  · have := (time013_fire_live h).2
    revert this
    decide
  · have := (time013_reap_inv h).2.1
    revert this
    decide

end Libpetri.Spec
