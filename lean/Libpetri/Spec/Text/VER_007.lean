import Libpetri.Spec.Text

requirement_text VER_007
  id "VER-007"
  title "Invariant Strengthening from P-Semiflows"
  priority SHOULD
  kind F
  body r#"⟦s1|The verifier's encoders conjoin every accepted conservation law `y·M = y·M0` into the
transition-rule bodies of the CHC/IC3 encoding ([VER-004], [VER-005]).⟧ ⟦s2|A law is accepted only
by the **exact gate**: `y·C = 0` against the incidence matrix and `y·M0 = c` are re-checked in
exact (overflow-checked) integer arithmetic, and `y` MUST carry zero weight on every place a
transition consumes with `all()` / `atLeast(n)` or clears with a reset arc, because the
encoder's fire relation is not linear there (Lean `Strengthening.lean`, hypotheses H1/H2;
injected environment places are covered by [VER-006], H3').⟧ ⟦s3|A law that fails the gate is
dropped from the encoding and listed in the report.⟧

⟦s4|The encoders *shall* receive a conservation law only when the law passed the exact gate: `y·C = 0` against every column of the incidence matrix, each column counting every token its flat transition deposits and the injector columns of [VER-006] included, and `y·M0` equal to the law's constant, both in exact integer arithmetic, and zero weight on every place a transition consumes with `all()` / `atLeast(n)` or clears with a reset arc.⟧

⟦s5|The encoders *shall* receive every basis row of [VER-005] that passed the gate, whatever the option's setting.⟧

⟦s6|A law whose weights or exact sums leave the implementation's integer range fails the gate with a weight-overflow reason.⟧ ⟦s7|Every implementation's range holds a law whose weights, and the sum of the absolute values of the terms of each of its sums `y·C` and `y·M0`, are at most `2^31 − 1`.⟧

Two sources feed the gate. The null-space basis of [VER-005] is one basis of many: Gaussian
elimination returns mixed-sign rows (discarded as not semi-positive) and rows that fold a reset
place into a chain whose other combinations avoid it (dropped by the gate). On a net with a
handful of reset arcs this can lose every law of the chains those arcs touch, and IC3 then has
to rediscover each conservation law itself, which on a net of a hundred places it does not do
within any practical budget. The non-negative **P-semiflows** (`y ≥ 0`, `y·C = 0`, the minimal
laws of the net, computed by the Farkas / Colom-Silva enumeration) are the missing laws.

**The enumeration is expensive and MUST be skipped when nothing will read it.** The minimal
semiflows of a net are worst-case exponential in its branching: `k` independent diamonds in
series have `2^k` of them, measured at 2 048 for eleven and past the implementation's backstop
beyond thirteen. Computing them for a caller who did not enable this option is a large unforced
cost (27 s of preprocessing on a 24-layer net before the solver sees anything), and on a wide
net an **uncatchable** one, since the heap it exhausts aborts the process rather than returning a
verdict. An implementation MUST compute semiflows only when the option is on, or is `auto` and the
gate dropped a basis row for its weight on a consume-all or reset place. No other phase
reads them: the colour-slot bound of [NU-053] is a linear program over the incidence matrix, not
a semiflow search.

⟦s8|An implementation SHOULD therefore offer an option that unions the gate-validated semiflows
into the invariant list the encoders receive, and SHOULD offer an **`auto`** setting that
applies the condition above on the caller's behalf: compute and union the semiflows exactly
when the basis lost a law to the H1 guard, and skip them otherwise.⟧ That is decidable in one
pass, because the drops are known before the semiflows are needed. It is the setting to prefer
**for verification**: the two useful cases are told apart by a fact the pipeline already has, and
leaving that to the caller has a poor record — the option's unqualified reputation as "the
biggest lever" has led a consumer to enable it globally and then build a size ceiling around its
cost.

⟦s9|*While* the option is off, the encoders *shall* receive exactly the basis rows that passed the gate.⟧

⟦s10|*While* the option is on, the encoders *shall* receive exactly the basis rows and the enumerated semiflows that passed the gate.⟧

⟦s11|*While* the option is `auto`, the encoders *shall* receive what they receive with the option on when the gate dropped a basis row for its weight on a consume-all or reset place, and what they receive with the option off otherwise.⟧

*If* the option is off, or it is `auto` and the gate dropped no basis row for its weight on a consume-all or reset place, *then* the verifier *shall not* compute the semiflows.

**What `auto` does not decide.** It answers whether the semiflows would add information to the
**encoding**, not whether they would appear in the result for a caller who *inspects* the
invariant list. A complete basis spans every conservation law, so a semiflow it spans constrains
nothing further and the solver gains nothing — but the basis is the *signed* null-space, and a
law it spans need not appear in it in **non-negative** form. Only the Farkas enumeration produces
that form. A caller looking for a law by its shape — "a non-negative law weighting the budget
place and every running place positively" — can therefore find nothing on a net that plainly has
such a law, because `auto` correctly skipped an enumeration that would have added no constraint.
Such a caller MUST request the union explicitly. The two claims are both true and easily
confused: `auto` is right about strengthening and says nothing about presentation. The option is **off by default** so that reports
stay byte-identical across releases. It is pure strengthening (Lean `Semiflow.lean`,
`semiflow_union_sound`: conjoining any list of gate-validated laws preserves the abstract
reachable set), so enabling it can never turn a `Violated` into a `Proven`.

**What enabling it does and does not promise.** It is a *strength* option, not a
*correctness* one, and on a branchy net the distinction is sharp. An implementation caps the
rows that survive each elimination round, so where the minimal set is exponential the semiflows
that reach the encoders are an **arbitrary truncation** of it: a proof that needs one particular
law can miss it even though the phase ran to completion and reported no drop. Enabling the
option therefore means "try harder", never "this answer is now trustworthy" — a `Proven` is
equally sound either way, and an `Unknown` with the option on is not evidence that no such law
exists. Implementations SHOULD report the truncation when it binds.

"The encoders" is both of them. The strengthened list reaches the **name-coloured** encoder of
[NU-050] exactly as it reaches the flat one — a coloured place's term becomes the sum over its
colour slots, its aggregate count, so one law stays one equation — and the option is at its most
decisive there: a coloured query already carries the
colour layer's cost, so the laws IC3 would otherwise have to rediscover are the ones it can
least afford to. The trigger is worth stating plainly, because it is the common shape rather
than an exotic one: **a net with even one `all()` / `atLeast(n)` or reset arc on a busy place
loses every basis row whose support touches that place**, so the encoder runs on a deficient
invariant set with nothing in the report to say a law is missing beyond the `Dropped` lines.
Draining an input queue is the everyday case. The option does not rescue those rows — semiflows
face the same gate and a law whose support touches the place is dropped either way. It supplies
the *other* laws: the minimal ones that avoid the place entirely, which elimination had folded
away.

**Acceptance Criteria:**
1. ⟦s12|Semiflows are re-validated by the same exact gate as the basis rows before use; a semiflow
   that fails it is dropped with a `Dropped semiflow:` report line and is never encoded.⟧
2. With the option disabled (the default) the semiflows do not reach the encoders, are not
   computed at all, and the report is byte-identical to a build without the feature.
3. Under `auto` the report says which way it went and why, the union happens exactly when the
   gate dropped a basis row for its weight on a consume-all or reset place, and the verdict never differs from whichever explicit setting `auto` chose. The
   report's "off" wording MUST say that the skipped semiflows add no *constraint*, not that they
   would add nothing, so a caller reading the invariant list is not misled about their absence.
4. With the option enabled the report carries `  Semiflows encoded as invariants: N`, where
   `N` counts the semiflows added after deduplication against the basis rows, and the result's
   invariant count and list include them.
5. `Proven` is never weakened: where the certificate check applies (the flat encoding) it
   receives the strengthened list and re-proves every law's initiation and consecution against
   the unstrengthened step relation before the verdict is reported.
6. A genuine violation stays `Violated` with the option enabled.
7. The strengthened list reaches the name-coloured encoder ([NU-050]) as well as the flat one:
   there is a net on the coloured path whose encoded script differs between the option's two
   states. (Not every such net: a semiflow already present in the basis dedups away, and AC4
   admits `N = 0`, in which case the two scripts are identical.) This is about what the encoder
   receives, not about certification: AC5's certificate check is flat-path only, and a coloured
   `Proven` reports `  Certificate check: not applicable (name-coloured encoding)`.

**Implementation notes:**
- Java: `SmtVerifier.semiflowInvariants(boolean)` and `semiflowInvariants(SemiflowMode)` (`OFF`, `ON`, `AUTO`).
- TypeScript: `SmtVerifier.semiflowInvariants(enabled | 'auto')`.
- Rust: `SmtVerifier::semiflow_invariants(impl Into<SemiflowMode>)`: a `bool`, or `SemiflowMode::Off`, `On` or `Auto`.
- Python: `verify(..., semiflow_invariants=True)`, or `semiflow_invariants="auto"`.

**Depends on:** [VER-004], [VER-005], [VER-006], [NU-050], [NU-053]

**Test derivation:** a budgeted work loop with one reset arc on a side place, whose null-space
basis folds the reset place into the loop's law: a `placeBound` on the loop is proven only with
the option; a bound the loop genuinely exceeds stays `Violated` with it. For AC7, the same loop
beside a budget-declared ν-net, with the reset arc on the uncoloured half (the coloured encoder
refuses a reset on a coloured place, and the net would silently fall back to the flat encoding):
the encoded script must report itself coloured and must differ between the option's two states."#
