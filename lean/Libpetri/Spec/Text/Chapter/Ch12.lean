import Libpetri.Spec.Text
import Libpetri.Spec.Text.NU_001
import Libpetri.Spec.Text.NU_010
import Libpetri.Spec.Text.NU_011
import Libpetri.Spec.Text.NU_020
import Libpetri.Spec.Text.NU_021
import Libpetri.Spec.Text.NU_022
import Libpetri.Spec.Text.NU_030
import Libpetri.Spec.Text.NU_060
import Libpetri.Spec.Text.NU_040
import Libpetri.Spec.Text.NU_050
import Libpetri.Spec.Text.NU_051
import Libpetri.Spec.Text.NU_052
import Libpetri.Spec.Text.NU_053
import Libpetri.Spec.Text.NU_054
import Libpetri.Spec.Text.NU_055

spec_chapter "12-nu-nets.md"
  scope "Token name identity, fresh-name minting (ν-binder/fork), join by name equality, join relay, name alignment, bounded-budget decidability ledger"
  md r#"# 12 — ν-nets: Correlated Fork / Join by Identity

This document specifies **ν-net** capability: tokens carrying an opaque
correlation **name**, transitions that **mint** fresh names (the ν-binder), and
transitions that **join** by **name equality** across their inputs. Together
these express *fork a unit of work into parallel branches, then re-merge exactly
the siblings that belong together* — without smuggling correlation through
mutable external state (which would reintroduce the TOCTOU hazards CTPN exists to
avoid).

The design adds back the single **decidable** predicate — equality of opaque
names — as a *structural* cross-input constraint (like cardinality), NOT a
general guard. Arbitrary value predicates were removed in [IO-006]; ν-matching
does not reintroduce them (see the note under [IO-006]).

---

## Name Identity"#
  req NU_001
  md r#"---

## ν-binder (Fork)"#
  req NU_010
  md r#"---"#
  req NU_011
  md r#"---

## Join by Name Equality"#
  req NU_020
  md r#"---"#
  req NU_021
  req NU_022
  md r#"---

## Composition"#
  req NU_030
  md r#"---"#
  req NU_060
  md r#"---

## Decidability — the bounded-budget ledger"#
  req NU_040
  md r#"---"#
  req NU_050
  md r#"---"#
  req NU_051
  md r#"---"#
  req NU_052
  md r#"---"#
  req NU_053
  md r#"---"#
  req NU_054
  md r#"---"#
  req NU_055
  md r#"---

## Implementation Notes

- The selection + tie-break ([NU-020]) is a single algorithm shared by both
  executor backends in each language and ported verbatim across languages
  (Rust `match_engine::select_match_name`, Java/TS `MatchEngine.selectMatchName`),
  so firing order is byte-identical.
- A transition with no match spec pays nothing: enablement and consumption take
  the existing fast path; the match path is gated on a per-transition flag.
- Python (`libpetri-py`) inherits the Rust runtime; the key projection is a
  Python callable evaluated under the GIL per candidate token, and `ctx.fresh_name()`
  delegates to the executor-installed minter.
- The bounded-budget lever ([NU-040]) is verified through two dedicated safety
  properties — `BranchPlaceBound(place, k)` (a budget/branch count bound) and
  `JoinedOrDeadLettered(pending)` (no reachable quiescent marking holds a
  `pending` token) — alongside the existing `PlaceBound`. The verifier is told
  which place gates minting via a **budget-place declaration**
  (`budget_place(s)` / `budgetPlaces(...)`); this is what asserts the bounded
  fragment.
- Name alignment ([NU-055]) is the one ν property that compares names rather than
  counting tokens; only Route B decides it, and no other route gives it a verdict.
- The sound **over-approximation baseline** (the name-blind CHC encoding) cannot
  decide two cases soundly: a ν-net with no declared budget (unbounded fresh
  names), and any **quiescence-based** property (deadlock-freedom,
  joined-or-dead-lettered) on a ν-net — whose violation turns on the *absence* of
  an enabled join, which over-firing distorts. The verifier routes exactly those
  cases (and timed ν-nets) to the **Route B** name-aware state-class graph; only
  when Route B also cannot bound the live-name pool (graph truncation) does the
  verdict remain `Unknown`.
- The [NU-050] carve-out (**Route A: bounded name-colouring**) is
  implemented for the **mint → matched-join fragment** of a budget-declared
  ν-net: there, reachability-safety properties are decided over `k` colour slots,
  with no counterexample that equates two different names, so neither `Proven` nor
  `Violated` carries the over-approximation caveat. The verdict rests on the mint and
  relay contracts ([NU-010], [NU-051]). A
  budget-declared ν-net **outside** that fragment falls back to the sound
  over-approximation: a reachability-safety `Proven` is sound (the real net fires
  strictly fewer joins) and a `Violated` is flagged as possibly spurious pending
  the fuller [NU-050] analysis.
- The [NU-050] **Route B** exact analysis (the **SCG name-partition quotient**) is
  implemented in all four bindings (Rust is the source of truth; Python inherits
  it through `verify`; Java and TypeScript port it byte-faithfully, sharing the
  canonical name-partition key format). It decides reachability-safety **and**
  quiescence over the mint → matched-join fragment **without requiring a declared
  budget** for finiteness (that comes from the name-permutation symmetry quotient;
  the mints are still declared, [NU-010]), and
  composes with the timed firing domain (name × time). It is solver-free (it does
  not invoke Z3). The verifier keeps Route A's bounded name-colouring as the
  primary path for budget-declared, untimed reachability-safety (Z3 IC3 scales
  there) and uses Route B for the cases the SMT path cannot decide exactly —
  quiescence, budget-less ν-nets, and timed ν-nets.

---

## References

ν-nets implement the **ν-Petri net** (ν-PN) model — place/transition nets
extended with *pure name creation* (the ν-binder) and name management — and
inherit its decidability frontier: coverability is decidable while reachability
is undecidable. [NU-040] and [NU-050] navigate that frontier with the
bounded-budget lever and the name-aware state-class graph.

- **[RV-08]** F. Rosa-Velardo and D. de Frutos-Escrig. *Name Creation vs.
  Replication in Petri Net Systems.* Fundamenta Informaticae 88(3):329–356, 2008.
- **[RV-11]** F. Rosa-Velardo and D. de Frutos-Escrig. *Decidability and
  Complexity of Petri Nets with Unordered Data.* Theoretical Computer Science
  412(34):4439–4451, 2011. doi:10.1016/j.tcs.2011.05.007"#
