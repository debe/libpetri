import Libpetri.Spec.Text

spec_chapter "00-index.md"
  md r#"# CTPN Technical Requirements Specification

## Purpose

This specification defines the **observable contract** of the Coloured Time Petri Net (CTPN) engine — what the engine guarantees, not how any particular language implements it. It exists for:

1. **AI verification** — ask "does implementation X still match spec Y?"
2. **Test derivation** — every requirement maps to testable criteria
3. **Cross-implementation consistency** — all three languages agree on behavior
4. **Living documentation** — single source of truth for the engine contract

## Implementations

| Implementation | Language | Location | Runtime | Maturity |
|---|---|---|---|---|
| **libpetri-java** | Java 25 | `java/` | Virtual threads | Production |
| **libpetri-ts** | TypeScript | `typescript/` | JS event loop + Promises | Production |
| **libpetri-rs** | Rust 1.85+ | `rust/` | Tokio async | v0.1.0 |
| **libpetri-py** | Python ≥3.11 | `python/` (binds Rust) | Tokio async via PyO3 | Beta |

## Spec Philosophy

- **Language-agnostic**: Requirements describe *what*, not *how*. No Java types, Rust traits, or TypeScript interfaces appear in requirement text.
- **Verifiable**: Every requirement has acceptance criteria that can be tested.
- **Traceable**: Requirements use `[PREFIX-NNN]` cross-references.
- **Rule only**: requirement text states no runtime status. Per-language API names are in each language's own documentation; defects, unbuilt requirements and implementation-defined divergences are in the runtime ledger ([runtime-defects.md](runtime-defects.md)).
- **Status lines**: an accepted requirement carries no `Status` line. `**Status:** Proposed` marks a requirement that at least one implementation it targets has not built yet. The spec does not say which: each such implementation has an UNBUILT entry for the requirement in the runtime ledger ([runtime-defects.md](runtime-defects.md)), and the Status line is deleted when the last entry closes. `**Status:** Removed` marks a tombstone. Requirement text states the rule only; what a runtime does beyond it belongs to that runtime's own documentation, and where a runtime breaks an accepted requirement, to a defect entry in the ledger.

---

## Spec Files"#
  table files
  table tombstones
  md r#"The advice that [CORE-064], [CONC-012] and [EXEC-050] carried is kept in [Usage guidance (non-normative)](#usage-guidance-non-normative)."#
  md r#"[glossary.md](glossary.md) defines the terms of the CORE and IO firing semantics. It is unnumbered, holds no requirements and is not counted above.

[runtime-defects.md](runtime-defects.md) is the runtime ledger. It records each place where a runtime breaks or broke a requirement the spec keeps (`RD-NN`, open or fixed, with the change that fixed it), each Proposed requirement a targeted runtime has not built (UNBUILT), and the implementation-defined divergences the spec allows. It is unnumbered, holds no requirements and is not counted above.

---

## Alphabetical Cross-Reference Index"#
  table crossref
  md r#"---

## Priority Distribution"#
  table priorities
  md r#"---

## Coverage Matrix

The proof and test coverage of every active requirement, per implementation, is [coverage-matrix.md](coverage-matrix.md), which `scripts/spec-coverage-matrix.py` generates from the Lean evidence and the `[ID]` citations in the tests."#
  md r#"---

## Real-World Pattern Examples

These patterns are derived from a representative real-time event-driven workflow (~50 transitions, 70+ places) and are called out in the relevant spec files:

| Pattern | Spec Requirement | Example |
|---|---|---|
| Reset arcs don't require tokens | [CORE-034] | Timestamp place cleared on new operation |
| Read arcs enable multi-reader | [CORE-033] | Shared result list read by multiple downstream actions |
| Inhibitor negative precondition | [CORE-031] | Violation flag blocks downstream fork |
| XOR exactly-one routing | [IO-012] | Guard → safe/violation; Classification → branch A/branch B |
| In.all() drain semantics | [IO-003] | Buffered data drained on processing window open |
| Competitive scheduling | [EXEC-003] + [TIME-014] | Primary action P=10 vs fallback P=-10 with 3s delay |
| Implicit long-running behavior | [ENV-010] | Session awaits external events indefinitely |
| Multiple environment places | [ENV-012] | Activity signals, data streams, tool requests, state changes |
| Action timeout | [EXEC-022] | Guard actions with 2s timeout |
| Stale detection via read arc | [CORE-032] + [CORE-010] (see [Usage guidance](#usage-guidance-non-normative)) | Commit action reads latest timestamp to detect staleness |

## Usage guidance (non-normative)

This section holds advice that used to be written as requirements. It binds no implementation,
has no acceptance criteria and is not counted above. Each entry names the tombstone it came
from.

### Stale detection with a read arc (from [EXEC-050])

A transition can tell whether the data it consumes is still current by comparing timestamps. It
reads a "latest request timestamp" through a read arc ([CORE-032]) and compares it with the
creation timestamp of the token it consumes ([CORE-010]). The engine provides only these
primitives: the comparison is action logic, and a stale token can be routed to a discard
branch through an XOR output ([IO-012]). To test it, read the latest timestamp, consume an
older token and check that the action takes the discard branch.

### Bounding concurrent actions with a permit place (from [CONC-012])

An executor may expose a limit on the number of actions in flight at once, to keep a net with
many enabled transitions from exhausting resources; no implementation does today. The same
bound is better written in the net: a permit place holding N tokens, an input arc from it on
every transition that starts bounded work and an output arc back to it on the transition that
finishes that work.
At most N such actions are then in flight, the rest wait until a permit returns, and the bound
is visible to verification as a place bound.

### Host objects in the transition context (from [CORE-064])

A language binding may let the host put objects such as a tracing span or configuration into
the transition context, keyed by type or by string key, so that the action can read them while
it runs and gets nothing (null or None) for a key that was never set. Not every implementation
offers this, and no requirement depends on it."#
