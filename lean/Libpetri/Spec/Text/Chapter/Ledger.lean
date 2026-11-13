import Libpetri.Spec.Text

spec_chapter "runtime-defects.md"
  md r#"# Runtime Ledger

This file is not a requirement file. It holds no requirement IDs of its own and is not counted
in the 13 spec files or the active requirements of [00-index.md](00-index.md).

It holds three kinds of entry:

- **Defect** (`RD-NN`): a runtime breaks a requirement that the spec keeps. See [Defects](#defects).
- **UNBUILT** (`UB-NN`): a `**Status:** Proposed` requirement that a runtime it targets has not
  built. There is one entry per requirement and set of runtimes. An entry is removed when those
  runtimes build the requirement, and the requirement's Status line is deleted when its last entry
  goes.
- **Divergence**: an implementation-defined difference that the spec allows. It needs no fix and
  has no status.

## Unbuilt requirements"#
  table unbuilt
  md r#"## Divergences

Python binds the Rust crate, so it follows the Rust column unless a cell says otherwise."#
  table divergences
  md r#"## Defects

A **runtime defect** is a place where a runtime breaks a requirement that the spec keeps. The
spec was not weakened to match the runtime: the requirement stays as written, the Lean block
states it, and the runtime is fixed later in a runtime change. Each entry names the requirements
it breaks, the runtimes that break them, where in the code, and the Lean evidence that shows it,
if there is any. A Lean block that calls something a recorded defect cites the entry by its
number (`RD-NN`).

An entry stays `open` until the runtime change lands. Its status is then `fixed, unreleased` until
a release carries the fix, and `fixed in <version>` after that. A fixed entry stays here as history,
with a **Fix** item that says what changed and names the regression tests in each runtime. Code
is named by its function, type or test, not by line number.

Every entry from RD-01 to RD-43 is fixed. RD-44 to RD-47 were found while those fixes were made and
are recorded here already fixed.

RD-10, RD-13 and RD-14 were withdrawn on 2026-11-12 as not defects: transition names are assumed
distinct (ruling D23), non-ASCII cluster names are implementation-defined (ruling D46 (a)), and the
collision of sanitized IDs is a known limit of EXP-016. Their numbers are not reused."#
  table defectTable
  table defects
