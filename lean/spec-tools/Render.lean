import Libpetri.Spec.All
/-! Regenerates `spec/<chapter>.md` for every chapter declared with `spec_chapter` (the text DSL of
`Libpetri/Spec/Text.lean`; the index's tables, the glossary terms and the runtime ledger are
computed by `Libpetri/Spec/Generate.lean`), and only those. Run from `lean/` after `lake build`:
`lake env lean spec-tools/Render.lean`. Before it writes, it checks the whole program, the Lean
sources under `Libpetri/` included (`#render_spec`), so it runs from `lean/`. CI runs it and fails
when a generated file differs from the committed one, so a hand edit to a generated file fails CI:
edit the Lean source under `Libpetri/Spec/Text/` or `Libpetri/Spec/Ledger/` instead. It imports
`Libpetri.Spec.All`, which imports every module under `Libpetri/Spec/` directly
(`scripts/lean-module-coverage-check.py`), so no chapter or ledger entry is missed. -/

#render_spec "../spec"
