import Libpetri.Spec.All
/-! Regenerates `spec/<chapter>.md` for every chapter declared with `spec_chapter` (the text DSL of
`Libpetri/Spec/Text.lean`), and only those. Run from `lean/` after `lake build`:
`lake env lean spec-tools/Render.lean`. CI runs it and fails when a generated file differs from
the committed one, so a hand edit to a generated file fails CI: edit the Lean text under
`Libpetri/Spec/Text/` instead. It imports `Libpetri.Spec.All`, which imports every module under
`Libpetri/Spec/` directly (`scripts/lean-module-coverage-check.py`), so no chapter is missed. -/

#render_spec "../spec"
