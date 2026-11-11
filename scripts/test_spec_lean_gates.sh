#!/usr/bin/env bash
# Planted-fault self-test of the spec/Lean gates. Every case plants one fault in the working
# tree, runs the one gate that must catch it, and passes only if that gate FAILS *and* its output
# contains the gate's own finding text (a fixed string, matched with grep -F). A gate that fails
# for some other reason (a build error, a missing file) therefore does not count as a catch.
#
# Every planted file is restored from a backup right after its case, and again on exit whatever
# happens. Modules a case rebuilt from planted source are rebuilt from the restored source on
# exit. The last step compares the md5 of every file the script may touch with the md5 it had
# at the start, and fails on any difference.
#
# Run from anywhere: scripts/test_spec_lean_gates.sh. Needs the built Lean tree (lake build).
set -uo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lean="$repo/lean"
export PATH="$HOME/.elan/bin:$PATH"

# Every file a case may plant into, relative to the repo root.
core=lean/Libpetri/Spec/Core.lean
all=lean/Libpetri/Spec/All.lean
spec01=spec/01-core-model.md
other=lean/Libpetri/Novel/TimedScg.lean   # a non-Spec module no other module imports
report=lean/spec-tools/Report.lean
router=spec-site/src/app/router.ts        # browser code of the spec site
files=("$core" "$all" "$spec01" "$other" "$report" "$router")

work="$(mktemp -d)"
for f in "${files[@]}"; do mkdir -p "$work/$(dirname "$f")"; cp "$repo/$f" "$work/$f"; done
cp -r "$lean/report" "$work/report"
(cd "$repo" && md5sum "${files[@]}" && find lean/report -type f -print0 | sort -z | xargs -0 md5sum) \
  > "$work/md5.before"

rebuild=()   # lake targets built from planted source; rebuilt on exit
restore() {
  for f in "${files[@]}"; do cp "$work/$f" "$repo/$f"; done
  rm -rf "$lean/report" && cp -r "$work/report" "$lean/report"
}
cleanup() {
  restore
  if [ "${#rebuild[@]}" -gt 0 ]; then
    (cd "$lean" && lake build "${rebuild[@]}" >/dev/null 2>&1) \
      || echo "WARNING: rebuilding ${rebuild[*]} from the restored source failed"
  fi
  rm -rf "$work"
}
trap cleanup EXIT
pass=0; fail=0

# expect_caught NAME CHECK PLANT EXPECTED...: run PLANT, then CHECK (both from lean/). CHECK must
# exit non-zero and its output must contain every EXPECTED string.
expect_caught() {
  local name="$1" check="$2" plant="$3"; shift 3
  local log="$work/case.log" missing=()
  if ! (cd "$lean" && eval "$plant") >"$log" 2>&1; then
    echo "PLANT FAILED $name"; tail -5 "$log"; fail=$((fail + 1)); restore; return
  fi
  if (cd "$lean" && eval "$check") >"$log" 2>&1; then
    echo "NOT CAUGHT  $name (the gate passed)"; tail -5 "$log"; fail=$((fail + 1))
  else
    for want in "$@"; do grep -qF -- "$want" "$log" || missing+=("$want"); done
    if [ "${#missing[@]}" -eq 0 ]; then
      echo "caught      $name: $(grep -m1 -F -- "$1" "$log" | sed 's/^ *//' | cut -c1-110)"
      pass=$((pass + 1))
    else
      echo "WRONG GATE  $name: failed, but without: ${missing[*]}"; tail -8 "$log"
      fail=$((fail + 1))
    fi
  fi
  restore
}

# Gates, as CI runs them (from lean/).
BUILD_CORE='lake env lean Libpetri/Spec/Core.lean'
ESCAPE='python3 ../scripts/lean-escape-hatch-check.py'
AUDIT_SPEC='lake build Libpetri.Spec.All && lake env lean spec-tools/Audit.lean'
AUDIT_OTHER='lake build Libpetri.Novel.TimedScg && lake env lean spec-tools/Audit.lean'
LEANCHECK='lake build Libpetri.Spec.Core && lake env leanchecker Libpetri.Spec.Core'
MODULES='python3 ../scripts/lean-module-coverage-check.py'
ALIGN='python3 ../scripts/spec-lean-alignment.py --report lean/report/requirements.json --spec spec'
# Alignment over a report regenerated from the planted source (the plant is a Lean change).
ALIGN_REGEN="lake build Libpetri.Spec.All && lake env lean spec-tools/Report.lean && $ALIGN"
# Freshness: regenerate and compare with the report as it was before the plant (CI compares
# with the committed report through git diff).
FRESH="lake build Libpetri.Spec.All && lake env lean spec-tools/Report.lean && diff -r '$work/report' report"

# Append Lean text before the closing `end Libpetri.Spec` of Core.lean (python, not sed, so the
# planted text needs no sed escaping). Usage: plant_core 'TEXT'.
plant_core() {
  PLANT="$1" python3 - <<'EOF'
import os
p = "Libpetri/Spec/Core.lean"
s = open(p).read()
assert s.count("\nend Libpetri.Spec\n") == 1
open(p, "w").write(s.replace("\nend Libpetri.Spec\n", "\n" + os.environ["PLANT"] + "\n\nend Libpetri.Spec\n"))
EOF
}

# ---- registry: the `requirement` command and the @[evidence] shape check ------------------

# 1. A blank reading line is rejected by the `requirement` command.
expect_caught "blank reading                -> requirement command" "$BUILD_CORE" \
  'sed -i "s/  reading \"For every transition t and every inhibitor place p of t:\"/  reading \"\"/" Libpetri/Spec/Core.lean' \
  "requirement Libpetri.Spec.CORE_031: a reading line is empty"

# 2. forbids evidence whose statement is not a negation. The planted theorem is true (it is the
#    holds theorem), so only the shape check can fail it.
expect_caught "forbids without ¬            -> evidence shape check" "$BUILD_CORE" \
  "plant_core '/-- planted -/
@[evidence forbids CORE_031]
theorem planted_forbids : CORE_031 (RefFire (N := Nat)) := CORE_031_reference'" \
  "@[evidence forbids] on Libpetri.Spec.planted_forbids: the statement is not a negation"

# 3. holds evidence that assumes the requirement it claims to show.
expect_caught "holds with (h : R F)         -> evidence shape check" "$BUILD_CORE" \
  "plant_core '/-- planted -/
@[evidence holds CORE_031]
theorem planted_holds {N : Type} [DecidableEq N] (h : CORE_031 (RefFire (N := N))) :
    CORE_031 (RefFire (N := N)) := h'" \
  "@[evidence holds] on Libpetri.Spec.planted_holds: the hypothesis" \
  "is not allowed: evidence assumes nothing"

# 4. nonvacuous evidence whose statement is True.
expect_caught "nonvacuous : True            -> evidence shape check" "$BUILD_CORE" \
  "plant_core '/-- planted -/
@[evidence nonvacuous CORE_031]
theorem planted_nonvacuous : True := trivial'" \
  "@[evidence nonvacuous] on Libpetri.Spec.planted_nonvacuous: the statement is True"

# 5. A sign-off naming a hash the block no longer has.
expect_caught "signoff with a stale hash    -> requirement command" "$BUILD_CORE" \
  'sed -i "s/  signoff \"pending\"/  signoff \"2026-11-06 0000000000000000\"/" Libpetri/Spec/Core.lean' \
  "requirement Libpetri.Spec.CORE_031: signoff hash 0000000000000000 does not match the statement hash"

# ---- escape hatches: the source scanner, the axiom audit and the kernel replay -------------

# 5b. A cites tag on a theorem declared in another module: the report would record the tagging
#     module as the theorem's module.
expect_caught "cites on another module's thm -> evidence attribute" "$BUILD_CORE" \
  "plant_core 'attribute [evidence cites \"VER-004\" \"planted\"] Nat.add_comm'" \
  "Nat.add_comm is declared in another module"

# 5c. A cites fragment made only of a zero-width space: trimming does not strip it.
expect_caught "cites with invisible fragment -> evidence attribute" "$BUILD_CORE" \
  "plant_core '/-- planted -/
@[evidence cites \"VER-002\" \"\\u200B\"]
theorem planted_invisible : 1 + 1 = 2 := rfl'" \
  "cites VER-002: the fragment is blank"

# 6. A private axiom in a Spec file: the escape-hatch scan and the axiom audit both catch it.
AX="plant_core 'private axiom cheat : False
/-- planted -/
theorem planted_cheat : 1 = 2 := cheat.elim'"
expect_caught "private axiom                -> escape-hatch scan" "$ESCAPE" "$AX" \
  "ESCAPE axiom lean/Libpetri/Spec/Core.lean:"
rebuild+=(Libpetri.Spec.All)
expect_caught "private axiom                -> #audit_axioms" "$AUDIT_SPEC" "$AX" \
  "axiom audit failed" "is an axiom"

# 7. native_decide: the escape-hatch scan and the axiom audit both catch it. On toolchain v4.32
#    native_decide declares an auxiliary axiom `<thm>._native.native_decide.ax_…` per use.
NATIVE='sed -i "0,/refine ⟨by decide, /s//refine ⟨by native_decide, /" Libpetri/Spec/Core.lean'
expect_caught "native_decide                -> escape-hatch scan" "$ESCAPE" "$NATIVE" \
  "ESCAPE native_decide lean/Libpetri/Spec/Core.lean:"
expect_caught "native_decide                -> #audit_axioms" "$AUDIT_SPEC" "$NATIVE" \
  "axiom audit failed" "Libpetri.Spec.CORE_031_nonvacuous depends on Libpetri.Spec.CORE_031_nonvacuous._native.native_decide."

# 8. sorry in a module outside Libpetri.Spec: the axiom audit walks every Libpetri module.
rebuild+=(Libpetri.Novel.TimedScg)
expect_caught "sorry in a non-Spec module   -> #audit_axioms" "$AUDIT_OTHER" \
  'printf "\nnamespace Libpetri\n/-- planted -/\ntheorem lean_gates_planted_sorry : 1 = 2 := sorry\nend Libpetri\n" >> Libpetri/Novel/TimedScg.lean' \
  "axiom audit failed" "Libpetri.lean_gates_planted_sorry depends on sorryAx"

# 9. A theorem of False added to the environment without the kernel check. #print axioms is
#    blind to it ("does not depend on any axioms"); the source scan and the kernel replay are not.
CHEAT="plant_core 'open Lean Elab Command in
run_cmd liftCoreM do
  let decl := Declaration.thmDecl
    { name := \`plantedFalse, levelParams := [], type := mkConst \`\`False,
      value := mkConst \`\`True.intro }
  match (← getEnv).addDeclCore 0 decl none (doCheck := false) with
  | .ok env => setEnv env
  | .error e => throwKernelException e'"
expect_caught "addDeclCore doCheck := false -> escape-hatch scan" "$ESCAPE" "$CHEAT" \
  "ESCAPE addDeclCore lean/Libpetri/Spec/Core.lean:" "ESCAPE doCheck lean/Libpetri/Spec/Core.lean:"
expect_caught "addDeclCore doCheck := false -> leanchecker" "$LEANCHECK" "$CHEAT" \
  "(kernel) declaration type mismatch"

# ---- module coverage --------------------------------------------------------------------

# 10. A Spec module that All.lean does not import: its blocks would be missing from the report.
expect_caught "Spec module not in All.lean  -> module coverage" "$MODULES" \
  'sed -i "/^import Libpetri.Spec.Core$/d" Libpetri/Spec/All.lean' \
  "MODULES missing Libpetri.Spec.Core in lean/Libpetri/Spec/All.lean"

# 10b. A Libpetri module that Report.lean does not import: its cites tags would silently be
#      missing from proof-coverage.json. Sha256 is reached by no other import.
expect_caught "module not in Report.lean    -> module coverage" "$MODULES" \
  'sed -i "/^import Libpetri.Reference.Sha256$/d" spec-tools/Report.lean' \
  "MODULES missing Libpetri.Reference.Sha256 in lean/spec-tools/Report.lean"

# ---- alignment with the markdown spec ----------------------------------------------------

# 11. The markdown quote drifts from the Lean block.
expect_caught "quote edited in spec/01      -> alignment" "$ALIGN" \
  'sed -i "s/the transition \*shall not\* fire\./the transition *should not* fire./" ../spec/01-core-model.md' \
  "ALIGN quote-missing Libpetri.Spec.CORE_031"

# 12. The quoted sentence survives only inside an HTML comment, which renders as nothing.
expect_caught "quote only in an HTML comment -> alignment" "$ALIGN" \
  'sed -i "s/^\*While\* an inhibitor place of a transition is unmarked, .*$/<!-- & -->/" ../spec/01-core-model.md' \
  "ALIGN quote-missing Libpetri.Spec.CORE_031"

# 13. A citation of a removed (tombstoned) requirement.
expect_caught "citation of tombstoned IO-006 -> alignment" "$ALIGN_REGEN" \
  "plant_core '/-- planted -/
@[evidence cites \"IO-006\" \"guard\"]
theorem planted_cites : 1 + 1 = 2 := rfl'" \
  "ALIGN citation-inactive Libpetri.Spec.planted_cites" "IO-006, a removed (tombstoned) requirement"

# ---- report freshness --------------------------------------------------------------------

# 14. A reading line edited without regenerating the report.
expect_caught "report not regenerated       -> report freshness" "$FRESH" \
  'sed -i "s/t does not fire from a marking in which p is marked;/t never fires from a marking in which p is marked;/" Libpetri/Spec/Core.lean' \
  "diff -r" "t never fires from a marking in which p is marked;"

# 15. A claim added to the generated proof-coverage.json by hand instead of as an
#     @[evidence cites] tag. CI compares the regenerated file with the committed one; here the
#     planted file stands for the committed one, so it is kept before the regeneration.
COV_FRESH="cp report/proof-coverage.json '$work/planted-coverage.json' && lake env lean spec-tools/Report.lean && diff '$work/planted-coverage.json' report/proof-coverage.json"
expect_caught "proof-coverage.json hand edit -> report freshness" "$COV_FRESH" \
  "python3 -c '
import json
p = \"report/proof-coverage.json\"
d = json.load(open(p))
d[\"theorems\"].append({\"name\": \"planted_claim\", \"module\": \"Libpetri/Soundness.lean\",
                       \"specIds\": [{\"id\": \"VER-004\", \"fragment\": \"hand-added\"}]})
open(p, \"w\").write(json.dumps(d, indent=2, ensure_ascii=False) + \"\\n\")
'" \
  "planted_claim" "hand-added"

# ---- spec site -----------------------------------------------------------------------------

# 16. A wrong-typed assignment in the site's browser code: `npm run check` (both tsconfigs, as
#     CI runs it) must fail on it. Needs spec-site/node_modules (npm ci in spec-site).
if [ -d "$repo/spec-site/node_modules" ]; then
  expect_caught "type error in spec-site/src/app -> npm run check" '(cd ../spec-site && npm run check)' \
    'printf "\nexport const plantedTypeError: number = \"planted\";\n" >> ../spec-site/src/app/router.ts' \
    "src/app/router.ts(" "error TS2322: Type 'string' is not assignable to type 'number'."
else
  echo "skipped     type error in spec-site/src/app: spec-site/node_modules is missing (run npm ci in spec-site)"
fi

# ---- every planted file is back as it was -------------------------------------------------
restore
if [ "${#rebuild[@]}" -gt 0 ]; then
  (cd "$lean" && lake build "${rebuild[@]}" >/dev/null 2>&1) || { echo "rebuild failed"; fail=$((fail + 1)); }
  rebuild=()
fi
if (cd "$repo" && md5sum --quiet -c "$work/md5.before") >"$work/md5.log" 2>&1 \
   && [ "$(cd "$repo" && find lean/report -type f | wc -l)" -eq "$(grep -c ' lean/report/' "$work/md5.before")" ]; then
  echo "restored    every planted file has its original md5"
else
  echo "NOT RESTORED"; cat "$work/md5.log"; fail=$((fail + 1))
fi

echo "planted faults caught: $pass, not caught: $fail"
[ "$fail" -eq 0 ]
