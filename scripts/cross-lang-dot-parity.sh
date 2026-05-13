#!/usr/bin/env bash
# Cross-language DOT byte-parity check per spec/09-export.md [EXP-014].
#
# Builds a battery of canonical fixture nets in all three languages, captures
# each language's DOT output, and asserts the three files are byte-identical
# per scenario.
#
# Scenarios exercised:
#   - pipeline           — producer / bounded-buffer / consumer composed via
#                          PetriNet.builder().compose(...) (clusters present).
#   - flat               — plain non-composed net (no composition / clusters).
#   - junctions          — nested AND(XOR(a,b), c) output spec; exercises
#                          XOR/AND junction synthesis per EXP-012.
#   - reset-output       — transition with both Out.Place(P) and reset(P);
#                          exercises reset+output collapse per EXP-013.
#   - inhibitor-read     — transition with Read + Inhibitor arcs; exercises
#                          distinct styling categories.
#
# Per-language fixture-runner naming convention (`<lang>` ∈ {java, ts, rust}):
#   - Java:       java/src/test/java/org/libpetri/export/CrossLang<Scenario>Dot.java
#                 (run via `./mvnw test -Dtest=CrossLang<Scenario>Dot`)
#   - TypeScript: typescript/scripts/cross-lang-<scenario>-dot.ts
#                 (run via `npx tsx scripts/cross-lang-<scenario>-dot.ts`)
#   - Rust:       rust/libpetri/tests/cross_lang_<scenario>_dot.rs
#                 (run via `cargo test --test cross_lang_<scenario>_dot`)
#
# Usage (from repo root or anywhere):
#   ./scripts/cross-lang-dot-parity.sh [--keep-tmp]
#
# Exit codes:
#   0 — all three DOT outputs are byte-identical for every scenario
#   1 — at least two languages produced different DOT in at least one scenario
#   2 — one of the per-language runners failed to execute
#
# Options:
#   --keep-tmp  Do not delete the temp directory holding the captured DOT files.
#               (Useful for post-mortem inspection; the path is printed.)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JAVA_DIR="$REPO_ROOT/java"
TS_DIR="$REPO_ROOT/typescript"
RUST_DIR="$REPO_ROOT/rust"

TMP_DIR="$(mktemp -d -t libpetri-cross-lang-parity-XXXXXX)"
KEEP_TMP=0
for arg in "$@"; do
    case "$arg" in
        --keep-tmp) KEEP_TMP=1 ;;
        -h|--help)
            sed -n '1,30p' "$0"
            exit 0
            ;;
        *)
            echo "Unknown argument: $arg" >&2
            exit 2
            ;;
    esac
done

cleanup() {
    if [[ "$KEEP_TMP" -eq 0 ]]; then
        rm -rf "$TMP_DIR"
    else
        echo
        echo "Kept temp dir: $TMP_DIR"
    fi
}
trap cleanup EXIT

echo "=== libpetri cross-language DOT byte-parity check ==="
echo "Temp dir: $TMP_DIR"
echo

EXIT=0

# Scenario table: each row is
#   <scenario-id> <java-test-class> <ts-script-stem> <rust-test-stem>
# The TS and Rust stems are interpolated into per-language paths.
SCENARIOS=(
    "pipeline       CrossLangPipelineDot      cross-lang-pipeline-dot       cross_lang_pipeline_dot"
    "flat           CrossLangFlatDot          cross-lang-flat-dot           cross_lang_flat_dot"
    "junctions      CrossLangJunctionsDot     cross-lang-junctions-dot      cross_lang_junctions_dot"
    "reset-output   CrossLangResetOutputDot   cross-lang-reset-output-dot   cross_lang_reset_output_dot"
    "inhibitor-read CrossLangInhibitorReadDot cross-lang-inhibitor-read-dot cross_lang_inhibitor_read_dot"
)

compare() {
    local a_label="$1" a_path="$2" b_label="$3" b_path="$4"
    if cmp -s "$a_path" "$b_path"; then
        echo "    $a_label vs $b_label: identical"
    else
        echo "    $a_label vs $b_label: DIFFER"
        echo "      diff (first 30 lines):"
        # `diff` returns non-zero when files differ; tolerate that under
        # `set -e` / pipefail so the surrounding loop keeps running and
        # reports every diverging scenario, not just the first.
        diff "$a_path" "$b_path" 2>&1 | head -30 | sed 's/^/        /' || true
        EXIT=1
    fi
}

run_scenario() {
    local scenario="$1" java_class="$2" ts_stem="$3" rust_stem="$4"
    local scenario_dir="$TMP_DIR/$scenario"
    mkdir -p "$scenario_dir"
    local java_dot="$scenario_dir/java.dot"
    local ts_dot="$scenario_dir/ts.dot"
    local rust_dot="$scenario_dir/rust.dot"

    echo "=== Scenario: $scenario ==="

    echo "  --- Java ($java_class) ---"
    (
        cd "$JAVA_DIR"
        ./mvnw -q test \
            -Dtest="$java_class" \
            -Dlibpetri.crossLang.outFile="$java_dot" \
        >/dev/null
    ) || {
        echo "  Java runner failed for scenario '$scenario'." >&2
        exit 2
    }
    [[ -s "$java_dot" ]] || { echo "  Java DOT output is empty: $java_dot" >&2; exit 2; }
    echo "    wrote $java_dot ($(wc -c <"$java_dot" | tr -d ' ') bytes)"

    echo "  --- TypeScript ($ts_stem.ts) ---"
    (
        cd "$TS_DIR"
        npx tsx "scripts/$ts_stem.ts" --out="$ts_dot" >/dev/null
    ) || {
        echo "  TypeScript runner failed for scenario '$scenario'." >&2
        exit 2
    }
    [[ -s "$ts_dot" ]] || { echo "  TypeScript DOT output is empty: $ts_dot" >&2; exit 2; }
    echo "    wrote $ts_dot ($(wc -c <"$ts_dot" | tr -d ' ') bytes)"

    echo "  --- Rust ($rust_stem) ---"
    (
        cd "$RUST_DIR"
        LIBPETRI_CROSS_LANG_OUT="$rust_dot" \
            cargo test -q -p libpetri --test "$rust_stem" >/dev/null 2>&1
    ) || {
        echo "  Rust runner failed for scenario '$scenario'." >&2
        exit 2
    }
    [[ -s "$rust_dot" ]] || { echo "  Rust DOT output is empty: $rust_dot" >&2; exit 2; }
    echo "    wrote $rust_dot ($(wc -c <"$rust_dot" | tr -d ' ') bytes)"

    echo "  Comparison:"
    compare "Java"       "$java_dot" "TypeScript" "$ts_dot"
    compare "Java"       "$java_dot" "Rust"       "$rust_dot"
    compare "TypeScript" "$ts_dot"   "Rust"       "$rust_dot"
    echo
}

for row in "${SCENARIOS[@]}"; do
    # shellcheck disable=SC2086 -- intentional word-splitting on the row.
    set -- $row
    run_scenario "$1" "$2" "$3" "$4"
done

if [[ "$EXIT" -eq 0 ]]; then
    echo "All scenarios: DOT outputs are byte-identical across Java, TypeScript, and Rust."
else
    echo "Cross-language DOT parity broken — see diffs above."
fi
exit "$EXIT"
