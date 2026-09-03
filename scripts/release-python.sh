#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PYTHON_DIR="$PROJECT_ROOT/python"
RUST_DIR="$PROJECT_ROOT/rust"

DRY_RUN=false
VERSION=""

usage() {
    cat <<EOF
Usage: $(basename "$0") [--dry-run] <version>

Release libpetri Python wheels to PyPI.

Builds wheels + sdist via maturin, smoke-installs the built wheel, uploads to
PyPI, tags python/v<version>, creates GitHub release. Resyncs Cargo.lock at
the end (mirrors release-rust.sh gotcha).

Prerequisites:
  - python3, maturin, twine
  - PyPI credentials via ~/.pypirc or TWINE_USERNAME/TWINE_PASSWORD
  - gh CLI authenticated

Arguments:
  version       Release version (e.g. 2.6.0)

Options:
  --dry-run     Build + smoke-test only; skip upload, tag, release
  -h, --help    Show this help
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run) DRY_RUN=true; shift ;;
        -h|--help) usage; exit 0 ;;
        -*) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
        *) VERSION="$1"; shift ;;
    esac
done

if [[ -z "$VERSION" ]]; then
    echo "Error: version argument required" >&2
    usage >&2
    exit 1
fi

info()  { echo "==> $*"; }
error() { echo "Error: $*" >&2; exit 1; }

# Extract the CHANGELOG.md section for the given version. Matches a `## ` header
# that contains the version as a space-delimited token, so it works with the
# coordinated multi-language headers (e.g. `## Java 4.0.0 / Python 3.1.0 — …`)
# as well as a bare `## 3.1.0`. Prints empty string if no section matches.
changelog_section() {
    awk -v v="$1" '
        BEGIN { gsub(/\./, "\\.", v); re = " " v " " }
        /^## / && $0 ~ re { p = 1; next }
        p && /^## / { exit }
        p
    ' "$PROJECT_ROOT/CHANGELOG.md"
}

have_pypi_auth() {
    if [[ -n "${TWINE_USERNAME:-}" && -n "${TWINE_PASSWORD:-}" ]]; then
        return 0
    fi
    [[ -f ~/.pypirc ]] && grep -q '^\[pypi\]' ~/.pypirc
}

cleanup() {
    rm -rf "$PYTHON_DIR/.release-venv"
}
trap cleanup EXIT

info "Validating prerequisites"

if ! git -C "$PROJECT_ROOT" diff --quiet || ! git -C "$PROJECT_ROOT" diff --cached --quiet; then
    error "Working tree has uncommitted changes. Commit or stash first."
fi

command -v python3 >/dev/null 2>&1 || error "python3 not found in PATH"
command -v maturin >/dev/null 2>&1 || error "maturin not found in PATH"
python3 -m twine --version >/dev/null 2>&1 || error "twine not available"

if ! gh auth status >/dev/null 2>&1; then
    error "GitHub CLI not authenticated. Run 'gh auth login' first."
fi

if [[ "$DRY_RUN" == false ]] && ! have_pypi_auth; then
    error "No PyPI credentials. Configure ~/.pypirc or TWINE_USERNAME/TWINE_PASSWORD."
fi

if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "python/v${VERSION}" >/dev/null 2>&1; then
        error "Tag python/v${VERSION} already exists."
    fi
fi

info "Setting libpetri-py (Python wheel) version to ${VERSION}"
cd "$RUST_DIR"
# Python is versioned independently of the Rust crates: bump only the
# libpetri-py package version (maturin reads it via the dynamic version),
# never the shared workspace version of the published Rust crates.
sed -i "s/^version = \".*\"/version = \"$VERSION\"/" libpetri-py/Cargo.toml

# Sync Cargo.lock so the maturin `--locked` build below doesn't reject the
# now-stale lockfile.
cargo update --workspace --offline >/dev/null

cd "$PROJECT_ROOT"
git add rust/libpetri-py/Cargo.toml rust/Cargo.lock
git diff --cached --quiet || git commit -m "release: python ${VERSION}"

info "Building Python wheel and sdist"
cd "$PYTHON_DIR"
rm -rf dist
maturin build --release --locked --out dist --compatibility pypi
maturin sdist --out dist

info "Smoke-testing built wheel in a virtual environment"
python3 -m venv .release-venv
# shellcheck disable=SC1091
source .release-venv/bin/activate
python -m pip install --upgrade pip
python -m pip install dist/libpetri-*.whl pytest pytest-asyncio
# `pytest`, not `python -m pytest`: the -m form prepends the cwd to sys.path,
# and the cwd here is python/, which contains the libpetri source package. That
# shadows the wheel we just installed, so the smoke test silently exercised the
# source tree against whatever stale `python/libpetri/_libpetri*.so` a previous
# `maturin develop` left behind — gitignored, so invisible in `git status`. It
# failed 37 tests against a perfectly good 3.0.1 wheel before this was fixed.
# The console script does not touch sys.path, so the import resolves to
# site-packages and the test covers what actually ships.
pytest tests
deactivate

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run complete. Python artifacts in python/dist/."
    info "Note: version commit created. Run 'git reset HEAD~1' to undo if needed."
    exit 0
fi

info "Uploading wheels and sdist to PyPI"
python3 -m twine upload dist/*

cd "$PROJECT_ROOT"
info "Creating tag python/v${VERSION}"
git tag -a "python/v${VERSION}" -m "Release python ${VERSION}"

info "Pushing commit and tag"
git push origin HEAD
git push origin "python/v${VERSION}"

info "Creating GitHub release"
NOTES=$(changelog_section "$VERSION")
if [[ -z "${NOTES// }" ]]; then
    gh release create "python/v${VERSION}" \
        --title "Python v${VERSION}" \
        --generate-notes
else
    gh release create "python/v${VERSION}" \
        --title "Python v${VERSION}" \
        --notes "$NOTES"
fi

# Resync Cargo.lock if maturin/cargo touched it. Mirrors the documented
# release-rust.sh gotcha: lockfile updates after a workspace version bump
# need a separate commit so subsequent CI runs use the bumped version.
info "Checking for Cargo.lock drift"
cd "$RUST_DIR"
if ! git -C "$PROJECT_ROOT" diff --quiet rust/Cargo.lock; then
    cd "$PROJECT_ROOT"
    git add rust/Cargo.lock
    git commit -m "chore: sync rust Cargo.lock to ${VERSION}"
    git push origin HEAD
fi

info "Released Python v${VERSION} to PyPI and GitHub."
