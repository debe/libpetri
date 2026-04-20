#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

# --- Defaults ---
DRY_RUN=false
VERSION=""

# --- Usage ---
usage() {
    cat <<EOF
Usage: $(basename "$0") [--dry-run] <version>

Release libpetri Rust crates to crates.io.

Publishes 8 crates in dependency order with indexing delays.

Prerequisites:
  - cargo login (crates.io token in ~/.cargo/credentials.toml)
  - gh CLI authenticated (for GitHub release)

Arguments:
  version       Release version (e.g. 1.3.2)

Options:
  --dry-run     Build and test only; skip publish, tag, release
  -h, --help    Show this help

Example:
  $(basename "$0") 1.3.2
  $(basename "$0") --dry-run 1.3.2
EOF
}

# --- Parse args ---
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

# --- Helpers ---
info()  { echo "==> $*"; }
error() { echo "Error: $*" >&2; exit 1; }

# --- Validate prerequisites ---
info "Validating prerequisites"

# Clean working tree (untracked files are OK)
if ! git -C "$PROJECT_ROOT" diff --quiet || ! git -C "$PROJECT_ROOT" diff --cached --quiet; then
    error "Working tree has uncommitted changes. Commit or stash first."
fi

# cargo authenticated
if [[ ! -f ~/.cargo/credentials.toml ]]; then
    error "No cargo credentials found. Run 'cargo login' first."
fi

# gh CLI authenticated
if ! gh auth status >/dev/null 2>&1; then
    error "GitHub CLI not authenticated. Run 'gh auth login' first."
fi

# Check tag doesn't already exist (unless dry-run)
if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "rust/v${VERSION}" >/dev/null 2>&1; then
        error "Tag rust/v${VERSION} already exists."
    fi
fi

# --- Set version ---
info "Setting Rust version to ${VERSION}"
cd "$RUST_DIR"
# Workspace version (inherited by all crates via version.workspace = true)
sed -i "s/^version = \".*\"/version = \"$VERSION\"/" Cargo.toml
# Workspace dependency version pins (path = "...", version = "X.Y.Z")
sed -i "s/\(path = \"[^\"]*\"\), version = \"[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\"/\1, version = \"$VERSION\"/g" Cargo.toml

# --- Commit the version bump ---
cd "$PROJECT_ROOT"
git add rust/Cargo.toml
git diff --cached --quiet || git commit -m "release: rust ${VERSION}"

# --- Build and test ---
info "Building and testing Rust crates"
cd "$RUST_DIR"

cargo build --all-features
cargo test --all-features

RUST_CRATES=(
    libpetri-event
    libpetri-core
    libpetri-export
    libpetri-docgen
    libpetri-runtime
    libpetri-verification
    libpetri-debug
    libpetri
)

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: verifying crate packages"
    for crate in "${RUST_CRATES[@]}"; do
        (cd "$crate" && cargo package --allow-dirty 2>&1 | tail -1)
    done
    info "Dry run complete. Rust crates verified."
    info "Note: version commit created. Run 'git reset HEAD~1' to undo if needed."
    exit 0
fi

# --- Publish ---
info "Publishing Rust crates to crates.io"
for crate in "${RUST_CRATES[@]}"; do
    info "Publishing $crate"
    (cd "$crate" && cargo publish)
    # crates.io needs time to index before dependents can publish
    if [[ "$crate" != "libpetri" ]]; then
        sleep 15
    fi
done

# --- Tag and release ---
cd "$PROJECT_ROOT"
info "Creating tag rust/v${VERSION}"
git tag -a "rust/v${VERSION}" -m "Release rust ${VERSION}"

info "Pushing commit and tag"
git push origin HEAD
git push origin "rust/v${VERSION}"

info "Creating GitHub release"
gh release create "rust/v${VERSION}" \
    --title "Rust v${VERSION}" \
    --generate-notes

info "Released Rust v${VERSION} to crates.io and GitHub."
