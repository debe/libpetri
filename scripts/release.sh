#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
JAVA_DIR="$PROJECT_ROOT/java"
TS_DIR="$PROJECT_ROOT/typescript"
RUST_DIR="$PROJECT_ROOT/rust"

# --- Defaults ---
DRY_RUN=false
VERSION=""

# --- Usage ---
usage() {
    cat <<EOF
Usage: $(basename "$0") [--dry-run] <version>

Release libpetri to Maven Central, npm, and crates.io.

Maven handles Java: build, test, sign (local GPG agent), bundle,
upload to Central Portal, and wait for publication.
npm handles TypeScript: build, test, publish.
Cargo handles Rust: build, test, publish (crates in dependency order).

Prerequisites:
  - GPG signing key available to gpg-agent
  - ~/.m2/settings.xml with <server id="central"> credentials
  - gh CLI authenticated (for GitHub release)
  - npm authenticated with publish access to 'libpetri'
  - cargo login (crates.io token in ~/.cargo/credentials.toml)

Arguments:
  version       Release version (e.g. 0.4.0)

Options:
  --dry-run     Build and sign only (mvn verify); skip upload, tag, release
  -h, --help    Show this help

Example:
  $(basename "$0") 0.4.0
  $(basename "$0") --dry-run 0.4.0-rc1
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

# GPG key available
if ! gpg --list-secret-keys --keyid-format SHORT 2>/dev/null | grep -q sec; then
    error "No GPG secret key found. Import your signing key first."
fi

# gh CLI authenticated
if ! gh auth status >/dev/null 2>&1; then
    error "GitHub CLI not authenticated. Run 'gh auth login' first."
fi

# Central credentials in settings.xml
if ! grep -q '<id>central</id>' ~/.m2/settings.xml 2>/dev/null; then
    error "No <server id=\"central\"> found in ~/.m2/settings.xml"
fi

# npm authenticated
if ! npm whoami >/dev/null 2>&1; then
    error "Not logged in to npm. Run 'npm login' or set an auth token first."
fi

# cargo authenticated
if [[ ! -f ~/.cargo/credentials.toml ]]; then
    error "No cargo credentials found. Run 'cargo login' first."
fi

# Check tag doesn't already exist (unless dry-run)
if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "v${VERSION}" >/dev/null 2>&1; then
        error "Tag v${VERSION} already exists."
    fi
fi

# --- Set versions in both Java and TypeScript ---
info "Setting version to ${VERSION}"
cd "$JAVA_DIR"
./mvnw versions:set -DnewVersion="$VERSION" -DgenerateBackupPoms=false -q

cd "$TS_DIR"
npm version "$VERSION" --no-git-tag-version --allow-same-version

# Rust: update workspace version and dependency versions in Cargo.toml
cd "$RUST_DIR"
# Workspace version (inherited by all crates via version.workspace = true)
sed -i "s/^version = \".*\"/version = \"$VERSION\"/" Cargo.toml
# Workspace dependency version pins (path = "...", version = "X.Y.Z")
sed -i "s/\(path = \"[^\"]*\"\), version = \"[0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\"/\1, version = \"$VERSION\"/g" Cargo.toml

# --- Commit the version bump ---
cd "$PROJECT_ROOT"
git add java/pom.xml typescript/package.json typescript/package-lock.json
git add rust/Cargo.toml
git diff --cached --quiet || git commit -m "release: ${VERSION}"

# --- Java: Build / Deploy ---
cd "$JAVA_DIR"
if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: building, testing, and signing (no upload)"
    GOAL=verify
else
    info "Building, testing, signing, and publishing to Maven Central"
    GOAL=deploy
fi

if ! ./mvnw clean "$GOAL" -Prelease; then
    info "Build failed — version commit remains, fix and retry or reset"
    exit 1
fi

# --- TypeScript: build, test, publish ---
info "Building and testing TypeScript package"
cd "$TS_DIR"

npm install
npm run build
npm run check
npm test

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: verifying npm package contents"
    npm pack --dry-run
fi

# --- Rust: build, test, publish ---
info "Building and testing Rust crates"
cd "$RUST_DIR"

cargo build --all-features
cargo test --all-features

RUST_CRATES=(
    libpetri-core
    libpetri-event
    libpetri-runtime
    libpetri-export
    libpetri-verification
    libpetri-debug
    libpetri
)

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: verifying crate packages"
    for crate in "${RUST_CRATES[@]}"; do
        (cd "$crate" && cargo package --allow-dirty 2>&1 | tail -1)
    done
    info "Dry run complete. Java artifacts in java/target/, TypeScript in typescript/dist/, Rust crates verified."
    info "Note: version commit created. Run 'git reset HEAD~1' to undo if needed."
    exit 0
fi

info "Publishing to npm"
cd "$TS_DIR"
npm publish

info "Publishing Rust crates to crates.io"
cd "$RUST_DIR"
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
info "Creating tag v${VERSION}"
git tag -a "v${VERSION}" -m "Release ${VERSION}"

info "Pushing tag"
git push origin "v${VERSION}"

info "Creating GitHub release"
gh release create "v${VERSION}" \
    --title "v${VERSION}" \
    --generate-notes

info "Released v${VERSION} to Maven Central, npm, crates.io, and GitHub."
