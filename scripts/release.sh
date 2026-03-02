#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
JAVA_DIR="$PROJECT_ROOT/java"

# --- Defaults ---
DRY_RUN=false
VERSION=""

# --- Usage ---
usage() {
    cat <<EOF
Usage: $(basename "$0") [--dry-run] <version>

Release libpetri to Maven Central.

Maven handles everything: build, test, sign (local GPG agent), bundle,
upload to Central Portal, and wait for publication.

Prerequisites:
  - GPG signing key available to gpg-agent
  - ~/.m2/settings.xml with <server id="central"> credentials
  - gh CLI authenticated (for GitHub release)

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

# Check tag doesn't already exist (unless dry-run)
if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "v${VERSION}" >/dev/null 2>&1; then
        error "Tag v${VERSION} already exists."
    fi
fi

# --- Set version ---
info "Setting version to ${VERSION}"
cd "$JAVA_DIR"
./mvnw versions:set -DnewVersion="$VERSION" -DgenerateBackupPoms=false -q

# --- Build / Deploy ---
if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: building, testing, and signing (no upload)"
    GOAL=verify
else
    info "Building, testing, signing, and publishing to Maven Central"
    GOAL=deploy
fi

if ! ./mvnw clean "$GOAL" -Prelease; then
    info "Build failed, reverting version change"
    git checkout pom.xml
    exit 1
fi

# --- Clean up version change ---
info "Reverting version in pom.xml"
cd "$PROJECT_ROOT"
git checkout java/pom.xml

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run complete. Artifacts in java/target/"
    exit 0
fi

# --- Tag and release ---
info "Creating tag v${VERSION}"
git tag -a "v${VERSION}" -m "Release ${VERSION}"

info "Pushing tag"
git push origin "v${VERSION}"

info "Creating GitHub release"
gh release create "v${VERSION}" \
    --title "v${VERSION}" \
    --generate-notes

info "Released v${VERSION} to Maven Central and GitHub."
