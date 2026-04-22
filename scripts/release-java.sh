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

Release libpetri Java to Maven Central.

Maven handles: build, test, sign (local GPG agent), bundle,
upload to Central Portal, and wait for publication.

Prerequisites:
  - GPG signing key available to gpg-agent
  - ~/.m2/settings.xml with <server id="central"> credentials
  - gh CLI authenticated (for GitHub release)

Arguments:
  version       Release version (e.g. 1.3.1)

Options:
  --dry-run     Build and sign only (mvn verify); skip upload, tag, release
  -h, --help    Show this help

Example:
  $(basename "$0") 1.3.1
  $(basename "$0") --dry-run 1.3.1
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

# Extract the CHANGELOG.md section for the given version (between `## <v>` and
# the next `## `). Prints empty string if the version has no section.
changelog_section() {
    awk -v v="$1" '
        $0 == "## " v { p = 1; next }
        p && /^## / { exit }
        p
    ' "$PROJECT_ROOT/CHANGELOG.md"
}

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

# Central credentials in settings.xml
if ! grep -q '<id>central</id>' ~/.m2/settings.xml 2>/dev/null; then
    error "No <server id=\"central\"> found in ~/.m2/settings.xml"
fi

# gh CLI authenticated
if ! gh auth status >/dev/null 2>&1; then
    error "GitHub CLI not authenticated. Run 'gh auth login' first."
fi

# Check tag doesn't already exist (unless dry-run)
if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "java/v${VERSION}" >/dev/null 2>&1; then
        error "Tag java/v${VERSION} already exists."
    fi
fi

# --- Set version ---
info "Setting Java version to ${VERSION}"
cd "$JAVA_DIR"
./mvnw versions:set -DnewVersion="$VERSION" -DgenerateBackupPoms=false -q

# --- Commit the version bump ---
cd "$PROJECT_ROOT"
git add java/pom.xml
git diff --cached --quiet || git commit -m "release: java ${VERSION}"

# --- Build / Deploy ---
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

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run complete. Java artifacts in java/target/."
    info "Note: version commit created. Run 'git reset HEAD~1' to undo if needed."
    exit 0
fi

# --- Tag and release ---
cd "$PROJECT_ROOT"
info "Creating tag java/v${VERSION}"
git tag -a "java/v${VERSION}" -m "Release java ${VERSION}"

info "Pushing commit and tag"
git push origin HEAD
git push origin "java/v${VERSION}"

info "Creating GitHub release"
NOTES=$(changelog_section "$VERSION")
if [[ -z "${NOTES// }" ]]; then
    gh release create "java/v${VERSION}" \
        --title "Java v${VERSION}" \
        --generate-notes
else
    gh release create "java/v${VERSION}" \
        --title "Java v${VERSION}" \
        --notes "$NOTES"
fi

info "Released Java v${VERSION} to Maven Central and GitHub."
