#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TS_DIR="$PROJECT_ROOT/typescript"

# --- Defaults ---
DRY_RUN=false
VERSION=""

# --- Usage ---
usage() {
    cat <<EOF
Usage: $(basename "$0") [--dry-run] <version>

Release libpetri TypeScript to npm.

npm handles: build, type-check, test, publish.

Prerequisites:
  - npm authenticated with publish access to 'libpetri'
  - gh CLI authenticated (for GitHub release)

Arguments:
  version       Release version (e.g. 1.3.1)

Options:
  --dry-run     Build and test only; skip publish, tag, release
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

# Extract the CHANGELOG.md section for the given version. Matches a `## ` header
# that contains the version as a space-delimited token, so it works with the
# coordinated multi-language headers (e.g. `## Java 2.10.1 / Rust 3.4.1 — …`)
# as well as a bare `## 2.10.1`. Prints empty string if no section matches.
changelog_section() {
    awk -v v="$1" '
        BEGIN { gsub(/\./, "\\.", v); re = " " v " " }
        /^## / && $0 ~ re { p = 1; next }
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

# npm authenticated
if ! npm whoami >/dev/null 2>&1; then
    error "Not logged in to npm. Run 'npm login' or set an auth token first."
fi

# gh CLI authenticated
if ! gh auth status >/dev/null 2>&1; then
    error "GitHub CLI not authenticated. Run 'gh auth login' first."
fi

# Check tag doesn't already exist (unless dry-run)
if [[ "$DRY_RUN" == false ]]; then
    if git -C "$PROJECT_ROOT" rev-parse "typescript/v${VERSION}" >/dev/null 2>&1; then
        error "Tag typescript/v${VERSION} already exists."
    fi
fi

# --- Set version ---
info "Setting TypeScript version to ${VERSION}"
cd "$TS_DIR"
npm version "$VERSION" --no-git-tag-version --allow-same-version

# --- Re-stamp the viewer bundle ---
# The bundle carries the package version (src/viewer/version.ts, injected by
# both bundlers) so a generated doc page can report which viewer drew it. That
# makes the built asset a function of package.json, so bumping the version
# without rebuilding leaves the committed mirrors stale — and CI's
# "No viewer-asset drift" step rebuilds from locked deps and demands a
# byte-identical match, so the release commit would land red. Rebuild here and
# ship the mirrors in the same commit as the bump.
info "Rebuilding the viewer bundle at ${VERSION}"
bash "$PROJECT_ROOT/scripts/build-viewer.sh"

# --- Commit the version bump ---
cd "$PROJECT_ROOT"
git add typescript/package.json typescript/package-lock.json \
    spec/viewer-bundle.sha256 \
    java/src/main/resources/javadoc/petrinet-diagrams.js \
    java/src/main/resources/javadoc/petrinet-diagrams.css \
    rust/libpetri-docgen/resources/petrinet-diagrams.js \
    rust/libpetri-docgen/resources/petrinet-diagrams.css \
    typescript/src/doclet/resources/petrinet-diagrams.js \
    typescript/src/doclet/resources/petrinet-diagrams.css
git diff --cached --quiet || git commit -m "release: typescript ${VERSION}"

# --- Build, test ---
info "Building and testing TypeScript package"
cd "$TS_DIR"

npm install
npm run build
npm run check
npm test

if [[ "$DRY_RUN" == true ]]; then
    info "Dry run: verifying npm package contents"
    npm pack --dry-run
    info "Dry run complete. TypeScript in typescript/dist/."
    info "Note: version commit created. Run 'git reset HEAD~1' to undo if needed."
    exit 0
fi

# --- Publish ---
info "Publishing to npm"
npm publish

# --- Tag and release ---
cd "$PROJECT_ROOT"
info "Creating tag typescript/v${VERSION}"
git tag -a "typescript/v${VERSION}" -m "Release typescript ${VERSION}"

info "Pushing commit and tag"
git push origin HEAD
git push origin "typescript/v${VERSION}"

info "Creating GitHub release"
NOTES=$(changelog_section "$VERSION")
if [[ -z "${NOTES// }" ]]; then
    gh release create "typescript/v${VERSION}" \
        --title "TypeScript v${VERSION}" \
        --generate-notes
else
    gh release create "typescript/v${VERSION}" \
        --title "TypeScript v${VERSION}" \
        --notes "$NOTES"
fi

info "Released TypeScript v${VERSION} to npm and GitHub."
