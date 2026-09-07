#!/usr/bin/env python3
"""Validate the agent skills this repo ships, against every harness that loads them.

The skill in plugins/libpetri/skills/petri-net-design/ is consumed by four agent
CLIs that share the SKILL.md contract but not its validation rules. The strictest
rule wins, and it is invisible in the others:

  * opencode hard-validates `description` at 1..1024 characters and `name` against
    ^[a-z0-9]+(-[a-z0-9]+)*$ matching the containing directory. A skill that fails
    either is dropped SILENTLY: no error, no log line, it simply never appears.
    This repo shipped a 1289-character description for one release; `claude plugin
    validate` passed on it the whole time, which is why this script exists.
  * Codex budgets the whole skills list at 2% of the context window (8000 chars
    when unknown), so an oversized description also crowds out other skills.
  * oh-my-pi discovers skills exactly one level under a skills root; a nested
    skills/group/name/SKILL.md is skipped entirely.
  * All three read the repo-local .agents/skills/ symlink. If a checkout turns it
    into a regular file (Windows without core.symlinks, or a GitHub ZIP), the
    skill stops loading everywhere at once.

Checks (all read-only):
  (a) frontmatter is the first block and parses as YAML
  (b) name matches the harness regex and equals its directory name
  (c) 1 <= len(description) <= 1024, warning above 900
  (d) frontmatter keys are within what the harnesses recognise
  (e) each skill sits exactly one level under its skills root
  (f) every references/*.md cited in SKILL.md exists, with no absolute or .. path
  (g) .agents/skills/<name> is a relative symlink resolving into the canonical dir
  (h) the two Claude Code manifests agree on version

Requires PyYAML: `description` is a folded scalar, and measuring a folded scalar
with a regex is exactly the bug this script is here to catch.

Exit 0 when clean (warnings do not fail), 1 on any error.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ModuleNotFoundError:  # pragma: no cover
    sys.exit("error: PyYAML is required (pip install pyyaml)")

REPO = Path(__file__).resolve().parent.parent

CANONICAL_SKILLS_ROOT = REPO / "plugins" / "libpetri" / "skills"
# Every harness that reads a repo-local skills root, and the link it reads.
# Codex reads $REPO_ROOT/.agents/skills; opencode and oh-my-pi read it too
# (verified against opencode 1.17.8 and omp 18.1.6), so one link serves all three.
LINKED_ROOTS = [REPO / ".agents" / "skills"]

NAME_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")
DESCRIPTION_MAX = 1024
DESCRIPTION_WARN = 900
# The intersection of what opencode recognises and what Claude Code uses.
ALLOWED_KEYS = {"name", "description", "license", "compatibility", "metadata", "allowed-tools"}

REFERENCE_RE = re.compile(r"`(references/[^`]+\.md)`")

errors: list[str] = []
warnings: list[str] = []


def error(msg: str) -> None:
    errors.append(msg)


def warn(msg: str) -> None:
    warnings.append(msg)


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO))
    except ValueError:
        return str(path)


def split_frontmatter(text: str, where: str) -> dict | None:
    """Return the parsed frontmatter mapping, or None if it is unusable."""
    if not text.startswith("---\n"):
        error(f"{where}: no YAML frontmatter as the first block")
        return None
    end = text.find("\n---", 4)
    if end == -1:
        error(f"{where}: frontmatter is not terminated")
        return None
    try:
        data = yaml.safe_load(text[4:end])
    except yaml.YAMLError as exc:
        error(f"{where}: frontmatter is not valid YAML ({exc.__class__.__name__})")
        return None
    if not isinstance(data, dict):
        error(f"{where}: frontmatter is not a mapping")
        return None
    return data


def check_skill(skill_dir: Path) -> None:
    where = rel(skill_dir / "SKILL.md")
    skill_md = skill_dir / "SKILL.md"
    if not skill_md.is_file():
        error(f"{rel(skill_dir)}: no SKILL.md")
        return

    text = skill_md.read_text(encoding="utf-8")
    data = split_frontmatter(text, where)
    if data is None:
        return

    name = data.get("name")
    if not isinstance(name, str) or not name:
        error(f"{where}: frontmatter has no `name`")
    else:
        if not NAME_RE.match(name):
            error(f"{where}: name {name!r} does not match ^[a-z0-9]+(-[a-z0-9]+)*$ (opencode rejects it)")
        if name != skill_dir.name:
            error(f"{where}: name {name!r} != directory {skill_dir.name!r} (opencode requires they match)")

    description = data.get("description")
    if not isinstance(description, str) or not description.strip():
        error(f"{where}: frontmatter has no `description`")
    else:
        n = len(description)
        if n > DESCRIPTION_MAX:
            error(
                f"{where}: description is {n} chars, over the {DESCRIPTION_MAX} limit. "
                f"opencode will drop this skill silently."
            )
        elif n > DESCRIPTION_WARN:
            warn(f"{where}: description is {n} chars, within {DESCRIPTION_MAX - n} of the hard limit")

    unknown = sorted(set(data) - ALLOWED_KEYS)
    if unknown:
        error(f"{where}: unrecognised frontmatter keys {unknown}; allowed: {sorted(ALLOWED_KEYS)}")

    for cited in sorted(set(REFERENCE_RE.findall(text))):
        if os.path.isabs(cited) or ".." in Path(cited).parts:
            error(f"{where}: cited path {cited!r} is absolute or escapes the skill directory")
            continue
        if not (skill_dir / cited).is_file():
            error(f"{where}: cites {cited!r}, which does not exist")

    # Anything that looks like a repo-root path and is not reachable from the skill
    # directory only resolves inside a libpetri checkout. Warn, do not fail: the
    # prose legitimately mentions `spec/` in the abstract.
    for match in re.findall(r"`((?:spec|java|typescript|rust|python|lean)/[^`]*)`", text):
        if "github.com/debe/libpetri" not in text:
            warn(f"{where}: cites repo path {match!r} with no URL fallback for a standalone install")
            break


def check_layout(root: Path) -> list[Path]:
    """Skills must sit exactly one level under the root; oh-my-pi skips deeper ones."""
    skills = []
    for entry in sorted(root.iterdir()):
        if not entry.is_dir():
            continue
        if (entry / "SKILL.md").is_file():
            skills.append(entry)
            for nested in entry.rglob("SKILL.md"):
                if nested.parent != entry:
                    error(
                        f"{rel(nested)}: nested more than one level under {rel(root)}; "
                        f"oh-my-pi will not discover it"
                    )
        else:
            for nested in entry.rglob("SKILL.md"):
                error(
                    f"{rel(nested)}: nested more than one level under {rel(root)}; "
                    f"oh-my-pi will not discover it"
                )
    return skills


def check_links(expected: set[str]) -> None:
    for root in LINKED_ROOTS:
        if not root.is_dir():
            error(f"{rel(root)}: missing; the skill will not load in Codex, opencode or oh-my-pi")
            continue
        linked = {p.name for p in root.iterdir()}
        for name in sorted(expected - linked):
            error(f"{rel(root / name)}: missing link to the canonical skill")
        for name in sorted(linked):
            link = root / name
            if not link.is_symlink():
                error(
                    f"{rel(link)}: not a symlink. A Windows checkout without core.symlinks turns "
                    f"these into text files; run `git config core.symlinks true` and re-checkout."
                )
                continue
            target = os.readlink(link)
            if os.path.isabs(target):
                error(f"{rel(link)}: symlink target {target!r} is absolute; it must be relative")
            resolved = link.resolve()
            if not resolved.is_dir() or CANONICAL_SKILLS_ROOT.resolve() not in resolved.parents:
                error(f"{rel(link)}: resolves to {resolved}, outside {rel(CANONICAL_SKILLS_ROOT)}")


def check_manifest_versions() -> None:
    import json

    marketplace = REPO / ".claude-plugin" / "marketplace.json"
    plugin = REPO / "plugins" / "libpetri" / ".claude-plugin" / "plugin.json"
    if not marketplace.is_file() or not plugin.is_file():
        error("missing a Claude Code manifest")
        return
    entries = json.loads(marketplace.read_text(encoding="utf-8")).get("plugins", [])
    plugin_version = json.loads(plugin.read_text(encoding="utf-8")).get("version")
    for entry in entries:
        if entry.get("name") == "libpetri" and entry.get("version") != plugin_version:
            error(
                f"version mismatch: {rel(marketplace)} says {entry.get('version')}, "
                f"{rel(plugin)} says {plugin_version}"
            )


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()

    if not CANONICAL_SKILLS_ROOT.is_dir():
        print(f"error: {rel(CANONICAL_SKILLS_ROOT)} does not exist", file=sys.stderr)
        return 1

    skills = check_layout(CANONICAL_SKILLS_ROOT)
    if not skills:
        error(f"{rel(CANONICAL_SKILLS_ROOT)}: no skills found")
    for skill in skills:
        check_skill(skill)
    check_links({s.name for s in skills})
    check_manifest_versions()

    for msg in warnings:
        print(f"warning: {msg}")
    for msg in errors:
        print(f"error: {msg}", file=sys.stderr)

    if errors:
        print(f"\n{len(errors)} error(s) in the shipped agent skills.", file=sys.stderr)
        return 1
    checked = ", ".join(s.name for s in skills)
    print(f"ok: {len(skills)} skill(s) valid for Claude Code, Codex, opencode and oh-my-pi ({checked})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
