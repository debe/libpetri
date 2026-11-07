#!/usr/bin/env python3
"""Check that the Lean requirement blocks still agree with the markdown spec.

Input is the registry that `#write_requirements_report` writes
(lean/report/requirements.json), checked against spec/*.md, spec/00-index.md and
spec/lean-proposed.txt. Every failure line starts with a stable prefix:

  ALIGN quote-missing       a `verbatim` block quotes text that is not a whole
                            sentence, run of consecutive sentences or list
                            bullet of its section body; or the block has no
                            quotes, no `#### ID:` heading, or a sourceRef that
                            does not name the file holding the heading.
  ALIGN uncovered           a normative unit of a section that has a verbatim
                            block is neither quoted nor named in an `assumes`
                            line of that ID: a sentence containing "shall"
                            (named by its exact text) or a numbered Acceptance
                            Criteria bullet (named as `AC<n>`).
  ALIGN citation-inactive   a citation names an ID that is malformed, removed
                            (tombstoned) or not in spec/00-index.md at all.
  ALIGN citation-empty      a citation has an empty fragment.
  ALIGN id-inactive         a block's own ID is not an active requirement.
  ALIGN proposed-not-allowed  a block with source `proposed` whose ID is not
                            listed in spec/lean-proposed.txt.
  ALIGN no-blocks           the report holds no requirement block.
  ALIGN evidence-missing    a block without evidence, a kind-B block without
                            `holds` or `nonvacuous`, or a block with neither
                            `forbids` nor `mutant` (no negative example).
  ALIGN duplicate-heading   two canonical `#### ID:` headings for one ID.
  ALIGN schema              unknown kind or source.

A heading such as `### CORE-031:` or `#### CORE-031 :` is not canonical: it is
reported on stderr as a warning and does not open a section.

Section text. A section runs from its `#### ID:` heading to the next heading of
level 1-4; the heading line itself is not matched. Before matching, the file is
stripped of HTML comments, fenced code blocks (CommonMark: fence indented at
most 3 spaces, closed by a fence of the same character at least as long; an
unclosed fence runs to the end of the file), indented code blocks and
~~strikethrough~~. Neither a comment nor a code block can hold a heading. The
body is cut into units (paragraphs, list bullets without their marker, table
rows), each unit into sentences at `.`/`!`/`?` followed by a space and an
upper-case letter, digit, quote or bracket. Both sides are compared with
markdown emphasis (`*`, `_`) removed and whitespace collapsed.

Citations are read from the top-level `citations` list (the report's own
shape), the legacy `cites` list, top-level `evidence` entries with role `cites`
and block evidence entries with role `cites`.

Exit 0 when everything agrees, 1 on any finding (all findings are printed)
or when an input cannot be read or parsed.

python3 stdlib only.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

HEADING_RE = re.compile(r"^ {0,3}(#{1,6})(?:\s|$)")
CANON_HEADING_RE = re.compile(r"^#### ([A-Z]+-\d+):")
LOOSE_ID_HEADING_RE = re.compile(r"^ {0,3}#{1,6}\s*([A-Z]+-\d+)\s*:")
FENCE_OPEN_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")
LIST_RE = re.compile(r"^(\s*)(\d{1,9}[.)]|[-*+])(?:\s+|$)(.*)$")
THEMATIC_RE = re.compile(r"^ {0,3}([-*_])(?:\s*\1){2,}\s*$")
STRIKE_RE = re.compile(r"~~.*?~~")
SENTENCE_SPLIT_RE = re.compile(r"(?:(?<=[.!?])|(?<=[.!?][\"')\]]))\s+(?=[A-Z0-9\"'`(\[])")
SHALL_RE = re.compile(r"\bshall\b", re.IGNORECASE)
AC_HEAD_RE = re.compile(r"^acceptance criteria:?$", re.IGNORECASE)
AC_MENTION_RE = re.compile(r"\bAC\s?(\d+)\b")
CITE_ID_RE = re.compile(r"^[A-Z]+-\d{3}$")
KINDS = set("BFTQAN")
PROPOSED_FILE = "lean-proposed.txt"


class InputError(Exception):
    """An input file is missing or malformed."""


def norm(s: str) -> str:
    """Drop markdown emphasis markers and collapse whitespace."""
    return re.sub(r"\s+", " ", re.sub(r"[*_]", "", s)).strip()


def sentences(text: str) -> list[str]:
    """Split normalised text into sentences."""
    return [s for s in SENTENCE_SPLIT_RE.split(text) if s]


# --------------------------------------------------------------------------
# markdown stripping
# --------------------------------------------------------------------------

def strip_markdown(lines: list[str]) -> list[str]:
    """Blank HTML comments and fenced code, drop ~~strikethrough~~.

    The result has one entry per input line, so line numbers survive.
    Indented code blocks need list context and are dropped by `units`.
    """
    out: list[str] = []
    in_comment = False
    fence: tuple[str, int] | None = None  # (char, length)
    for line in lines:
        if fence is not None:
            c, n = fence
            if re.match(rf"^ {{0,3}}{re.escape(c)}{{{n},}}\s*$", line):
                fence = None
            out.append("")
            continue
        if not in_comment:
            m = FENCE_OPEN_RE.match(line)
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence = (m.group(2)[0], len(m.group(2)))
                out.append("")
                continue
        kept = ""
        rest = line
        while rest:
            if in_comment:
                end = rest.find("-->")
                if end < 0:
                    rest = ""
                else:
                    rest = rest[end + 3:]
                    in_comment = False
            else:
                start = rest.find("<!--")
                if start < 0:
                    kept += rest
                    rest = ""
                else:
                    kept += rest[:start]
                    rest = rest[start + 4:]
                    in_comment = True
        out.append(STRIKE_RE.sub("", kept))
    return out


# --------------------------------------------------------------------------
# spec sections
# --------------------------------------------------------------------------

class Unit:
    """A paragraph, list bullet or table row of a section body (normalised).

    `ac` is the number of a top-level Acceptance Criteria bullet, else None.
    """

    def __init__(self, sents: list[str], ac: int | None = None):
        self.sents = sents
        self.ac = ac


class Section:
    """The body of one `#### ID:` section: its file, heading line and units."""

    def __init__(self, fname: str, line: int, units: list[Unit]):
        self.fname = fname
        self.line = line
        self.units = units


def units(body: list[str]) -> list[Unit]:
    """Cut stripped section body lines into units; drop indented code blocks."""
    raw: list[tuple[str, list[str], int | None, int]] = []  # (kind, lines, number, indent)
    cur: list | None = None
    in_list = False

    def close():
        nonlocal cur
        if cur is not None:
            raw.append(tuple(cur))
        cur = None

    for line in body:
        if not line.strip():
            close()
            continue
        exp = line.expandtabs(4)
        indent = len(exp) - len(exp.lstrip(" "))
        if indent >= 4 and cur is None and not in_list:
            continue  # indented code block (cannot interrupt a paragraph)
        if THEMATIC_RE.match(exp):
            close()
            in_list = False
            continue
        m = LIST_RE.match(exp)
        if m and (indent < 4 or in_list):
            close()
            marker = m.group(2)
            num = int(marker[:-1]) if marker[0].isdigit() else None
            cur = ["item", [m.group(3)], num, indent]
            in_list = True
            continue
        if HEADING_RE.match(exp) or exp.lstrip().startswith("|"):
            close()
            raw.append(("other", [exp.strip().lstrip("#")], None, indent))
            in_list = False
            continue
        if cur is not None:
            cur[1].append(exp.strip())
            continue
        if not (in_list and indent >= 2):
            in_list = False
        cur = ["para", [exp.strip()], None, indent]
    close()

    result: list[Unit] = []
    ac_indent: int | None = None
    in_ac = False
    for kind, ls, num, indent in raw:
        text = norm(" ".join(ls))
        if not text:
            continue
        ac = None
        if kind == "para" and AC_HEAD_RE.match(text):
            in_ac, ac_indent = True, None
        elif kind == "item" and in_ac:
            if num is not None and (ac_indent is None or indent == ac_indent):
                ac_indent = indent
                ac = num
        elif in_ac and not (kind == "para" and ac_indent is not None and indent > ac_indent):
            in_ac = False
        result.append(Unit(sentences(text), ac))
    return result


def spec_sections(spec_dir: Path) -> tuple[dict[str, Section], list[str], list[str]]:
    """Return (sections by ID, duplicate-heading findings, warnings)."""
    sections: dict[str, Section] = {}
    dups: list[str] = []
    warns: list[str] = []
    files = sorted(spec_dir.glob("*.md"))
    if not files:
        raise InputError(f"no *.md files in {spec_dir}")
    for f in files:
        lines = strip_markdown(f.read_text(encoding="utf-8").splitlines())
        is_heading = [False] * len(lines)
        for i, line in enumerate(lines):
            m = HEADING_RE.match(line)
            is_heading[i] = bool(m and len(m.group(1)) <= 4)
            if LOOSE_ID_HEADING_RE.match(line) and not CANON_HEADING_RE.match(line):
                warns.append(
                    f"{f.name}:{i + 1}: non-canonical requirement heading {line.strip()!r} "
                    f"(use '#### ID: Title'); it does not open a section"
                )
        for i, line in enumerate(lines):
            if not is_heading[i]:
                continue
            m = CANON_HEADING_RE.match(line)
            if not m:
                continue
            rid = m.group(1)
            if rid in sections:
                prev = sections[rid]
                dups.append(
                    f"ALIGN duplicate-heading {rid}: '#### {rid}:' at {prev.fname}:{prev.line} "
                    f"and {f.name}:{i + 1}"
                )
                continue
            j = i + 1
            while j < len(lines) and not is_heading[j]:
                j += 1
            sections[rid] = Section(f.name, i + 1, units(lines[i + 1:j]))
    return sections, dups, warns


# --------------------------------------------------------------------------
# active IDs from spec/00-index.md (same approach as spec-coverage-matrix.py)
# --------------------------------------------------------------------------

def active_ids(index_text: str) -> tuple[set[str], set[str]]:
    """Return (active, tombstones) from the Alphabetical Cross-Reference Index.

    Rows live under `### PREFIX — Title` sub-headings; a struck-through
    `~~ID~~` first cell is a tombstone and is not active.
    """
    start = index_text.find("## Alphabetical Cross-Reference Index")
    if start < 0:
        raise InputError("'## Alphabetical Cross-Reference Index' heading not found in the spec index")
    rest = index_text[start:]
    end = re.search(r"\n## (?!#)", rest[1:])
    section = rest[: end.start() + 1] if end else rest

    active: set[str] = set()
    tombstones: set[str] = set()
    prefix: str | None = None
    tomb_cell = re.compile(r"^~~\s*([A-Z]+-\d+)\s*~~")
    id_cell = re.compile(r"^([A-Z]+-\d+)$")
    for line in section.splitlines():
        h = re.match(r"^### ([A-Z]+) — ", line)
        if h:
            prefix = h.group(1)
            continue
        if prefix is None or not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        first = cells[0]
        if first in ("ID", "") or set(first) <= {"-", " "}:
            continue
        m = tomb_cell.match(first)
        if m:
            tombstones.add(m.group(1))
            continue
        m = id_cell.match(first)
        if m:
            active.add(m.group(1))
    if not active:
        raise InputError("no active IDs parsed from the spec index")
    return active, tombstones


def proposed_allowlist(spec_dir: Path) -> set[str]:
    """IDs listed in spec/lean-proposed.txt (one per line, `#` comments); empty if absent."""
    f = spec_dir / PROPOSED_FILE
    if not f.exists():
        return set()
    ids: set[str] = set()
    for line in f.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            ids.add(line)
    return ids


# --------------------------------------------------------------------------
# registry
# --------------------------------------------------------------------------

def _names(entry: dict) -> list[str]:
    for key in ("reqs", "req", "requirements", "requirement"):
        v = entry.get(key)
        if isinstance(v, str):
            return [v]
        if isinstance(v, list):
            return [x for x in v if isinstance(x, str)]
    return []


def _list(path: Path, data: dict, key: str) -> list:
    v = data.get(key) or []
    if not isinstance(v, list):
        raise InputError(f"{path}: '{key}' must be a list")
    return v


def load_registry(path: Path) -> tuple[list[dict], list[dict]]:
    """Return (blocks, citations); each block gets a merged `evidence` list."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise InputError(f"{path} not found (run `lake env lean spec-tools/Report.lean` from lean/)")
    except json.JSONDecodeError as e:
        raise InputError(f"{path} is not valid JSON: {e}")

    top_evidence: list = []
    cites: list = []
    if isinstance(data, list):
        blocks = data
    elif isinstance(data, dict):
        blocks = data.get("blocks", data.get("requirements"))
        if blocks is None:
            raise InputError(f"{path}: object has neither 'blocks' nor 'requirements'")
        top_evidence = _list(path, data, "evidence")
        cites = _list(path, data, "citations") + _list(path, data, "cites")
    else:
        raise InputError(f"{path}: expected a list or an object at the top level")
    if not isinstance(blocks, list) or not all(isinstance(b, dict) for b in blocks):
        raise InputError(f"{path}: blocks must be a list of objects")
    if not all(isinstance(c, dict) for c in cites):
        raise InputError(f"{path}: citations must be objects")

    for b in blocks:
        if "id" not in b:
            raise InputError(f"{path}: block without 'id': {b.get('decl', b)!r}")
        ev = b.get("evidence") or []
        cites += [e for e in ev if isinstance(e, dict) and e.get("role") == "cites"]
        b["evidence"] = [e for e in ev if isinstance(e, dict) and e.get("role") != "cites"]

    by_name: dict[str, list[dict]] = {}
    for b in blocks:
        for key in (b.get("decl"), b.get("id")):
            if key:
                by_name.setdefault(key, []).append(b)

    for e in top_evidence:
        if not isinstance(e, dict):
            raise InputError(f"{path}: evidence entry is not an object: {e!r}")
        if e.get("role") == "cites":
            cites.append(e)
            continue
        seen: set[int] = set()
        for n in _names(e):
            for b in by_name.get(n, []):
                if id(b) not in seen:
                    seen.add(id(b))
                    b["evidence"].append(e)
    return blocks, cites


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------

def _label(b: dict) -> str:
    return b.get("decl") or b["id"]


def _names_file(source_ref: str, fname: str) -> bool:
    return fname in re.split(r"[\s/,;#()]+", source_ref)


def _short(s: str, n: int = 120) -> str:
    return s if len(s) <= n else s[: n - 3] + "..."


def match_quote(q: str, sec: Section) -> list[tuple[int, int]]:
    """Positions (unit, sentence) covered by every whole-sentence run equal to `q`."""
    hits: list[tuple[int, int]] = []
    for ui, u in enumerate(sec.units):
        for a in range(len(u.sents)):
            run = ""
            for b in range(a, len(u.sents)):
                run = u.sents[b] if b == a else run + " " + u.sents[b]
                if len(run) > len(q):
                    break
                if run == q:
                    hits.extend((ui, k) for k in range(a, b + 1))
                    break
    return hits


def check(blocks: list[dict], cites: list[dict], sections: dict[str, Section],
          active: set[str], tombstones: set[str], allowed: set[str]) -> tuple[list[str], int]:
    """Return (findings, number of verbatim quotes found)."""
    bad: list[str] = []
    found = 0
    if not blocks:
        bad.append("ALIGN no-blocks: the report holds no requirement block")

    covered: dict[str, set[tuple[int, int]]] = {}
    assumes: dict[str, list[str]] = {}

    for b in blocks:
        name, rid = _label(b), b["id"]

        if rid in tombstones:
            bad.append(f"ALIGN id-inactive {name}: {rid} is a removed (tombstoned) requirement in spec/00-index.md")
        elif rid not in active:
            bad.append(f"ALIGN id-inactive {name}: {rid} is not an active requirement in spec/00-index.md")

        kind = b.get("kind")
        if kind not in KINDS:
            bad.append(f"ALIGN schema {name}: unknown kind {kind!r} (expected one of {''.join(sorted(KINDS))})")

        source = b.get("source")
        if source == "verbatim":
            covered.setdefault(rid, set())
            assumes.setdefault(rid, []).extend(
                norm(a) for a in (b.get("assumes") or []) if isinstance(a, str))
            quotes = b.get("quotes") or []
            if not quotes:
                bad.append(f"ALIGN quote-missing {name}: verbatim block without quotes")
            sec = sections.get(rid)
            if sec is None:
                bad.append(f"ALIGN quote-missing {name}: no '#### {rid}:' heading in spec/*.md")
            else:
                ref = b.get("sourceRef") or ""
                if not _names_file(ref, sec.fname):
                    bad.append(f"ALIGN quote-missing {name}: sourceRef {ref!r} does not name "
                               f"{sec.fname}, where {rid} is defined")
                for q in quotes:
                    hits = match_quote(norm(q), sec) if norm(q) else []
                    if hits:
                        found += 1
                        covered[rid].update(hits)
                    else:
                        bad.append(f"ALIGN quote-missing {name}: not a whole sentence, sentence run "
                                   f"or bullet of the '#### {rid}:' body in {sec.fname}: {q!r}")
        elif source == "proposed":
            if rid not in allowed:
                bad.append(f"ALIGN proposed-not-allowed {name}: source 'proposed' but {rid} "
                           f"is not listed in spec/{PROPOSED_FILE}")
        else:
            bad.append(f"ALIGN schema {name}: unknown source {source!r} (expected 'verbatim' or 'proposed')")

        roles = {e.get("role") for e in b["evidence"]}
        if not roles:
            bad.append(f"ALIGN evidence-missing {name}: no evidence theorem (tag one with @[evidence ROLE {name}])")
        if kind == "B":
            for role in ("holds", "nonvacuous"):
                if role not in roles:
                    bad.append(f"ALIGN evidence-missing {name}: kind-B block without a '{role}' evidence theorem")
        if not roles & {"forbids", "mutant"}:
            bad.append(f"ALIGN evidence-missing {name}: no 'forbids' or 'mutant' evidence theorem "
                       f"(every requirement needs a negative example)")

    # coverage of normative text, for IDs with a verbatim block and a section
    for rid in sorted(covered):
        sec = sections.get(rid)
        if sec is None:
            continue
        cov, ass = covered[rid], assumes[rid]
        acs = {int(n) for a in ass for n in AC_MENTION_RE.findall(a)}
        for ui, u in enumerate(sec.units):
            if u.ac is not None:
                if u.ac in acs or all((ui, si) in cov for si in range(len(u.sents))):
                    continue
                bad.append(f"ALIGN uncovered {rid}: Acceptance Criteria bullet AC{u.ac} in {sec.fname} "
                           f"is neither quoted nor named as 'AC{u.ac}' in an assumes line: "
                           f"{_short(' '.join(u.sents))!r}")
                continue
            for si, s in enumerate(u.sents):
                if not SHALL_RE.search(s) or (ui, si) in cov or any(s in a for a in ass):
                    continue
                bad.append(f"ALIGN uncovered {rid}: 'shall' sentence in {sec.fname} is neither quoted "
                           f"nor stated in an assumes line: {_short(s)!r}")

    for c in cites:
        cid = c.get("id")
        thm = c.get("theorem", "?")
        mod = c.get("module")
        where = f"{thm} ({mod})" if mod else thm
        if not isinstance(cid, str) or not CITE_ID_RE.match(cid):
            bad.append(f"ALIGN citation-inactive {where}: cites malformed ID {cid!r} (expected e.g. VER-002)")
        elif cid in tombstones:
            bad.append(f"ALIGN citation-inactive {where}: cites {cid}, a removed (tombstoned) requirement")
        elif cid not in active:
            bad.append(f"ALIGN citation-inactive {where}: cites {cid}, which is not an active "
                       f"requirement in spec/00-index.md")
        frag = c.get("fragment")
        if not isinstance(frag, str) or not frag.strip():
            bad.append(f"ALIGN citation-empty {where}: cites {cid} with an empty fragment")

    return bad, found


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--report", default="lean/report/requirements.json",
                    help="registry JSON written by #write_requirements_report (repo-relative)")
    ap.add_argument("--spec", default="spec", help="spec directory (repo-relative)")
    a = ap.parse_args(argv)

    report = Path(a.report)
    spec = Path(a.spec)
    if not report.is_absolute():
        report = REPO / report
    if not spec.is_absolute():
        spec = REPO / spec

    try:
        blocks, cites = load_registry(report)
        sections, dups, warns = spec_sections(spec)
        index = spec / "00-index.md"
        if not index.exists():
            raise InputError(f"{index} not found")
        active, tombstones = active_ids(index.read_text(encoding="utf-8"))
        allowed = proposed_allowlist(spec)
    except InputError as e:
        sys.stderr.write(f"spec-lean-alignment: ERROR: {e}\n")
        return 1

    for w in warns:
        sys.stderr.write(f"spec-lean-alignment: WARNING: {w}\n")

    bad, found = check(blocks, cites, sections, active, tombstones, allowed)
    bad = dups + bad
    if bad:
        print(f"spec-lean-alignment FAILED, {len(bad)} finding(s):")
        for line in bad:
            print(line)
        return 1
    proposed = sum(1 for b in blocks if b.get("source") == "proposed")
    print(
        f"spec-lean-alignment ok: {len(blocks)} blocks ({proposed} proposed), "
        f"{found} verbatim quotes under their IDs, {len(cites)} citations of active IDs"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
