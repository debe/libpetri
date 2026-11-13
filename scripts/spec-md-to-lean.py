#!/usr/bin/env python3
"""Convert one spec chapter from markdown into the Lean text DSL (lean/Libpetri/Spec/Text.lean).

One-shot migration tool: after a chapter is converted, its Lean text is the source and
`spec/<chapter>.md` is generated from it by lean/spec-tools/Render.lean.

For `spec/NN-name.md` it

* writes `lean/Libpetri/Spec/Text/<KEY>.lean`, one `requirement_text` per `#### ID:` section
  (KEY is the ID with `-` replaced by `_`), and `lean/Libpetri/Spec/Text/Chapter/ChNN.lean`, the
  `spec_chapter` listing the markdown chunks and requirement texts in order;
* wraps every quote of a `verbatim` requirement block of the chapter's IDs (taken from
  lean/report/requirements.json) as a span `⟦sN|…⟧` of the ID's body. Quotes match the markdown
  only after normalisation (emphasis `*`/`_` dropped, whitespace collapsed, as
  scripts/spec-lean-alignment.py compares them), so the match runs on the normalised body and is
  mapped back to the raw markdown through an index map; emphasis markers at either end of the
  match are taken into the span when that makes the span read exactly as the quote;
* rewrites each such block's `quote "…" …` in its Lean module to `covers KEY.sN, …` and imports
  the text module there;
* imports every new module from lean/Libpetri/Spec/All.lean, lean/spec-tools/Audit.lean and
  lean/spec-tools/Report.lean (scripts/lean-module-coverage-check.py requires it).

A `covers` reference resolves to its span with every line break (and the whitespace around it)
turned into one space and the ends trimmed (`Text.joinLines`); the resolved strings are the
block's quotes, so a block keeps its statement hash, and its sign-off, exactly when every span
resolves to the old quote. The script reports every quote whose span resolves differently (that
block's hash changes; its sign-off is reset to "pending") and every quote it cannot place (that
block keeps its `quote` strings).

Before writing anything it renders the chapter the way Render.lean does (without the banner) and
fails unless the result is the markdown byte for byte.

Usage: spec-md-to-lean.py spec/10-performance.md [--report lean/report/requirements.json]
                          [--dry-run]
Exit 0 on success (differences are reported, not fatal), 1 on an error.

python3 stdlib only.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN = REPO / "lean"
TEXT_DIR = LEAN / "Libpetri" / "Spec" / "Text"

_spec = importlib.util.spec_from_file_location("spec_lean_alignment", REPO / "scripts" / "spec-lean-alignment.py")
ALIGN = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ALIGN)

HEAD_RE = re.compile(r"^#### ([A-Z]+-\d{3}): (.*)$")
FIELD_RE = re.compile(r"^\*\*(Priority|Kind|Status):\*\* ([A-Za-z][A-Za-z0-9_]*)$")
FIELDS = ["Priority", "Kind", "Status"]
BANNER_RE = re.compile(r"^<!-- Generated from .*-->$")
LEAN_WS = " \t\r\n"


class ConvertError(Exception):
    """The chapter cannot be converted as it stands."""


# --------------------------------------------------------------------------
# what Text.lean computes, in Python
# --------------------------------------------------------------------------

def join_lines(s: str) -> str:
    """`Text.joinLines`: every whitespace run (space, tab, CR, LF) that holds a line break becomes
    one space, other runs stay as they are, and the ends are trimmed."""
    return re.sub(r"[ \t\r]*\n[ \t\r\n]*", " ", s).strip(LEAN_WS)


def strip_markers(body: str) -> str:
    return re.sub(r"⟦[A-Za-z][A-Za-z0-9_]*\|", "", body).replace("⟧", "")


def render_req(r: dict) -> str:
    fields = "".join(f"**{k}:** {r[k]}\n" for k in FIELDS if r.get(k))
    return f"#### {r['id']}: {r['title']}\n\n{fields}\n{strip_markers(r['body'])}\n"


def render_chapter(items: list[tuple[str, object]]) -> str:
    """`Chapter.render` without the banner."""
    return "\n".join(v + "\n" if k == "md" else render_req(v) for k, v in items)


# --------------------------------------------------------------------------
# splitting the markdown
# --------------------------------------------------------------------------

def _md_gap(g: str) -> str | None:
    """The chunk between two items, `None` when the gap is one blank line (no chunk), or raise
    ValueError when no chunk renders as `g`."""
    if g == "\n":
        return None
    if len(g) >= 3 and g[0] == "\n" and g.endswith("\n\n"):
        return g[1:-2]
    raise ValueError


def _md_prefix(p: str) -> str | None:
    if p == "":
        return None
    if p.endswith("\n\n"):
        return p[:-2]
    raise ValueError


def _md_suffix(s: str) -> str | None:
    if s == "":
        return None
    if len(s) >= 2 and s[0] == "\n" and s.endswith("\n"):
        return s[1:-1]
    raise ValueError


def split_chapter(text: str, fname: str):
    """Return (items, reqs): items as [("md", text) | ("req", req dict)], reqs by ID."""
    lines = text.split("\n")
    if lines and BANNER_RE.match(lines[0]):
        lines = lines[1:]
        text = "\n".join(lines)
    if not text.endswith("\n"):
        raise ConvertError(f"{fname}: the file does not end with a line break")
    off = [0]
    for line in lines:
        off.append(off[-1] + len(line) + 1)
    stripped = ALIGN.strip_markdown(lines)
    heading = []
    for s in stripped:
        m = ALIGN.HEADING_RE.match(s)
        heading.append(bool(m and len(m.group(1)) <= 4))
    starts = [i for i, s in enumerate(stripped) if heading[i] and ALIGN.CANON_HEADING_RE.match(s)]

    reqs: dict[str, dict] = {}
    sections: list[tuple[int, int, dict]] = []  # (start offset, end line, req)
    for h in starts:
        where = f"{fname}:{h + 1}"
        if "<!--" in lines[h] or "-->" in lines[h]:
            raise ConvertError(f"{where}: the heading line holds an HTML comment")
        m = HEAD_RE.match(lines[h])
        if not m:
            raise ConvertError(f"{where}: the heading is not '#### ID: Title'")
        rid, title = m.group(1), m.group(2)
        if rid in reqs:
            raise ConvertError(f"{where}: {rid} has a second heading")
        j = h + 1
        while j < len(lines) and not heading[j]:
            j += 1
        if h + 1 >= j or lines[h + 1] != "":
            raise ConvertError(f"{where}: no blank line after the heading")
        r = {"id": rid, "title": title, "key": rid.replace("-", "_")}
        b = h + 2
        order = 0
        while b < j:
            fm = FIELD_RE.match(lines[b])
            if not fm:
                break
            k = FIELDS.index(fm.group(1))
            if k < order:
                raise ConvertError(f"{fname}:{b + 1}: {rid}: field {fm.group(1)} out of order "
                                   f"(expected Priority, Kind, Status)")
            order = k + 1
            r[fm.group(1)] = fm.group(2)
            b += 1
        if not r.get("Status") and not (r.get("Priority") and r.get("Kind")):
            raise ConvertError(f"{where}: {rid} needs **Priority:** and **Kind:** lines, or **Status:**")
        if b >= j or lines[b] != "":
            raise ConvertError(f"{fname}:{b + 1}: {rid}: no blank line after the "
                               f"priority, kind and status lines")
        b += 1
        e = j
        while e > b and (lines[e - 1].strip() == "" or ALIGN.THEMATIC_RE.match(lines[e - 1])):
            e -= 1
        if e == b:
            raise ConvertError(f"{where}: {rid} has an empty body")
        r["_lo"], r["_j"] = b, j
        reqs[rid] = r
        sections.append((off[h], e, r))

    # Pick each section's end so that every gap renders: a gap of one blank line is no chunk,
    # anything else a chunk between a blank line on either side. Blank lines the gap cannot take
    # go back to the body before it.
    items: list[tuple[str, object]] = []
    if not sections:
        items.append(("md", text[:-1]))
        return items, reqs
    try:
        p = _md_prefix(text[:sections[0][0]])
    except ValueError:
        raise ConvertError(f"{fname}: no blank line before the first requirement heading")
    if p is not None:
        items.append(("md", p))
    for n, (_, e, r) in enumerate(sections):
        nxt = sections[n + 1][0] if n + 1 < len(sections) else len(text)
        last = n + 1 == len(sections)
        while True:
            gap = text[off[e]:nxt]
            try:
                md = _md_suffix(gap) if last else _md_gap(gap)
                break
            except ValueError:
                if e >= min(r["_j"], len(lines) - 1):
                    raise ConvertError(f"{fname}: {r['id']}: the text after the section "
                                       f"({gap[:40]!r}) cannot be rendered; put a blank line "
                                       f"before the next heading")
                e += 1
        r["body"] = text[off[r["_lo"]]:off[e] - 1]
        items.append(("req", r))
        if md is not None:
            items.append(("md", md))
    return items, reqs


# --------------------------------------------------------------------------
# placing the quotes
# --------------------------------------------------------------------------

def visible(body: str) -> list[bool]:
    """Per character: is it outside fenced code, HTML comments and ~~strikethrough~~ (what the
    alignment check compares)?"""
    vis = [True] * len(body)
    pos = 0
    fence: tuple[str, int] | None = None
    in_comment = False
    for line in body.split("\n"):
        start, end = pos, pos + len(line)
        pos = end + 1
        if fence is not None:
            for i in range(start, end):
                vis[i] = False
            c, n = fence
            if re.match(rf"^ {{0,3}}{re.escape(c)}{{{n},}}\s*$", line):
                fence = None
            continue
        if not in_comment:
            m = ALIGN.FENCE_OPEN_RE.match(line)
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence = (m.group(2)[0], len(m.group(2)))
                for i in range(start, end):
                    vis[i] = False
                continue
        i = start
        while i < end:
            if in_comment:
                k = body.find("-->", i, end)
                stop = end if k < 0 else k + 3
                for x in range(i, stop):
                    vis[x] = False
                i = stop
                if k >= 0:
                    in_comment = False
            else:
                k = body.find("<!--", i, end)
                if k < 0:
                    break
                i, in_comment = k, True
        for m in ALIGN.STRIKE_RE.finditer(line):
            for x in range(start + m.start(), start + m.end()):
                vis[x] = False
    return vis


def normalised(body: str) -> tuple[str, list[int]]:
    """`norm` of the visible body, with the raw index of every normalised character."""
    vis = visible(body)
    out: list[str] = []
    idx: list[int] = []
    for i, c in enumerate(body):
        if not vis[i] or c in "*_":
            continue
        if c.isspace():
            if out and out[-1] != " ":
                out.append(" ")
                idx.append(i)
            continue
        out.append(c)
        idx.append(i)
    return "".join(out), idx


def place(body: str, quote: str) -> tuple[tuple[int, int] | None, bool, int]:
    """Find the raw span of `quote` in `body`: (span or None, resolves exactly, occurrences)."""
    n, idx = normalised(body)
    q = ALIGN.norm(quote)
    if not q:
        return None, False, 0
    found: list[tuple[int, int]] = []
    p = n.find(q)
    while p >= 0:
        found.append((idx[p], idx[p + len(q) - 1] + 1))
        p = n.find(q, p + 1)
    def ends(a: int, b: int) -> list[tuple[int, int]]:
        la = 0
        while a - la - 1 >= 0 and body[a - la - 1] in "*_":
            la += 1
        rb = 0
        while b + rb < len(body) and body[b + rb] in "*_":
            rb += 1
        return [(a - x, b + y) for x in range(la + 1) for y in range(rb + 1)]

    for a, b in found:
        for x, y in ends(a, b):
            if join_lines(body[x:y]) == quote:
                return (x, y), True, len(found)
    if found:
        # No span reads as the quote: take the widest one whose emphasis markers pair up.
        cands = ends(*found[0])
        best = max(cands, key=lambda s: (body[s[0]:s[1]].count("*") % 2 == 0, s[1] - s[0]))
        return best, False, len(found)
    return None, False, 0


# --------------------------------------------------------------------------
# Lean sources
# --------------------------------------------------------------------------

def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def lean_raw(s: str) -> str:
    n = 1
    while '"' + "#" * n in s:
        n += 1
    return f'r{"#" * n}"{s}"{"#" * n}'


def text_module(r: dict) -> str:
    fields = "".join(f"  {k.lower()} {r[k]}\n" for k in FIELDS if r.get(k))
    return (f"import Libpetri.Spec.Text\n\nrequirement_text {r['key']}\n  id {lean_str(r['id'])}\n"
            f"  title {lean_str(r['title'])}\n{fields}  body {lean_raw(r['body'])}\n")


def chapter_module(fname: str, items) -> str:
    keys = [v["key"] for k, v in items if k == "req"]
    out = "import Libpetri.Spec.Text\n" + "".join(f"import Libpetri.Spec.Text.{k}\n" for k in keys)
    out += f"\nspec_chapter {lean_str(fname)}\n"
    for k, v in items:
        out += f"  md {lean_raw(v)}\n" if k == "md" else f"  req {v['key']}\n"
    return out


def chapter_module_name(fname: str) -> str:
    stem = fname[:-3]
    m = re.match(r"^(\d+)-", stem)
    if m:
        return "Ch" + m.group(1)
    return "".join(w.capitalize() for w in re.split(r"[-_]", stem))


def read_lean_string(src: str, i: int) -> tuple[str, int]:
    """Decode the Lean string literal starting at src[i] == '"'; return (value, end index)."""
    assert src[i] == '"'
    out: list[str] = []
    i += 1
    while True:
        c = src[i]
        if c == '"':
            return "".join(out), i + 1
        if c == "\\":
            e = src[i + 1]
            if e in '\\"\'':
                out.append(e)
                i += 2
            elif e in "ntr":
                out.append({"n": "\n", "t": "\t", "r": "\r"}[e])
                i += 2
            elif e == "x":
                out.append(chr(int(src[i + 2:i + 4], 16)))
                i += 4
            elif e == "u":
                out.append(chr(int(src[i + 2:i + 6], 16)))
                i += 6
            elif e == "\n":
                i += 2
                while src[i] in " \t\r\n":
                    i += 1
            else:
                raise ConvertError(f"unknown escape \\{e} in a Lean string")
        else:
            out.append(c)
            i += 1


def skip_ws(src: str, i: int) -> int:
    while i < len(src):
        if src[i] in " \t\r\n":
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            break
    return i


def quote_clause(src: str, short: str) -> tuple[int, int, list[str], int] | None:
    """Locate `quote "…" …` of `requirement <short>`: (start, end, strings, block start), or None
    when the block takes `covers` already."""
    m = re.search(rf"(?m)^requirement\s+{re.escape(short)}\s", src)
    if not m:
        raise ConvertError(f"no 'requirement {short}' command")
    i = m.end()
    while True:
        i = skip_ws(src, i)
        if src[i] == '"':
            _, i = read_lean_string(src, i)
            continue
        w = re.match(r"[A-Za-z_][A-Za-z0-9_.]*", src[i:])
        if not w:
            raise ConvertError(f"requirement {short}: unexpected {src[i:i + 20]!r} before quote")
        word = w.group(0)
        if word in ("covers", "reading", "statement"):
            return None
        if word == "quote":
            start = i
            i += len(word)
            vals: list[str] = []
            end = i
            while True:
                j = skip_ws(src, i)
                if j < len(src) and src[j] == '"':
                    v, i = read_lean_string(src, j)
                    vals.append(v)
                    end = i
                else:
                    return start, end, vals, m.start()
        i += len(word)


def covers_text(refs: list[str], indent: int) -> str:
    out, line = [], "covers"
    for n, r in enumerate(refs):
        piece = r + ("," if n + 1 < len(refs) else "")
        if len(line) + 1 + len(piece) + indent > 100 and line != "covers":
            out.append(line)
            line = " " * 6 + piece
        else:
            line += " " + piece
    out.append(line)
    return ("\n" + " " * indent).join(out)


def ensure_import(path: Path, module: str, sort: bool) -> bool:
    """Add `import <module>` to the import header of `path`; sorted among the `import Libpetri.`
    lines when `sort`, else after the last import. Return True when the file changed."""
    lines = path.read_text(encoding="utf-8").split("\n")
    want = f"import {module}"
    if want in lines:
        return False
    imps = [i for i, l in enumerate(lines) if l.startswith("import ")]
    if not imps:
        raise ConvertError(f"{path}: no import header")
    header_end = imps[0]
    while header_end < len(lines) and lines[header_end].startswith("import "):
        header_end += 1
    at = header_end
    if sort:
        for i in range(imps[0], header_end):
            if lines[i].startswith("import Libpetri.") and lines[i] > want:
                at = i
                break
    lines.insert(at, want)
    path.write_text("\n".join(lines), encoding="utf-8")
    return True


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def convert(chapter: Path, report: Path, dry: bool) -> int:
    fname = chapter.name
    text = chapter.read_text(encoding="utf-8")
    items, reqs = split_chapter(text, fname)
    plain = text.split("\n", 1)[1] if BANNER_RE.match(text.split("\n", 1)[0]) else text
    for r in reqs.values():
        if "⟦" in r["body"] or "⟧" in r["body"]:
            raise ConvertError(f"{r['id']}: the body already holds ⟦ or ⟧")
    if render_chapter(items) != plain:
        raise ConvertError(f"{fname}: the rendered chapter differs from the markdown")

    blocks = [b for b in json.loads(report.read_text(encoding="utf-8"))["requirements"]
              if b["id"] in reqs and b["source"] == "verbatim"]
    # Place every quote; one span per distinct raw range of a body.
    placed: dict[str, dict[tuple[int, int], str]] = {rid: {} for rid in reqs}
    plan: list[tuple[dict, list[tuple[int, int]] | None]] = []
    differs: list[str] = []
    unplaced: list[str] = []
    repeated: list[str] = []
    for b in blocks:
        body = reqs[b["id"]]["body"]
        got: list[tuple[int, int]] = []
        ok = True
        for q in b["quotes"]:
            span, exact, count = place(body, q)
            if span is None:
                unplaced.append(f"{b['decl']}: {q!r}")
                ok = False
                continue
            if count > 1:
                repeated.append(f"{b['decl']}: {q[:70]!r} occurs {count} times; the first is wrapped")
            if not exact:
                differs.append(f"{b['decl']}: quote {q!r}\n    resolves to {join_lines(body[span[0]:span[1]])!r}")
            got.append(span)
        plan.append((b, got if ok else None))
        if ok:
            for s in got:
                placed[b["id"]][s] = ""
    # Labels in order of appearance; spans must not overlap.
    for rid, spans in placed.items():
        order = sorted(spans)
        for x, y in zip(order, order[1:]):
            if y[0] < x[1]:
                raise ConvertError(f"{rid}: two quotes overlap: {reqs[rid]['body'][x[0]:x[1]]!r} "
                                   f"and {reqs[rid]['body'][y[0]:y[1]]!r}")
        for n, s in enumerate(order):
            spans[s] = f"s{n + 1}"
        body = reqs[rid]["body"]
        out, at = [], 0
        for s in order:
            out += [body[at:s[0]], f"⟦{spans[s]}|", body[s[0]:s[1]], "⟧"]
            at = s[1]
        reqs[rid]["body"] = "".join(out) + body[at:]
    if render_chapter(items) != plain:
        raise ConvertError(f"{fname}: the chapter with spans renders differently")

    mod = chapter_module_name(fname)
    print(f"spec-md-to-lean: {fname}: {len(reqs)} requirement texts, chapter "
          f"Libpetri.Spec.Text.Chapter.{mod}; {sum(len(b['quotes']) for b in blocks)} quotes in "
          f"{len(blocks)} verbatim blocks, {sum(len(s) for s in placed.values())} spans")
    for title, rows in (("quotes whose span resolves differently (hash changes, sign-off reset to pending)", differs),
                        ("quotes not found (the block keeps its quote strings)", unplaced),
                        ("quotes found more than once", repeated)):
        print(f"  {title}: {len(rows)}")
        for row in rows:
            print(f"    {row}")
    if dry:
        return 0

    TEXT_DIR.mkdir(parents=True, exist_ok=True)
    (TEXT_DIR / "Chapter").mkdir(exist_ok=True)
    new_modules = ["Libpetri.Spec.Text"]
    for r in reqs.values():
        (TEXT_DIR / f"{r['key']}.lean").write_text(text_module(r), encoding="utf-8")
        new_modules.append(f"Libpetri.Spec.Text.{r['key']}")
    (TEXT_DIR / "Chapter" / f"{mod}.lean").write_text(chapter_module(fname, items), encoding="utf-8")
    new_modules.append(f"Libpetri.Spec.Text.Chapter.{mod}")

    differs_decls = {d.split(":", 1)[0] for d in differs}
    for b, got in plan:
        if got is None:
            continue
        path = LEAN / (b["module"].replace(".", "/") + ".lean")
        src = path.read_text(encoding="utf-8")
        short = b["decl"].rsplit(".", 1)[1]
        found = quote_clause(src, short)
        if found is None:
            continue
        start, end, vals, blk = found
        if vals != b["quotes"]:
            raise ConvertError(f"{path}: the quotes of {short} differ from the report; "
                               f"regenerate lean/report first")
        key = reqs[b["id"]]["key"]
        refs = [f"{key}.{placed[b['id']][s]}" for s in got]
        indent = start - (src.rfind("\n", 0, start) + 1)
        src = src[:start] + covers_text(refs, indent) + src[end:]
        if b["decl"] in differs_decls:
            m = re.compile(r'signoff "[^"]*"').search(src, blk)
            src = src[:m.start()] + 'signoff "pending"' + src[m.end():]
        path.write_text(src, encoding="utf-8")
        ensure_import(path, f"Libpetri.Spec.Text.{key}", sort=False)
        print(f"  {path.relative_to(REPO)}: {short} covers {', '.join(refs)}")

    for f, sort in ((LEAN / "Libpetri/Spec/All.lean", False), (LEAN / "spec-tools/Audit.lean", True),
                    (LEAN / "spec-tools/Report.lean", True)):
        for m in new_modules:
            ensure_import(f, m, sort)
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("chapter", help="the chapter, e.g. spec/10-performance.md")
    ap.add_argument("--report", default="lean/report/requirements.json")
    ap.add_argument("--dry-run", action="store_true", help="report only, write nothing")
    a = ap.parse_args(argv)
    chapter = Path(a.chapter)
    report = Path(a.report)
    chapter = chapter if chapter.is_absolute() else REPO / chapter
    report = report if report.is_absolute() else REPO / report
    try:
        return convert(chapter, report, a.dry_run)
    except ConvertError as e:
        print(f"spec-md-to-lean: ERROR: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
