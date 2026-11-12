#!/usr/bin/env python3
"""libpetri slide for the Haystack talk: results pair by identity, not by arrival order.

Writes two SVGs with live text (Lato + Fira Code) into the output directory:
  libpetri-slide.src.svg    full 16:9 slide (title band, QR, both panels, footer)
  libpetri-diagram.src.svg  the same drawing without the title band
render.sh turns them into PNGs and outlined (font-free) SVGs.
"""
import math
import re
import sys
from pathlib import Path

from PIL import ImageFont

HERE = Path(__file__).resolve().parent
OUT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE
QR = HERE / 'qr-libpetri.svg'

# Palette for a white ground.
INK, INK2, MUTED, FAINT = '#0f172a', '#334155', '#64748b', '#94a3b8'
HAIR, HAIR2, PANEL, TILE = '#e2e8f0', '#cbd5e1', '#f8fafc', '#f1f5f9'
TEAL, TEAL50 = '#0d9488', '#f0fdfa'
ROSE, ROSE50, ROSE200 = '#e11d48', '#fff1f2', '#fecdd3'
SNEAKER, WHITE = '#ef4444', '#ffffff'
GHOST_BLUE = '#a9c4f5'                  # token 2, overwritten
HALO_OUT, HALO_IN = '#e7f3f4', '#c5e4e3'  # teal at 7 % and 16 % over the panel, pre-blended
ID = {1: ('#d97706', '#b45309'), 2: ('#2563eb', '#1d4ed8')}  # token fill, text tint

SANS = "Lato, 'Helvetica Neue', Arial, sans-serif"
MONO = "'Fira Code', 'DejaVu Sans Mono', monospace"
LATO = {400: 'Regular', 500: 'Medium', 600: 'Semibold', 700: 'Bold', 800: 'Heavy', 900: 'Black'}
_fonts = {}


def tw(s, size, weight=400, mono=False, ls=0):
    """Advance width of s in px, measured with the installed font files."""
    key = (size, weight, mono)
    if key not in _fonts:
        path = ('/usr/share/fonts/truetype/firacode/FiraCode-Medium.ttf' if mono
                else f'/usr/share/fonts/truetype/lato/Lato-{LATO[weight]}.ttf')
        _fonts[key] = ImageFont.truetype(path, size)
    return _fonts[key].getlength(s) + ls * max(len(s) - 1, 0)


def n(v):
    return f'{v:.2f}'.rstrip('0').rstrip('.') if isinstance(v, float) else str(v)


def pt(p):
    return f'{n(p[0])} {n(p[1])}'


def esc(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;')


class Canvas:
    def __init__(self):
        self.el = []

    def raw(self, s):
        self.el.append(s)

    def text(self, x, y, s, size, weight=400, fill=INK, anchor='start', mono=False, ls=0):
        a = [f'x="{n(x)}"', f'y="{n(y)}"', f'font-family="{MONO if mono else SANS}"',
             f'font-size="{size}"', f'font-weight="{weight}"', f'fill="{fill}"']
        if anchor != 'start':
            a.append(f'text-anchor="{anchor}"')
        if ls:
            a.append(f'letter-spacing="{ls}"')
        self.raw(f'<text {" ".join(a)}>{esc(s)}</text>')

    def rect(self, x, y, w, h, rx=0, fill='none', stroke=None, sw=1.5, dash=None, opacity=None):
        a = [f'x="{n(x)}"', f'y="{n(y)}"', f'width="{n(w)}"', f'height="{n(h)}"', f'fill="{fill}"']
        if rx:
            a.append(f'rx="{n(rx)}"')
        if stroke:
            a.append(f'stroke="{stroke}" stroke-width="{n(sw)}"')
        if dash:
            a.append(f'stroke-dasharray="{dash}"')
        if opacity is not None:
            a.append(f'opacity="{opacity}"')
        self.raw(f'<rect {" ".join(a)}/>')

    def circle(self, cx, cy, r, fill='none', stroke=None, sw=1.5):
        s = f' stroke="{stroke}" stroke-width="{n(sw)}"' if stroke else ''
        self.raw(f'<circle cx="{n(cx)}" cy="{n(cy)}" r="{n(r)}" fill="{fill}"{s}/>')

    def path(self, d, stroke, sw=2, dash=None, fill='none', cap='round'):
        s = f' stroke-dasharray="{dash}"' if dash else ''
        self.raw(f'<path d="{d}" fill="{fill}" stroke="{stroke}" stroke-width="{n(sw)}" '
                 f'stroke-linecap="{cap}" stroke-linejoin="round"{s}/>')

    def polygon(self, pts, fill):
        self.raw(f'<polygon points="{" ".join(f"{n(x)},{n(y)}" for x, y in pts)}" fill="{fill}"/>')


# ---------------------------------------------------------------- primitives

def token(c, cx, cy, k, r=15, fill=None):
    c.circle(cx, cy, r, fill or ID[k][0])
    fs = round(r * 1.2)
    c.text(cx, cy + fs * 0.36, str(k), fs, 900, WHITE, anchor='middle')


def run(c, x, y, items, size, anchor='start'):
    """Inline text with id discs. items: ('t', text, weight, fill) or ('d', k).

    SVG drops leading and trailing spaces inside <text>, so they become explicit advances.
    """
    r = round(size * 0.55)
    laid = []  # (kind, payload, advance_before, width)
    for it in items:
        if it[0] == 'd':
            laid.append(('d', it, 0, 2 * r + 2))
            continue
        s, weight = it[1], it[2]
        body = s.strip()
        space = tw(' ', size, weight)
        lead = (len(s) - len(s.lstrip())) * space
        trail = (len(s) - len(s.rstrip())) * space
        laid.append(('t', (body,) + it[2:], lead, tw(body, size, weight) + trail))
    total = sum(before + w for _, _, before, w in laid)
    cur = {'start': x, 'middle': x - total / 2, 'end': x - total}[anchor]
    for kind, it, before, w in laid:
        cur += before
        if kind == 't':
            c.text(cur, y, it[0], size, it[1], it[2])
        else:
            token(c, cur + 1 + r, y - size * 0.34, it[1], r)
        cur += w
    return total


def head(c, tip, ang, color, L=13, W=6.5):
    bx, by = tip[0] - L * math.cos(ang), tip[1] - L * math.sin(ang)
    nx, ny = -math.sin(ang), math.cos(ang)
    c.polygon([tip, (bx + W * nx, by + W * ny), (bx - W * nx, by - W * ny)], color)


def arrow(c, p0, p3, color=INK2, sw=2, c1=None, c2=None, dash=None, L=13, W=6.5):
    """Straight or cubic arrow; the stroke stops under the head so the tip stays sharp."""
    ref = c2 if c2 else p0
    ang = math.atan2(p3[1] - ref[1], p3[0] - ref[0])
    dx, dy = (L - 1) * math.cos(ang), (L - 1) * math.sin(ang)
    end = (p3[0] - dx, p3[1] - dy)
    if c1:
        d = f'M {pt(p0)} C {pt(c1)} {pt((c2[0] - dx, c2[1] - dy))} {pt(end)}'
    else:
        d = f'M {pt(p0)} L {pt(end)}'
    c.path(d, color, sw, dash, cap='butt')
    head(c, p3, ang, color, L, W)


def bez(p0, c1, c2, p3, t):
    m = 1 - t
    return tuple(m ** 3 * a + 3 * m * m * t * b + 3 * m * t * t * q + t ** 3 * d
                 for a, b, q, d in zip(p0, c1, c2, p3))


def on_circle(cx, cy, r, deg):
    a = math.radians(deg)
    return cx + r * math.cos(a), cy + r * math.sin(a)


def pill(c, cx, cy, label, size, fg, bg, stroke, mono=False, weight=800, padx=14, h=32):
    w = tw(label, size, weight, mono) + 2 * padx
    c.rect(cx - w / 2, cy - h / 2, w, h, h / 2, bg, stroke, 1.5)
    c.text(cx, cy + size * 0.35, label, size, weight, fg, anchor='middle', mono=mono)
    return w


SNEAKER_UPPER = ('M1 12.5 C1 8 3 4.5 7 4.5 L10.5 4.5 C12 4.5 13 6 15 7.2 '
                 'C18 8.8 22 9.4 26 10 C29.5 10.5 31.5 12 31.5 14.5 L1 14.5 Z')


def tile(c, x, y, price, k):
    c.rect(x, y, 104, 44, 10, TILE)
    c.raw(f'<g transform="translate({n(x + 12)},{n(y + 13)})">'
          f'<path d="{SNEAKER_UPPER}" fill="{SNEAKER}"/>'
          f'<rect x="0.5" y="14" width="31.5" height="3.8" rx="1.9" fill="{INK2}"/>'
          f'<path d="M9 11.2 C14 12.3 19 12.1 24.5 10.6" fill="none" stroke="{WHITE}" '
          f'stroke-width="1.4" stroke-linecap="round"/></g>')
    c.text(x + 52, y + 29, price, 19, 800, INK)
    c.circle(x + 9, y + 9, 4.5, ID[k][0])


# ---------------------------------------------------------------- layout grid

PY, PH, PW = 196, 704, 876      # panel top, height, width
ROW0, ROW1, ROW2, ROW3 = 321, 410, 540, 674   # chips, searches, stores, reply (centre y)
ANS_Y = 738                     # answer card top
R_PLACE = 52


def panel_frame(c, px, title, color, sub):
    c.rect(px, PY, PW, PH, 26, PANEL, HAIR, 1.5)
    c.text(px + 40, PY + 46, title, 20, 900, color, ls=2)
    c.text(px + 40, PY + 74, sub, 18, 400, MUTED)


def chip(c, x, cy, k, label, note=None):
    w = 54 + tw(label, 22, 600) + 22 + (tw(note, 16, 800) + 14 if note else 0)
    c.rect(x, cy - 25, w, 50, 25, WHITE, HAIR2, 1.5)
    token(c, x + 28, cy, k, 14)
    c.text(x + 54, cy + 8, label, 22, 600, INK)
    if note:
        c.text(x + w - 20, cy + 7, note, 16, 800, MUTED, anchor='end')
    return w


def step_node(c, cx, cy, k, label, dur=None, petri=False):
    """A step-graph node (soft corners, room for a duration) or a Petri transition."""
    h = 60
    if petri:
        w = 160
        c.rect(cx - w / 2, cy - h / 2, w, h, 8, WHITE, INK2, 2.2)
        gx = cx - (36 + tw(label, 22, 700)) / 2
        token(c, gx + 13, cy, k, 13)
        c.text(gx + 36, cy + 8, label, 22, 700, INK)
        return
    w = 210
    x = cx - w / 2
    c.rect(x, cy - h / 2, w, h, 18, WHITE, FAINT, 2)
    token(c, x + 28, cy, k, 13)
    c.text(x + 50, cy + 8, label, 22, 700, INK)
    if dur:
        c.text(x + w - 18, cy + 7, dur, 18, 800, ID[k][1], anchor='end')


def inputs(c, px, petri):
    """The two queries and their searches. Durations only matter on the step-graph side."""
    x1 = px + 40
    w1 = chip(c, x1, ROW0, 1, 'red sneakers')
    x2 = x1 + w1 + 20
    w2 = chip(c, x2, ROW0, 2, 'red sneakers under €100', note='+0.3 s')
    s1, s2 = x1 + w1 / 2, x2 + w2 / 2
    for sx, k, dur in ((s1, 1, '1.8 s'), (s2, 2, '0.4 s')):
        arrow(c, (sx, ROW0 + 25), (sx, ROW1 - 30), MUTED, 2)
        step_node(c, sx, ROW1, k, 'search', None if petri else dur, petri)
    return s1, s2, x2 + w2


def answer(c, cx, k_results, prices, ok):
    w, h = 440, 108
    x0 = cx - w / 2
    c.rect(x0, ANS_Y, w, h, 16, WHITE, HAIR2, 1.5)
    run(c, x0 + 20, ANS_Y + 29, [('t', 'answer for ', 400, MUTED), ('d', 2),
                                 ('t', ' red sneakers under €100', 800, INK2)], 16)
    for i, price in enumerate(prices):
        tile(c, x0 + 20 + i * 114, ANS_Y + 46, price, k_results)
    bx, by = x0 + w - 42, ANS_Y + 68
    c.circle(bx, by, 22, TEAL if ok else ROSE)
    if ok:
        c.path(f'M{n(bx - 9)} {n(by + 1)} L{n(bx - 3)} {n(by + 7)} L{n(bx + 9)} {n(by - 6)}', WHITE, 4)
    else:
        c.path(f'M{n(bx - 7)} {n(by - 7)} L{n(bx + 7)} {n(by + 7)} '
               f'M{n(bx + 7)} {n(by - 7)} L{n(bx - 7)} {n(by + 7)}', WHITE, 4)
    color = TEAL if ok else ROSE
    run(c, cx, ANS_Y + h + 30, [('t', 'results of ', 900, color), ('d', k_results),
                                ('t', ' shown for ', 900, color), ('d', 2)], 18, anchor='middle')


def side_note(c, x, y, lines, color):
    for i, line in enumerate(lines):
        c.text(x, y + i * 23, line, 17, 800, color)


# ---------------------------------------------------------------- panels

def left_panel(c, px):
    panel_frame(c, px, 'STEP GRAPH + SHARED STATE', INK2,
                'steps hand results over through one shared slot')
    s1, s2, _ = inputs(c, px, petri=False)

    # One slot. Both searches write it; the slower one writes last.
    cx0, cx1 = s1 - 80, s2 + 80
    cx, top = (cx0 + cx1) / 2, ROW2 - 60
    c.rect(cx0, top, cx1 - cx0, 120, 16, WHITE, FAINT, 2)
    c.text(cx0 + 22, top + 30, 'state["results"]', 18, 500, INK2, mono=True)
    c.raw(f'<line x1="{n(cx0)}" y1="{n(top + 44)}" x2="{n(cx1)}" y2="{n(top + 44)}" '
          f'stroke="{HAIR}" stroke-width="1.5"/>')
    # The overwritten value: solid pale colours, because group opacity is doubled by
    # Inkscape's text-to-path export and is unreliable in slide tools.
    token(c, cx0 + 34, top + 69, 2, 11, fill=GHOST_BLUE)
    c.text(cx0 + 54, top + 76, 'under €100', 20, 700, FAINT)
    c.raw(f'<line x1="{n(cx0 + 50)}" y1="{n(top + 69)}" x2="{n(cx0 + 58 + tw("under €100", 20, 700))}" '
          f'y2="{n(top + 69)}" stroke="{FAINT}" stroke-width="2"/>')
    token(c, cx0 + 34, top + 99, 1, 11)
    c.text(cx0 + 54, top + 106, 'all red sneakers', 20, 700, INK)
    pill(c, cx1 - 16 - (tw('last write wins', 16, 800) + 28) / 2, top + 99,
         'last write wins', 16, ROSE, ROSE50, ROSE200)

    arrow(c, (s1, ROW1 + 30), (s1, top), INK2, 2)
    arrow(c, (s2, ROW1 + 30), (s2, top), INK2, 2)
    # Query 2 is sent at 0.3 s and searched in 0.4 s; query 1 needs 1.8 s.
    c.text(s1 + 12, top - 12, 'overwrites at 1.8 s', 16, 900, ROSE)
    c.text(s2 + 12, top - 12, 'writes at 0.7 s', 16, 700, MUTED)

    # Query 2's reply starts at 0.7 s and reads the slot after its 1.5 s LLM call.
    # Nothing ties that read to the query it answers.
    w = 210
    arrow(c, (cx, top + 120), (cx, ROW3 - 30), INK2, 2)
    c.text(cx + 12, ROW3 - 44, 'reads at 2.2 s', 16, 700, MUTED)
    step_node(c, cx, ROW3, 2, 'reply', '1.5 s')
    side_note(c, cx + w / 2 + 22, ROW3 - 6, ['reads the slot,', 'whoever wrote last'], ROSE)
    arrow(c, (cx, ROW3 + 30), (cx, ANS_Y), INK2, 2)
    c.text(cx + 12, ANS_Y - 12, 'sends', 16, 700, MUTED)
    answer(c, cx, 1, ['€129', '€149', '€189'], ok=False)


def right_panel(c, px):
    panel_frame(c, px, 'PETRI NET + TOKEN IDENTITY', TEAL,
                'libpetri: every token keeps the id of its query')
    s1, s2, chip2_right = inputs(c, px, petri=True)

    rx, ry = (s1 + s2) / 2, ROW2          # results place
    ox, oy = px + 720, ROW2               # open query place
    tx = (rx + ox) / 2                    # the selected transition
    tw_, th = 240, 60

    # Selection halo first, so arcs and the transition sit on top of it.
    c.rect(tx - tw_ / 2 - 18, ROW3 - th / 2 - 18, tw_ + 36, th + 36, 24, HALO_OUT)
    c.rect(tx - tw_ / 2 - 9, ROW3 - th / 2 - 9, tw_ + 18, th + 18, 16, HALO_IN)

    # Searches add tokens to one place. Nothing is overwritten: both ids stay.
    for sx in (s1, s2):
        ang = math.degrees(math.atan2(ROW1 + 30 - ry, sx - rx))
        p3 = on_circle(rx, ry, R_PLACE, ang)
        out = on_circle(rx, ry, R_PLACE + 30, ang)
        arrow(c, (sx, ROW1 + 30), p3, INK2, 2.2, c1=(sx, ROW1 + 62), c2=out)
    c.circle(rx, ry, R_PLACE, WHITE, INK2, 2.4)
    token(c, rx - 19, ry, 1, 16)
    token(c, rx + 19, ry, 2, 16)
    c.text(rx - R_PLACE - 14, ry - 2, 'results', 19, 800, INK2, anchor='end')
    c.text(rx - R_PLACE - 14, ry + 19, 'any arrival order', 15, 700, MUTED, anchor='end')

    # The query stays open until its answer is sent.
    arrow(c, (chip2_right, ROW0), (ox, oy - R_PLACE), INK2, 2.2,
          c1=(ox, ROW0), c2=(ox, ROW0 + 60))
    c.circle(ox, oy, R_PLACE, WHITE, INK2, 2.4)
    token(c, ox, oy, 2, 16)
    c.text(ox - 14, oy - R_PLACE - 40, 'open query', 19, 800, INK2, anchor='end')
    c.text(ox - 14, oy - R_PLACE - 18, 'only the newest waits', 15, 700, MUTED, anchor='end')

    # reply <n>: both inputs must carry the same id.
    for (px0, py0), deg, tip_x in (((rx, ry), 38, tx - 62), ((ox, oy), 142, tx + 62)):
        p0 = on_circle(px0, py0, R_PLACE, deg)
        c1 = on_circle(px0, py0, R_PLACE + 34, deg)
        p3 = (tip_x, ROW3 - th / 2)
        c2 = (tip_x, ROW3 - th / 2 - 34)
        arrow(c, p0, p3, TEAL, 2.8, c1=c1, c2=c2, L=14, W=7)
        mx, my = bez(p0, c1, c2, p3, 0.5)
        pill(c, mx, my, '⟨n⟩', 17, TEAL, TEAL50, TEAL, mono=True, weight=500, padx=10, h=28)

    c.rect(tx - tw_ / 2, ROW3 - th / 2, tw_, th, 10, TEAL)
    lbl, sub = 'reply ', '⟨n⟩'
    total = tw(lbl, 23, 800) + tw(sub, 21, 500, mono=True)
    c.text(tx - total / 2, ROW3 + 8, lbl, 23, 800, WHITE)
    c.text(tx - total / 2 + tw(lbl, 23, 800), ROW3 + 7, sub, 21, 500, WHITE, mono=True)
    side_note(c, tx + tw_ / 2 + 36, ROW3 - 6, ['fires only when', 'both ids match'], TEAL)

    # The late token never finds a partner; a delayed drain removes it.
    dx0, dw = px + 40, 160
    p0 = on_circle(rx, ry, R_PLACE, 150)
    arrow(c, p0, (dx0 + dw / 2 + 20, ROW3 - 26), FAINT, 2, dash='6 5',
          c1=on_circle(rx, ry, R_PLACE + 30, 150), c2=(dx0 + dw / 2 + 20, ROW3 - 60))
    c.rect(dx0, ROW3 - 26, dw, 52, 8, WHITE, FAINT, 2, dash='6 5')
    c.text(dx0 + dw / 2, ROW3 + 7, 'drain', 19, 800, MUTED, anchor='middle')
    run(c, dx0 + dw / 2, ROW3 + 54, [('d', 1), ('t', ' finds no partner,', 700, MUTED)], 16, anchor='middle')
    c.text(dx0 + dw / 2, ROW3 + 76, 'drained after a delay', 16, 700, MUTED, anchor='middle')

    arrow(c, (tx, ROW3 + th / 2), (tx, ANS_Y), INK2, 2)
    c.text(tx + 12, ANS_Y - 12, 'sends', 16, 700, MUTED)
    answer(c, tx, 2, ['€69', '€79', '€89'], ok=True)


# ---------------------------------------------------------------- bands

def title_band(c):
    c.text(72, 78, 'OPEN SOURCE BUILDING BLOCKS', 16, 900, TEAL, ls=3)
    c.text(68, 142, 'libpetri', 62, 900, INK)
    x = 68 + tw('libpetri', 62, 900) + 34
    c.text(x, 112, 'Coloured Time Petri nets for concurrent orchestration', 23, 800, INK2)
    c.text(x, 142, 'Java · TypeScript · Rust · Python · open source, Apache-2.0', 19, 400, MUTED)
    svg = QR.read_text()
    d = re.search(r'<path stroke="#000000" d="([^"]+)"', svg).group(1)
    mods = int(re.search(r'viewBox="0 0 (\d+) \d+"', svg).group(1))
    size, qx, qy = 116, 1856 - 116, 40
    c.raw(f'<g transform="translate({qx},{qy}) scale({size / mods:.5f})">'
          f'<path d="{d}" fill="none" stroke="{INK}" stroke-width="1" shape-rendering="crispEdges"/></g>')
    c.text(qx - 26, 98, 'libpetri.org', 30, 900, INK, anchor='end')
    c.text(qx - 26, 130, 'github.com/debe/libpetri', 18, 400, MUTED, anchor='end')
    c.raw(f'<line x1="64" y1="176" x2="1856" y2="176" stroke="{HAIR}" stroke-width="1.5"/>')


def footer(c):
    c.text(960, 972, 'Results pair by identity, not by arrival order.', 40, 900, INK, anchor='middle')
    c.text(960, 1014, 'The id match is part of the firing rule: there is no check-then-act gap. '
           'Runs in production, checked by Z3 in CI.', 21, 400, MUTED, anchor='middle')


ARIA = ('Two panels, same input: a customer searches for red sneakers, then refines to red sneakers '
        'under 100 euros while the first search is still running. Left, a step graph with shared state: '
        'the slow first search overwrites the results slot and the reply shows its items for the second '
        'query. Right, a libpetri Petri net: result tokens keep their query id, the reply transition fires '
        'only when result and open query carry the same id, and the late token is drained.')


def build(full):
    c = Canvas()
    c.rect(0, 0, 1920, 1080, 0, WHITE)
    if full:
        title_band(c)
    left_panel(c, 64)
    right_panel(c, 980)
    footer(c)
    vb, h = ('0 0 1920 1080', 1080) if full else ('0 164 1920 886', 886)
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{vb}" width="1920" height="{h}" '
            f'role="img" aria-label="{esc(ARIA)}">\n<title>libpetri: results pair by identity</title>\n'
            + '\n'.join(c.el) + '\n</svg>\n')


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'libpetri-slide.src.svg').write_text(build(full=True))
    (OUT / 'libpetri-diagram.src.svg').write_text(build(full=False))
    print('wrote', OUT)
