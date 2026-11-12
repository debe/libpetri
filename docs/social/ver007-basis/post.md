# libpetri LinkedIn series

Running order. Each post stands alone; together they build.

| # | Post | Angle | Status |
|---|------|-------|--------|
| 1 | Who verifies the verifier? | Every `Proven` discharges its own certificate, every `Violated` is replayed. We stopped trusting our own output. | copy drafted, needs art |
| 2 | A proof that cannot go stale | `lean/fidelity.toml` hashes 89 shipped Rust functions and pins them to the theorems that model them. Change one, CI fails. Plus the coverage matrix that publishes its own gaps. | outlined |
| 3 | **The laws were there. The basis was not.** (VER-007) | A correctness gate silently disarmed the prover. The fix was a better basis, not a weaker gate. 120 s to ~1 s. | **ready, below** |
| 4 | One solver transport | Four languages, byte-identical SMT text, diffed in CI against goldens. Conformance as a diff, not a debate. | optional tail |

Post 3 is the strongest of the four and works as the climax: 1 sets up the distrust, 2 shows how the distrust is enforced, 3 is what the distrust cost and then bought.

---

## Post 3 — VER-007

**Images, in order:**

| | File | Carries |
|---|---|---|
| 1 | [`01-the-basis-was-wrong.png`](01-the-basis-was-wrong.png) | The mechanism: two rows of the same null space, one dropped, one encoded |
| 2 | [`02-nothing-says-a-law-is-missing.png`](02-nothing-says-a-law-is-missing.png) | Why it went unnoticed: the basis shredded, and the whole report signal |
| 3 | [`03-proved-then-ported.png`](03-proved-then-ported.png) | 120 s to ~1 s, and the two Lean theorems that gate it |

SVG sources sit beside each PNG. Re-render with
`inkscape --export-type=png --export-width=1200 <file>.svg`.

### Copy

Draining an input queue was enough to stop our verifier proving anything.

libpetri hands IC3 the net's conservation laws, the weighted token sums that firing never changes, so the solver does not have to rediscover them. Last release we started rejecting any law that carries weight on a place a transition drains with all(), atLeast(n) or a reset arc. The encoder's step relation is not linear there, and a law like that silently deletes reachable states and manufactures a proof. That check is correct and it stays.

Where the laws came from is what we missed. We were reading them off the null-space basis that Gaussian elimination happens to return, and elimination is free to fold a reset place into a row that never needed to touch one. The law is true. The way it is written is not usable. So the gate drops it, correctly, and takes every other row of that chain with it. One drain arc on a busy place, and nothing in the report tells you a law went missing beyond a Dropped line.

The fix was not a weaker gate. It was a better basis. The P-semiflows, the minimal non-negative laws of the net, are exactly the combinations that avoid the drained place, and elimination had folded them away. We enumerate those, put them through the identical gate with no exemption, and union what survives into what the encoders receive.

On the net that surfaced this, eight reachability queries had been burning a 120 second budget and returning Unknown. They close in about a second now.

Off by default, so existing reports stay byte-identical. Two Lean theorems gate it in CI: the union is pure strengthening and can never turn a Violated into a Proven, and semi-positivity alone does not earn an exemption from the check.

libpetri, Apache 2.0. Java / TypeScript / Rust / Python.

### Alternate openings

- "We shipped a correctness fix that quietly stopped our own prover from proving anything."
- "The conservation law was right. The way linear algebra had written it down was not."

---

## Verification of the claims in post 3

Run from `lean/` with `~/.elan/bin` on PATH.

```
$ lake build
Build completed successfully (20 jobs).

$ lake env lean Ax.lean
'Libpetri.semiflow_union_sound' depends on axioms: [propext, Quot.sound]
'Libpetri.semiflow_gate_is_necessary' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`. Both are in the CI axiom gate (`.github/workflows/ci.yml:211-213`).

Other numbers: `spec/07-verification.md` (VER-007 body and AC1-AC6), `CHANGELOG.md`
(Java 4.0.0 / TypeScript 4.0.0 / Rust 4.1.0 / Python 3.1.0 wave) for the 120 s figure and the
byte-identical-report default.

### Notes on the copy

- No hashtags. This audience does not search them.
- First two sentences are what survives the "see more" fold.
- The `Dropped` line and `Semiflows encoded as invariants: N` are the real report strings, not paraphrases.
