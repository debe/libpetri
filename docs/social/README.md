# libpetri social posts

One folder per post. Each holds `post.md` (copy, image order, sources) plus the SVG sources
and rendered 1200x1200 PNGs.

Re-render any graphic with:

```
inkscape --export-type=png --export-width=1200 <file>.svg
```

## Series

| # | Post | Angle | Status |
|---|------|-------|--------|
| 1 | Who verifies the verifier? | Every `Proven` discharges its own certificate, every `Violated` is replayed. | copy drafted, art needed |
| 2 | A proof that cannot go stale | `lean/fidelity.toml` hashes 89 shipped Rust functions and pins them to the theorems modelling them. Change one, CI fails. | outlined |
| 3 | [The laws were there. The basis was not.](ver007-basis/post.md) | VER-007 on a toy net: a correctness gate silently disarmed the prover; the fix was a better basis. | **ready** |
| 4 | [The twelve missing laws](assistant-backend/post.md) | The same failure in the production AI assistant backend. 50 minutes to Unknown, 15 seconds to Proven. | **ready** |
| 5 | One solver transport | Four languages, byte-identical SMT text, diffed in CI against goldens. | optional tail |

3 and 4 are a pair: mechanism, then the production instance. 4 is the stronger of the two on
its own, so it can also run first with 3 as the follow-up for readers who want the detail.

## House style

Dark ground `#0b1220`, teal accent `#2dd4bf`, red `#f5556d`, amber `#fbbf24`, ink `#e8eef6` /
`#c7d4e2` / `#8295ab`. Matches `docs/talks/*.svg`.

No em-dashes in copy. No hashtags. Public copy never names the employer or the product, and
never uses "checked map" framing for what the firing rule does.
