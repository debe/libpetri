# Post — the AI assistant backend, and the twelve missing laws

Production companion to the VER-007 post. That one explains the mechanism on a toy net;
this one is the same failure in a real system, with real numbers.

**Disclosure boundaries agreed for this post:** the system is "the backend of our AI
assistant". No employer, no product name, no vertical. Net vocabulary is limited to the safe
subset (`CUSTOMER_INPUT`, `TURN_BUDGET`, `ForkInput`, `CloseTurn`, tool round, guard
violation, model response). Nothing about speculative search or delegation routing appears
in the copy or the graphics.

**Images, in order:**

| | File | Carries |
|---|---|---|
| 1 | [`01-three-laws-of-fifteen.png`](01-three-laws-of-fifteen.png) | 50 min to Unknown, against 15 s to Proven, and why |
| 2 | [`02-the-arc-that-did-it.png`](02-the-arc-that-did-it.png) | The net shape stripped down, with the consume-all arc that did it |
| 3 | [`03-what-the-proof-says.png`](03-what-the-proof-says.png) | The five claims the whole-net proof carries, and the two that did not close |

SVG sources sit beside each PNG. Re-render with
`inkscape --export-type=png --export-width=1200 <file>.svg`.

## Copy

The backend of our AI assistant had a proof that ran for 50 minutes and then said it did not know.

Same net, same question, same search depth: it comes back Proven in 15 seconds now. The verifier had been working with three of the net's fifteen conservation laws.

Here is where the other twelve went. The net drains its customer input queue with a consume-all arc, so everything that arrived while the previous turn was still running gets taken in one go. Our verifier refuses any conservation law carrying weight on a place drained like that, because the encoder's step relation is not linear there and such a law can quietly delete reachable states and hand back a proof of a net that is not yours. That rule is right and it stays.

The problem sat upstream of it. The laws were read off whatever null-space basis Gaussian elimination happened to return, and elimination folds that one place into rows that never needed to touch it. The gate dropped them, correctly, and took most of the net's laws with it. The report says Dropped. It does not say the prover just lost the arithmetic it needed.

So the fix was a better basis rather than a weaker rule. P-semiflows, the minimal non-negative laws of a net, are exactly the combinations that avoid the drained place. Same gate, no exemption, union in what survives. Twelve came back.

That bought a proof of the whole net from a session's start marking, instead of slice proofs chained together by hand. With fresh messages allowed to arrive at any moment: ten places that carry a turn hold at most one token, so exactly one turn is admitted however fast the client sends; a guard violation and a model response never coexist; one tool round is open at a time; no correlation token outlives the turn it belongs to.

Two claims stayed undecided, so they are not in the suite. The same week we deleted the last test that had been passing on Unknown, and the helper that allowed it. A green test means a proof now.

The customer-facing half of it: everything that piled up while the assistant was working is answered together, once, rather than one sequential turn per message.

libpetri is Apache 2.0. Java, TypeScript, Rust, Python.

## Alternate openings

- "A green test that is green because the verifier said it did not know is not a test. We had one. We deleted it."
- "Our prover was quietly running on three of fifteen conservation laws, and the only sign was a line saying Dropped."

## Accuracy notes

Checked against the branch before writing, because these are public claims about a production system.

- **50 min to Unknown, 15 s to Proven, same k=13** and **3 of ~15 laws, 12 semiflows**: commit
  `833250e1`, "prove both whole nets deadlock-free".
- **One turn at a time**: `TextCriticalRouteSafetyTest.oneTurnAtATime` proves `placeBound(place, 1)`
  on ten places carrying a turn, on the session net with the three environment places open at
  `bounded(2)`.
- **Verdicts never crossed**: same class, `neverTogetherByLaw` and `neverTogetherByRoute`.
- **Whole-net deadlock freedom**: `TextWholeNetDeadlockFreedomTest`, `VoiceWholeNetDeadlockFreedomTest`.
- **The two undecided claims**: named in `833250e1` and deliberately excluded from the suite.
- **The test that passed on Unknown**: commit `231724ad`.
- **Queue drain into one turn**: commit `1731edd4`.

One thing the copy deliberately does **not** say: that the net is fully concurrent across turns.
It is not, and the branch proves the opposite. `TURN_BUDGET` holds one token and turns are
strictly sequential by construction. The concurrency is inside a turn (guard, intent and
response branches, plus tool rounds) and the "no waiting" claim is the queue drain: a customer
never waits through N sequential turns for messages they sent while the assistant was busy.
