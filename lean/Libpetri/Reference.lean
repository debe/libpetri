import Libpetri.Reference.Marking
import Libpetri.Reference.Semantics
import Libpetri.Reference.Step
import Libpetri.Reference.Search
import Libpetri.Reference.Decide
import Libpetri.Reference.Link
import Libpetri.Reference.Situation

/-!
# The executable reference verifier ([VER-002], untimed, closed nets)

Root of `Libpetri/Reference/`, the machine-checked reference `lake exe reference` runs
(`spec/verification-fixtures/conformance/README.md`). Written from the spec, not from any
implementation:

* `Marking.lean` — canonical markings: sorted association lists without zero entries.
* `Semantics.lean` — the firing rule on named count markings ([CORE-022], [CORE-030]–[CORE-036],
  [IO-001]–[IO-016]) and [VER-002]'s properties.
* `Step.lean` — the executable successor function, equal to the one-step relation
  (`mem_succ_iff`).
* `Search.lean` — the capped breadth-first exploration (`explore_complete_iff`).
* `Decide.lean` — explored set = reachable set (`explored_eq_reachable`), exact verdicts
  (`verdict_proven_iff`), replayed traces (`verdict_violated_run`, `replayViolates_iff`).
* `Link.lean` — the firing rule is the development's: `ForwardDeposit.StepCD`,
  `Seam.StepNC` / `Seam.NDeadlock`, and `Enumeration.rows_enumeration_exact`'s `ReachAD`.
* `Situation.lean` — a situation's steps replayed one by one: each fired step is a firing
  with the chosen outcome, each blocked step cannot fire for the reason reported
  (`replaySituation_sound`; `spec/situations/README.md`).

`Load.lean` (the unverified JSON front end), `Sha256.lean` (the version stamp) and `Main.lean`
(the CLI) are not imported here.
-/
