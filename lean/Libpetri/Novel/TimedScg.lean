import Libpetri.Novel.TimedScg.Zone
import Libpetri.Novel.TimedScg.Succ
import Libpetri.Novel.TimedScg.Timing
import Libpetri.Novel.TimedScg.Run
import Libpetri.Novel.TimedScg.Grid
import Libpetri.Novel.TimedScg.Progress
import Libpetri.Novel.TimedScg.Late
import Libpetri.Novel.TimedScg.Retrodict

/-!
# The timed state-class graph successor ([VER-010], [VER-011], [VER-023], [TIME-012], [TIME-013])

Root of the `Novel/TimedScg/` modules, gap R6 of the Lean coverage review: the timed path of
`state_class_graph.rs::compute_successor` (firing-domain construction, `dbm.rs`
`create` / `let_time_pass` / `fire_transition` / `permuted`, the `is_empty` drop) against the
Time Petri net semantics with the [TIME-012] clock rule, and against an executor that falls
behind and reaps deadlines.

* `Zone.lean`: the positional DBM operations, tied to `Novel/Dbm.lean` (`toFin_canonN`), and
  which valuations each keeps.
* `Succ.lean`: the model of the successor and of the timed semantics; `successor_sound`,
  `delay_sound`, `init_sound`. The premises about the Rust are listed there, including the
  executor's clock rule (premise 9, assumed).
* `Timing.lean`: the Rust `Timing` enum and the intervals the graph reads from it (`latest()` is
  the finite `MAX_DURATION_MS` for `immediate` / `delayed`), when premise 6 holds, and the
  millisecond grid.
* `Run.lean`: `timed_run_sound`, `timed_markings_discovered` (with `Enumeration.lean`), the
  persistence rule and the [TIME-012] bullets.
* `Grid.lean`: every zone of the graph stays on the grid of the net's bounds, so the Rust
  `EPSILON = 1e-9` flag is the exact one.
* `Progress.lean`: a class with an enabled transition always has a successor (`succ_exists`,
  `reachable_quiescent_iff_dead`, `faithful_quiescent_iff_dead`), as [VER-023] requires.
* `Late.lean`: verification that accounts for deadline reaping. A late executor (`LateStep`,
  tolerance, soft `exact`, revival) is covered by the graph of the net with its upper bounds
  dropped (`late_run_sound`), and it may rest only in a class whose clocks are all reapable
  (`late_quiescence_sound`).
* `Retrodict.lean`: the pre-6.0.0 persistence rule loses a timed run (`old_rule_loses_run`);
  deadline reaping, action duration and `delayed(after > MAX_DURATION_MS)` escape the timed
  graph; a name-disabled ν-join bounds time in a count-based graph (model level).

What `timed_counterexample_check` gets from this: its `SPURIOUS_UNDER_TIMING` half and its
quiescence reading, for an executor that is on time and whose actions deposit at once. Its
`TIMED_CONFIRMED` half (the graph is complete: every class is realised by a run) is not proven.
-/
