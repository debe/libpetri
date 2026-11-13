import Libpetri.Spec.Text

requirement_text NU_055
  id "NU-055"
  title "Name Alignment"
  priority MAY
  kind F
  body r#"The ν properties of [NU-040] and [VER-002] count tokens. Some contracts are about which name the
tokens carry. A search box that shows the results of the latest query should hold one name in the
place that records the query and in the place that shows its results; a stale reply that lands
after the user has typed again breaks that while every count stays in range. An implementation MAY
offer two properties that read the name layer of Route B ([NU-050], [VER-012]):

- ⟦s1|**NameAligned(S)**, for a non-empty list `S` of places: in every reachable marking, the places of
  `S` together hold at most one distinct name.⟧ ⟦s2|For places `p` and `q` of `S`, the same place
  included, and the name-symbols `s` and `t`: `s` resident in `p` and `t` resident in `q` imply
  `s = t`.⟧ ⟦s3|An empty place imposes nothing, but a place holding two names violates it whatever the
  others hold, so the singleton `NameAligned(p)` says that `p` never holds two names.⟧
- ⟦s4|**QuiescentNameAligned(S)**: the same predicate, read only in the reachable quiescent markings.⟧
  Quiescence is the reap-aware quiescence of [VER-002]: on the graph, an expanded class every
  firing out of which is of a reapable transition. Like `JoinedOrDeadLettered` ([NU-040]) it
  carries no sink clause: declared sink places ([VER-002], [VER-014]) do not weaken it.

⟦s5|*Where* name alignment is offered, `NameAligned(S)` for a non-empty `S` *shall* hold on a class of the graph exactly when, for places `p` and `q` of `S`, the same place included, every name-symbol resident in `p` equals every name-symbol resident in `q`.⟧

`NameAligned` is a reachability-safety property and `QuiescentNameAligned` a quiescence property,
for every rule of [VER-012] that distinguishes the two (the early stop of AC5, the prefix rule of
AC3). ⟦s6|The predicate compares names only for equality, so it is invariant under any permutation of
the name-symbols.⟧ ⟦s7|It is therefore a function of the canonical key of a class ([VER-012] AC2), and
deciding it on the name-permutation quotient decides it on the graph.⟧

⟦s8|*When* the graph closes, Route B *shall* answer `Proven` for `NameAligned(S)` exactly when every class of the graph is name-aligned on `S`, and for `QuiescentNameAligned(S)` exactly when every class of the graph at which the net rests is.⟧

`S` keeps the order the caller gives. ⟦s9|Its places compare by name, and a place listed twice counts
once, at its first occurrence, so `NameAligned(box, list, box)` is `NameAligned(box, list)`.⟧ An
empty `S` MUST be rejected where it is constructed, as the language reports a caller's error,
rather than yield a verdict. ⟦s10|The order of `S` changes no verdict; it fixes the description and
which place a reason names.⟧

**Coloured places only.** ⟦s11|Every place of `S` MUST be a coloured place of the fragment Route B
classified for the call: match keys ([NU-020]), declared carriers ([NU-051]) and relay targets
([NU-054]).⟧ An uncoloured place carries no name in the name layer, so the predicate on it holds
vacuously and a `Proven` would say nothing about the net. ⟦s12|A place that is uncoloured, or absent from
the net (the net does not declare it and the initial marking does not mark it), MUST fail loudly: the
verdict is `Unknown`, never `Proven`, and where no earlier refusal of the refusal order below applies,
its reason names a place of `S`: the first absent place of `S`, otherwise the first uncoloured one.⟧
A place that a mint or a coloured consumer writes is coloured only when it is one of these, which is
why the worked example declares `inflightA`, `inflightB` and `list` as carriers. The coloured set is
the one the classifier computes for the call (Rust `coloured_order`, the `co` of the Lean
theorems), not a set the caller names.

The name a carrier or relay target holds is the name the analysis threads into it. No projection
reads a carrier, so that this name is the name the token's value is about rests on the documented,
unchecked contract of the coloured consumers that write it ([NU-051]): a `fetchA` whose action
answered a different query than the name it relays would still prove aligned. The property is
exactly as faithful to what a token carries as those contracts are.

⟦s13|The coloured places MUST start empty (the `hempty` premise of the Lean theorems).⟧ ⟦s14|A call whose
initial marking holds a token in a coloured place (a restored marking, [CORE-073], [NU-011]) is
`Unknown`, and where no earlier refusal of the refusal order below applies, its reason names the
place, the first in code-point order of place names when several are marked; since nothing else
decides the property, there is no fallback.⟧

**EXTENDED.** ⟦s15|Under **BASE** the coloured set is the match keys alone ([NU-051], [NU-054]), so a
property place that is a carrier or a relay target is uncoloured there.⟧ ⟦s16|Such a call is refused at
step 2 or at step 6 of the refusal order below unless an earlier step refuses it, and the reason of
either step MUST name EXTENDED.⟧ A net outside the EXTENDED fragment gets the "EXTENDED declined" note of [NU-051] and the
verdict `Unknown`. For a name-alignment property the note MUST NOT say that the property was
verified by another route; it says the verdict is `Unknown`.

**Route B only.** Route A ([NU-050], [NU-053]), the name-blind SMT pipeline ([VER-001]), the linear
bound ([VER-015]), the state-equation and firing-bound phases ([VER-018], [VER-019]), the bounded
witness phase ([VER-025]), the bounded enumeration ([VER-017]) and the structural checks ([VER-020]) do not see names. None of them decides a
name-alignment property: called directly, each returns no verdict, or `Unknown` with a reason
saying that it is decided only by the name-partition graph, and the dispatcher MUST NOT defer a
Route B `Unknown` to any of them (no [NU-053] fallback). The script encoders (`encodeScripts`,
`encode_scripts`, `encode_smt_scripts`) return no script for these properties.

A name-alignment query goes to Route B whatever the shape of the net: it needs no matched
transition, only a coloured fragment. For every other property the classifier returns no fragment
for a net without a matched transition and the dispatcher sends such a net to the flat phases; an
implementation MUST lift both gates for the name-alignment properties, and only for them. The
dispatcher sends a name-alignment property to Route B before its other routing tests: a declared
budget place, which keeps a reachability-safety property on Route A ([NU-050]), does not apply.

**Modelled injection.** Under `AlwaysAvailable` or `Bounded(k)` ([VER-006]) the decline rule of
[NU-050] and [VER-006] AC8 applies to both properties. ⟦s17|In addition, under these modes
`QuiescentNameAligned` with a registered environment place that the net declares is `Unknown`, and
where no earlier refusal of the refusal order below applies, nor an earlier rule of its step 5, the
reason names the first such place in code-point order and points to `Arrivals` ([VER-006]); the
vacuity reading of [VER-006] AC6 does not apply to it.⟧ Route B keeps
an environment place inexhaustible and never consumes it. A net that reads input from one (say, a
keystroke stream into `first` and `retire`) therefore has no resting class in the graph, and the
vacuity reading would turn any graph of it that closes into `Proven`, even on a misaligned net,
while the executor rests misaligned between keystrokes. On the worked example the graph does not
close at all (each keystroke mints a name that can wait in `inflightB`), so the verdict would be a
truncation `Unknown`; the rule makes the reason name the environment place instead. Under `Arrivals` the
net has no environment places left ([VER-006]); the decline of [VER-006] AC10 for an arrival into
a coloured place still applies.

**Refusal order.** ⟦s18|A call can meet several of these refusals at once.⟧ ⟦s19|Its verdict is `Unknown` with
the reason of the first that applies, in this order, so every implementation names the same place:⟧

1. ⟦s20|The refusals that precede every route for every property, in this order: a call cancelled or
   out of total budget before it starts ([VER-013]); a place of `S` that the net does not declare
   and the initial marking does not mark ([VER-003] AC5), naming the first such place of `S`; a
   `Bounded(k)` environment outside its premises ([VER-006] AC3); the in-flight refusal of
   [VER-004].⟧
2. ⟦s21|The net is outside the fragment of the mode even when every transition counts as a mint: the
   fragment decline of the mode, under EXTENDED the note of **EXTENDED** above, under BASE a decline
   that names EXTENDED.⟧
3. ⟦s22|Under `Arrivals(k)` or `Arrivals(min, max)`, an arrival into a coloured place ([VER-006] AC10),
   naming the first such place in the order the environment places were registered.⟧
4. ⟦s23|The net is outside the fragment only because a transition writes a coloured place without
   consuming one and is not a declared mint: the decline names those transitions in declaration
   order ([NU-010]).⟧
5. ⟦s24|Under `AlwaysAvailable` or `Bounded(k)`, an environment place Route B cannot model ([VER-006]
   AC8). The rules run in this order, each over the environment places the net declares in
   code-point order of names: one that is coloured; one that an inhibitor arc tests (naming the
   first such transition in code-point order); where conflict priority is in effect ([NU-052]), one
   that two or more transitions consume; then, for `QuiescentNameAligned`, the first of them (**Modelled
   injection** above), and for `NameAligned`, the first that is in `S`.⟧
6. ⟦s25|The first place of `S`, in the order of `S`, that is not coloured. Under BASE the reason also
   names EXTENDED.⟧
7. ⟦s26|A coloured place the initial marking marks: the first in code-point order of place names.⟧

⟦s27|Steps 3 and 5 apply whether or not the coloured places start empty.⟧ A declared mint or carrier that is not in the net is the caller's
error and is reported as [NU-010] and [NU-051] say, outside this order. The `Ignore` downgrade of a
`Proven` ([VER-006]) and a truncation `Unknown` are not refusals: they follow a graph that was
built.

⟦s28|*If* a name-alignment call meets a refusal of step 1 of the refusal order, *then* the verifier *shall* answer `Unknown` with the reason of the first refusal of step 1 that applies, in the order step 1 lists them, naming for an absent place the first place of `S` that the net does not declare and the initial marking does not mark.⟧

⟦s29|*If* no refusal of step 1 applies and the net is outside the fragment of the mode even when every transition counts as a mint, *then* the verifier *shall* answer `Unknown` with the fragment decline of the mode, whose reason names EXTENDED under BASE.⟧

⟦s30|*If* no refusal of steps 1 and 2 applies and, under `Arrivals(k)` or `Arrivals(min, max)`, an arrival feeds a coloured place, *then* the verifier *shall* answer `Unknown` naming the first such place in the order the environment places were registered.⟧

⟦s31|*If* no refusal of steps 1 to 3 applies and transitions write a coloured place without consuming one and are not declared mints, *then* the verifier *shall* answer `Unknown` naming those transitions in declaration order.⟧

⟦s32|*If* no refusal of steps 1 to 4 applies and, under `AlwaysAvailable` or `Bounded(k)`, a rule of step 5 applies, *then* the verifier *shall* answer `Unknown` naming the first environment place, in code-point order, that the first applicable rule finds, and for an inhibitor arc also the first transition in code-point order that tests it.⟧

⟦s33|*If* no refusal of steps 1 to 5 applies and a place of `S` is not coloured, *then* the verifier *shall* answer `Unknown` naming the first such place in the order of `S`, and under BASE the reason *shall* also name EXTENDED.⟧

⟦s34|*If* no refusal of steps 1 to 6 applies and the initial marking marks a coloured place, *then* the verifier *shall* answer `Unknown` naming the first marked coloured place in code-point order of place names.⟧

⟦s35|*If* no step of the refusal order applies, *then* the verifier *shall not* refuse the call with a refusal of that order: unless the call is the caller's error of a declared mint or carrier that is not in the net, or a later poll sees a stop ([VER-013]), Route B builds the graph, and the verdict is the one it reads off that graph.⟧

**Truncation.** ⟦s36|A graph that does not close within the class bound never yields `Proven` (Lean
`Decide.truncated_never_proven`).⟧ ⟦s37|The prefix rule of [VER-012] AC3 applies: a `NameAligned`
violated by a stored class, or a `QuiescentNameAligned` violated by an expanded class at which the
net rests (every firing out of it is of a reapable transition; with nothing reapable, an expanded
class with no successor, Lean `Decide.quiescentAt`), is `Violated` with the shortest witness in
the explored graph and a report line naming the truncation; otherwise the verdict is `Unknown`.⟧

⟦s38|*If* the graph does not close, because the build reaches the class bound, runs out of total budget or is cancelled ([VER-013]), *then* Route B *shall not* answer `Proven` for either property.⟧

⟦s39|*If* the graph does not close and the prefix rule finds no violation, *then* Route B *shall* answer `Unknown`.⟧

**Violated.** A counterexample is reported as every Route B counterexample is ([VER-003],
[VER-012]): the shortest path in the name-partition graph from the initial class to a violating
class, attributed to Route B, with `counterexampleConfirmed` absent (the trace is a path of the
graph, not of the flat abstract semantics) and `counterexampleTiming` set by [VER-003]. The graph
expands every base-enabled firing and lets a coloured consumer take any resident name, where the
executor takes the oldest token ([EXEC-010]); a run of the net follows the trace when the executor's
order meets the graph's choice.

⟦s40|*If* Route B answers `Violated` for either property, *then* the class its counterexample ends at *shall* violate the property.⟧

**Soundness.** ⟦s41|Lean `Novel/RouteB/Aligned.lean` (`routeB_untimed_nameAligned_sound`,
`routeB_untimed_quiescentNameAligned_sound`) proves: for the **untimed, environment-free executor
with atomic firings**, a `Proven` of either property holds in every marking that executor reaches
(for the quiescent form, every marking at which it rests): the tokens in the places of `S` all
carry the same name.⟧ The premises are:

- the coloured places start empty;
- the mints and coloured consumers keep their contracts ([NU-010], [NU-051], [NU-054]);
- the projection contract of [NU-050]: every match-key and relay projection reads one name per
  token, the name its writer gave it, agreeing across keys and relays and never returning no name
  (Lean `Exec.ProjCoherent`, built into the model, checked by no implementation);
- every firing writes one token to each output place its branch names ([IO-016] AC4). A mint or
  relay that writes two tokens carrying different names into `box` is exactly the kind of firing
  that would falsify a `Proven` alignment;
- every place of `S` coloured, which the refusal above enforces;
- the conditions the classifier establishes (`InFragment`), unguarded inputs, and, for the
  quiescent form, join keys that consume at least one token (`PosKeys`).

⟦s42|*If* the premises above hold, *then* Route B *shall* answer `Proven` for `NameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking the untimed, environment-free executor with atomic firings reaches.⟧

⟦s43|*If* the premises above hold, *then* Route B *shall* answer `Proven` for `QuiescentNameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking that the untimed, environment-free executor with atomic firings reaches and rests at, resting being read with the reapable set of the call ([VER-002]).⟧

The proof reads the predicate on the executor's name view (`alignedAll_view_iff`) and shows that an
uncoloured place of `S` adds nothing to it (`alignedAll_uncoloured`), which is why that case is not
allowed to prove. Order and repeats in `S` do not change it (`alignedAll_congr_mem`).
Conflict-only priority ([NU-052]) applies as it does to every Route B property.

The proof does not cover what the shipped Route B computes on every net. Route B builds the timed
name × time graph (with the latest bounds dropped as [VER-002] requires), and its agreement with a
timed executor is not proved (gap R6 of `Novel/RouteB/Sound.lean`). This includes the all-immediate
worked example below. The Lean model also has no in-flight state. Informally, and not proved: the
predicate stays true when tokens are removed, and on a net without inhibitor, reset or drain arcs
a marking with actions in flight holds a subset of the tokens of a marking that an atomic run of
the graph's semantics reaches, where a coloured consumer may take any resident name. A FIFO atomic
run does not always reach one: on the buggy variant below, with `fetchA` and `fetchB` both in
flight, `staged` can hold the second name while `listEmpty` is still marked. So the in-flight
markings are covered by the graph for `NameAligned`, not by the atomic executor.

**Worked example (search as you type).** Uncoloured places `typed` (2 tokens, two keystrokes),
`idle` (1), `armedA`, `armedB`, `clr`, `ready`, `listEmpty` (1), `slot` (1); coloured places `box`,
`inflightA`, `inflightB`, `reply`, `staged`, `list`, all empty at the start. Under EXTENDED, with
`sendA` and `sendB` declared mints and `inflightA`, `inflightB`, `list` declared carriers:

| Transition | Firing | Role |
|---|---|---|
| `first` | `idle, typed → armedA` | ordinary |
| `retire` | `box(n), typed → armedB` | coloured consumer, drain |
| `sendA` | `armedA → box(n'), inflightA(n')` | declared mint (first query) |
| `sendB` | `armedB → box(n'), inflightB(n')` | declared mint (follow-up query) |
| `fetchA` | `inflightA(n) → reply(n)` | coloured consumer, relay (the action calls the API) |
| `fetchB` | `inflightB(n) → reply(n)` | coloured consumer, relay (the action calls the API) |
| `apply` | `match(reply, box), slot → box, staged, clr` | ν-join relaying to `box` (its own key) and `staged` |
| `clearNone` | `listEmpty, clr → ready` | ordinary, before the first result |
| `clear` | `list(m), clr → ready` | coloured consumer, drain |
| `show` | `staged(n), ready → list(n), slot` | coloured consumer, relay |

Each query has its own fetch transition, so with an API call that answers asynchronously the two
requests are in flight at once on every executor, whether or not it starts a transition again while
an earlier firing of it is in flight ([CONC-002]), and replies land in `reply` in the order the
actions answer. A stale reply stays in `reply`: `apply` is name-disabled for it once `retire` has
taken its name out of `box`. `box`, `staged`, `list`, `inflightA` and `inflightB` never hold more
than one token (`slot` bounds `staged` and `list`; `idle` and the two keystrokes bound the rest),
so the graph's free choice of a resident name coincides with the executor's FIFO order on them;
only `reply` can hold a stale reply beside the current one. The net is closed: `typed` holds exactly two keystrokes, and the verdicts below are about that net, not
about an unbounded keystroke stream (for one, see "Modelled injection" above). The net rests only
after both keystrokes are consumed (`retire` stays enabled while `typed` and `box` are non-empty),
so the quiescent verdicts speak about markings where all input has been typed and processed. The
results:

- `QuiescentNameAligned(box, list)` is `Proven`: at rest, the list shows the results of the query in
  the box.
- `NameAligned(box, list)` is `Violated` with a shortest witness of 8 firings: after the second
  keystroke the box holds the new name while the list still shows the old results. Only the
  quiescent form holds.
- `QuiescentCount({list}, 1, 1)` ([VER-002]) is `Proven`: at rest, exactly one result is shown.

The buggy variant replaces `apply` with `apply_bug: reply(n), slot → staged, clr`, a coloured
consumer relay with no match on `box` (`box`, `inflightA`, `inflightB`, `reply`, `staged`,
`list` declared carriers, `sendA` and `sendB` declared mints). `QuiescentNameAligned(box, list)`
is `Violated` with a shortest witness of 12 firings in which the reply to the first keystroke is
applied last and the list ends on the old results while `box` holds the new name. Every executor
takes that run when both fetch actions are in flight and `fetchA`'s action answers after
`fetchB`'s: `apply_bug` takes the oldest reply, which is then the reply to the second keystroke. The reported trace is one linearisation of that
run; where it lists both replies resident in `reply`, the executor realises the same firings with
`fetchB` answering first. With actions that complete synchronously the replies arrive in mint order
and the bug does not occur, which is why the verdict is about the net and not about one schedule.

**Acceptance Criteria:**
1. (MUST, where offered) On the search-as-you-type net under EXTENDED, `QuiescentNameAligned(box,
   list)` and `QuiescentCount({list}, 1, 1)` are `Proven` and `NameAligned(box, list)` is
   `Violated` with an 8-firing witness; on the buggy variant `QuiescentNameAligned(box, list)` is
   `Violated` with a 12-firing witness. Every verdict is attributed to Route B.
2. (MUST, where offered) On the same net, a property naming an uncoloured place
   (`QuiescentNameAligned(box, ready)`) or a place absent from the net (`QuiescentNameAligned(box,
   nope)`) is `Unknown` with a reason naming the place, never `Proven`. With two uncoloured places the reason names the first in
   `S`: `QuiescentNameAligned(box, ready, clr)` names `ready`.
3. (MUST, where offered) Under BASE the same net is `Unknown` for `QuiescentNameAligned(box, list)`:
   the coloured set is the match keys `reply` and `box`, `fetchA` and `fetchB` write `reply`
   without being mints, `retire` consumes `box` without a match, and `apply` produces its key
   `box`, so the net is outside the BASE fragment; the reason names EXTENDED and the report names the ignored relay
   declarations ([NU-054] AC5).
4. (MUST, where offered) No route other than Route B, listed above, decides either property: called
   directly, each returns no verdict or `Unknown` with the reason that only Route B decides them,
   and the script encoders return no script; a Route B truncation stays `Unknown` unless the
   prefix rule finds a violation.
5. (MUST, where offered) The predicate is invariant under name permutation: evaluated on a class and
   on that class with its name-symbols permuted, it gives the same answer, and running the
   search-as-you-type net with names minted in another scope ([NU-010]) changes no verdict. It is
   also invariant under reordering `S`.
6. (MUST, where offered) With `typed` registered as an environment place under `AlwaysAvailable`
   (and not in the initial marking), `QuiescentNameAligned(box, list)` is `Unknown` with a reason
   naming `typed`, on the fixed net and on the buggy variant; it is never `Proven`. A call whose
   initial marking holds a token in a coloured place is `Unknown`, with a reason naming the place
   where no earlier refusal of the refusal order applies: on the same net,
   `QuiescentNameAligned(box, list)` with `box` marked names `box`.
7. (MUST, where offered) `S` is a list. On the search-as-you-type net,
   `QuiescentNameAligned(box, staged, list)` and the singleton `NameAligned(list)` are `Proven`;
   `QuiescentNameAligned(box, list, reply)` is `Violated` with a 9-firing witness (a stale reply
   rests in `reply`), and `NameAligned(reply)` with a 6-firing witness (both replies resident). With
   `typed` marked with 3, `QuiescentNameAligned(reply, staged)` is `Violated` with a 12-firing
   witness: the net rests with two stale replies in `reply` and `staged` empty, a marking that
   the cross pair of `reply` and `staged`, without the self pairs, would accept. An empty `S` is rejected at construction, a
   repeated place counts once, at its first occurrence, and the descriptions of one, two and three
   places read as the API notes below give them.
8. (MUST, where offered) Refusals follow the refusal order. On the search-as-you-type net under
   EXTENDED: with `box` marked, `QuiescentNameAligned(box, ready)` names `ready` (an uncoloured
   place before a marked one); with `list` and `inflightB` marked, `QuiescentNameAligned(list, box)`
   names `inflightB` (the marked coloured places in code-point order, not in the order of `S` or of
   the marking); with `typed` registered as in AC6 and `box` marked, `QuiescentNameAligned(box,
   list)` names `typed` (an environment place before a marked coloured place).

**Depends on:** [VER-002], [VER-003], [VER-006], [VER-012], [NU-010], [NU-050], [NU-051], [NU-054]
**Test derivation:** the fixtures of `spec/verification-fixtures/nu-aligned-fixtures.json`, run in
every language: the four search-as-you-type verdicts of AC1, the uncoloured places of AC2, the BASE
run of AC3, the environment and marked-coloured-place runs of AC6, the list verdicts of AC7 and the
refusal-order runs of AC8, each asserting that the report names Route B or, for `Unknown`, that the
reason contains the fixture's `reasonContains`. AC4 by sending the AC1 fixed net to each other
route directly, as an in-module unit test, and by the budget fixture, which must still reach
Route B. AC5 as a unit test on the
predicate (with `S` permuted) and a run with a non-default minting scope. The construction rules and
descriptions of AC7 as unit tests.

**Implementation notes (API):** the properties sit beside `JoinedOrDeadLettered` and
`QuiescentCount`.

- Java: `SmtProperty.nameAligned(first, rest...)` and `SmtProperty.nameAligned(places)` for a
  collection, likewise `quiescentNameAligned`; records `NameAligned(List<Place<?>> places)` and
  `QuiescentNameAligned(List<Place<?>> places)`, whose constructors copy, deduplicate and reject an
  empty list. A new permitted record of the sealed `SmtProperty` breaks exhaustive switches, so it
  ships in a major release.
- TypeScript: `nameAligned(...places)` and `quiescentNameAligned(...places)`, typed to take at
  least one place, members of the `SmtProperty` union with `type: 'name-aligned'` and
  `type: 'quiescent-name-aligned'` and the field `places`.
- Rust: `SmtProperty::NameAligned { places: Vec<String> }` and
  `SmtProperty::QuiescentNameAligned { places }`, with constructors
  `SmtProperty::name_aligned(places)` and `SmtProperty::quiescent_name_aligned(places)` over any
  iterable of names, which panic on an empty one. A new variant of the exhaustive enum is a major
  change.
- Python: `name_aligned(places)` and `quiescent_name_aligned(places)` in `libpetri.verification`,
  over an iterable of places, raising `ValueError` on an empty one, through the Rust verifier, also
  re-exported from `libpetri`, as `joined_or_dead_lettered` and `quiescent_count` are.
- Every language describes them byte for byte on the report's `Property:` line as
  `Name alignment of ` and `Quiescent name alignment of ` followed by the names of the places of
  `S` after deduplication, in order, separated by `, ` except that ` and ` separates the last two:
  `Name alignment of box`, `Name alignment of box and list`, `Name alignment of a, b and c`, and
  `Quiescent name alignment of a, b and c` likewise."#
