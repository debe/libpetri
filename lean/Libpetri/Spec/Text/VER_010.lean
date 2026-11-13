import Libpetri.Spec.Text

requirement_text VER_010
  id "VER-010"
  title "State Class Graph Analysis"
  priority MAY
  kind B
  body r#"The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

An implementation that offers the graph is bound by the sentences below. ⟦s1|In them a timed run of the net starts at an initial marking with every clock at zero, on a net in which no transition's earliest firing time is below zero or above its latest, and follows the Time Petri net semantics: time may pass only as far as no enabled transition goes past its latest firing time, a transition fires no earlier than its earliest firing time and deposits its outputs at the instant it fires, and a clock is kept or restarted by the persistence rule below.⟧ ⟦s2|A class holds a state when the class's marking is the state's marking and its firing domain holds every combination of firing times the state allows the class's clocks.⟧ ⟦s3|A class is well formed when its clocks are the transitions enabled in its marking and its firing domain has the form letting time pass leaves: the closure of a matrix with a finite reference bound in which every clock's lower bound is zero.⟧ For a well-formed class that holds a state, the class's clocks are the state's enabled transitions.

⟦s4|*When* a timed run of the net reaches a state, the state class graph *shall* hold a class, reachable from its initial class, that holds the state.⟧

⟦s5|Every class the state class graph reaches from its initial class *shall* be well formed and *shall* list its clocks once each, in ascending order of transition name compared by Unicode code point ([VER-013]).⟧

⟦s6|*When* a transition can fire with one of its outcomes ([VER-001]) from a state in which no enabled transition is past its latest firing time, and a well-formed class holds that state, the state class graph *shall* give that class a successor, labelled with the transition's name and the outcome's index, that holds the state the firing leaves.⟧

⟦s7|Every successor of a class *shall* be labelled with the name of a transition among the class's clocks and the index of one of that transition's outcomes, and *shall* have the marking that firing the transition with that outcome leaves: each input place less the `consumptionCount(available)` of [IO-007], so an `All` or `AtLeast` input empties its place, each reset place emptied, and the outcome's tokens added.⟧

⟦s8|*When* a transition `t` fires from marking `M` into marking `M'`, the successor step of the state class graph *shall* keep the clock of a transition `t'` enabled in `M` exactly when `t'` is not `t` and is enabled both in `M'` and in the intermediate marking `M - Pre(t)`, which has the inputs of `t` consumed, its reset places drained and none of its outputs deposited.⟧

⟦s9|The canonical order of the state class graph *shall* either keep a list of transitions or return a permutation of its positions, and *shall* leave every list it is given in ascending order of transition name, compared by Unicode code point ([VER-013]).⟧

⟦s10|*If* the transition names of the net are unique, *then* the class key of the state class graph *shall* give two classes, each with the transitions enabled in its marking as clocks, once each in that order, and a canonical firing domain (closed, zero on the diagonal, every clock with a finite lower bound), the same key exactly when they have the same marking and their firing domains hold the same firing times.⟧

When every bound of the net is a whole number of milliseconds, the successor step of [VER-011] leaves every firing domain canonical, so two classes that step builds on a net with unique names are one exactly when they have the same marking and the same firing domain, whatever interleavings reached them. A net may give two transitions one name ([CORE-021]); the key sentence does not reach such a net, since an order by name cannot tell two enabling orders of one name apart. These sentences speak of the successor's soundness: a class holds every state the firing rule allows. That a class holds no state a timed run cannot reach is the exact half of the successor, not stated here, and so is the exact half of the fresh interval a newly enabled clock gets.

**Acceptance Criteria:**
1. State class graph enumerates reachable (marking, timing zone) pairs. A class's identity is
   its marking and its **full** firing domain, independent of the order in which its
   transitions became enabled: the successor step lays clocks out persistent-then-newly-
   enabled, which is path-dependent, so implementations MUST put every class's clocks in one
   canonical order (ascending transition name, in the code-point order of [VER-013]) and key
   on the complete difference-bound matrix ([VER-011]), not on the per-clock projections
   alone. Two arrivals at the same marking and zone by different interleavings are one class;
   two zones that agree on every projection but differ in a difference constraint are two. On
   an untimed workflow net the order-sensitive key inflated the class count 1.5× (one marking
   held by fourteen classes); the projection-only key merges classes whose successors differ,
   which can lose a reachable marking.
2. Successor computation correctly handles transition firing and clock updates. The
   number of tokens a firing removes from each input place MUST be the canonical
   `consumptionCount(available)` of [IO-007] — the same function the executor uses —
   and not the enablement threshold `requiredCount()`. In particular `All` and
   `AtLeast(m)` drain the place.
3. Every outcome of a transition, each XOR branch and a timeout outcome that deposits
   differently from every branch, is expanded into a virtual transition of its own
   ([VER-001]), and a successor is labelled with the fired transition's name and the
   outcome's index, counting the outcomes in the order in which [VER-001] numbers the
   `_b<i>` virtual transitions: the branches in enumeration order, then the timeout outcome.
4. Clock persistence uses the intermediate marking of Berthomieu and Diaz. After `t` fires
   from marking `M`, a transition `t' ≠ t` keeps its clock only if it is enabled in `M`, in
   the successor marking `M'`, and in the intermediate marking `M - Pre(t)`: inputs
   consumed, reset places drained, outputs not yet deposited. Every other transition
   enabled in `M'` gets a fresh firing interval. This is the executor's rule ([TIME-012])
   for an on-time executor with atomic firings, one that reaps no transition, fires none
   after its latest bound, and gives an action no duration, the assumptions [VER-023] lists;
   the enablement recheck of a firing pass ([EXEC-003] AC3) is part of atomic firings.
   A successor that keeps a clock the executor restarts under-approximates the executor's
   behaviors. A transition outside the in-flight split of [VER-004] fires atomically and
   takes no time (a split one completes through its immediate completion step at any later
   time). Under `alwaysAvailable` an environment input never disables a transition, and under
   `bounded(k)` only one that demands more than `k` tokens does, permanently ([VER-006] AC3).
5. The graph builder (`StateClassGraph.build` in every language) builds the graph of the net it
   is given and does not apply the in-flight split itself. A caller that builds the graph
   directly, outside `SmtVerifier`, MUST apply the split first (`splitInFlight` in TypeScript,
   `in_flight::split_in_flight` in Rust, `InFlight.split` in Java) to get the executor's
   two-step firing ([VER-004]); when the split is refused, no graph of this kind is faithful to
   the executor. The builder's documentation MUST say so.

**Depends on:** [IO-007], [EXEC-010], [TIME-012], [TIME-013], [VER-001], [VER-004], [VER-011],
[VER-013]

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `state_class_graph`)

**Test derivation:** Small timed net; construct state class graph; verify reachable
classes match expected. Regression: a transition with an `all(p)` input followed by a
transition inhibited on `p` — the inhibited successor MUST be reachable, since `p` is
drained; an `atLeast(2, p)` input over 5 tokens MUST leave `p` empty. For AC4, a timer
place `p` feeds a delayed transition `d`, and a refresh transition consumes `p` and deposits
into it again: `d` MUST be newly enabled in the successor class. With a second token in
`p` it MUST be persistent; with a reset arc on `p` it MUST be newly enabled."#
