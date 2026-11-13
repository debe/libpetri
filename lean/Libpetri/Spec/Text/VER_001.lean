import Libpetri.Spec.Text

requirement_text VER_001
  id "VER-001"
  title "SMT Verification Pipeline"
  priority SHOULD
  kind F
  body r#"The engine supports safety property verification using SMT solvers via the IC3/PDR (Property Directed Reachability) algorithm. The implementation notes list the phases of the SMT route; their order describes the implementations and is not a requirement.

**Undeclared marked places are inert places.** An initial marking MAY put tokens on a place the
net does not declare; the executor retains them, inert ([CORE-072] AC3). Verification models the
same net the executor runs, so every place the initial marking marks that the net does not
declare is added to the verified net as a place with **no arcs**, after the declared places, in
the order the marking lists them, so the place order is deterministic. Such a place keeps its
tokens forever: `DeadlockFree` counts it as stranded unless it is a declared sink, `PlaceBound`
counts its tokens, and it is its own trivial P-invariant. The rule applies before any route runs,
so every route sees the same net: the enumeration route ([VER-017]), Route B and the ν name layer
([VER-012]), Route A ([NU-053]), the structural checks ([VER-020]), the linear bound ([VER-015]),
the state equation ([VER-018]), the encoders and `encodeScripts()` ([VER-013]), open-net closure
([VER-022]), the environment rewrites ([VER-006]), the terminal rewrite ([EXEC-042]) and the
state-space cache key ([VER-017]). A net whose initial marking marks only declared places is
unaffected, byte for byte.

⟦s1|*When* the verifier verifies a net from an initial marking, it *shall* verify the net whose places are the declared places followed by every place the initial marking marks that the net does not declare, in the order the marking lists them, and whose transitions are the net's own, with no arc added.⟧

**Places are identified by name.** Verification identifies a place by its name, in every
implementation. An environment place ([VER-006]), a sink or conditional sink ([VER-002],
[VER-014]), a budget or carrier place ([NU-040], [NU-051]), a place a property names, a terminal
([EXEC-042]), a match key or relay target ([NU-020], [NU-054]) and a subnet port ([MOD-051])
each denote the net's place of that name, whichever object or value the caller used to name it.
In TypeScript, where `place('p')` called twice gives two objects of one place ([MOD-024]), no
route and no analysis may test membership by object identity: an environment place registered
through one object and named on an arc through another is still an environment place. Java's
place equality also compares the token type ([CORE-002]); a Java net whose places have distinct
names gets the same answer either way.

**Timeout outcomes are virtual transitions.** The verifier expands a transition into one virtual
transition per way a firing can end: each output branch the action may write ([IO-016], one
token per place), in enumeration order, then the **timeout outcome** when the spec has a
`Timeout` and that outcome deposits differently from every branch. The timeout outcome is
what the executor deposits when the timeout fires ([IO-013] AC5, [IO-014]): the timeout
child's places only, one minted token each, and for a `ForwardInput(from, to)` one token in
`to` per token consumed from `from`, which is the required count of a `One` / `Exactly(n)` input.
Every analysis that fires a transition whose `Timeout` forwards no `All` / `AtLeast` input reads
this one expansion: the flattener behind the
encoders, the linear bound ([VER-015]), the state equation ([VER-016], [VER-018]), the firing
bound ([VER-019]), the bounded witness phase ([VER-025]), the enumeration route ([VER-017]),
Route B and the ν fragment ([VER-012]), the name-coloured encoder ([NU-053]) and open-net
closure ([VER-022]). A virtual transition is
named after its transition alone when there is one, and `<t>_b<i>` when there are several. A
forward from an `All` / `AtLeast` input deposits the drained batch, which depends on the
marking the firing drains: a **transfer**. The graph routes fire each class's marking, so
they count the drained batch exactly as the executor does: the enumeration route
([VER-017]), the timed state-class graph ([VER-010]) and Route B ([VER-012]) decide such a
net. No post vector holds it, so every route that reads the flat net (the structural
pre-check ([VER-020]), the P-invariants ([VER-005]), the linear bound ([VER-015]), the state
equation ([VER-016], [VER-018]), the firing bound ([VER-019]), the bounded witness phase
([VER-025]), the fixpoint query and Route A ([NU-053])) refuses it with `Unknown`. The refusal
sits after the graph routes and before the first linear one, so no exit of the pipeline bypasses it ([VER-003] AC5).

⟦s2|*When* the verifier expands a transition that has an output spec and no `Timeout` that forwards an `All` or `AtLeast` input, it *shall* produce one virtual transition per output branch the action may write, in enumeration order, then one virtual transition for the timeout outcome when the spec has a `Timeout` and that outcome deposits differently from every branch.⟧

⟦s3|The verifier *shall* expand a transition with no output spec into one virtual transition that deposits nothing.⟧

⟦s4|The virtual transition of the timeout outcome *shall* deposit one token in each place the `Timeout` child names through `Place` and, for each `ForwardInput(from, to)` of the child, as many tokens in `to` as the required count of the input on `from`.⟧

⟦s5|The verifier *shall* name a virtual transition `<t>` when its transition `t` has one virtual transition, and `<t>_b<i>` when it is the `i`-th of several, counting from 0.⟧

⟦s6|*If* the `Timeout` of a transition forwards an `All` or `AtLeast` input, *then* no route *shall* read an expansion of that transition into virtual transitions.⟧

**Acceptance Criteria:**
1. Pipeline accepts a net, initial marking, and property.
2. Returns a verdict (Proven, Violated, or Unknown) with supporting evidence.
3. **Inert undeclared places.** For the net `t: c → d` with sink `d` and initial marking
   `{a: 1}`, where `a` is on no arc and not declared, `DeadlockFree` is `Violated` at every
   enumeration budget (0, 1 and the default), whichever route decides it, and
   `PlaceBound(a, 0)` is `Violated`. The verdict does not depend on the class budget or the
   route. The same net with no token on `a` gets the verdict and the scripts it got before.
4. **Timeout forwards deposit per consumed token.** For `t: exactly(2, a) → xor(c,
   timeout(50, forwardInput(a, b)))` from `{a: 2}`, the flat net has three virtual transitions
   `t_b0` (post `c`), `t_b1` (post `b`) and `t_b2` (post `2·b`). The linear bound ([VER-015])
   reads the same three virtual transitions and does not prove `PlaceBound(b, 1)`, which is
   `Violated` with a one-step trace ending at `{b: 2}` on the state-equation phase ([VER-018]),
   the fixpoint query and the enumeration route ([VER-017]).
   A spec whose timeout outcome equals one of its branches gets the virtual transitions, and
   the scripts, it got before.
5. **Drained forwards are decided by the graphs and refused by the linear routes.** The same
   net with `all(a)` or `atLeast(1, a)` in place of `exactly(2, a)`, from `{a: 2}`: at the
   default enumeration budget the enumeration route decides it: `PlaceBound(b, 1)` is
   `Violated` with a one-step trace ending at `{b: 2}` and `PlaceBound(b, 2)` is `Proven`.
   With the enumeration off (budget 0) it is `Unknown`, with route `Unavailable`, with the
   reason `transition 't' forwards its All/AtLeast input 'a' to 'b' on timeout, which
   deposits one token per token drained (IO-014), a marking-dependent count the flat
   encodings cannot express; refusing to certify on the linear routes (the state-space
   graphs decide it exactly: VER-017 enumeration, Route B)`.

**Implementation notes:**
- The SMT route runs these phases in this order. Route B ([VER-012]), the linear bound when the
  enumeration route applies ([VER-015]), the enumeration route ([VER-017]) and the refusal of a
  drained forward run before them.
  1. **Flatten XOR**: expand each transition into its virtual transitions
  2. **Structural pre-check**: the siphon/trap check ([VER-020])
  3. **P-invariant computation**: derive place invariants from the incidence matrix ([VER-005])
  4. **Pre-fixpoint phases**: the linear bound ([VER-015]), the state-equation phase ([VER-018]),
     the firing-bound phase ([VER-019]) and, on the flat encoding, the bounded witness phase
     ([VER-025]), each of which can decide the property before the fixpoint query
  5. **SMT encoding**: encode the Petri net as CHC (Constrained Horn Clauses)
  6. **IC3 query**: invoke the Z3 Spacer engine for reachability analysis
  7. **Decode result**: extract verdict, counterexample, or inductive invariant
- All implementations: full pipeline; the CHC system is emitted as SMT-LIB2 text and solved by
  the `z3` executable with `fp.engine=spacer` through the one solver transport of [VER-013].
- Rust: behind the `z3` feature. Python exposes the Rust pipeline via the PyO3 binding (wheel
  built with the `z3` feature).

**Depends on:** [CORE-072]
**Test derivation:** Simple mutual exclusion net; verify Proven verdict for mutual exclusion property. The AC3 net at enumeration budgets 0, 1 and the default, plus `PlaceBound(a, 0)`, and the same net without the stray token. The AC4 net on every route, and its flattened rows; the AC5 nets at budget 0 (refused) and the default (decided both ways)."#
