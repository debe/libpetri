import Libpetri.Spec.Text

requirement_text IO_015
  id "IO-015"
  title "Output Validation"
  priority MUST
  kind F
  body r#"*When* an action completes, an executor with output validation enabled, which is the default
([CONC-026]), *shall* validate its produced set against the transition's output spec. The **produced set** is the places that received at least one
token.

Validation is an **exact-explanation search**. ⟦s1|An *assignment* selects exactly one child
at each `Xor` node it reaches; nodes beneath an unselected `Xor` child are never
evaluated.⟧ Each assignment *claims* a set of places:

- **Place** — claims that place.
- **ForwardInput** — claims `to`.
- **And** — claims the union of every child's claim. `And` is an **unordered** conjunction:
  its children are a set of obligations, not a sequence, and a verdict MUST NOT depend on
  the order they are declared in.
- **Xor** — claims the selected child's claim.
- **Timeout** — claims its child's claim.

⟦s2|Claims are compared with the produced set on the places the output spec names.⟧ ⟦s3|A token in a place the output spec never names takes no part in validation: a transition context never produces to such a place ([CORE-063]), and a token that bypasses the context is [CORE-072]'s subject, not an [IO-015] violation.⟧

⟦s4|*If* exactly one assignment claims a set *equal* to the produced set, *then* validation
*shall* succeed.⟧ ⟦s5|*If* no assignment claims a set equal to the produced set, *then*
validation *shall* fail, because nothing explains what was written.⟧ ⟦s6|*If* two or more
assignments claim a set equal to the produced set, *then* validation *shall* fail, because
the write is genuinely ambiguous.⟧ ⟦s7|For a transition that builds, no two assignments claim the
same set ([IO-012]), so on a firing this third case does not arise.⟧

⟦s8|The comparison is over **sets of places**: a spec names places, not counts, so an action
that deposits several tokens into one claimed place conforms.⟧ Every analysis that enumerates
branches models one token per claimed place ([IO-016]), so such a firing does more than the
analyses explore; the executor reports it ([IO-016] AC4) rather than reject it.

Equality rather than containment is what makes a token written to a declared place
*outside* the selected branch a violation, instead of being silently deposited.

No subsumption rule is needed: `Xor(And(A, B, C), And(A, B))` with A, B and C produced has
exactly one *exact* assignment, because `And(A, B)` claims only `{A, B}`.

*Implementation note (non-normative).* This check runs on every firing of an executor with
output validation enabled ([CONC-026]). A partial claim
that already contains a place outside the produced set can never extend to an exact match,
so pruning there keeps the search linear whenever `Xor` branches are distinguishable by
what was produced; the search need not continue once two exact assignments are found. The
exponential worst case requires several `Xor` children to be simultaneously consistent with
the produced set, which is the ambiguous case that [IO-012] rejects when the transition is built.

Validation failure is treated as a transition failure (error event emitted, tokens not restored).

The *built-in* passthrough ([CORE-051]) never reaches this check: a net pairing it with a
declared output spec is rejected earlier ([CORE-043]). What remains here is the case no
static check can decide — a hand-written action that produces nothing, or produces only on
some paths — which is validated per firing.

**Mid-action publication.** An implementation MAY offer a streaming primitive that
publishes buffered output before the action returns (Rust and Python expose
`ctx.flush()`; Java and TypeScript have no equivalent). Such a primitive is an explicit
atomicity boundary and interacts with this requirement in two ways, both of which an
implementation offering it MUST honour:

1. Places written by a published batch **count towards satisfying the spec**. They left
   the completion's output set, but they were produced, so omitting them would reject
   conforming firings.
2. Published tokens are **already in the marking** and are NOT withdrawn when validation
   later rejects the firing. A violating firing therefore deposits nothing *further*, but
   it does not roll back what was already published — the same guarantee the primitive
   gives for an action that fails outright.

An action that needs all-or-nothing output must not publish mid-action.

**Acceptance Criteria:**
1. Conforming output → success.
2. Non-conforming output → failure event emitted.
3. Consumed input tokens are NOT restored on failure.
4. Zero exact assignments → violation; two or more exact assignments → violation.
5. `Xor(And(A, B, C), And(A, B))` with A, B, C produced → success, because exactly one
   assignment claims exactly `{A, B, C}`. No subsumption rule is involved.
6. A transition declaring an output spec but bound to a hand-written action that produces nothing → validation failure on every firing (the built-in passthrough case is [CORE-043]'s, rejected before execution).
7. Where mid-action publication exists: an action that publishes to `A` then returns having also written `B`, against `And(A, B)` → success. An action that publishes to `A` then returns without writing `B` → violation, and the published `A` token remains in the marking.
8. **`And` is unordered.** Permuting the children of any `And` yields the same verdict for
   the same produced set. In particular `And(A, Xor(D, E))` and `And(Xor(D, E), A)` agree on
   every produced set, including the empty one.
9. **A write outside the selected branch is a violation.** `Xor(And(A, C), B)` with B and C
   produced → violation: no assignment claims exactly `{B, C}`. It is not a success that
   silently deposits C.
10. **An inner `Xor` never pre-empts an outer one.** `Xor(And(A, Xor(D, E)), A)` with only A
    produced → success, selecting the second branch, whose claim is exactly `{A}`.

**Depends on:** [EVT-007], [CORE-051], [CORE-043]
**Test derivation:** Action produces to wrong place; verify failure event. Nested `Xor`
of overlapping `And`s where the wider branch is fully written; verify success. Bind a
hand-written no-op to a transition declaring `Out.place(P)`; verify a failure event
rather than a compile error. Where mid-action publication exists, flush one half of an
`And` and return without the other; verify both the violation event and that the flushed
token survives."#
