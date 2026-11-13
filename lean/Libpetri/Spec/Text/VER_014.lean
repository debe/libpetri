import Libpetri.Spec.Text

requirement_text VER_014
  id "VER-014"
  title "Conditional Sink Places (Designed Terminals)"
  priority SHOULD
  kind F
  body r#"`DeadlockFree` ([VER-002]) reads a quiescent marking against the places where a token may
rest. Besides the unconditional **sink places**, the verifier accepts **conditional sink
places**: a set of places where a token may rest **while a marker place holds a token**,
declared as `sinkPlacesWhen(marker, places…)`. A marked marker is a *designed terminal* — a
halted or paused run, a cancelled batch — under which the work it interrupted legitimately
stays where it was delivered. The marker itself is at rest whenever it is marked, so
`sinkPlacesWhen(marker)` with no further places excuses exactly the marker.

Declarations union. ⟦s1|A token in place `p` of a quiescent marking `M` is **stranded** iff `p`
is not a declared sink, `p` is not a marker, and no conditional set naming `p` has its
marker marked in `M`.⟧ The `DeadlockFree` error condition becomes: (all transitions disabled)
∧ (some marked place is stranded). ⟦s2|Repeated declarations for one marker accumulate;
declarations for different markers are independent, so a place excused by two markers is
stranded only when both are unmarked.⟧ ⟦s3|`TerminatesAtSink` is unaffected and reads the
unconditional sinks only.⟧ An unresolved marker or place contributes nothing, as an
unresolved sink does: a mistyped marker makes the property stricter, never laxer.

⟦s4|The verifier *shall* read a token in place `p` of a marking `M` as stranded exactly when `p` is not a declared sink, `p` is not the marker of any conditional declaration, and every conditional declaration that names `p` has its marker unmarked in `M`.⟧

⟦s5|*When* the verifier decides `DeadlockFree`, it *shall* report a quiescent marking as a violation exactly when some marked place of it is stranded.⟧

⟦s6|*When* the verifier decides `TerminatesAtSink`, it *shall* report a quiescent marking as a violation exactly when it would without any conditional declaration.⟧

**Encoding.** In the flat and name-coloured CHC encodings the stranded disjunction of
[VER-002] gains, for each place `p` excused by markers `k₁ < … < kₙ` (flat indices), the
disjunct `(and (>= m_p 1) (= m_k₁ 0) … (= m_kₙ 0))` in place of `(>= m_p 1)`; declared sinks
and markers contribute no disjunct. Scripts without a conditional declaration are
byte-identical to those of [VER-002]. The report renders the declarations after the property
as `(sinks: a, b; when h: c, d; when p)`, in declaration order.

**Acceptance Criteria:**
1. A quiescent marking that marks a marker and holds tokens only in declared sinks, in the
   marker, and in that marker's conditional places is not a `DeadlockFree` violation.
2. A quiescent marking that holds a token in a conditional place whose marker is **unmarked**
   is a violation, exactly as without the declaration.
3. The marker needs no self-listing: `sinkPlacesWhen(p)` excuses a quiescent marking holding
   only `p`.
4. `TerminatesAtSink` ignores conditional declarations: a quiescent marking that marks a
   marker but no declared sink violates it.
5. Every route that decides `DeadlockFree` reads the same rest set, among them the flat
   encoder, the name-coloured encoder, the certificate check's safety condition, the abstract
   counterexample replay, the ν name-partition graph ([VER-012]), the enumeration route
   ([VER-017]), the state-equation phase ([VER-018]) and open-net verification ([VER-022]); the
   four implementations emit byte-identical scripts for the same declarations ([VER-013] AC1).

**Net-declared terminals.** A terminal place declared on the net ([EXEC-042]) is a designed
terminal that the caller does not restate. Every route verifies the net with `P` inhibiting each
transition, `P` added to the sinks, and `sinkPlacesWhen(P, all places)` added to the conditional
declarations. The open-net route ([VER-022]) merges it as a designed terminal. These additions
apply to the net's own terminals only. A net without them keeps its scripts byte-identical.

**Implementation notes:**
- Java: `SmtVerifier.sinkPlacesWhen(Place<?> marker, Place<?>... places)`.
- TypeScript: `SmtVerifier.sinkPlacesWhen(marker, ...places)`; `verification/rest-set`
  (`strandingExcuses`, `strandsToken`, `describeSinks`).
- Rust: `SmtVerifier::sink_places_when(marker, places)`.
- Python: `verify(..., sink_places_when={marker: [places…]})`.
- Fixtures: `sinkPlacesWhen` in `spec/verification-fixtures/fixtures.json`
  (`sink-partial-terminal-conditional-proven`, `dead-end-chain-marker-proven`,
  `dead-end-chain-unmarked-marker-violated`, `nu-mixed-terminal-route-b-conditional-proven`).

**Depends on:** [VER-002], [VER-012], [VER-013]

**Test derivation:** a fork whose one arm may halt while the other's token is still in
flight, with the halt marker inhibiting the second arm: `deadlockFree` with the halt as a
plain sink is violated (the in-flight token is stranded); with the in-flight place declared
under the halt marker it is proven; with the marker alone it stays violated; `terminatesAtSink`
with the same declarations is violated. A chain whose marker is consumed before quiescence
(AC2), and the same net with the resting place as its own marker (AC3)."#
