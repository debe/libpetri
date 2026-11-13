import Libpetri.Spec.Text

requirement_text EVT_012
  id "EVT-012"
  title "TokenRemoved Event"
  priority MUST
  kind B
  body r#"⟦s1|Emitted when a token is removed from a place (consumed by input arc or cleared by reset arc).⟧ Contains:
- Timestamp
- Place name
- The token (Java and TypeScript; Rust and Python when the event store captures tokens)

⟦s2|*When* a transition starts, the executor *shall* emit, for each place, one TokenRemoved event naming that place for each token the start removes from it, whether an input arc consumes the token or a reset arc drains it.⟧

⟦s3|The executor *shall* emit TokenRemoved events only when a transition starts.⟧

⟦s4|*Where* the TokenRemoved event carries the token (Java and TypeScript; Rust and Python when the event store captures tokens), the TokenRemoved events of a start *shall* carry, for each place, the tokens the start removes from it in the order they stood in the place's queue, and, where no correlated input of a match specification takes them ([NU-020]), these tokens followed by the tokens the place keeps *shall* be the place's queue before the start.⟧

**Acceptance Criteria:**
1. Emitted for every token removal.
2. Place name identifies the source place.

**Test derivation:** Fire transition consuming token; verify TokenRemoved event."#
