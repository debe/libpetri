import Libpetri.Spec.Text

requirement_text MOD_004
  id "MOD-004"
  title "Port Direction Semantics (advisory; arcs govern flow)"
  priority MUST
  kind B
  body r#"Port direction is **advisory metadata**: the subnet builder, `instantiate` and composition do not read it. Documentation, visualization and the verification harness of [MOD-051] read it. It does NOT constrain arc flow at runtime: an `Output` port's place MAY have input arcs from internal transitions; an `Input` port's place MAY be read by internal transitions. Actual token flow at run time is governed exclusively by arcs declared per CORE-030..CORE-035.

Implementations MAY emit a build-time warning when declared direction conflicts with the arc structure (e.g., an `Input` port whose place has no internal consumer transition), but MUST NOT reject the subnet on direction-versus-arc mismatch.

⟦s1|*When* two subnet declarations differ only in the directions of their ports, building the subnet definition *shall* succeed for both or fail for both.⟧

⟦s2|*When* two subnet definitions differ only in the directions of their ports, `instantiate` with one prefix *shall* succeed for both or fail for both, and two successes *shall* give the same places, the same transitions, the same port and channel handles, and the same ports apart from their directions.⟧

⟦s3|*When* building a subnet definition succeeds, the definition *shall* have a port with the name of each declared port, and each such port *shall* carry the declared direction.⟧

**Acceptance Criteria:**
1. Direction metadata is preserved and queryable via the port handle.
2. A subnet whose `Output` port place is also written internally by transitions is accepted at build.
3. A subnet whose `Input` port place is also read internally by transitions is accepted at build.
4. Where a warning channel exists, an obvious mismatch (declared `Input` with no internal consumer; declared `Output` with no internal producer) MAY emit a warning but MUST NOT raise an error.

**Depends on:** [CORE-030], [CORE-031], [CORE-032], [CORE-033], [CORE-034], [CORE-035]
**Test derivation:** Build a subnet whose `Output` port place has both an internal output arc (producer) and an internal input arc (consumer); verify build succeeds."#
