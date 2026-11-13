import Libpetri.Spec.Text

requirement_text ENV_001
  id "ENV-001"
  title "Environment Place Wrapper"
  priority MUST
  kind N
  body r#"An environment place is a marker wrapper around a regular place that designates it as an external event injection point. Tokens can be injected into environment places from outside the executor.

**Acceptance Criteria:**
1. An environment place wraps a regular place.
2. The underlying place's name and type are accessible.
3. Environment places are registered with the executor at construction time.

**Note (orthogonality with interface places):** Environment places (per this requirement) and interface places (ports per [MOD-003]) are **orthogonal concepts**. An environment place marks a *world boundary* — the seam where the engine accepts injections from outside the executor. An interface place marks a *composition boundary* — the seam where two net fragments are wired together at build time. A single underlying place MAY simultaneously be an environment place and a port: the resulting flat net (after composition per [MOD-020]) treats it as a regular place that the executor accepts injections into and that arcs from both fragments reference. Where this dual role is used (e.g., a subnet's input port is also the host's external event injection point), the environment-place registration applies after composition, on the post-composition place identity.

**Test derivation:** Create environment place wrapping place "UserInput"; verify name and type accessible."#
