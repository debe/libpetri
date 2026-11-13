import Libpetri.Spec.Text

requirement_text MOD_002
  id "MOD-002"
  title "Subnet Identity (sealed/sum-type distinction from PetriNet)"
  priority MUST
  kind Q
  body r#"The engine distinguishes between **closed** nets (a `PetriNet` per [CORE-040], runnable by an executor) and **open** nets (a subnet definition, not directly runnable). The two share a common type abstraction (sealed sum, sealed interface, or enum, depending on language) so APIs can accept "any net" or restrict to one variant.

APIs that require a runnable net MUST reject an open subnet at the type level where the language permits, and at construction-time otherwise. APIs that require an open fragment MUST symmetrically reject a closed net.

**Acceptance Criteria:**
1. A common abstraction (`Subnet`) classifies nets as closed or open.
2. The two variants are distinguishable by type (sealed/sum-type), not merely by a runtime tag.
3. Passing an open subnet to an executor-construction API is a compile-time error in languages with sealed types, or a clearly reported construction-time error otherwise.
4. Passing a closed net to a composition API that expects an open fragment is similarly rejected.

**Test derivation:** Attempt to construct an executor from an open subnet; verify the call site does not compile (Java/Rust) or fails fast at construction (TypeScript). Attempt to compose a closed net into a builder; verify symmetric rejection."#
