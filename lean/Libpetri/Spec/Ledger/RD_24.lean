import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.MOD_025

runtime_defect RD_24
  title "Java's compose token-type check reads one host place per name"
  requirements r#"MOD-025 (line 4: a body place whose name the builder holds with another token
type is rejected)."#
  runtimes r#"Java."#
  defect r#"`compose(SubnetDef)` compares each body place with one host place per name, the
one put last into a name-keyed map. When the builder already holds two places of one name with
different token types (Java's `Place` equality is structural on name and type) and the last one
has the body place's type, Java accepts the call where MOD-025 rejects it.
`java/src/main/java/org/libpetri/core/PetriNet.java` (`Builder.compose(SubnetDef)`)."#
  evidence r#"none; line 4 of MOD-025 (MOD_025.lean) states the rejection, and no theorem
models Java's name-keyed map."#
  fix r#"the check indexes the host places by name to a list and rejects a body place when any
host place of that name has another token type. Java
`ComposeDirectTest.composeDirect_placeTokenTypeConflict_withTwoSameNamedHostPlaces_throws_MOD025`."#
  status "fixed, unreleased"
