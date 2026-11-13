import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.CORE_002
import Libpetri.Spec.Text.CORE_040
import Libpetri.Spec.Text.IO_016
import Libpetri.Spec.Text.IO_017

runtime_defect RD_03
  title "TypeScript identifies places by object reference"
  requirements r#"CORE-040 (line 3, "no place twice"), CORE-002 (ruling D66 (a)), IO-016
(a branch is a set of places: the `And` line's union), IO-017 (the `And` and `Xor` lines'
union)."#
  runtimes r#"TypeScript."#
  defect r#"`place(name)` returns a new object on each call and the built net keeps places by
reference, while the compiled net keys them by name, so one place can be held twice.
`place` (`typescript/src/core/place.ts`), the `_places` field of `PetriNetBuilder` and its
`transition` method (`typescript/src/core/petri-net.ts`).
The output spec's place sets do the same: `allPlaces` and `enumerateBranches`
(`typescript/src/core/out.ts`) collect into a JS `Set` of place objects, so
`Xor(And(A, B), And(A', C))` with `A` and `A'` two `place('A')` objects (it builds: the IO-011
and IO-012 checks compare names) has an `allPlaces` set of four members for three places, and
the unbuildable `And(A, A')` enumerates one branch of two members for one place. The fusion
build and the `Transition` input, read and output place sets compare places by object as well,
so `fork` or `transform` on `Xor(And(A, B), And(A', C))` writes `A` twice."#
  evidence r#"none beyond the CORE_040, CORE_002, IO_016 and IO_017 assumes; under name
identity the TypeScript net breaks CORE_040 line 3, and the TypeScript `allPlaces` breaks the
union of IO_017's `Xor` line."#
  fix r#"places are kept by name, and the first object seen for a name wins, in the builder, the
fusion build, the transition place sets, `allPlaces` and `enumerateBranches`. TypeScript
`petri-net.test.ts`, "holds one place for two place objects with one name (CORE-002, CORE-040)"
and its fusion variant; `transition.test.ts`, "collects input, read and output places by name
(CORE-002)"; `out.test.ts`, "collects one place per name (CORE-002, IO-017)" and "a branch holds
one place per name (CORE-002, IO-016)"."#
  status "fixed, unreleased"
