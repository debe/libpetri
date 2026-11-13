import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.VER_017
import Libpetri.Spec.Text.VER_017

runtime_defect RD_28
  title "TypeScript's state-space cache grows on every `Arrivals` query and never hits"
  requirements r#"VER-017 (the cache key: under `Arrivals` the key covers the closure, or the
verifier does not use the cache for that query and says so in the report; AC7)."#
  runtimes r#"TypeScript."#
  defect r#"the enumeration looks the graph up under the caller's net and the closed initial
marking (`typescript/src/verification/smt-verifier.ts`, `enumerate`), and the marking
half of the key names `Place` objects by identity
(`typescript/src/verification/state-space-cache.ts`, `resolveStateSpace` and `markingKey`). The
`Arrivals` closure makes new arrival-source `Place` objects on every call
(`typescript/src/verification/smt-verifier.ts`, `applyArrivals`), so every query under
`Arrivals` misses, builds, and adds one more entry, and the report does not say that the cache
was not used. No verdict is wrong, since the cache never hits there. `Arrivals(0)`, and
`Arrivals` with no environment place, do not close the net and hit the cache. Java bypasses the
cache under `Arrivals` with a report line; Rust and Python key the fingerprint of the closed net."#
  evidence r#"none; ⟪VER_017_cache⟫ takes the key as an abstract value (its assumes
records the `Arrivals` clause as the key's job)."#
  fix r#"the enumeration does not use the cache when the `Arrivals` closure added arrival sources,
and writes Java's report line for it; `Arrivals(0)` still uses the cache. TypeScript
`state-space-cache.test.ts`, the two tests of "VER-017 AC7" (two `arrivals(k)` queries through one
cache each build and carry the line; `arrivals(0)` uses the cache)."#
  status "fixed, unreleased"
