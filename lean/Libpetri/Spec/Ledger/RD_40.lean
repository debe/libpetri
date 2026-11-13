import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.VER_010
import Libpetri.Spec.Text.VER_010
import Libpetri.Spec.Text.VER_012

runtime_defect RD_40
  title "Rust and TypeScript dedup state classes by a marking string that does not escape place names"
  requirements r#"VER-010 (the key sentence, `VER_010_key` line 2: two classes of the graph
share a key exactly when they have the same marking and zone; and through it the run coverage
of `VER_010` line 1 on a graph reported complete), VER-012 (`VER_012` line 8: the Route B graph
identifies two classes exactly when they have the same base class and name key; and through it
AC3's completeness of a closed graph)."#
  runtimes r#"Rust, TypeScript, and Python through Rust's verifier."#
  defect r#"both runtimes dedup state classes by a rendered string in which place names are not
escaped. Rust renders the marking as `name:count` entries joined by `,`
(`MarkingState::canonical_key`, `rust/libpetri-verification/src/marking_state.rs`), the
class key appends `|` and `Dbm::zone_key` (`StateClass::canonical_key` in `state_class.rs`;
`dbm.rs`, clock names joined by `,`), and `StateClassGraph::build` dedups by that string
(in `build_core`, `state_class_graph.rs`). TypeScript renders the marking as `{name:count, ...}`
(`MarkingState.toString`, `typescript/src/verification/marking-state.ts`) and dedups by
`classKey` = marking string, `|`, zone key (`analysis/state-class-graph.ts`, used in
`StateClassGraph.build`). Route B interns the base class by the same strings: Rust `intern_base`
(`name_state_class_graph.rs`, `canonical_key` then `#` and the `ready_earliest` bits),
TypeScript `internBase` over `baseKeyOf` (`analysis/name-state-class.ts`,
`analysis/name-state-class-graph.ts`). Place names are arbitrary strings (`Place::new`
checks nothing), so the markings {`a`:1, `b`:1} and {`a:1,b`:1} (TypeScript: {`a:1, b`:1}) get
one key. On the net `t1: x -> a, b`, `t2: x -> 'a:1,b'` from {`x`:1}, both successors of the
initial class have no clocks, so their class keys are equal: the Rust build reports
`complete=true` with 2 classes where the correct graph has 3, the edge (`t2`, 0) points to the
class with marking {`a`:1, `b`:1}, and `is_reachable` of {`a:1,b`:1} answers `false`. The
TypeScript build also stores 2 classes. A marking that a timed run reaches is then missing from
a graph reported closed, which can give an unsound `Proven`; in Route B the first arrival's base
class is kept and the second marking is lost the same way. Java keys by structure
(`StateClass.equals` over `MarkingState` and the DBM, and the record `BaseKey` in
`NameStateClassGraph.java`), so it does not collide. Rust's `reachable_markings` dedups by
the same string, and `zone_key` leaves clock names unescaped; TypeScript's counterexample
decoder dedups markings by `toString()` too. The fix is a key that cannot collide:
key the maps by the structured marking and zone, as Java does, or escape or length-prefix every
name in the rendering."#
  evidence r#"⟪VER_010_key_forbids_markingBlind⟫ (`VER_010.lean`): an identity that gives
two classes with different markings and one zone one key breaks ⟪VER_010_key⟫ line 2. The model
indexes places by number and has no place names, so the string rendering itself is not modelled."#
  fix r#"Rust escapes `\`, `,`, `:`, `|` and `#` in place and clock names in `canonical_key` and
`zone_key`, so the class key, `reachable_markings` and `intern_base` are injective. TypeScript
keys classes, Route B base classes, `StateClass.equals`, `isReachable` and the counterexample
decoder by `MarkingState.key()`, the JSON of the sorted entries; the public
`StateClassGraph.reachableMarkings()` still returns display strings. Rust `state_class_graph.rs`
`ver_010_class_key_does_not_merge_markings_through_place_names`, `marking_state.rs`
`ver_010_canonical_key_escapes_separators` and `dbm.rs` `ver_010_zone_key_escapes_clock_names`;
TypeScript `state-class-graph.test.ts`, "VER-010: a place named "a:1, b" does not share a class
key with {a:1, b:1}" and "VER-012: Route B keeps the marking that renders like the first
arrival's". Python runs the Rust verifier and has no test of its own."#
  status "fixed, unreleased"
