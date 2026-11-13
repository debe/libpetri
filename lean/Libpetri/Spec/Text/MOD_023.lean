import Libpetri.Spec.Text

requirement_text MOD_023
  id "MOD-023"
  title "Composition Produces Flat Net"
  priority MUST
  kind B
  body r#"After all `compose(...)` (and `fuse(...)` per [MOD-061]) calls have been made on a builder, `build()` MUST produce a `PetriNet` indistinguishable from a hand-written flat net that has the same places, transitions, arcs, timing, priority, and actions. Two records a composed net may carry sit beside that structure and are not part of it: the subnet membership of [MOD-026], which only direct composition records, and the declared-to-actual correspondence of [MOD-031], through which an action resolves the places its subnet declared where a hand-written action names the actual places.

In particular, downstream consumers, namely the executor (CONC, EXEC), the event subsystem (EVT), the verifier (VER) and the exporter (EXP), MUST require no awareness of composition structure to operate on the composed net, except that the exporter MAY read the subnet membership of [MOD-026] to draw subnet clusters ([MOD-040]). Compiled net representations per [CONC-007], [CONC-020] MUST be constructed identically whether the source net was composed from subnets or hand-written, provided the hand-written net declares its places in the order the composed net holds them.

⟦s1|*When* `build()` succeeds, every transition of the built net *shall* pass the checks of the transition builder ([CORE-030], [IO-002], [IO-004], [EXEC-012], [IO-011] to [IO-014]), whichever `compose(...)`, `fuse(...)` or other builder calls produced it.⟧

⟦s2|*When* `build()` succeeds, a new builder on which the places of the built net are declared, its transitions are added by hand in the same order with the same name, arcs, output specification, timing, priority and action and no correspondence ([MOD-031]), and its terminal places ([EXEC-042]) are declared *shall* build a net with the same transitions in the same order, the same places, each listed as often, in any order, and the same set of terminal places.⟧

⟦s3|*When* `build()` succeeds, no `compose(...)` call binds a channel ([MOD-021]) and no composed instance has two transitions of one name, the built net *shall* hold one transition for each transition added by hand and for each transition of a composed instance or of a directly composed subnet, in the order of the calls and, within one call, in the order of the subnet, each with the name, timing, priority and action it was added with.⟧

**Acceptance Criteria:**
1. Build the composed net and a hand-written equivalent net that declares its places in the order the composed net holds them; their compiled representations have identical place index, transition count, arc topology, bitmap masks, and timing arrays.
2. Running both nets, with the hand-written net's actions naming the actual places where the composed actions resolve the places their subnet declared ([MOD-031]), under the same executor with the same initial marking produces identical event sequences and final markings.
3. When the composed net carries no subnet membership ([MOD-026]), exporting both nets produces byte-equal DOT modulo group ordering; a directly composed net may differ from its hand-written equivalent by the subnet clusters drawn from its membership ([MOD-040]).
4. Running verification on both nets produces identical results.

**Depends on:** [MOD-020], [MOD-021], [CONC-007], [EXEC-001]
**Test derivation:** Build a composed net `N1` and a hand-written equivalent `N2` whose actions name the actual places; run both with identical initial markings; assert identical event sequences and final markings."#
