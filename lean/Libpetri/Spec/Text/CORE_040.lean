import Libpetri.Spec.Text

requirement_text CORE_040
  id "CORE-040"
  title "Net Builder"
  priority MUST
  kind F
  body r#"A Petri net is constructed via a builder pattern. The builder accepts places and transitions and produces an immutable net definition.

⟦s1|The sentences below concern a net builder used without composition ([MOD-020], [MOD-025], [MOD-027]) and without fusion sets ([MOD-060], [MOD-061]), which rewrite arcs, drop places or reject at build under their own requirements.⟧

⟦s2|*When* a net is built from transitions, each added once, whose names are pairwise distinct ([TIME-010]), the net *shall* hold exactly the added transitions, in the order they were added, which is the declaration order of its transitions.⟧

⟦s3|*When* a net is built, every declared place, every declared terminal place ([EXEC-042]), every place that an input, inhibitor, read or reset arc of an added transition names and every place in the `allPlaces` set of the output specification of an added transition ([IO-017]) *shall* be a place of the net.⟧

⟦s4|*When* a net is built, the net *shall not* hold any other place, and *shall not* hold a place twice ([CORE-002]).⟧

⟦s5|Building a net that declares no terminal place ([EXEC-042]) *shall* succeed.⟧

⟦s6|Which nets that declare terminal places build, and which terminal places a built net holds, are stated by [EXEC-042].⟧

**Acceptance Criteria:**
1. Builder can add places and transitions.
2. `build()` produces an immutable net.
3. Places referenced by transitions are auto-collected from arcs of all five kinds: input, inhibitor, read, reset and the output specification.

**Test derivation:** Build a net with transitions; verify all places from arcs are present in the net."#
