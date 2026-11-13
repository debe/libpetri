import Libpetri.Spec.Text

requirement_text NU_030
  id "NU-030"
  title "Freshness Scoping under Composition"
  priority MUST
  kind F
  body r#"Names minted in two instances never collide ([NU-010]); the transition component of a minted
name ([NU-011]) is the firing transition's post-compose name, which carries the instance prefix
unless the transition is channel-merged ([MOD-021]). The match specification of a composed join
follows the same place rewrite as its arcs ([MOD-020]), so a composed join still correlates the
renamed inputs and produces into the renamed relay targets ([NU-054]).

⟦s1|*When* a transition is rebuilt through a place rewrite (such as prefix renaming [MOD-010], port binding [MOD-020], place fusion [MOD-061], or the identity rewrite of action binding [CORE-042]), the set of input places of the rebuilt transition *shall* be the image under the rewrite of the set of input places of the original transition.⟧

⟦s2|*When* a transition is rebuilt through a place rewrite, the set of places of the output specification of the rebuilt transition *shall* be the image under the rewrite of the set of places of the output specification of the original transition.⟧

⟦s3|*When* a transition that carries a match specification is rebuilt through a place rewrite, the rebuilt transition *shall* carry a match specification whose correlated places and relay targets ([NU-054]) are the images under the same rewrite of the original ones, in the same order, each with the key projection it had.⟧

⟦s4|*When* a transition that carries no match specification is rebuilt through a place rewrite, the rebuilt transition *shall* carry no match specification.⟧

⟦s5|*When* a transition is rebuilt through a place rewrite, the name of the rebuilt transition *shall* be the original name with the instance prefix under prefix renaming ([MOD-010]) and the original name under every other rebuild.⟧

**Acceptance Criteria:**
1. Two instances of a forking subnet never mint colliding names.
2. After composition, a join's match correlates the renamed (host-bound) places,
   not the author-original ones.

**Depends on:** [MOD-010], [MOD-020], [MOD-021], [MOD-061], [CORE-042], [NU-010], [NU-011], [NU-054]
**Test derivation:** Instantiate a fork+join subnet twice; verify each instance's
joins merge only their own siblings."#
