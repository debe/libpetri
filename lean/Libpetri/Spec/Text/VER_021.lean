import Libpetri.Spec.Text

requirement_text VER_021
  id "VER-021"
  title "XOR Branch Analysis"
  priority SHOULD
  kind F
  body r#"The verifier supports analysis of the outcomes of transitions with XOR output branches over a built state class graph ([VER-010]), reporting which outcomes the graph takes. Each outcome of a transition, each XOR branch and a timeout outcome that deposits differently from every branch, is a virtual transition of its own ([VER-001]), and the outcomes are numbered from 0 in that order: the XOR branches in enumeration order, then the timeout outcome.

⟦s1|The XOR branch analysis *shall* report every transition of the net with two or more outcomes, and no other, once each with its number of outcomes.⟧

⟦s2|*While* the graph it reads does not split a transition in flight, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires the transition with that index.⟧

⟦s3|*While* the graph it reads splits a transition in flight ([VER-004]), that is, while an edge fires its completion `complete:<t>` or a class marks its place `inflight:<t>`, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires `complete:<t>` with that index.⟧

⟦s4|The XOR branch analysis *shall* report as untaken exactly the outcomes of a reported transition, numbered from 0 below its number of outcomes, that it does not report as taken.⟧

⟦s5|*When* the graph is closed, the XOR branch analysis *shall* report an outcome of a reported transition as untaken exactly when no run of the net from its initial marking fires the transition with that outcome, or fires `complete:<t>` with it when the graph splits the transition.⟧

An index is taken as the edge carries it, with no bound: a graph builder that fires a transition only with its own outcomes gives no index at or above the number of outcomes. A transition whose `Timeout` forwards an `All` or `AtLeast` input ([IO-014]) has no virtual transitions of [VER-001], so the first sentence does not cover it: the analysis may report it with the number of outcomes its graph builder fires, as the runtimes do, and still reports every other transition of the net.

The analysis reads only the graph it is given and does not report whether that graph is closed. On a graph truncated at its class budget ([VER-017]) an untaken outcome may still fire beyond the budget, so a caller reads the graph's completeness (`isComplete`, `is_complete` in Rust) before calling an outcome unreachable.

**Acceptance Criteria:**
1. Every outcome of a transition, each XOR branch and a timeout outcome that deposits differently from every branch, is expanded into a separate virtual transition.
2. An outcome no edge of the graph fires is reported untaken; on a closed graph it is one that no run fires.

**Depends on:** [IO-012], [IO-016], [VER-001], [VER-004], [VER-010]
**Test derivation:** Net with a XOR transition enabled after one step and a second XOR transition whose input place is never marked; on the closed graph the first XOR transition reports every outcome taken and the second every outcome untaken. A graph truncated before the first XOR transition fires is not complete and reports that transition's outcomes untaken. A transition split in flight is read off `complete:<t>`, a start edge alone takes none of its outcomes, and a class that marks `inflight:<t>` splits it before any completion fires. A XOR transition beside an unrelated drained forward is still reported."#
