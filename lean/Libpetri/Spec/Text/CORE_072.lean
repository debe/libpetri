import Libpetri.Spec.Text

requirement_text CORE_072
  id "CORE-072"
  title "Initial Marking"
  priority MUST
  kind B
  body r#"⟦s1|An executor can be initialized with an initial marking that pre-populates places with tokens before execution begins.⟧

⟦s2|*When* an executor is initialized with an initial marking, its marking *shall* hold, before execution begins, exactly the tokens the initial marking puts on each place, whether or not the net declares that place.⟧

⟦s3|*When* execution begins, a transition of the net *shall* be armed exactly when its enablement check passes on the initial marking, with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 ([TIME-010]).⟧

⟦s4|*While* a place is an unknown place, the executor *shall* retain its tokens in the marking, in their order and ahead of any token that reaches the place later, and *shall not* drop any of them.⟧

⟦s5|*While* a place is an unknown place, the executor *shall not* change its tokens when the firing clock advances or when it reaps a transition ([TIME-013]).⟧

**Acceptance Criteria:**
1. Initial marking distributes tokens to specified places.
2. Execution begins with these tokens available.
3. Tokens on places the net does not declare are **retained** in the observable
   marking (inert — no arc can reference them — but never silently dropped).
   This holds for every backend regardless of its internal token storage; the
   same retention applies to any token reaching a backend for an uncompiled
   place through production or injection seams. A transition context never
   produces to such a place, because an output call on a place the transition does
   not declare as an output reports an error ([CORE-063]); the production seam is
   reached only by a token that bypasses the context, such as the internal raw
   output collector (`rawOutput()`) of Java and TypeScript. Verification models such a place
   the same way, as a place with no arcs whose tokens stay ([VER-001]).
4. An implementation SHOULD surface the first write to an undeclared place as an
   observable diagnostic, emitted as the existing log-message event ([EVT-013]) —
   no new event type. Field shape: logger `libpetri.runtime` (omitted where the
   implementation's log-message event carries no logger field), level `WARN`,
   transition name = the producing transition's name, or `""` at the
   initial-marking and injection seams where no transition is firing; message
   `unknown place '<p>': tokens are retained in the marking but inert (the net
   declares no arc on it)`. Emitted once per distinct unknown place per executor,
   not once per token. Retention (AC3) does not depend on the diagnostic.

**Depends on:** [EVT-013]
**Test derivation:** Create executor with initial marking {P1: [a, b], P2: [c]}; verify tokens present before first firing. Include a place unknown to the net; verify its tokens appear unchanged in the final marking, and that exactly one `WARN` log-message event names that place however many tokens land on it."#
