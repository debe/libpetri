import Libpetri.Spec.Text

requirement_text MOD_020
  id "MOD-020"
  title "Composition Operation (port mapping by structural rewrite)"
  priority MUST
  kind B
  body r#"The enclosing net's builder MUST support a `compose(instance, bindings)` operation that integrates a module instance into the enclosing net by **structural rewriting**:

1. Each binding maps an interface port name (resolved on the instance) to a caller-side `Place<T>`.
2. For every binding `(portName -> callerPlace)`: the instance's renamed port place is substituted with the caller place at every arc in the instance's renamed body.
3. Every place an arc of a rewritten instance transition names is added to the enclosing builder; an internal place that no arc names is not added.
4. Every transition of the instance's renamed body that no channel binding names (with rewritten arcs) is added to the enclosing builder; a transition that a channel binding names is replaced by its merge with the caller-side transition ([MOD-021]).
5. Composition is **eager**: the rewrite happens at compose time, not at build, executor compile, or run time. The enclosing builder's place and transition sets reflect the composed structure immediately after `compose(...)` returns.

The result of composition over the enclosing builder MUST be observationally indistinguishable from a hand-written flat net containing the same places, transitions, and arcs.

Within a single `compose(instance, bindings)` call, every interface port appears in the bindings at most once. Re-binding the same port name (whether to the same caller place or a different caller place) within one `compose(...)` call is a compose-time error; the error message MUST name the port. Symmetrically, the same caller-side `Transition` appears as the target of at most one channel binding within a single `compose(...)` call; re-binding a caller transition to two channels of the same instance in one call is a compose-time error naming the caller transition and both channels (see also [MOD-021]).

**Port-binding collision.** Two *different* ports of one instance MAY be bound to the same caller place. When that substitution would give one transition of the instance two input arcs on the caller place (the transition consumed from both ports), composition MUST reject the call at compose time, before the rewritten transition is rebuilt, with an error naming the instance prefix, a port exposing each of the two places (in either order), the caller place and the transition, e.g.

```
ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/join' would consume from 'X' through two input arcs. Bind them to distinct places or use one port.
```

Without this check the rebuild would fail on [CORE-030] AC3 with a message that names only the rewritten transition, not the binding that caused it. When several pairs of bound ports collide on one transition, the error names one of the pairs.

The output side has the same shape. When the substitution would make one **AND branch** of a transition's output spec name the caller place twice (the transition wrote both ports in one branch), composition MUST reject the call at compose time with an error naming the instance prefix, a port exposing each of the two places (in either order), the caller place and the transition, e.g.

```
ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/split' would produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places or use one port.
```

and not with the generic [IO-011] rejection the rebuild would otherwise raise. A branch is taken after flattening nested `And`s, as in [IO-011]. Two ports that land in **different** `Xor` alternatives are not a port-binding collision, because each alternative still names the place once. *If* the substitution makes two distinct alternatives claim the same set of places, such as `Xor(a, b)` becoming `Xor(X, X)`, *then* rebuilding the transition *shall* fail with the [IO-012] ambiguity message, which names the transition, the two output branches and the places.

Other effects of binding two ports to one place (an input and an output, an input and an inhibitor) are unchanged: they are legal arcs with their usual semantics. Binding an input port and a read port of one transition to one place makes the rebuilt transition fail with the [EXEC-012] message. The checks apply wherever [MOD-020] bindings are processed, so the auto-bound form of [MOD-024] is covered too.

In the sentences below, two different bound port places of one instance, both bound to one caller place, are an *input collision* of an instance transition when it has an input arc on each of them, and an *output collision* of it when one AND branch of its output specification names both. A call is *coherent* when any two of its port bindings whose ports expose one renamed place bind it to one caller place; the sentences below that say coherent claim nothing about any other call ([MOD-003]). A call is *plain* when no caller place it binds is a place that an instance transition names, no instance transition has two input arcs on one place, and no AND branch of an instance transition's output specification names one place twice. A call *passes the binding checks* when it binds every port at most once, binds only ports the instance declares, binds every port to a caller place of the port's token type ([MOD-022]), binds every channel at most once, binds only channels the instance declares and whose transition is a transition of the instance, and binds no two channels to one instance transition. A call *meets the caller obligations* when the instance's transitions and the caller-side transitions of its channel bindings have pairwise distinct names, no caller-side transition is a transition of the enclosing builder, and no caller-side transition names a bound port place of the instance.

⟦s1|*When* a coherent `compose(instance, bindings)` call that meets the caller obligations succeeds, the enclosing builder *shall* hold its earlier transitions followed by one transition per instance transition, among them, in the instance's order, every instance transition that no channel binding names with each bound port place replaced by its caller place in every arc and in the output specification and its name, timing, priority and action unchanged, and, for every channel binding, the [MOD-021] merge of its caller-side transition with the instance transition it names after the rewrite, and its places *shall* be its earlier places and the places its new transitions name.⟧

⟦s2|*If* one `compose(...)` call binds a port name more than once, no channel name more than once and no caller-side transition to more than one channel, *then* the call *shall* fail with an error naming a port it binds more than once.⟧

⟦s3|*If* a `compose(...)` call binds a port name that the instance does not declare, *then* the call *shall* fail.⟧

⟦s4|*If* a coherent `compose(...)` call gives a transition of the instance an input collision, *then* the call *shall* fail.⟧

⟦s5|*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an input collision and no output collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the input collision message above, naming the instance prefix, a port exposing each of two places on which input arcs of `t` collide, in either order, their caller place and `t`.⟧

⟦s6|*If* a coherent `compose(...)` call gives a transition of the instance an output collision, *then* the call *shall* fail.⟧

⟦s7|*If* a coherent and plain `compose(...)` call passes the binding checks, an instance transition `t` has an output collision and no input collision, every instance transition before `t` has no collision and passes the checks of the transition builder after the rewrite, and no instance transition after `t` has a collision, *then* the call *shall* fail with the output collision message above, naming the instance prefix, a port exposing each of two places that collide in one AND branch of the output specification of `t`, in either order, their caller place and `t`.⟧

⟦s8|*If* a coherent and plain `compose(...)` call passes the binding checks and has no collision, every instance transition before a transition `t` passes the checks of the transition builder after the rewrite, and `t` after the rewrite does not, *then* the call *shall* fail with the transition builder's message for `t` after the rewrite.⟧

⟦s9|*When* a coherent `compose(...)` call that meets the caller obligations passes the binding checks, has no collision, every instance transition passes the checks of the transition builder after the rewrite, and every channel merge of [MOD-021] succeeds, the call *shall* succeed.⟧

⟦s10|*If* a `compose(...)` call binds a channel name more than once, binds a channel that the instance does not declare, binds a channel whose transition is not a transition of the instance, or binds two channels to one instance transition, *then* the call *shall* fail.⟧

**Acceptance Criteria:**
1. Compose an instance with binding `port "out" -> callerPlace P`; verify that every arc in the renamed body that referenced the port's renamed place now references `P` directly.
2. Internal places of the instance that an arc of a rewritten transition names appear in the enclosing builder under their renamed (prefixed) names.
3. Transition count of the enclosing builder after a compose call without channel bindings equals (prior count) + (instance transition count).
4. Building the enclosing net produces a `PetriNet` whose structure is identical to a hand-written equivalent.
5. Re-binding the same port name twice in a single `compose(...)` call (whether to the same caller place or different ones) is rejected at compose time with an error naming the port.
6. Binding the same caller-side transition to two distinct channels of one instance in a single `compose(...)` call is rejected at compose time with an error naming the caller transition and both channels.
7. Binding ports `a` and `b` of instance `s` to one caller place `X`, where instance transition `join` has an input arc on each port, is rejected at compose time with the port-binding collision message above, naming `a`, `b`, `s`, `X` and `s/join`. Binding the same two ports to `X` when no transition consumes from both is accepted.
8. Binding output ports `a` and `b` of instance `s` to one caller place `X`, where instance transition `split` declares `And(a, b)`, is rejected at compose time with the output collision message above, naming `a`, `b`, `s`, `X` and `s/split`, not with the generic [IO-011] message. With `Xor(a, b)` the same binding is rejected with the [IO-012] ambiguity message naming `s/split`, output branches 0 and 1, and `{X}`.

**Depends on:** [MOD-003], [MOD-010], [MOD-011], [MOD-021], [MOD-022], [CORE-030], [IO-011], [IO-012]
**Test derivation:** Build subnet with port `out`; compose with `out -> P`; export the resulting net and a hand-written equivalent; assert structural equivalence. Compose with `out -> P, out -> Q` in one call; verify rejection. Build a subnet whose transition `join` consumes from ports `a` and `b`; compose with `a -> X, b -> X`; verify rejection with the collision message. Repeat with a transition `split` producing `And(a, b)` (rejected, output message) and `Xor(a, b)` (rejected, [IO-012] message)."#
