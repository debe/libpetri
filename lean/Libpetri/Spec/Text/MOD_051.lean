import Libpetri.Spec.Text

requirement_text MOD_051
  id "MOD-051"
  title "SubnetDef.verify(harness) for local property verification"
  priority SHOULD
  kind B
  body r#"A subnet definition SHOULD support a local verification operation `verify(harness)` that proves properties of the subnet **in isolation**, without first composing it into an enclosing net. The harness supplies:

1. A `params` value of the subnet's parameter type.
2. For each input and in-out port, a token source. `verify` calls it once while it builds the synthetic net and discards the token, so a source that fails or returns no token makes `verify` fail. It does not bound the input: the environment mode of item 4 does.
3. The set of properties to check (per [VER-002]).
4. How injection into those environment places is modeled, per [VER-006]. It comes in the options of `verify` beside the harness, or the implementation defaults it.

The implementation realizes this by wrapping the subnet in a synthetic enclosing net where each input and in-out port is bound to an environment place and each output port to a place the properties can name, then invoking the standard verifier per [MOD-050].

Item 4, not the token sources of item 2, is what bounds the input (AC3). The synthetic net has environment places by construction, so the environment mode decides what a verdict is worth: under `Ignore` the verifier models no injection, and [VER-006] refuses to certify any `Proven` that results, so **a subnet with an input port can never be proven**. A `Violated` still comes back: for a reachability-safety property it is a counterexample with injection too, since a run without injection is a run with it, and for a quiescence property it is a rest of the subnet while the environment stays silent, which need not be a rest under injection ([VER-006]). `verify` therefore SHOULD default to `AlwaysAvailable`, under which a `Proven` holds for every environment, and SHOULD let the caller pass a mode instead. `Bounded(k)` caps the tokens **resident** in each input place at `k` and refills it forever ([VER-006]), so it bounds what one firing can take, not the input as a whole; `Arrivals(k)` is the mode that expresses a generator delivering at most `k` tokens to each input port over the whole run, and `Arrivals(min, max)` one delivering at least `min` of them; `Arrivals(k, k)` delivers exactly `k`, which a property counting outcomes against inputs at quiescence needs, since under `Arrivals(k)` a run that declines its arrivals always violates it.

**Verification options.** `verify` SHOULD accept an options value beside the harness, and the existing signatures keep working unchanged:

- the environment mode above;
- a **configure** hook, called once per property with the per-property verifier *after* the implementation's own setup (property, environment places, environment mode) and with the synthetic net, returning the verifier to run. It is how a caller sets anything the verifier offers: the per-call timeout and the total budget or cancellation of [VER-013], sink places, the state-equation and enumeration options, the ν options below. The synthetic net lets the hook resolve the names the harness's properties already use: the subnet's own places under the `sut/` prefix, the ports under their harness names. The hook has the semantics of the open-net `configureSmt` of [VER-022]: what it sets overrides the implementation's setup, and a hook that replaces the environment mode takes responsibility for it.

Python cannot hand a callback the Rust builder cheaply, so `verify_subnet` takes keyword arguments forwarded to each per-property verification instead: at least the keywords `verify` accepts for the timeout, total budget, cancellation, sink places, enumeration budget and state-space options, and the ν options (budget places, carrier places, fragment mode, the Route B class bound). Place names in them are the synthetic net's names, spelled as in the properties (`sut/<place>`). An unknown name behaves as it does in `verify`: an
unknown sink place is ignored, and an unknown carrier place makes the verdict `Unknown`.

**ν subnets need the ν options.** A subnet that mints and joins correlation names ([NU-010], [NU-020]) and threads a name through a relay is verified in the BASE fragment unless the caller says otherwise ([NU-051]). BASE reads such a relay as a fresh mint: a different model, in which a join the real net reaches may never fire, so a safety property can come back `Proven` although the net violates it. Declaring the carrier places and selecting the EXTENDED fragment through the options (the hook, or the Python keywords) is what makes the per-property verifier decide the subnet exactly; implementations SHOULD say so where they document `verify`.

**Binding actions on a definition.** A subnet definition SHOULD offer `bindActions(...)`, mirroring the net-level operation of [CORE-042] with the same argument forms (mapping and resolver) and, per form, the same treatment of transitions it does not name, divergence included. It is keyed by the definition's own, unprefixed transition names and returns a **new** definition whose ports, channels and parameters are unchanged; the receiver is not modified. Instances created from the new definition carry the bound actions as their shared defaults ([MOD-030]). The [CORE-043] check in `verify` applies to the bound definition as to any other.

⟦s1|*When* `verify` returns a result, the synthetic net it verified *shall* be the net that a new enclosing builder builds from one call that composes the subnet's instance under the prefix `sut`, binds each port to its harness place (`harness_in_<port>` for an input port, `harness_out_<port>` for an output port, `harness_io_<port>` for an in-out port), binds no channel and declares nothing else.⟧

⟦s2|*If* instantiating the subnet under the prefix `sut` fails or building the synthetic net fails, *then* `verify` *shall* fail.⟧

⟦s3|*If* the harness supplies no token source for an input or in-out port of the subnet, *then* `verify` *shall* fail and *shall* return no verification result.⟧

⟦s4|*If* the harness supplies a token source for every input and in-out port and the [CORE-043] check fails on the synthetic net, *then* `verify` *shall* fail with an error that names the transition the check names, also when the harness lists no property.⟧

⟦s5|*When* `verify` returns a result, the result *shall* hold an entry for each property of the harness and no entry for another property, and each entry for a property *shall* be the result of the standard verifier ([VER-003], [VER-006]) on the synthetic net, set up with that property, the harness places of the input and in-out ports as environment places, the selected environment mode, the verifier's default options and the empty initial marking, and then passed, together with the synthetic net, through the configure hook, whose changes override that setup.⟧

⟦s6|*When* `verify` is called without options, it *shall* verify under the environment mode `AlwaysAvailable` with no configure hook.⟧

⟦s7|*When* actions are bound on a subnet definition, in either form, the new definition *shall* have the name, the ports and the channels of the original definition and the place correspondence ([MOD-031]) of each of its transitions, in the same order.⟧

⟦s8|*When* actions are bound on a subnet definition with a resolver or a mapping, the body of the new definition *shall* be the net that binding the same resolver or mapping on the original body gives at net level ([CORE-042]), so the resolver or the mapping is keyed by the definition's own, unprefixed transition names.⟧

**Acceptance Criteria:**
1. Where provided, `verify(harness)` returns a verification result of the same shape as the standard verifier per [VER-003].
2. Invoking `verify` does not require the subnet to be composed into any enclosing net.
3. The environment mode of item 4, not the token sources, bounds the input behavior for the verification, and a missing token source for an input or in-out port is an error.
4. The environment-analysis mode of [VER-006] is selectable per verification and defaults to one that models injection, so a subnet with an input port is not refused a `Proven` by default.
5. `Arrivals(k)` is selectable, and bounds the total injected into each input port to `k`: a subnet that forwards each input token to an output port proves `placeBound` of that output at `k` under `Arrivals(k)` and violates it under `Bounded(k)`.
6. The configure hook (Python: the forwarded keywords) reaches every per-property verifier. A setting made there is visible in the result: a total budget too small to finish yields its exhaustion reason ([VER-013]), and a sink place named there changes a quiescence verdict.
7. **ν options reach the verifier.** A ν subnet whose property is `Proven` with the options unset (BASE) is `Violated`, or at least not `Proven`, once carrier places and the EXTENDED fragment are passed through the options: the options are shown to change the model, not merely to be accepted.
8. `bindActions` on a definition returns a new definition whose instances carry the bound actions, keyed by unprefixed names; the receiver's instances keep the old ones; ports and parameters are unchanged.

**Implementation notes:** TypeScript `verify(harness, options?: { environmentMode?, configure?: (verifier: SmtVerifier, synth: PetriNet) => SmtVerifier })`; Java `verify(harness, SubnetVerifyOptions)`, a record of the environment mode and a `BiFunction<SmtVerifier, PetriNet, SmtVerifier> configure`, with withers; Rust `SubnetVerifyOptions`, whose `configure` field takes the verifier and the synthetic net (`OpenNetOptions::configure_smt` plus the net); Python `verify_subnet(..., *, environment_mode=..., <forwarded keywords>)`. `bindActions` / `bind_actions` on `SubnetDef` in all four.

**Depends on:** [MOD-001], [MOD-030], [VER-001], [VER-006], [VER-013], [VER-022], [ENV-001], [CORE-042], [CORE-043], [NU-051]
**Test derivation:** Build a leaky-bucket subnet parameterised by rate; supply a harness with a request generator and leave its permit place unseeded; verify that the bucket's `accepted` place is `0`-bounded — unreachable however much the environment injects — under the default mode and under `Bounded(k)`, and that the same query is refused under `Ignore`. A forwarding subnet under `Arrivals(2)` against `Bounded(2)` (AC5); a total budget of 1 ms set through the hook (AC6); a fork → relay → join subnet with carrier places, verified with and without the ν options (AC7); `bindActions` on a definition, then two instances of the old and the new definition (AC8)."#
