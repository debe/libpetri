import Libpetri.Spec.Text

requirement_text ENV_002
  id "ENV-002"
  title "Environment Place Registration"
  priority MUST
  kind B
  body r#"⟦s1|Environment places must be registered with the executor before execution begins.⟧ ⟦s2|The executor maintains a set of registered environment places.⟧

**Acceptance Criteria:**
1. Executor builder accepts environment place registrations.
2. ⟦s3|Where inject takes an environment-place handle (Java, TypeScript), only registered environment places accept injections.⟧
3. ⟦s4|Where inject takes an environment-place handle (Java, TypeScript), attempting to inject into a non-environment place returns an error.⟧
4. ⟦s5|Where inject takes a place name (Rust, Python), the host injects only into registered environment places.⟧

⟦s6|The set of registered environment places is fixed when the executor is built; no step of a run adds or removes one.⟧

⟦s7|*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *if* a caller injects into a place that is not a registered environment place, *then* the executor *shall* answer with an error, and *shall not* answer with a refusal even when it is draining, closed, stopped or finished.⟧

⟦s8|*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *if* a caller injects into a place that is not a registered environment place, *then* the executor *shall* leave its state unchanged: it *shall not* queue the token and *shall not* change the marking.⟧

⟦s9|*Where* an executor's inject takes an environment-place handle (Java, TypeScript), the executor *shall* answer an injection into a place that is not a registered environment place with an error in every state of the run, before and after the run finishes.⟧

⟦s10|*Where* an executor's inject takes an environment-place handle (Java, TypeScript), the executor *shall not* answer an injection into a registered environment place with an error, in any state of the run.⟧

⟦s11|*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *while* the run has not finished, the executor is not draining, closed or stopped and no terminal place is marked ([EXEC-042]), the executor *shall* accept an injection into a registered environment place.⟧

⟦s12|An executor whose inject takes a place name (Rust, Python) deposits an injected token into the place the name resolves to, whether or not that place is registered; for it, registration decides only whether the run waits at quiescence ([ENV-010]) and which arcs the dead-arc report lists ([CORE-037]).⟧

⟦s13|*Where* an executor's inject takes a place name (Rust, Python), the host *shall* inject only into registered environment places.⟧

**Depends on:** [ENV-001]
**Test derivation:** Java, TypeScript: register 3 environment places; inject into registered one → success; inject into unregistered → error. Rust, Python: AC4 is an assumption on the host, and no executor test checks it."#
