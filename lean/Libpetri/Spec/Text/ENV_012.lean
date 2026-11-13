import Libpetri.Spec.Text

requirement_text ENV_012
  id "ENV-012"
  title "Event-Driven Workflow Pattern"
  priority SHOULD
  kind Q
  body r#"The engine supports event-driven workflow patterns where ~10 environment places represent external event sources (activity signals, data streams, tool requests, state changes, etc.) and the executor runs indefinitely, processing events as they arrive.

This requirement adds no behaviour of its own. What the executor does with each injection is stated by [ENV-002], [ENV-003], [ENV-004] and [ENV-010], and how an injected token gets the transitions it enables armed is stated by [EXEC-001] step 3, [CONC-002], [CONC-005], [TIME-010] and [TIME-013]. None of them depends on how many environment places are registered. The sentence below restates them for many sources, and no requirement block of its own quotes it.

*While* ten or more environment places are registered and the executor is open and running with no terminal place marked, the executor *shall* accept an injection into any of them as [ENV-010] requires, queue and inject it as [ENV-003] and [ENV-004] require for a single environment place, and *shall* arm the transitions the injected token enables as [EXEC-001] step 3, [CONC-002], [CONC-005], [TIME-010] and [TIME-013] require.

The number ten and the concurrency of AC2 are quality targets for tests to check; what concurrent callers of `inject()` get is [ENV-003]'s subject.

**Acceptance Criteria:**
1. 10+ environment places can be registered simultaneously.
2. Injection from multiple concurrent sources works correctly.
3. The net reacts to each injection by enabling relevant transitions.

**Depends on:** [ENV-001], [ENV-002], [ENV-003], [ENV-004], [ENV-010], [EXEC-001], [CONC-002], [CONC-005], [TIME-010], [TIME-013]
**Test derivation:** Build a net with 10 environment places; inject events from multiple sources; verify correct transition firing."#
