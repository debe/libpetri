# Causality, Not Order: Coloured Time Petri Nets for Verifiable Agentic LLM Orchestration

**Status:** outline / scope only. Work in preparation (2026). No section prose written yet.
**Author:** Dennis Berger.
**Type:** experience + method blend (a production case study with a conceptual core).

---

## Abstract (stub — points to cover, not final prose)

- Problem: multi-agent / LLM orchestration is largely "prompt-and-hope"; concurrency, timing, and failure handling are held together by ad-hoc callbacks, flags, and locks.
- Claim: model an orchestration session as a Coloured Time Petri Net (CTPN), and the substrate becomes something you can reason about and prove properties of.
- Method: agent steps are transitions, session state is coloured tokens, LLM calls are subnets, external events are environment places; coordination is by token consumption.
- Result: whole classes of failures (race, TOCTOU, lost update, deadlock) are designed out at the model level; deadlock-freedom, boundedness, and liveness-flavored properties are checked before the net runs; every run is event-sourced and replayable.
- Evidence: libpetri, an open-source executable CTPN runtime (Java/TS/Rust + a Python binding), and a shipped production voice-and-text commerce assistant whose sessions each run as a ~110-place net verified in CI.

## Contributions (thread these through the paper)

1. **CTPN as an executable production runtime for agent orchestration** ("the net is the program"). Coordination-by-consumption designs out race / TOCTOU / lost-update / deadlock at the model level rather than by careful coding.
2. **ν-nets (name-creating nets) for fork/join of a unit of work** — scatter/gather over N parallel agent/LLM calls, with correlation expressed *in the firing rule* (a `MatchSpec`), not through external mutable state.
3. **Budget-as-a-typed-place** — a structural discipline that bounds agent retry / re-ask loops and keeps verification decidable.
4. **Two verification routes** — Route A: CHC encoding + Z3 Spacer IC3/PDR over an untimed over-approximation; Route B (novel): a solver-free, *exact* name-and-time-aware state-class graph (Berthomieu–Diaz + DBM zones + name-permutation symmetry quotient), where undecidability surfaces as truncation, never as an unsound verdict.
5. **Petri nets as a module system** — typed subnets with interfaces, composition by structural rewrite into a flat net, per-instance action binding; subnets verifiable in isolation.
6. **A prove-before-run + replay-after-fail lifecycle** for trustworthy orchestration.

---

## Table of Contents

1. **Introduction** — the reliability gap in multi-agent/LLM orchestration ("prompt-and-hope"); thesis (orchestration as CTPNs gives a verifiable substrate); contributions; note that it is shipped in production.
2. **Motivation: Sequences Are the Wrong Primitive** — state-machine blowup (7 parallel paths give 2⁷ combined states); races / TOCTOU / lost update / deadlock in agent tool-use; causality vs. order; requirements for a substrate (concurrency, timing, verifiability, replay).
3. **Background: Coloured Time Petri Nets** — places / transitions / tokens / colours; the five arc types (input, output, inhibitor, read, reset); Time-Petri-Net firing intervals `[earliest, latest]`, deadlines, clocks; marking and the atomic firing rule.
4. **Modeling Agentic Systems as Nets** — the mapping (session state = coloured tokens; agent steps / tools = transitions with async actions; an LLM call = a subnet with request/response ports; external events = environment places); coordination by consumption; a single-threaded orchestrator with concurrent actions; timing as first-class (deadlines, fallbacks, barge-in, inactivity); ν-net fork/join for scatter/gather; budget-as-typed-place for bounded loops.
5. **libpetri: An Executable CTPN Runtime** — "executable, not a simulator"; typed subnets and composition (module system); the executor (bitmap enablement O(W), virtual threads / Tokio / promises; precompiled executor near 190 ns per transition); one 203-requirement executable spec across Java / TS / Rust plus a Python binding; Apache-2.0 and published coordinates.
6. **Verification** — properties (deadlock-freedom, mutual exclusion, boundedness, unreachability, joined-or-dead-lettered liveness, budget bounds); structural pre-checks (siphon/trap, Commoner) and Farkas P-invariants; Route A (Z3 Spacer IC3/PDR, soundness of the untimed over-approximation); Route B (exact name-by-time state-class graph); prove-before-run in CI ("rewire, not rewrite").
7. **Deterministic Replay and Observability** — event-sourced state; the session-archive format; the marking replay cache (periodic snapshots, frame-by-frame debugging); determinism from a single-threaded total order plus replay-stable fresh names; the honest distinction between in-engine deterministic replay and closed-loop evaluation once actions call live LLMs.
8. **Case Study: A Production Voice-and-Text Assistant** — system (Java 25 / Helidon, Gemini via Vertex plus Gemini Live); one net per session; the measured voice net (110 places / 67 transitions / 16 subnets; text 99 / 70 / 15); concrete patterns (input/output guards, an intent-detection LLM subnet with primary/fallback timeouts, priority-ordered parallel product-search strategies, barge-in, inactivity, model-activity windows); real timing budgets; CI formal-analysis tests (state-class graph plus SMT deadlock-freedom, the "three terminal states" example); closed-loop replay plus LLM-as-judge evaluation and the guardrail feedback loop (the session archive as a latent evaluation dataset). All generalized and anonymized.
9. **Discussion and Lessons** — what the model buys (races designed out, proofs before incidents, deterministic debugging); the hard part moves to net design; the formalism's boundary (data-dependent delays pushed to the environment; guards abstracted during verification); when not to use it; cost and performance.
10. **Related Work** — Petri nets and CPN (Petri 1962, Jensen), workflow / WF-nets (van der Aalst), Time Petri Nets (Berthomieu–Diaz), ν-PN (Rosa-Velardo and de Frutos-Escrig); model checking (IC3/PDR, Z3/Spacer, CHC), state-class graphs, DBM; agent-orchestration frameworks (LangGraph, AutoGen, CrewAI, Google ADK, LangChain4j, Temporal / workflow engines, BPMN).
11. **Conclusion and Future Work** — the self-improving loop (replay as a fitness function; an agentic harness that proposes net rewrites verified by SMT before shipping); applicability beyond agents.

- **Appendix A** — the racing-LLM-agent-pipeline example net (`rust/libpetri/examples/basic.rs`) as Figure 1.
- **Appendix B** — property definitions and a CHC-encoding sketch.
- **Appendix C** — reproducibility (libpetri coordinates, versions, the executable spec).
- **References.**

### Figure candidates

- Racing LLM agent pipeline (`rust/libpetri/examples/basic.rs`) — Figure 1.
- State-machine-vs-net state blowup (`docs/talks/state-machine-vs-petri.png`).
- The "show me red sneakers under 100 EUR gives eight things at once" concurrency slide (`docs/talks/marvin-concurrency.png`).
- Coordination by consumption (`docs/talks/coordination-by-consumption.png`).
- The two verification routes (A: Z3 IC3/PDR; B: name-partition SCG).

---

## Author notes for the writing phase

### Confidentiality (clear with employer before publishing)
Marvin is an OTTO-internal repository. The CTPN method, net-size counts, timing constants, arc usage, verification methodology, and replay design are the author's own IP (libpetri / adk-libpetri) and are publishable in generalized form. Get explicit employer sign-off before quoting any false-positive / true-positive or quality percentage, any customer utterance, or internal service codenames and infrastructure identifiers. Anonymize the product as "a production voice-and-text commerce assistant."

### Accuracy corrections vs. earlier prose (talks, CV, cover letters)
- The voice net measures **110 places / 67 transitions / 16 subnets** (text 99 / 70 / 15). Cite these, not the older "about 50 transitions."
- Replay is **closed-loop evaluation**, not byte-exact, once LLM actions run; keep the two notions distinct.
- The **"10k security tests"** figure is unsubstantiated in-repo (the red-team suite is roughly 63 attack plugins times 20 tests times strategies). Do not state 10k as fact; use the plugin-based figure or confirm a real number.

### Target format / venue
An arXiv preprint is the fastest path to a citable artifact (and lets the CV move from "in preparation" to "preprint"). Optionally target an experience / industry track or a Petri-nets / formal-methods workshop. Author-friendly typesetting is **Typst** (already installed and used for the CV); switch to a venue's LaTeX template only for camera-ready if required.

---

## Key source-file index (for drafting)

- Thesis / narrative: `README.md`, `docs/talks/causality-not-order.md` (+ compiled PDF and diagrams).
- Executable spec: `spec/00-index.md` .. `spec/12-nu-nets.md` (esp. `03-timing.md`, `07-verification.md`, `08-events-observability.md`, `11-modular-composition.md`, `12-nu-nets.md`).
- Core model (Rust reference): `rust/libpetri-core/src/{place,transition,token,arc,input,output,timing,context,match_spec,name,petri_net}.rs`.
- Verification: `rust/libpetri-verification/src/{smt_verifier,smt_encoder,property,p_invariant,structural_check,state_class_graph,dbm,nu_scg_verifier,name_state_class_graph}.rs`.
- Replay / observability: `rust/libpetri-debug/src/{marking_cache.rs,archive/}`.
- Example nets (figures): `rust/libpetri/examples/basic.rs`, `examples/java-parser/`, `debug-ui/src/net/definition.ts`.
- Case study (separate OTTO repo, generalize): `nucleus_marvin/src/main/java/de/otto/nucleus/marvin/voice/VoiceWorkflowConfig.java`, `.../voice/VoicePlaces.java`, `.../voice/WorkflowPetriNetFormalAnalysisTest.java` (in `src/test`), `.../replay/ReplayHarness.java`.
