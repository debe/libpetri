import Libpetri.Spec.Text

requirement_text EVT_014
  id "EVT-014"
  title "MarkingSnapshot Event"
  priority SHOULD
  kind B
  body r#"Emitted at specific points during execution to capture the marking. Contains:
- Timestamp
- Map of place name → list of tokens

⟦s1|*When* a run starts, the executor *shall* emit, before the run's first cycle, an ExecutionStarted event and, after it, a MarkingSnapshot event that carries the initial marking.⟧

⟦s2|*When* a run finishes ([EXEC-041]), whatever its termination reason, the executor *shall* emit a MarkingSnapshot event that carries the marking the run ends with and, after it, an ExecutionCompleted event.⟧

⟦s3|The marking a MarkingSnapshot event carries *shall* list every place the net declares that holds a token, *shall* list each place it lists with all of that place's tokens in FIFO order, and *shall not* list a place that holds no token.⟧

⟦s4|The marking a MarkingSnapshot event carries *shall* list each place at most once and *shall* list its places in ascending code-point order of the place name, also for a place name above U+FFFF ([CORE-073]).⟧

A place the net does not declare may be listed with its tokens or left out.

A marking snapshot carried on this event is the snapshot form of [CORE-073], and [CORE-073]'s
canonical place-order rule applies to it: the places of the marking it carries MUST appear in
ascending code-point order of the place name. The event is an ordered, in-process value, so the
order is both meetable and observable there, and it is one of the two places a host takes a
snapshot from.

The order is **not** promised past the event. A JSON session archive ([EVT-025]) and the JSON
debug protocol are unordered media, and code-point order is deliberately not required of them.
What is required of any rendering of this event — those two included — is **reproducibility
across runs of the same implementation**: two runs over identical data MUST produce identical
output, so a rendering MUST NOT pass the marking through a container whose iteration order is
randomised per process ([CORE-073]).

Emitting this event MUST NOT fail the run. In particular the refusal [CORE-073] requires for two
same-named places belongs to the host-facing snapshot and restore operations, not to this event.

**Acceptance Criteria:**
1. Emitted at least at execution start (initial marking) and before execution completion.
2. Snapshot is a deep defensive copy (not a live reference).
3. Only non-empty places are included.
4. The places of the marking carried on the event appear in ascending code-point order of the
   place name ([CORE-073] AC12), on every executor that emits the event, including for a place name above U+FFFF.
5. Rendering the same event stream twice with one implementation — into an archive or onto the
   debug protocol — yields identical output.

**Depends on:** [CORE-073]
**Test derivation:** Run net; verify MarkingSnapshot at start and end; verify snapshot accuracy.
For AC4, run a net whose place names include one above U+FFFF and one in U+E000–U+FFFF and assert
the order on the emitted event. For AC5, render one recorded stream twice — in two processes where
the implementation's default map is randomised per process — and compare the output."#
