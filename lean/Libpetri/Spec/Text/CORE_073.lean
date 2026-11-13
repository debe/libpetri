import Libpetri.Spec.Text

requirement_text CORE_073
  id "CORE-073"
  title "Marking Snapshot and Restore"
  priority MUST
  kind F
  body r#"A marking can be captured as a structured snapshot that preserves, for every token, both its
value and its `created_at` timestamp, and restored as the initial marking of a new execution
(a "resume").

⟦s1|*When* a snapshot of a marking is restored, the restored marking *shall* hold on every place exactly the tokens the marking held there, in the same FIFO order, each token unchanged in its value and its `created_at`.⟧

⟦s2|A snapshot an implementation returns to the host *shall* list its places in strictly ascending code-point order of the place name and *shall not* list a place that holds no token.⟧

⟦s3|*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold on each place the snapshot names exactly the tokens of that place's entry, in their order, whatever the place name and whether or not the receiving net declares the place.⟧

⟦s4|*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold no token on a place the snapshot does not name.⟧

⟦s5|*If* an executor is constructed with a restored marking together with an explicit initial marking that holds a token, *then* the construction *shall* fail with an error to the caller, and the executor *shall not* merge the two markings or keep either one.⟧

⟦s6|*When* an executor is constructed with a restored marking together with an explicit initial marking that names no place, the executor's initial marking *shall* be the restored marking.⟧

⟦s7|*When* an executor is constructed with a restored marking together with an explicit initial marking that holds no token and the construction succeeds, the executor's initial marking *shall* be the restored marking.⟧

⟦s8|*When* a restored marking seeds a new executor, each restored token *shall* keep its value and its `created_at`, whatever the executor's epoch clock ([TIME-015]).⟧

⟦s9|*When* a restored marking seeds a new executor, that executor's initial marking *shall* hold on every place the token count the restored marking holds there, whether or not the net declares the place ([CORE-072]).⟧

⟦s10|*When* execution resumes from a restored marking, each transition of the net that the restored marking enables *shall* be armed with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 whatever the `created_at` of the restored tokens ([TIME-010]).⟧

**The snapshot form is normative, because four implementations inventing four shapes is the whole
problem this requirement exists to prevent.** A snapshot is a mapping from **place name** to an
**ordered sequence** of entries, each carrying a token's `value` and its `created_at`:

- The sequence is the place's **FIFO order** ([CORE-013]), and a restore MUST reproduce it. Token
  order decides which token a firing consumes, so a snapshot that loses it is not a restore.
- A snapshot an implementation **emits** MUST omit a place that holds no tokens, as [EVT-014] AC3
  already requires of the event. A **restore** MUST accept both forms — the place omitted, and the
  place present as an empty sequence — and MUST restore them identically, because a snapshot a
  host authored or edited may carry either. Omission is fixed on the emitting side rather than left
  open because the alternative makes a snapshot a function of *history*: a place that was drained
  and a place that never held a token are the same marking, and a form that tells them apart gives
  two equal markings two different artefacts — between languages, within one language, and even
  between two executors of one implementation that store tokens differently.
- A place name the receiving net does not declare MUST be retained rather than dropped, exactly as
  [CORE-072] requires of any initial marking, so a snapshot survives a round-trip through a net
  that has since gained or lost a place.
- An entry is the implementation's **own token representation**, not a parallel type invented for
  snapshots: a token already *is* a value plus a `created_at`, and a second type carrying the same
  two fields diverges from the language's own model rather than converging on this one. Where the
  form must cross a language boundary, the binding's rendering of that token is the entry.
- **A place name is an arbitrary string, and none of them is reserved.** An implementation MUST NOT
  drop, rename or mangle an entry because its name collides with a construct of the host language
  or of the serialization it happens to use. Names reach this form from wherever the net was built
  — in a compiled workflow they are user input — so a name that happens to match a language's
  special property, a prototype key, a reserved word or a magic method is ordinary data. Losing one
  is silent: the snapshot simply has fewer places than the marking did, with no error to notice.
  The shape to look for is narrower than "anywhere a name is used as a key": it is the
  implementation **writing** a name it did not choose into a container that reserves some — a plain
  object, an attribute set, a keyword-argument expansion. Reading through an entries-style iteration
  is safe, and a container keyed by a closed vocabulary is not at risk at all.
- The form is **structural, not serialized**. The engine MUST NOT impose a value codec and MUST NOT
  require token values to be serializable: the host owns that, because only the host knows what its
  values are. An implementation whose values are already a serializable type MAY expose a
  convenience encoder, but MUST NOT make it the only path.

**Restoring resolves names against the receiving net.** A snapshot carries place *names*, not
places, which is what lets it survive a net that gained or lost one. An implementation whose
marking is keyed by name alone can restore from the snapshot unaided. An implementation whose place
equality is structural over name *and* token type ([MOD-024]) cannot: a place synthesised from a
name has no token type to supply, so it does not compare equal to the receiving net's own place and
the restored tokens land where the executor cannot see them. Such an implementation MUST resolve
each snapshot name against the receiving net's declared places, and its restore operation therefore
takes the net — or its places — as a second input. That is a required consequence of [MOD-024], not
an API divergence to be smoothed away: a signature matched at the cost of a restore that silently
loses its tokens is the worse trade. Names the receiving net does not declare are still retained
per [CORE-072], under whatever placeholder place the implementation can construct.

For the same reason such an implementation MUST **reject** — with an error raised to the caller,
never by keeping one place and dropping the other — a snapshot or a restore over a set of places
in which two share one name: the form is keyed by name alone, so two same-named places of
different token type collapse into one entry on the way out and cannot be told apart on the way
in. The refusal belongs to the host-facing operations, and is raised where the host asked — when
it requests the snapshot, or configures the restore — not later from inside the run. The
marking-snapshot event ([EVT-014]), which the orchestrator emits on its own initiative, MUST NOT
fail a run over it. Whether such a net may be *built* at all is [MOD-024]'s question and is not
changed here.

**A restore and an initial marking are two descriptions of one thing.** Where an executor accepts
both a restored marking and an explicit initial marking, supplying a restored marking together with
an explicit initial marking that holds a token MUST be **rejected** rather than resolved. Merging them invents a state neither caller described; preferring either silently
discards the other's tokens, and the caller who supplied the discarded one has no way to find out.
Rejecting costs one error at construction and removes a class of silent loss. An explicit initial
marking that names no place describes nothing and is accepted alongside a restore; whether one that
names places but holds no token is rejected as well is left to the implementation, but one that is
accepted seeds the restored marking, since it holds no token to keep. An executor whose only
initial marking is the restored marking itself has no second input, and the rule does not apply
to it.

**Place order is not semantic, but it MUST be canonical.** The form is a *mapping*, so a restore
MUST NOT depend on the order places appear in. But a host persists a snapshot, and the moment it
does it will diff, hash or content-address the result — at which point a mapping walked in hash
order produces a different artefact on every run of the same net, for no reason a reader could
guess.

So where an implementation renders a snapshot in any ordered medium, places MUST appear in
**ascending code-point order of the place name** — the same canonical order the verification
encoders already use, and for the same reason ([VER-013]). Merely *deterministic* is not enough:
two implementations each stable in their own order still disagree, and the point of one normative
form is that a snapshot of the same marking lists the same places in the same order in every
language — so a host that serializes it with one codec gets one artefact, **byte for byte**,
whichever implementation took it. Omitting empty places on emission (above) is the other half of
that: order alone does not make two snapshots agree if one of them lists places the other leaves
out.

The trap is that a language's natural string order is usually not this order. Sorting by UTF-16
code unit — Java's `String.compareTo`, JavaScript's `<` — diverges from code-point order wherever a
character above U+FFFF meets one in U+E000–U+FFFF, so a place name outside the Basic Multilingual
Plane is enough to break the comparison. [VER-013] documents the same hazard for script output;
an implementation SHOULD reuse whatever canonical comparator it already has rather than reach for
the default.

**The rule follows the form — as far as the medium can carry an order.** It applies wherever a
marking snapshot is rendered into an ordered medium: not only to the value a host is handed, but
to a snapshot carried on an event ([EVT-014]). An implementation that canonicalises the returned
snapshot and then discards that order on the way into the event has fixed one of the two places a
host takes a snapshot from and left the other arbitrary.

It does **not** reach a JSON session archive or the JSON debug protocol. A JSON object is an
unordered collection, and at least one runtime cannot emit arbitrary keys in a chosen order at all
([EVT-025]), so a code-point-order MUST on those media would be unmeetable there without a change
of wire format and is deliberately not made. Event bodies are in any case per-language and
explicitly not byte-compatible across implementations ([EVT-025]), so cross-language byte equality
was never implied for them. What **is** required of those media is **reproducibility across runs of
the same implementation**: an archive, or a debug-protocol message, written twice from identical
run data MUST NOT differ. Watch for container types whose iteration order is randomised
*per process* rather than merely unspecified — several standard libraries provide one, and they
defeat reproducibility in a way an ordinary hash map does not, because the artefact changes on
every run rather than merely being arbitrary.

An implementation MUST NOT silently re-stamp a restored token's `created_at`. Restoring is the one
path on which the engine hands back a timestamp it did not choose, and re-stamping would make a
resume indistinguishable from a fresh start ([TIME-015]'s token-stamping boundary).

The preserved `created_at` is **token metadata** carried for fidelity (observability, archival,
timed-value inspection). It is independent of the firing clock: when a restored marking seeds a
new executor, every initially-enabled transition's timing clock starts fresh at that executor's
enablement moment, per [TIME-010] / [TIME-011]. Restoring does **not** resume a partially elapsed
firing interval — a token's `created_at` never advances or shortcuts any `Delayed`, `Window`,
`Deadline`, or `Exact` decision.

> **Note (non-normative).** `created_at` does take part in one firing decision that is not a
> timing decision: the [NU-022] tie-break orders eligible correlation names by their oldest
> token's `created_at`. Restored tokens keep the stamps of the clock that made them, while tokens
> the resumed execution produces are stamped from *its* epoch clock ([TIME-015]). A host that
> injects an epoch clock on a resumed execution should therefore seed it at or above the
> snapshot's maximum `created_at`; seeded below it, the two populations sit on unrelated time
> bases and the tie-break order between restored and fresh groups is unspecified. The remedy is
> on the clock, never on the tokens: the engine does not re-stamp (AC9), and the tie-break key
> does not change.

**The fresh clock is safe for lower bounds and unsafe for upper bounds.** Re-waiting a `Delayed`
or `Exact` lower bound after a restore still satisfies it: a bound measured again from zero is
still at least that bound. A `Deadline` or `Window` **upper** bound is not symmetric — it receives
a fresh full budget, so a deadline the net promised to enforce can be silently missed across a
restore, and a `TransitionTimedOut` ([EVT-009]) that would have fired does not. A host that needs
a hard bound to survive a restore MUST NOT express it as net timing: it belongs in the token
payload (an absolute instant the net tests against) or in an action-level timeout ([IO-013]),
which severs the output rather than restarting a clock.

**Soundness is conditional on restore being infrequent.** Every restore restarts every clock
([TIME-011]). A transition whose `Delayed(d)` clock is restarted more often than every `d` never
accumulates `d` and never fires — starvation, not slowdown. This contract is therefore sound for
restore as an *occasional* operation (a suspend boundary, a durable checkpoint, a crash-recovery
point) and unsound for a scheduler that parks and resumes a run as a matter of course. An
implementation offering restore SHOULD state this bound rather than leave it to be discovered.

**A timed proof does not cross a restore.** The state-class construction ([VER-010]) enumerates
classes reachable from the initial marking *and its initial clock valuation*. A restored marking
seeds a new execution with every clock at zero — a different initial state, not necessarily a
class of the original graph — so a timed property proved for the original run says nothing about
the resumed one. Re-verifying with the restored marking as the initial marking covers the resumed
segment exactly. An untimed proof ([VER-004]) is unaffected: it is clock-blind, and a restored
marking that came from a real run, taken at a moment with no work in flight ([ENV-014]), is
reachable by construction. That last clause does not hold for
a hand-authored marking no run produced.

**Acceptance Criteria:**
1. Snapshot → restore round-trips each token's value and `created_at` unchanged.
2. A restored marking pre-populates places exactly like any other initial marking ([CORE-072]).
3. A `Delayed` / `Window` transition enabled by restored tokens waits its full interval measured
   from the resuming executor's enablement, regardless of how old the tokens' `created_at` is.
4. A `Deadline(d)` transition enabled by restored tokens is reaped once its elapsed time, measured
   from the stamp the **resuming** executor gave it, is strictly greater than `d` plus the deadline
   tolerance ([TIME-013]), not measured from the original enablement: the original hard bound does
   not survive the restore, and no `TransitionTimedOut` is emitted for the elapsed original
   budget.
5. Restoring the same marking repeatedly at an interval shorter than `d` never fires its
   `Delayed(d)` transition, demonstrating the frequency bound above.
6. **FIFO order survives.** A place holding tokens A, B, C snapshots and restores to A, B, C, and
   the first firing that consumes one takes A.
7. **Empty and unknown places.** A place present but empty restores identically to one omitted,
   and a snapshot the implementation emits omits empty places — so a drained place and a place
   that never held a token snapshot identically, on every executor. A place name the receiving net
   does not declare is retained in the restored marking ([CORE-072]) rather than dropped.
8. **No codec is imposed.** A token whose value is not serializable by any built-in mechanism —
   a closure, a native handle, an arbitrary host object — snapshots and restores within the
   process without the engine attempting to encode it.
9. **The engine does not re-stamp.** Every restored token's `created_at` equals the value in the
   snapshot, including where the executor was given an injected epoch clock ([TIME-015]).
10. **A restored marking is visible to the executor.** Tokens restored under a snapshot name are
    the tokens the net's own transitions consume — including where place equality is structural and
    the name had to be resolved against the receiving net. Where that resolution is ambiguous
    because two of the places share one name, the snapshot and the restore are rejected to the
    caller rather than resolved in favour of either.
11. **Both is an error.** Constructing an executor with a restored marking *and* an explicit
    initial marking that holds a token is rejected, not merged and not silently resolved in favour
    of either; an explicit initial marking that names no place is accepted, and an executor
    constructed with a restore always starts from the restored marking.
12. **Canonical place order where the medium is ordered.** Snapshotting the same marking twice
    yields the same place order; a restore is unaffected by presenting the places in any other
    order; and the order is ascending code-point order of the place name, so two implementations
    snapshotting the same marking agree key for key — including for a place name above U+FFFF,
    which is where a UTF-16 sort diverges.

**Depends on:** [CORE-010], [CORE-011], [CORE-013], [CORE-072], [TIME-010], [TIME-011], [TIME-013],
[TIME-015], [ENV-014], [EVT-009], [EVT-014], [EVT-025], [IO-013], [MOD-024], [NU-022], [VER-004],
[VER-010], [VER-013]

**Test derivation:** Seed an executor from a restored marking whose token `created_at` is in the
distant past feeding a `Delayed(d)` transition; verify it fires ~`d` after start, not immediately
(the existing `async_delayed_timing` test already exercises an epoch-`created_at` token through a
`delayed(100)` transition)."#
