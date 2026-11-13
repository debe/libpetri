import Libpetri.Spec.Text

requirement_text NU_011
  id "NU-011"
  title "Resume-Safe Fresh-Name Minting"
  priority MUST
  kind F
  body r#"[NU-010] scopes minted-name uniqueness to "a single execution". Restoring a marking
([CORE-073]) begins a **new** execution whose initial marking already holds names minted by
the previous one. An implementation that satisfies [NU-010] by counting firings from zero
therefore re-mints names that are already live — and because a [NU-020] join correlates on
name equality alone, the collision does not surface as an error: it silently correlates
tokens from different run segments, merging a restored token with an unrelated fresh one.

Names minted by an execution seeded from a restored marking MUST NOT collide with names
minted by any other execution in the same restore lineage, other than a replay of the same
segment (AC3), whether or not those names are still present in that marking. The mechanism is not prescribed. Two that satisfy it:

- a per-execution **scope** supplied by the host and incorporated into every minted name;
- carrying the minter's high-water mark in the snapshot and resuming strictly above it.

Under the scope mechanism, names minted under two different accepted scopes never collide, so
the guarantee rests on the executions of a lineage running under different scopes: the default
scope is drawn at random per executor (below), and a pinned scope is the host's promise. A
replay that re-runs a segment under its pinned scope, from the marking the segment started from
and with the same `freshName()` calls, mints the segment's names again, which is AC3, not a
collision between segments. A name the host writes into a token itself, such as a copied
correlation id, is not a minted name and is not covered.

**The restore lineage crosses processes.** [CORE-073] offers restore as a suspend boundary, a
durable checkpoint, a crash-recovery point — so the execution that resumes a marking is, in the
normal case, running in a *different process* from the one that minted the names in it. "Unique
per executor" read as "unique within a process" is therefore not enough. Anything derived from a
per-process counter restarts with the process, and the first executor of the new process re-mints
the first name of the old one: exactly the silent merge above, in the default configuration.

**The default scope MUST be unique across processes — and is therefore not the run identifier.**
Absent a host-supplied scope, an implementation using the scope mechanism MUST
draw one per executor from the platform's random source: a 128-bit value rendered as exactly **32 lowercase hexadecimal characters**, of
which at least 122 bits are random (a version-4 UUID with its dashes removed conforms). The
rendering is fixed so that a default-scope name looks alike, and parses alike, in every language.

An earlier revision of this requirement said that an implementation which already publishes a run
identifier SHOULD default the scope to it, "so one value means one thing". **That SHOULD is
withdrawn**, because the two values are required to have opposite properties. A run identifier
SHOULD be *reproducible* for a fixed construction order ([TIME-015] AC#14) — that is what lets a
replay carry the same identifier, and it is what a per-process counter provides. A default scope
MUST *differ* between two processes that did nothing differently — which is precisely what a
reproducible value cannot do. One value cannot be both. The run identifier remains the
reproducible one, the default scope is the unique one, and an implementation MUST NOT derive
either from the other.

**The scope's uniqueness is required; its observability is not.** The default scope MAY be entirely
internal — an implementation is not required to publish it, on an event or anywhere else, and MUST
NOT be read as required to merely to satisfy this requirement. What a host can observe is the
*name*, and the property that matters is that two executors never mint the same one. An
implementation whose scope is internal therefore conforms exactly as one whose scope is visible,
and the difference is not a divergence in behaviour.

**The name format, and what a scope may contain.** An implementation using the scope mechanism
mints `<transition>#<scope>:<n>`, where `<n>` is a per-executor counter from zero. A host-supplied
scope MUST be rejected when the executor is configured — not at the first mint — if it is **empty**
or contains **`:`** or **`#`**; the separators are rejected rather than escaped. Two details are
fixed because the implementations otherwise drift apart on them:

- *Empty* means length zero. A whitespace-only scope is legal, if unwise; an implementation MUST
  NOT trim the scope or test it for blankness, since "blank" is defined differently by every
  standard library and the same configuration would then be accepted in one language and refused
  in another.
- Rejecting `:` alone is **not** enough. Transition `a` under scope `b#c` and transition `a#b`
  under scope `c` both mint `a#b#c:0` — a collision between two segments of one lineage, which is
  what this requirement forbids. With `#` banned as well, a minted name parses uniquely whatever
  the transition name contains: the **last `:`** splits off the counter, and the **last `#` before
  it** splits off the scope; everything in front is the transition name.

A pinned scope is host text, so it SHOULD stay within the Basic Multilingual Plane for the reason
given under [NU-020]'s tie-break; this is advice to the host, not a validation.

Deriving the floor by scanning the restored marking is **not** sufficient in general: name
carrying values are opaque to the engine ([VER-004]), and a name minted into a token that has
since been consumed leaves no trace in the marking while remaining live in host state and in
any token the host holds across the restore.

Replay stability ([NU-010] AC3) is preserved **within** a run segment: for a fixed scope (or
a fixed restored high-water mark) and a fixed order of `freshName()` calls, the minted
sequence MUST be reproducible. The firing order fixes the order of the calls when at most one
minting action is in flight at a time, or when every call is made inline by a synchronous
action. Randomness is therefore admitted in exactly **one** place — the *default* scope,
chosen once per executor — and nowhere else: the counter `<n>` MUST NOT be random, and a scope
the host pinned MUST be used verbatim, with nothing random mixed into it or into the sequence
minted under it. A host that needs a reproducible segment pins its scope (AC3). A host that pins
nothing gets uniqueness instead of reproducibility, and that is the right default: an
unreproducible name is visible and harmless, a cross-segment merge is neither.

⟦s1|*If* a host-supplied scope is empty or contains `:` or `#`, *then* the executor *shall* reject it when it is configured.⟧

⟦s2|The executor *shall* accept a host-supplied scope that is not empty and contains neither `:` nor `#`, a whitespace-only scope included.⟧

⟦s3|*Where* an executor uses the scope mechanism, the `i`-th `freshName()` call it answers, counting from zero across all its firings and transitions, *shall* return `<t>#<s>:<i>` with `i` written in decimal, where `t` is the name of the calling transition and `s` is the executor's scope, verbatim as the host pinned it or as it was drawn by default.⟧

⟦s4|*Where* executors use the scope mechanism, no name minted by an execution under one accepted scope *shall* equal a name minted by an execution under a different accepted scope.⟧

⟦s5|*Where* an executor is given no scope, the executor *shall* draw its scope from the platform's random source as 32 lowercase hexadecimal characters, which neither its construction order nor its run identifier determines.⟧

⟦s6|A host *shall not* pin one scope for two executions of one restore lineage, except for a replay: an execution that re-runs an earlier segment, after it and not alongside it, from the marking that segment started from and with the same `freshName()` calls.⟧

**Acceptance Criteria:**
1. Restore a marking holding a name `n` minted by a prior execution; run the resumed
   execution, under the default scope or a pinned scope other than the prior execution's, so
   it mints at least as many names as the original minted; no minted name equals `n`.
2. A restored token awaiting its sibling at a [NU-020] join is not correlated with a
   freshly minted token of the resumed segment.
3. For a fixed scope and a fixed order of `freshName()` calls, two runs from the same restored
   marking mint the identical name sequence.
4. Two concurrent executions restored from the same snapshot, under the default scope or under
   two different pinned scopes, mint disjoint name sets.
5. **The default scope is not process-local.** An executor given no scope mints names whose scope
   component is 32 lowercase hexadecimal characters, different for every executor and — where
   the implementation publishes a run identifier — not equal to it. AC1 and AC2 therefore hold
   when the resuming executor is the *first* one constructed in its process, which is the case a
   per-process counter fails.
6. **Scope validation and the parse rule.** An empty scope, a scope containing `:` and a scope
   containing `#` are each rejected at configuration; a whitespace-only scope is accepted. A name
   minted by a transition whose own name contains `#` and `:` splits back into transition, scope
   and counter by the rule above.

**Depends on:** [NU-010], [NU-020], [CORE-073], [TIME-015], [VER-004]
**Test derivation:** Run a ν-fork net under a **pinned** scope until a token carrying a minted
name awaits its sibling at a join; snapshot and restore into a fresh execution under a different
pinned scope — and again under the default one; fire the fork and assert the new name differs
from the restored one and that the join does not merge the restored token with the new one.
Repeat the restore twice concurrently and assert the two name sets are disjoint. No test may
depend on how many executors the process constructed before it: compare names structurally
(transition, scope, counter) or pin the scope, and include a case in which the resuming executor
is the first one constructed."#
