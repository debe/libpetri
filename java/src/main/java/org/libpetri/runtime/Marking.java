package org.libpetri.runtime;

import java.util.*;
import java.util.stream.Collectors;

import org.libpetri.core.Place;
import org.libpetri.core.Token;

/**
 * Mutable marking (token state) of a Petri Net during execution.
 *
 * <p>A marking represents the distribution of tokens across places at a given
 * point in time. This class provides the runtime state container used by
 * the runtime executors during net execution.
 *
 * <h2>Threading Model</h2>
 * <p>This class is <strong>not thread-safe</strong>. All access must be from
 * the orchestrator thread (the thread calling {@link PetriNetExecutor#run()}).
 * Transition actions must not access the marking directly.
 *
 * <h2>Token Ordering</h2>
 * <p>Tokens in each place are maintained in FIFO order using {@link ArrayDeque}.
 * When a transition fires, it consumes the oldest token first.
 *
 * <h2>Type Safety</h2>
 * <p>All operations are type-safe via generics. The place's type parameter
 * ensures only compatible tokens can be added or retrieved.
 *
 * @see PetriNetExecutor
 * @see Place
 * @see Token
 */
public final class Marking {
    /** Place → FIFO queue of tokens. */
    private final Map<Place<?>, ArrayDeque<Token<?>>> tokens;

    private Marking(Map<Place<?>, ArrayDeque<Token<?>>> tokens) {
        this.tokens = tokens;
    }

    /**
     * Creates an empty marking with no tokens.
     *
     * @return empty marking
     */
    public static Marking empty() {
        return new Marking(new HashMap<>());
    }

    /**
     * Creates a marking from an initial token distribution.
     *
     * @param initial map of places to their initial tokens
     * @return marking with initial tokens
     */
    public static Marking from(Map<Place<?>, List<Token<?>>> initial) {
        var tokens = new HashMap<Place<?>, ArrayDeque<Token<?>>>();
        initial.forEach((place, list) -> {
            list.forEach((token) -> {
                if (!place.accepts(token)) {
                    throw new IllegalArgumentException("Place " + place + " does not accept token " + token);
                }
            });
            tokens.put(place, new ArrayDeque<>(list));
        });
        return new Marking(tokens);
    }

    // ======================== Bulk Operations ========================

    /**
     * Removes all tokens from all places.
     * Package-private for use by PrecompiledNetExecutor to sync from ring buffers.
     */
    void clear() {
        tokens.clear();
    }

    // ======================== Token Addition ========================

    /**
     * Adds a token to a place.
     *
     * <p>The token is added to the end of the FIFO queue for the place.
     *
     * @param <T> token value type
     * @param place destination place
     * @param token token to add
     */
    public <T> void addToken(Place<T> place, Token<T> token) {
        tokens.computeIfAbsent(place, _ -> new ArrayDeque<>()).addLast(token);
    }

    // ======================== Token Removal ========================

    /**
     * Removes and returns the oldest token from a place.
     *
     * <p>Returns {@code null} if the place has no tokens. This avoids
     * {@link Optional} allocation on hot paths.
     *
     * @param <T> token value type
     * @param place source place
     * @return oldest token, or {@code null} if empty
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> removeFirst(Place<T> place) {
        var queue = tokens.get(place);
        if (queue == null || queue.isEmpty()) {
            return null;
        }
        return (Token<T>) queue.removeFirst();
    }

    /**
     * Removes and returns the first (oldest) token in a place satisfying
     * {@code predicate}, preserving the FIFO order of the rest.
     *
     * <p>Returns {@code null} if no token matches. Used by ν-net joins to
     * consume the name-matched token rather than the oldest (NU-020).
     *
     * @param <T>       token value type
     * @param place     source place
     * @param predicate token test
     * @return the first matching token, or {@code null}
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> removeFirstMatching(Place<T> place, java.util.function.Predicate<Token<?>> predicate) {
        var queue = tokens.get(place);
        if (queue == null || queue.isEmpty()) {
            return null;
        }
        var it = queue.iterator();
        while (it.hasNext()) {
            var token = it.next();
            if (predicate.test(token)) {
                it.remove();
                return (Token<T>) token;
            }
        }
        return null;
    }

    /**
     * Removes and returns all tokens from a place.
     *
     * <p>Used for reset arcs that clear all tokens from a place.
     *
     * @param <T> token value type
     * @param place source place
     * @return list of all removed tokens (empty if place was empty)
     */
    @SuppressWarnings("unchecked")
    public <T> List<Token<T>> removeAll(Place<T> place) {
        var queue = tokens.remove(place);
        if (queue == null || queue.isEmpty()) {
            return List.of();
        }
        return (List<Token<T>>) (List<?>) new ArrayList<>(queue);
    }

    // ======================== Token Inspection ========================

    /**
     * Returns an unmodifiable view of all tokens in a place.
     *
     * <p>Zero-copy operation - returns a view, not a copy.
     *
     * @param <T> token value type
     * @param place place to inspect
     * @return unmodifiable collection of tokens (empty if place has no tokens)
     */
    @SuppressWarnings("unchecked")
    public <T> Collection<Token<T>> peekTokens(Place<T> place) {
        var queue = tokens.get(place);
        if (queue == null) return List.of();
        return (Collection<Token<T>>) (Collection<?>) Collections.unmodifiableCollection(queue);
    }

    /**
     * Returns the oldest token in a place without removing it.
     *
     * <p>Returns {@code null} if the place has no tokens.
     *
     * @param <T> token value type
     * @param place place to inspect
     * @return oldest token, or {@code null} if empty
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> peekFirst(Place<T> place) {
        var queue = tokens.get(place);
        return queue == null || queue.isEmpty() ? null : (Token<T>) queue.peekFirst();
    }

    /**
     * Checks if a place has any tokens.
     *
     * @param <T> token value type
     * @param place place to check
     * @return {@code true} if the place has at least one token
     */
    public <T> boolean hasTokens(Place<T> place) {
        var queue = tokens.get(place);
        return queue != null && !queue.isEmpty();
    }

    /**
     * Returns the number of tokens in a place.
     *
     * @param <T> token value type
     * @param place place to count
     * @return token count (0 if place has no tokens)
     */
    public <T> int tokenCount(Place<T> place) {
        var queue = tokens.get(place);
        return queue == null ? 0 : queue.size();
    }

    // ======================== Snapshotting ========================

    /**
     * Captures this marking as the structured snapshot form of <b>CORE-073</b>: place
     * <b>name</b> to the place's tokens in FIFO order ([CORE-013]).
     *
     * <p><b>Keyed by name, never by {@link Place}</b> — and the reason is load-bearing, so do
     * not "improve" it. Java's {@code Place} is a record with structural {@code (name,
     * tokenType)} equality, which makes a {@code Map<Place<?>, …>} look natural. But CORE-073
     * requires a snapshot to retain a place name the <i>receiving</i> net does not declare, and
     * for such a name there is no {@code Place} to construct and no {@code tokenType} to guess.
     * A {@code Place}-keyed snapshot cannot express the case the requirement exists for.
     *
     * <p><b>Entry type is {@link Token}</b>, not a parallel snapshot-entry type: a token
     * already <i>is</i> a value plus a {@code created_at}, and a second type with the same two
     * fields would leave Java with two identical-but-distinct snapshot forms, since
     * {@link org.libpetri.event.NetEvent.MarkingSnapshot} already carries this one.
     *
     * <p>Empty places are omitted. CORE-073 AC#7 makes that conforming — an omitted place and a
     * present-but-empty one must restore identically — so the obligation sits on
     * {@link #fromSnapshot}, which accepts both.
     *
     * <p>Key order is <b>ascending code-point order of the place name</b>, the same canonical
     * order the verification encoders use and for the same reason ([VER-013]). The form is a
     * mapping, so a restore must not depend on order — but a host that persists a snapshot will
     * diff, hash or content-address it, and the point of one normative form is that a snapshot
     * of the same marking compares equal <b>byte for byte</b> across implementations. Merely
     * <i>deterministic</i> does not buy that: two implementations each stable in their own order
     * still disagree.
     *
     * <p><b>Not {@link String#compareTo}.</b> Java's natural string order is UTF-16 <i>code
     * unit</i> order, which diverges from code-point order wherever a character above U+FFFF
     * meets one in U+E000&ndash;U+FFFF — a leading surrogate is {@code 0xD800}&ndash;{@code
     * 0xDBFF}, so an astral character sorts <i>before</i> a private-use one by code unit and
     * after it by code point. A place name carrying an emoji is enough to make Java disagree
     * with Rust and TypeScript about the same marking, and an all-ASCII test cannot see it
     * because the two orders agree there.
     *
     * <p><b>Two marked places with one name</b> — legal in Java alone, where {@code Place}
     * equality includes the token type ([MOD-024]) — share one entry: their tokens are
     * concatenated, ordered by token-type name, rather than one silently overwriting the other.
     * <b>This method never throws</b>: the executors call it on the orchestrator thread to emit
     * the {@code MarkingSnapshot} event, where a throw would abort the run or swallow its
     * completion event. The merged entry is an <i>observation</i>; it is not restorable, which
     * is why {@code executor.snapshot()}, {@link #fromSnapshot} and {@link #resolveSnapshot}
     * reject such a net on the caller's thread instead.
     *
     * @return place name to that place's tokens, FIFO order preserved, values defensively copied
     */
    public Map<String, List<Token<?>>> snapshot() {
        var result = new TreeMap<String, List<Token<?>>>(
            org.libpetri.core.internal.CodePointOrder.COMPARATOR);
        for (var entry : tokens.entrySet()) {
            if (!entry.getValue().isEmpty()
                && result.put(entry.getKey().name(), List.copyOf(entry.getValue())) != null) {
                return snapshotMergingSharedNames();
            }
        }
        return result;
    }

    /** The slow path of {@link #snapshot()}: some name is shared by two marked places. */
    private Map<String, List<Token<?>>> snapshotMergingSharedNames() {
        var entries = new ArrayList<>(tokens.entrySet());
        // HashMap order over a record hash that includes Class.hashCode() varies per JVM run.
        entries.sort(java.util.Comparator.comparing(e -> e.getKey().tokenType().getName()));
        var result = new TreeMap<String, List<Token<?>>>(
            org.libpetri.core.internal.CodePointOrder.COMPARATOR);
        for (var entry : entries) {
            if (entry.getValue().isEmpty()) continue;
            result.merge(entry.getKey().name(), List.copyOf(entry.getValue()), (first, second) -> {
                var both = new ArrayList<Token<?>>(first);
                both.addAll(second);
                return List.copyOf(both);
            });
        }
        return result;
    }

    /**
     * Restores a marking from the <b>CORE-073</b> snapshot form, resolving place names against
     * {@code places}.
     *
     * <p><b>Why this takes a second argument when TypeScript and Rust do not.</b> Their
     * {@code Place} equality is name-only, so a name alone reconstructs a usable key. Java's is
     * structural over {@code (name, tokenType)} ([MOD-024]), so a {@code Place} synthesised from
     * a name alone would <i>not</i> compare equal to the net's own {@code Place} and the
     * restored tokens would land nowhere the executor could see. Resolving against the receiving
     * net's places is what makes the restored marking usable. This is the [MOD-024] divergence
     * surfacing in a new place, not a different design.
     *
     * <p>A name {@code places} does not cover is <b>retained</b> rather than dropped, per
     * [CORE-072], under a synthesised {@code Place} of unknown token type — the tokens are inert
     * but present, so a snapshot survives a round-trip through a net that has since lost a place.
     *
     * <p>Accepts an omitted place and a present-but-empty sequence <b>identically</b> (AC#7):
     * an empty sequence contributes no tokens, exactly as absence does. Capture never emits an
     * empty sequence, so only a hand-built or foreign snapshot exercises that path — which is
     * why it is stated rather than left to a round-trip test that could never reach it.
     *
     * <p>Timestamps are carried through <b>unchanged</b>. Restoring is the one path on which the
     * engine hands back a {@code created_at} it did not choose, and re-stamping would make a
     * resume indistinguishable from a fresh start ([TIME-015]'s token-stamping boundary) — so
     * this never consults a clock, injected or otherwise.
     *
     * @param snapshot the snapshot form: place name to tokens in FIFO order
     * @param places   the receiving net's places, used to resolve names to typed places
     * @return a marking holding the snapshot's tokens, FIFO order and timestamps preserved
     * @throws IllegalArgumentException if {@code places} holds two places with one name; see
     *                                  {@link #resolveSnapshot}
     */
    public static Marking fromSnapshot(
        Map<String, List<Token<?>>> snapshot,
        java.util.Collection<Place<?>> places
    ) {
        var tokens = new HashMap<Place<?>, ArrayDeque<Token<?>>>();
        resolveSnapshot(snapshot, places).forEach((place, list) ->
            tokens.put(place, new ArrayDeque<>(list)));
        return new Marking(tokens);
    }

    /**
     * Resolves a <b>CORE-073</b> snapshot's place names against {@code places}, yielding the
     * initial-token map an executor builder takes.
     *
     * <p>Shared with {@link #fromSnapshot} so the two cannot drift: a restore routed through
     * the builder and one routed through {@code Marking} must resolve names identically, or
     * [CORE-073] AC#10 — restored tokens are visible to the net's transitions — holds on one
     * path and not the other.
     *
     * <p>A name {@code places} does not cover is retained under a synthesised
     * {@code Place.of(name, Object.class)} per [CORE-072]. {@code Object.class} accepts any
     * value, so retention never rejects a token whose type the receiving net cannot name.
     *
     * <p><b>Two places with one name are rejected</b>, whether or not the snapshot mentions
     * that name. Java permits a net to hold {@code Place.of("x", String.class)} and
     * {@code Place.of("x", Integer.class)} as distinct places ([MOD-024]); the snapshot form
     * knows only {@code "x"}, so whose tokens they are is not recoverable, and resolving to
     * whichever place iteration order offered last landed them on the wrong place or the right
     * one by luck. Rejecting on the net rather than on the collision keeps the outcome a
     * property of the net, not of what one particular snapshot happened to hold.
     *
     * @param snapshot the snapshot form: place name to tokens in FIFO order
     * @param places   the receiving net's places
     * @return typed place to tokens, FIFO order and timestamps preserved
     * @throws IllegalArgumentException if {@code places} holds two places with one name
     */
    public static Map<Place<?>, List<Token<?>>> resolveSnapshot(
        Map<String, List<Token<?>>> snapshot,
        java.util.Collection<Place<?>> places
    ) {
        var byName = new HashMap<String, Place<?>>();
        for (var p : places) {
            var other = byName.put(p.name(), p);
            if (other != null && !other.equals(p)) {
                var types = new TreeSet<>(List.of(other.tokenType().getName(), p.tokenType().getName()));
                throw new IllegalArgumentException(
                    "cannot restore a snapshot into a net declaring two places named '" + p.name()
                        + "' (" + String.join(" and ", types) + "). Java tells them apart by token type (MOD-024) but the CORE-073 "
                        + "snapshot form is keyed by place name, so which place the tokens "
                        + "belong to is not recoverable. Rename one place.");
            }
        }

        var resolved = new java.util.LinkedHashMap<Place<?>, List<Token<?>>>();
        snapshot.forEach((name, list) -> {
            var place = byName.get(name);
            if (place == null) place = Place.of(name, Object.class);
            resolved.put(place, List.copyOf(list));
        });
        return resolved;
    }

    /**
     * Returns an independent copy of this marking.
     *
     * <p>Tokens are immutable, so the copy shares them; only the per-place queues are new. The
     * executors use this to publish an owned snapshot that a monitoring thread can then read
     * without racing the live marking.
     *
     * <p><b>Not thread-safe.</b> Call only from the thread that owns this marking (the
     * orchestrator). It iterates the backing map and queues directly; a concurrent structural
     * change on another thread can make it throw or spin. Cross-thread observation goes through
     * the executor's published snapshot, not through calling this on a live marking.
     *
     * @return an independent marking that shares only the (immutable) tokens
     */
    public Marking copy() {
        var copied = new HashMap<Place<?>, ArrayDeque<Token<?>>>();
        for (var entry : tokens.entrySet()) {
            var queue = entry.getValue();
            if (queue == null || queue.isEmpty()) continue;
            copied.put(entry.getKey(), new ArrayDeque<>(queue));
        }
        return new Marking(copied);
    }

    // ======================== Debugging ========================

    /**
     * Returns a concise string representation showing place names and token counts.
     *
     * <p>Example: {@code Marking{Ready: 1, Processing: 2}}
     *
     * @return concise marking description
     */
    @Override
    public String toString() {
        return tokens.entrySet().stream()
            .filter(e -> !e.getValue().isEmpty())
            .map(e -> e.getKey().name() + ": " + e.getValue().size())
            .collect(Collectors.joining(", ", "Marking{", "}"));
    }

    /**
     * Returns a detailed multi-line description for debugging.
     *
     * <p>Shows each place with token counts and value types. Useful for
     * understanding the current state during debugging.
     *
     * <p>Example output:
     * <pre>
     * Marking:
     *   Ready: 1 token(s) [UserRequest]
     *   Processing: 2 token(s) [Task, Task]
     * </pre>
     *
     * @return detailed marking description
     */
    public String inspect() {
        if (tokens.isEmpty()) return "Marking is empty";
        return tokens.entrySet().stream()
            .filter(e -> !e.getValue().isEmpty())
            .map(e -> {
                var place = e.getKey();
                var toks = e.getValue();
                var types = toks.stream()
                    .map(t -> t.value() == null ? "null" : t.value().getClass().getSimpleName())
                    .collect(Collectors.joining(", "));
                return "  %s: %d token(s) [%s]".formatted(place.name(), toks.size(), types);
            })
            .collect(Collectors.joining("\n", "Marking:\n", ""));
    }
}
