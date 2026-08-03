package org.libpetri.fixtures;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.Place;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;

import java.util.concurrent.CompletableFuture;

/**
 * Fixture factory for canonical subnet definitions used across the modular
 * composition test suite (MOD-010 through MOD-023).
 *
 * <p>These fixtures are deliberately minimal: each declares one or two
 * interface ports and a small body of internal places and transitions.
 * Transitions that declare an output carry a token-forwarding action, since
 * [CORE-043] rejects the passthrough default there. Tests pair them via
 * {@link org.libpetri.core.PetriNet.Builder#compose} to verify port-place
 * merging and per-instance state isolation.
 *
 * <h2>Available fixtures</h2>
 * <ul>
 *   <li>{@link #producer()} — single {@code output} port, internal
 *       {@code nextItem} place, one {@code produce} transition.</li>
 *   <li>{@link #boundedBuffer(int)} — {@code put}/{@code get} ports, internal
 *       {@code slots} capacity place pre-loaded with {@code capacity} tokens
 *       (declared structurally; the initial-marking step is the caller's
 *       responsibility), and {@code enqueue}/{@code dequeue} transitions.</li>
 *   <li>{@link #consumer()} — single {@code input} port, internal
 *       {@code consumed} sink, one {@code consume} transition.</li>
 *   <li>{@link #retryPolicy()} — single {@code attempt} sync channel
 *       (interface transition) and one internal {@code attemptCount} place
 *       written by the channel transition, used by channel-composition tests
 *       (MOD-021).</li>
 *   <li>{@link #leakyBucket(int)} — {@code request} input port, {@code accept}
 *       and {@code reject} output ports, internal {@code slots} capacity
 *       place. Used by fusion-composition tests (MOD-060/061) to model a
 *       shared rate limiter across multiple bucket instances.</li>
 * </ul>
 *
 * @see PaperNetworks
 */
public final class SubnetFixtures {

    private SubnetFixtures() { }

    /**
     * A producer subnet: one transition draws from an internal
     * {@code nextItem} place and emits to the {@code output} port. The
     * {@code nextItem} place is internal (per-instance state isolated per
     * MOD-012); callers seed it via initial marking.
     *
     * <p>Interface:
     * <ul>
     *   <li>{@code output} (Output port) — token type {@link String}</li>
     * </ul>
     *
     * @return an unparameterised producer subnet definition
     */
    public static SubnetDef<Void> producer() {
        Place<String> nextItem = Place.of("nextItem", String.class);
        Place<String> output = Place.of("output", String.class);

        Transition produce = Transition.builder("produce")
            .inputs(In.one(nextItem))
            .outputs(Out.place(output))
            .action(TransitionAction.fork())
            .build();

        return SubnetDef.builder("Producer")
            .place(nextItem)
            .transition(produce)
            .outputPort("output", output)
            .build();
    }

    /**
     * A bounded-buffer subnet of the requested capacity. {@code enqueue}
     * consumes a slot token and forwards a token from {@code put} to the
     * internal {@code items} place; {@code dequeue} returns a slot and
     * forwards from {@code items} to {@code get}.
     *
     * <p>The {@code slots} capacity place is declared structurally; the
     * caller is responsible for seeding it with {@code capacity} initial
     * tokens at execution time (initial-marking concern is caller-side per
     * the MOD-012 isolation contract).
     *
     * <p>Action-less: tokens just move through the buffer.
     *
     * <p>Interface:
     * <ul>
     *   <li>{@code put} (Input port) — token type {@link String}</li>
     *   <li>{@code get} (Output port) — token type {@link String}</li>
     * </ul>
     *
     * @param capacity declared capacity (recorded as the {@code params}-style
     *                 metadata; the caller still supplies initial tokens)
     * @return an unparameterised bounded-buffer subnet definition
     */
    public static SubnetDef<Void> boundedBuffer(int capacity) {
        if (capacity < 1) {
            throw new IllegalArgumentException("capacity must be >= 1, got: " + capacity);
        }

        Place<String> put = Place.of("put", String.class);
        Place<String> get = Place.of("get", String.class);
        Place<String> items = Place.of("items", String.class);
        Place<String> slots = Place.of("slots", String.class);

        Transition enqueue = Transition.builder("enqueue")
            .inputs(In.one(put), In.one(slots))
            .outputs(Out.place(items))
            .build();

        Transition dequeue = Transition.builder("dequeue")
            .inputs(In.one(items))
            .outputs(Out.and(get, slots))
            .build();

        return SubnetDef.builder("BoundedBuffer-" + capacity)
            .place(items)
            .place(slots)
            .transition(enqueue)
            .transition(dequeue)
            .inputPort("put", put)
            .outputPort("get", get)
            .build();
    }

    /**
     * A consumer subnet: one transition draws from the {@code input} port
     * and emits to an internal {@code consumed} sink.
     *
     * <p>Interface:
     * <ul>
     *   <li>{@code input} (Input port) — token type {@link String}</li>
     * </ul>
     *
     * @return an unparameterised consumer subnet definition
     */
    public static SubnetDef<Void> consumer() {
        Place<String> input = Place.of("input", String.class);
        Place<String> consumed = Place.of("consumed", String.class);

        Transition consume = Transition.builder("consume")
            .inputs(In.one(input))
            .outputs(Out.place(consumed))
            .action(TransitionAction.fork())
            .build();

        return SubnetDef.builder("Consumer")
            .place(consumed)
            .transition(consume)
            .inputPort("input", input)
            .build();
    }

    /**
     * A retry-policy subnet: exposes a single synchronous channel
     * {@code attempt} (interface transition) per <b>MOD-005</b> with a
     * caller-side transition fused in at compose time per <b>MOD-021</b>.
     * The channel transition produces a token to the internal
     * {@code attemptCount} place each time it fires — composing this subnet
     * lets the host net "tap" each invocation of the bound caller transition.
     *
     * <p>Body shape:
     * <pre>{@code
     *   attempt (no inputs) -> attemptCount   // structural; no action set
     * }</pre>
     *
     * <p>Action-less by default, matching the convention of the other
     * fixtures: callers bind the {@code attempt} action via
     * {@link org.libpetri.core.Instance#bindActions} when they need the
     * channel's instance-side action to do work (e.g., increment a counter).
     *
     * <p>Interface:
     * <ul>
     *   <li>{@code attempt} (Channel) — synchronous; merges with a caller-side
     *       transition at compose time.</li>
     * </ul>
     *
     * @return an unparameterised retry-policy subnet definition
     */
    /**
     * Parameter record for {@link #leakyBucket(int)} (and the parameterised
     * variant if one is added later). Carries a declared {@code rate}
     * (effective bucket capacity) and an optional {@code label} for
     * disambiguation in fusion-composition tests where multiple instances
     * share a single rate limiter.
     *
     * @param rate  declared capacity (slots place is sized for this value)
     * @param label human-readable disambiguation label (may be empty)
     */
    public record LeakyBucketParams(int rate, String label) { }

    /**
     * A leaky-bucket subnet: one transition consumes a {@code request} token
     * plus a {@code slots} token and emits to {@code accept}; a second
     * transition consumes a {@code request} token (with an inhibitor on
     * {@code slots}) and emits to {@code reject}.
     *
     * <p>The internal {@code slots} place models the per-bucket capacity:
     * fusion-composition tests (MOD-060/061) declare a fusion set across
     * the {@code slots} places of multiple bucket instances to model a
     * shared rate limiter.
     *
     * <p>Action-less by default — tokens just move through the bucket. The
     * caller seeds {@code slots} with {@code rate} initial tokens at execution
     * time (initial-marking concern is caller-side, matching {@link #boundedBuffer(int)}).
     *
     * <p>Interface:
     * <ul>
     *   <li>{@code request} (Input port) — token type {@link String}</li>
     *   <li>{@code accept} (Output port) — token type {@link String}</li>
     *   <li>{@code reject} (Output port) — token type {@link String}</li>
     * </ul>
     *
     * @param rate declared capacity (recorded as the {@code params}-style
     *             metadata; the caller still supplies initial slot tokens)
     * @return an unparameterised leaky-bucket subnet definition
     */
    public static SubnetDef<Void> leakyBucket(int rate) {
        if (rate < 1) {
            throw new IllegalArgumentException("rate must be >= 1, got: " + rate);
        }

        Place<String> request = Place.of("request", String.class);
        Place<String> accept = Place.of("accept", String.class);
        Place<String> reject = Place.of("reject", String.class);
        Place<String> slots = Place.of("slots", String.class);

        // accept-path: needs a slot, consumes the request, emits accept.
        Transition acceptT = Transition.builder("accept")
            .inputs(In.one(request), In.one(slots))
            .outputs(Out.place(accept))
            .action(ctx -> {
                ctx.output(accept, ctx.input(request));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        // reject-path: no slot available (inhibitor), still consumes request,
        // emits reject.
        Transition rejectT = Transition.builder("reject")
            .inputs(In.one(request))
            .inhibitor(slots)
            .outputs(Out.place(reject))
            .action(TransitionAction.fork())
            .build();

        return SubnetDef.builder("LeakyBucket-" + rate)
            .place(slots)
            .transitions(acceptT, rejectT)
            .inputPort("request", request)
            .outputPort("accept", accept)
            .outputPort("reject", reject)
            .build();
    }

    public static SubnetDef<Void> retryPolicy() {
        Place<String> attemptCount = Place.of("attemptCount", String.class);

        Transition attempt = Transition.builder("attempt")
            .outputs(Out.place(attemptCount))
            .build();

        return SubnetDef.builder("RetryPolicy")
            .place(attemptCount)
            .transition(attempt)
            .channel("attempt", attempt)
            .build();
    }
}
