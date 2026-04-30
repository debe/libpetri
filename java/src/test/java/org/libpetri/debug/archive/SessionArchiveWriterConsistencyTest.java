package org.libpetri.debug.archive;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.debug.DebugEventStore;
import org.libpetri.debug.DebugSessionRegistry;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.time.Instant;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies the EVT-025 invariant that an archive header's {@code eventCount} equals
 * the number of events actually serialized into the body, after a write→read round-trip.
 *
 * <p>Two regression cases:
 * <ul>
 *   <li><b>Eviction (Bug A):</b> when the event store evicts older events to stay under
 *       its capacity, the header must report the retained body size — not the cumulative
 *       lifetime append count carried by {@link DebugEventStore#eventCount()}.</li>
 *   <li><b>Concurrent producer (Bug B):</b> when a thread appends events while the writer
 *       is serializing, the writer must take a single atomic snapshot. Header and body
 *       both derive from that snapshot and therefore match exactly.</li>
 * </ul>
 *
 * <p>Both cases failed on libpetri ≤ 1.8.2 where header {@code eventCount} read from
 * a separate, non-atomic source compared to body iteration.
 */
class SessionArchiveWriterConsistencyTest {

    private static final Place<String> INPUT = Place.of("Input", String.class);
    private static final Place<String> OUTPUT = Place.of("Output", String.class);

    private static final PetriNet TEST_NET = PetriNet.builder("TestNet")
            .transitions(
                    Transition.builder("Process")
                            .inputs(In.one(INPUT))
                            .outputs(Out.place(OUTPUT))
                            .build()
            )
            .build();

    /**
     * Append more events than the store's capacity, forcing eviction. The header must
     * report retained-body size, not the lifetime cumulative count.
     */
    @Test
    void headerEventCountEqualsBodyAfterEviction() throws IOException {
        int cap = 10;
        int totalAppends = 100;
        var registry = new DebugSessionRegistry(16, sid -> new DebugEventStore(sid, cap));
        var session = registry.register("evict-session", TEST_NET);

        var now = Instant.now();
        for (int i = 0; i < totalAppends; i++) {
            session.eventStore().append(
                    new NetEvent.TokenAdded(now.plusMillis(i), "Output", Token.of("v" + i)));
        }

        // Sanity: the live store's cumulative counter is 100 but only 10 are retained.
        assertEquals(totalAppends, session.eventStore().eventCount(),
                "lifetime counter must reflect every append");
        assertEquals(cap, session.eventStore().size(),
                "retained queue must be capped at maxEvents");

        var bytes = writeArchive(session);

        // Header reflects the body length — not the lifetime cumulative count.
        var reader = new SessionArchiveReader();
        var header = reader.readMetadata(new ByteArrayInputStream(bytes));
        assertEquals(cap, header.eventCount(),
                "header eventCount must equal retained body size, not cumulative counter");

        // The body must contain exactly that many events when read back.
        var imported = reader.readFull(new ByteArrayInputStream(bytes));
        assertEquals(cap, imported.eventStore().events().size(),
                "body event count must match header");
        assertEquals(header.eventCount(), imported.eventStore().events().size(),
                "round-trip invariant: header.eventCount == body.size");

        // V2/V3 metadata histogram must sum to header.eventCount.
        if (header instanceof SessionArchive.V2 v2) {
            long sum = v2.metadata().eventTypeHistogram().values().stream().mapToLong(Long::longValue).sum();
            assertEquals(header.eventCount(), sum,
                    "histogram values must sum to header eventCount");
        } else if (header instanceof SessionArchive.V3 v3) {
            long sum = v3.metadata().eventTypeHistogram().values().stream().mapToLong(Long::longValue).sum();
            assertEquals(header.eventCount(), sum,
                    "histogram values must sum to header eventCount");
        }
    }

    /**
     * Stress test for the multi-snapshot temporal race (Bug B). A producer virtual
     * thread keeps appending while the writer runs; afterwards the archive must still
     * satisfy {@code header.eventCount == body.size}.
     */
    @RepeatedTest(20)
    void headerEventCountEqualsBodyUnderConcurrentAppend() throws Exception {
        // Generous cap so eviction does not interfere with the race signal.
        var registry = new DebugSessionRegistry(16, sid -> new DebugEventStore(sid, 1_000_000));
        var session = registry.register("race-session", TEST_NET);

        var stop = new AtomicBoolean(false);
        var producer = Thread.ofVirtual().start(() -> {
            long i = 0;
            var t0 = Instant.now();
            while (!stop.get()) {
                session.eventStore().append(
                        new NetEvent.TokenAdded(t0.plusNanos(i), "Output", Token.of("v" + i)));
                i++;
            }
        });

        // Let the producer build up a backlog before the writer starts.
        Thread.sleep(2);

        var bytes = writeArchive(session);

        stop.set(true);
        producer.join();

        var reader = new SessionArchiveReader();
        var header = reader.readMetadata(new ByteArrayInputStream(bytes));
        var imported = reader.readFull(new ByteArrayInputStream(bytes));

        assertTrue(header.eventCount() > 0, "expected at least one event in the snapshot");
        assertEquals(header.eventCount(), imported.eventStore().events().size(),
                "header eventCount must equal body size even under concurrent append");
    }

    private static byte[] writeArchive(DebugSessionRegistry.DebugSession session) throws IOException {
        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);
        return buf.toByteArray();
    }
}
