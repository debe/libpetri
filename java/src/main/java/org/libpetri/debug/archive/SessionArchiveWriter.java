package org.libpetri.debug.archive;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import net.jpountz.lz4.LZ4FrameOutputStream;
import org.libpetri.debug.DebugSessionRegistry.DebugSession;
import org.libpetri.debug.NetEventSerializer;

import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Map;

/**
 * Writes a debug session to a length-prefixed binary archive format.
 *
 * <p>Format (inside LZ4 frame):
 * <pre>
 * [4 bytes: metadata JSON length][N bytes: metadata JSON]
 * [4 bytes: event JSON length][N bytes: event JSON]
 * ...
 * (EOF terminates the stream)
 * </pre>
 *
 * <p>The write path is designed for zero per-event heap allocations after the first event:
 * a reusable {@link ByteArrayOutputStream} holds Jackson's serialization output, and
 * {@link ByteArrayOutputStream#writeTo(OutputStream)} transfers bytes without copying.
 *
 * <h2>Format selection</h2>
 * <p>{@link #write(DebugSession, OutputStream)} defaults to {@link SessionArchive#CURRENT_VERSION}
 * (v2 as of libpetri 1.7.0). Callers that need to emit legacy archives — e.g., compatibility
 * tests or downstream writers that haven't upgraded their reader — can call
 * {@link #writeV1(DebugSession, OutputStream)}. v2 archives cost one extra pass over the
 * event store to pre-compute {@link SessionMetadata}; the savings at read time (no event
 * scan needed to answer hasErrors / histogram queries) pay it back the first time a caller
 * lists or samples a bucket of sessions.
 *
 * @see SessionArchiveReader
 */
public final class SessionArchiveWriter {

    private final ObjectMapper metadataMapper;
    private final NetEventSerializer eventSerializer;

    public SessionArchiveWriter() {
        this.metadataMapper = new ObjectMapper();
        this.metadataMapper.registerModule(new JavaTimeModule());
        this.metadataMapper.disable(SerializationFeature.WRITE_DATES_AS_TIMESTAMPS);
        this.eventSerializer = new NetEventSerializer();
    }

    /**
     * Writes a complete session archive in the current archive format
     * ({@link SessionArchive#CURRENT_VERSION}, which is v2 as of libpetri 1.7.0).
     *
     * <p>The caller is responsible for closing the output stream.
     *
     * @param session the debug session to archive
     * @param out the output stream to write to (will be LZ4-compressed)
     * @throws IOException if writing fails
     */
    public void write(DebugSession session, OutputStream out) throws IOException {
        writeV2(session, out);
    }

    /**
     * Writes a session in the legacy v1 format. Use only for compatibility testing
     * or when producing archives for consumers pinned to libpetri ≤ 1.5.3.
     */
    public void writeV1(DebugSession session, OutputStream out) throws IOException {
        var header = new SessionArchive.V1(
            1,
            session.sessionId(),
            session.netName(),
            session.dotDiagram(),
            session.startTime(),
            session.eventStore().eventCount(),
            session.buildNetStructure()
        );
        writeFramed(header, session, out);
    }

    /**
     * Writes a session in the v2 format — richer header with {@code endTime}, {@code tags},
     * and pre-computed {@link SessionMetadata} (event-type histogram, first/last event
     * timestamps, {@code hasErrors} flag).
     *
     * <p>Requires two passes over the event store: one to compute {@code SessionMetadata},
     * one to serialize events into the archive. The {@link org.libpetri.debug.DebugEventStore}
     * returns a fresh iterator from {@code eventIterator()} each call, so this is safe.
     * The metadata pass touches each event as a single {@code getClass() + timestamp()}
     * read — cheap compared to the JSON serialization pass.
     */
    public void writeV2(DebugSession session, OutputStream out) throws IOException {
        var eventStore = session.eventStore();

        // First pass: aggregate stats. Single allocation for the histogram map.
        var metadata = SessionMetadata.computeFrom(eventStore::eventIterator);

        var header = new SessionArchive.V2(
            2,
            session.sessionId(),
            session.netName(),
            session.dotDiagram(),
            session.startTime(),
            session.endTime(),
            eventStore.eventCount(),
            // Snapshot of tags at archive-write time — record the tag state that was current
            // when the session was archived, not whatever happens on the live session after.
            Map.copyOf(session.tags()),
            metadata,
            session.buildNetStructure()
        );

        writeFramed(header, session, out);
    }

    /**
     * Shared framing logic: LZ4 wrap, write length-prefixed header JSON, then
     * length-prefixed event JSON one by one.
     */
    private void writeFramed(SessionArchive header, DebugSession session, OutputStream out) throws IOException {
        // BufferedOutputStream(64K) batches small DataOutputStream writes into large LZ4 blocks.
        // 4MB LZ4 block size: typical sessions fit in a single block for optimal compression.
        try (var dataOut = new DataOutputStream(
                new BufferedOutputStream(
                    new LZ4FrameOutputStream(out, LZ4FrameOutputStream.BLOCKSIZE.SIZE_4MB), 65_536))) {

            // Header — single alloc, known size. Jackson serializes the concrete record type
            // (V1 or V2), so v1 bytes remain backwards-compatible with old readers.
            byte[] metaBytes = metadataMapper.writeValueAsBytes(header);
            dataOut.writeInt(metaBytes.length);
            dataOut.write(metaBytes);

            // Events — reusable serialization buffer, zero per-event alloc after first.
            // Both v1 and v2 archives use the identical event wire format.
            var serializeBuf = new ByteArrayOutputStream(512);
            var it = session.eventStore().eventIterator();
            while (it.hasNext()) {
                serializeBuf.reset();
                eventSerializer.serializeTo(it.next(), serializeBuf);
                dataOut.writeInt(serializeBuf.size());
                serializeBuf.writeTo(dataOut);
            }
        }
    }
}
