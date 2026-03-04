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
     * Writes a complete session archive to the given output stream.
     *
     * <p>The caller is responsible for closing the output stream.
     *
     * @param session the debug session to archive
     * @param out the output stream to write to (will be LZ4-compressed)
     * @throws IOException if writing fails
     */
    public void write(DebugSession session, OutputStream out) throws IOException {
        var structure = session.buildNetStructure();

        var metadata = new SessionArchive(
            SessionArchive.CURRENT_VERSION,
            session.sessionId(),
            session.netName(),
            session.dotDiagram(),
            session.startTime(),
            session.eventStore().eventCount(),
            structure
        );

        // BufferedOutputStream(64K) batches small DataOutputStream writes into large LZ4 blocks.
        // 4MB LZ4 block size: typical sessions fit in a single block for optimal compression.
        try (var dataOut = new DataOutputStream(
                new BufferedOutputStream(
                    new LZ4FrameOutputStream(out, LZ4FrameOutputStream.BLOCKSIZE.SIZE_4MB), 65_536))) {

            // Metadata — single alloc, known size
            byte[] metaBytes = metadataMapper.writeValueAsBytes(metadata);
            dataOut.writeInt(metaBytes.length);
            dataOut.write(metaBytes);

            // Events — reusable serialization buffer, zero per-event alloc after first
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
