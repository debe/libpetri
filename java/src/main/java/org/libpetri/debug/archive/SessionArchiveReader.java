package org.libpetri.debug.archive;

import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import net.jpountz.lz4.LZ4FrameInputStream;
import org.libpetri.debug.DebugEventStore;
import org.libpetri.debug.NetEventSerializer;

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.EOFException;
import java.io.IOException;
import java.io.InputStream;

/**
 * Reads session archives from length-prefixed binary format.
 *
 * <p>Format (inside LZ4 frame):
 * <pre>
 * [4 bytes: metadata JSON length][N bytes: metadata JSON]
 * [4 bytes: event JSON length][N bytes: event JSON]
 * ...
 * (EOF terminates the stream)
 * </pre>
 *
 * <p>The read path reuses a single byte buffer that grows to the maximum event size,
 * eliminating per-event allocations.
 *
 * @see SessionArchiveWriter
 */
public final class SessionArchiveReader {

    private static final int MAX_EVENT_SIZE = 10 * 1024 * 1024; // 10 MB

    private final ObjectMapper metadataMapper;
    private final NetEventSerializer eventSerializer;

    public SessionArchiveReader() {
        this.metadataMapper = new ObjectMapper();
        this.metadataMapper.registerModule(new JavaTimeModule());
        this.metadataMapper.disable(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES);
        this.eventSerializer = new NetEventSerializer();
    }

    /**
     * Reads only the metadata header from an archive.
     *
     * @param in the input stream (LZ4-compressed binary)
     * @return the archive metadata
     * @throws IOException if reading or parsing fails
     */
    public SessionArchive readMetadata(InputStream in) throws IOException {
        try (var dataIn = new DataInputStream(
                new BufferedInputStream(
                    new LZ4FrameInputStream(in), 65_536))) {
            int metaLen = dataIn.readInt();
            byte[] metaBytes = new byte[metaLen];
            dataIn.readFully(metaBytes);
            var metadata = metadataMapper.readValue(metaBytes, SessionArchive.class);
            if (metadata.version() != SessionArchive.CURRENT_VERSION) {
                throw new IOException("Unsupported archive version: " + metadata.version()
                        + " (expected " + SessionArchive.CURRENT_VERSION + ")");
            }
            return metadata;
        }
    }

    /**
     * Reads the full archive: metadata + all events into a {@link DebugEventStore}.
     *
     * @param in the input stream (LZ4-compressed binary)
     * @return the imported session with metadata and populated event store
     * @throws IOException if reading or parsing fails
     */
    public ImportedSession readFull(InputStream in) throws IOException {
        try (var dataIn = new DataInputStream(
                new BufferedInputStream(
                    new LZ4FrameInputStream(in), 65_536))) {

            // Metadata — exact-sized alloc
            int metaLen = dataIn.readInt();
            byte[] metaBytes = new byte[metaLen];
            dataIn.readFully(metaBytes);
            var metadata = metadataMapper.readValue(metaBytes, SessionArchive.class);
            if (metadata.version() != SessionArchive.CURRENT_VERSION) {
                throw new IOException("Unsupported archive version: " + metadata.version()
                        + " (expected " + SessionArchive.CURRENT_VERSION + ")");
            }

            // Events — reusable buffer, grows to max event size then stays
            var eventStore = new DebugEventStore(metadata.sessionId(), Integer.MAX_VALUE);
            byte[] eventBuf = new byte[512];
            while (true) {
                int eventLen;
                try {
                    eventLen = dataIn.readInt();
                } catch (EOFException _) {
                    break;
                }
                if (eventLen <= 0 || eventLen > MAX_EVENT_SIZE) {
                    throw new IOException("Invalid event size: " + eventLen);
                }
                if (eventLen > eventBuf.length) {
                    eventBuf = new byte[eventLen];
                }
                dataIn.readFully(eventBuf, 0, eventLen);
                eventStore.append(eventSerializer.deserialize(eventBuf, 0, eventLen));
            }

            return new ImportedSession(metadata, eventStore);
        }
    }

    /**
     * Result of reading a full archive.
     *
     * @param metadata the archive metadata header
     * @param eventStore populated event store with all archived events
     */
    public record ImportedSession(SessionArchive metadata, DebugEventStore eventStore) {}
}
