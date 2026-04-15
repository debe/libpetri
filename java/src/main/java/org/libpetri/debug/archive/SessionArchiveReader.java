package org.libpetri.debug.archive;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
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
 * <p>The reader peeks the header's {@code version} field with a tiny lenient DTO,
 * then dispatches to the correct {@link SessionArchive} subtype. Both v1 (libpetri 1.5.x)
 * and v2 (libpetri 1.7.0+) archives are supported and may coexist in the same storage
 * bucket. Events inside the body use the same wire format across versions, so the event
 * read path is shared.
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
     * @return the archive metadata — either {@link SessionArchive.V1} or
     *         {@link SessionArchive.V2}, callers pattern-match to distinguish
     * @throws IOException if reading or parsing fails, or if the archive version is unsupported
     */
    public SessionArchive readMetadata(InputStream in) throws IOException {
        try (var dataIn = new DataInputStream(
                new BufferedInputStream(
                    new LZ4FrameInputStream(in), 65_536))) {
            return readHeader(dataIn);
        }
    }

    /**
     * Reads the full archive: metadata + all events into a {@link DebugEventStore}.
     *
     * <p>The returned {@link ImportedSession} exposes the header as a {@link SessionArchive}
     * reference — callers that care about v2-only fields (tags, endTime, metadata) should
     * pattern-match on {@link SessionArchive.V2}; v1 archives report default empty/null
     * values for those accessors.
     *
     * @param in the input stream (LZ4-compressed binary)
     * @return the imported session with metadata and populated event store
     * @throws IOException if reading or parsing fails
     */
    public ImportedSession readFull(InputStream in) throws IOException {
        try (var dataIn = new DataInputStream(
                new BufferedInputStream(
                    new LZ4FrameInputStream(in), 65_536))) {

            var metadata = readHeader(dataIn);

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
     * Peeks the archive {@code version}, then deserializes the header bytes into the
     * matching {@link SessionArchive} subtype. Java 25 pattern switch makes future
     * versions an explicit compile-time decision.
     */
    private SessionArchive readHeader(DataInputStream dataIn) throws IOException {
        int metaLen = dataIn.readInt();
        if (metaLen <= 0 || metaLen > MAX_EVENT_SIZE) {
            throw new IOException("Invalid metadata size: " + metaLen);
        }
        byte[] metaBytes = new byte[metaLen];
        dataIn.readFully(metaBytes);

        var probe = metadataMapper.readValue(metaBytes, VersionProbe.class);
        return switch (probe.version()) {
            case 1 -> metadataMapper.readValue(metaBytes, SessionArchive.V1.class);
            case 2 -> metadataMapper.readValue(metaBytes, SessionArchive.V2.class);
            default -> throw new IOException(
                "Unsupported archive version: " + probe.version()
                    + " (reader supports " + SessionArchive.MIN_SUPPORTED_VERSION
                    + ".." + SessionArchive.CURRENT_VERSION + ")");
        };
    }

    /**
     * Lenient DTO used to peek the archive {@code version} before full header parsing.
     * All other fields are ignored — this record only needs to decode the integer tag.
     */
    @JsonIgnoreProperties(ignoreUnknown = true)
    private record VersionProbe(int version) {}

    /**
     * Result of reading a full archive.
     *
     * @param metadata the archive metadata header (v1 or v2)
     * @param eventStore populated event store with all archived events
     */
    public record ImportedSession(SessionArchive metadata, DebugEventStore eventStore) {}
}
