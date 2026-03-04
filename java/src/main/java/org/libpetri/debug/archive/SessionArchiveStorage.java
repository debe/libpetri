package org.libpetri.debug.archive;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.time.Instant;
import java.util.List;

/**
 * Storage backend for session archives.
 *
 * <p>Implementations provide persistence for LZ4-compressed binary archive files,
 * supporting store, list, and retrieve operations.
 *
 * @see SessionArchiveWriter
 * @see SessionArchiveReader
 */
public interface SessionArchiveStorage {

    /**
     * Consumer that writes archive data to an output stream.
     */
    @FunctionalInterface
    interface OutputStreamConsumer {
        void writeTo(OutputStream out) throws IOException;
    }

    /**
     * Stores an archive by streaming data through the provided consumer.
     *
     * <p>The consumer writes archive data directly to the storage-provided output stream,
     * avoiding intermediate heap buffering.
     *
     * @param sessionId the session identifier (used as filename base)
     * @param writer consumer that writes archive data to the output stream
     * @throws IOException if storage fails
     */
    void storeStreaming(String sessionId, OutputStreamConsumer writer) throws IOException;

    /**
     * Lists archived sessions, most recent first.
     *
     * @param limit maximum number of entries to return
     * @return list of archived session summaries
     * @throws IOException if listing fails
     */
    List<ArchivedSessionSummary> list(int limit) throws IOException;

    /**
     * Lists archived sessions filtered by session ID prefix, most recent first.
     *
     * @param limit maximum number of entries to return
     * @param prefix session ID prefix to filter by (null or blank for no filtering)
     * @return list of matching archived session summaries
     * @throws IOException if listing fails
     */
    default List<ArchivedSessionSummary> list(int limit, String prefix) throws IOException {
        if (prefix == null || prefix.isBlank()) return list(limit);
        return list(limit).stream()
                .filter(s -> s.sessionId().startsWith(prefix))
                .toList();
    }

    /**
     * Retrieves an archive by session ID.
     *
     * @param sessionId the session identifier
     * @return input stream for the archive data (caller must close)
     * @throws IOException if retrieval fails or session not found
     */
    InputStream retrieve(String sessionId) throws IOException;

    /**
     * Checks if this storage backend is available and configured.
     *
     * @return true if the backend can accept operations
     */
    boolean isAvailable();

    /**
     * Summary of an archived session for listing.
     *
     * @param sessionId the session identifier
     * @param key the storage key/path
     * @param sizeBytes file size in bytes
     * @param lastModified when the archive was last modified
     */
    record ArchivedSessionSummary(String sessionId, String key, long sizeBytes, Instant lastModified) {}
}
