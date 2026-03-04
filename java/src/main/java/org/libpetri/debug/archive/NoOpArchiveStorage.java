package org.libpetri.debug.archive;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

/**
 * No-op archive storage for when archival is disabled.
 *
 * <p>All write operations are silently ignored, list returns empty,
 * and retrieve throws since no archives exist.
 */
public class NoOpArchiveStorage implements SessionArchiveStorage {

    @Override
    public void storeStreaming(String sessionId, OutputStreamConsumer writer) {
        // intentionally empty
    }

    @Override
    public List<ArchivedSessionSummary> list(int limit) {
        return List.of();
    }

    @Override
    public InputStream retrieve(String sessionId) throws IOException {
        throw new IOException("Archive storage is not available");
    }

    @Override
    public boolean isAvailable() {
        return false;
    }
}
