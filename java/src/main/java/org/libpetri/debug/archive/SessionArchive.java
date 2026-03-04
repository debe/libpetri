package org.libpetri.debug.archive;

import org.libpetri.debug.DebugResponse;

import java.time.Instant;

/**
 * Metadata header for a session archive file.
 *
 * <p>This is serialized as the first length-prefixed entry in an LZ4-compressed binary archive.
 *
 * @param version archive format version (currently 1)
 * @param sessionId unique session identifier
 * @param netName name of the Petri net
 * @param dotDiagram DOT (Graphviz) diagram source
 * @param startTime when the session started
 * @param eventCount total number of events in the archive
 * @param structure net topology (places and transitions with graph ID mappings)
 */
public record SessionArchive(
    int version,
    String sessionId,
    String netName,
    String dotDiagram,
    Instant startTime,
    long eventCount,
    DebugResponse.NetStructure structure
) {
    /** Current archive format version. */
    public static final int CURRENT_VERSION = 1;
}
