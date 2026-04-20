package org.libpetri.debug.archive;

import com.fasterxml.jackson.annotation.JsonInclude;
import org.libpetri.debug.DebugResponse;

import java.time.Instant;
import java.util.Map;

/**
 * Metadata header for a session archive file. Sealed across format versions so
 * callers can exhaustively pattern-match on {@link V1} and {@link V2}.
 *
 * <p>Serialized as the first length-prefixed entry in an LZ4-compressed binary archive.
 *
 * <h2>Version contract</h2>
 * <ul>
 *   <li><b>v1</b> (libpetri 1.5.x): original format. Header carries
 *       {@code sessionId}, {@code netName}, {@code dotDiagram}, {@code startTime},
 *       {@code eventCount}, and net {@code structure}.</li>
 *   <li><b>v2</b> (libpetri 1.7.x): adds {@code endTime}, user-defined {@code tags},
 *       and pre-computed {@link SessionMetadata} (event-type histogram, first/last event
 *       timestamps, hasErrors). Events inside v2 archives use the toString-based token
 *       format — types are erased on disk.</li>
 *   <li><b>v3</b> (libpetri 1.8.0+): same header as v2. Differs in the event body: token
 *       values are serialized as structured JSON with an explicit {@code valueType} (FQN)
 *       and a {@code v} payload, so readers on the same classpath can reconstruct the
 *       original token type. See {@link org.libpetri.debug.NetEventSerializer} for wire
 *       format details. Unit tokens emit {@code {"valueType":"void"}} with no {@code v}
 *       for compact disk usage.</li>
 * </ul>
 *
 * <p>The {@link SessionArchiveReader} peeks the {@code version} field, dispatches to the
 * correct record type, and returns a unified {@link SessionArchive} reference. All
 * accessors defined here work for every version; v2/v3-only accessors like {@link #tags()}
 * return empty defaults for v1.
 *
 * @see SessionMetadata
 * @see SessionArchiveReader
 * @see SessionArchiveWriter
 */
public sealed interface SessionArchive permits SessionArchive.V1, SessionArchive.V2, SessionArchive.V3 {

    /** Archive format version this record represents. */
    int version();

    /** Unique session identifier — stable across archive versions. */
    String sessionId();

    /** Name of the Petri net that was executed. */
    String netName();

    /** DOT (Graphviz) diagram source of the net topology. */
    String dotDiagram();

    /** Instant the session started. Never null. */
    Instant startTime();

    /** Total number of events in the archive body. */
    long eventCount();

    /** Net topology with authoritative name→graphId mappings. */
    DebugResponse.NetStructure structure();

    /**
     * Instant the session ended. Always null for v1 archives, nullable for active sessions
     * archived while running, otherwise populated in v2.
     */
    default Instant endTime() {
        return null;
    }

    /**
     * User-defined session tags (e.g., {@code channel=voice}). Always an empty map for v1.
     * Callers can distinguish "no tags" from "v1 archive" via {@link #version()} if needed.
     */
    default Map<String, String> tags() {
        return Map.of();
    }

    /**
     * Pre-computed aggregate stats. {@code null} for v1 (use
     * {@link SessionMetadata#fromEvents} to compute on demand).
     */
    default SessionMetadata metadata() {
        return null;
    }

    /** Convenience: computes session duration in milliseconds if {@code endTime} is set. */
    default Long durationMs() {
        return endTime() == null
            ? null
            : java.time.Duration.between(startTime(), endTime()).toMillis();
    }

    /** Version written by {@link SessionArchiveWriter#write} by default (latest supported). */
    int CURRENT_VERSION = 3;

    /** Lowest version {@link SessionArchiveReader} can decode. */
    int MIN_SUPPORTED_VERSION = 1;

    /**
     * Legacy archive header from libpetri 1.5.x. Kept for read-path compatibility —
     * {@link SessionArchiveWriter} defaults to writing {@link V2} in 1.7.0+, but v1 archives
     * written by older clients remain fully readable.
     */
    @JsonInclude(JsonInclude.Include.NON_NULL)
    record V1(
        int version,
        String sessionId,
        String netName,
        String dotDiagram,
        Instant startTime,
        long eventCount,
        DebugResponse.NetStructure structure
    ) implements SessionArchive {
        public V1 {
            if (version != 1) {
                throw new IllegalArgumentException("V1 archive must have version=1, got " + version);
            }
        }
    }

    /**
     * v2 archive header (libpetri 1.7.x). Adds end time, tags, and pre-computed metadata
     * so listing tools and samplers can filter/aggregate without scanning the event body.
     *
     * <p>Events in v2 archives use the toString-based token format. Emitted by
     * {@link SessionArchiveWriter#writeV2} only; new writes default to {@link V3}.
     */
    @JsonInclude(JsonInclude.Include.NON_NULL)
    record V2(
        int version,
        String sessionId,
        String netName,
        String dotDiagram,
        Instant startTime,
        Instant endTime,
        long eventCount,
        Map<String, String> tags,
        SessionMetadata metadata,
        DebugResponse.NetStructure structure
    ) implements SessionArchive {
        public V2 {
            if (version != 2) {
                throw new IllegalArgumentException("V2 archive must have version=2, got " + version);
            }
            // Normalize: never store nulls for the collection-shaped fields.
            tags = tags == null ? Map.of() : Map.copyOf(tags);
            if (metadata == null) {
                metadata = SessionMetadata.empty();
            }
        }
    }

    /**
     * v3 archive header (libpetri 1.8.0+). Structurally identical to {@link V2} — the
     * format-version bump signals that the event body uses the structured
     * (typed) token serialization instead of the legacy toString form.
     *
     * <p>Split as a separate sealed subtype rather than piggy-backing on {@code V2} so
     * archive consumers can pattern-match on the writer's semantic guarantee: v3 tokens
     * are reconstructible on a classpath that carries the original value types.
     */
    @JsonInclude(JsonInclude.Include.NON_NULL)
    record V3(
        int version,
        String sessionId,
        String netName,
        String dotDiagram,
        Instant startTime,
        Instant endTime,
        long eventCount,
        Map<String, String> tags,
        SessionMetadata metadata,
        DebugResponse.NetStructure structure
    ) implements SessionArchive {
        public V3 {
            if (version != 3) {
                throw new IllegalArgumentException("V3 archive must have version=3, got " + version);
            }
            tags = tags == null ? Map.of() : Map.copyOf(tags);
            if (metadata == null) {
                metadata = SessionMetadata.empty();
            }
        }
    }
}
