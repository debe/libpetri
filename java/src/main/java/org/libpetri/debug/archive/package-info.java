/**
 * Session archive storage and serialization for Petri net debug sessions.
 *
 * <p>This package provides LZ4-compressed binary archival of debug sessions,
 * enabling offline replay and long-term storage. Key components:
 *
 * <ul>
 *   <li>{@link org.libpetri.debug.archive.SessionArchiveWriter} — writes sessions to compressed binary format</li>
 *   <li>{@link org.libpetri.debug.archive.SessionArchiveReader} — reads archives back, supports metadata-only reads</li>
 *   <li>{@link org.libpetri.debug.archive.SessionArchiveStorage} — pluggable storage backend interface</li>
 *   <li>{@link org.libpetri.debug.archive.FileSessionArchiveStorage} — filesystem backend</li>
 *   <li>{@link org.libpetri.debug.archive.NoOpArchiveStorage} — no-op fallback when archival is disabled</li>
 * </ul>
 *
 * @see org.libpetri.debug.SessionCompletionListener
 * @see org.libpetri.debug.DebugSessionRegistry
 */
package org.libpetri.debug.archive;
