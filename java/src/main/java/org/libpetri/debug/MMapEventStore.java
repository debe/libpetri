package org.libpetri.debug;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.ReentrantLock;

import org.libpetri.event.NetEvent;

/**
 * File-backed event store using memory-mapped files for persistence.
 *
 * <p>Extends {@link DebugEventStore} by writing serialized events to a memory-mapped file
 * before storing them in memory. This provides:
 * <ul>
 *   <li><strong>Persistence:</strong> Events survive process restarts</li>
 *   <li><strong>Recovery:</strong> Re-opening a file replays events into the in-memory store</li>
 *   <li><strong>Performance:</strong> OS-managed page cache handles I/O</li>
 * </ul>
 *
 * <h2>File Format</h2>
 * <p>Append-only with a simple header:
 * <pre>
 * [8 bytes: write position (long)]
 * [4 bytes: length][N bytes: JSON]...
 * [4 bytes: length][N bytes: JSON]...
 * </pre>
 *
 * <h2>Concurrency</h2>
 * <p>Uses lock-free slot claiming via {@link AtomicLong#getAndAdd(long)} for append operations.
 * Each writer atomically claims a non-overlapping region, then writes without contention.
 * A {@link ReentrantLock} is used only for the rare grow path (file expansion).
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * // Create a new store
 * var store = MMapEventStore.open("session-123", Path.of("/tmp/debug"));
 * store.append(event); // writes to file + in-memory
 *
 * // Later: reopen and replay
 * var store2 = MMapEventStore.open("session-123", Path.of("/tmp/debug"));
 * // store2.events() contains all previously written events
 *
 * store2.close(); // releases mmap resources
 * }</pre>
 *
 * @see DebugEventStore
 * @see NetEventSerializer
 */
public class MMapEventStore extends DebugEventStore implements AutoCloseable {

    private static final Logger LOG = System.getLogger(MMapEventStore.class.getName());

    /** Header size: 8 bytes for write position. */
    private static final int HEADER_SIZE = 8;

    /** Initial file size: 4 MB. */
    private static final int INITIAL_SIZE = 4 * 1024 * 1024;

    private final Path filePath;
    private final NetEventSerializer serializer;
    private final AtomicLong writePosition = new AtomicLong(HEADER_SIZE);
    private final ReentrantLock growLock = new ReentrantLock();
    private FileChannel channel;
    private volatile MappedByteBuffer buffer;
    private volatile int fileSize;

    private MMapEventStore(String sessionId, Path filePath, NetEventSerializer serializer) {
        super(sessionId);
        this.filePath = filePath;
        this.serializer = serializer;
    }

    /**
     * Opens or creates an MMap-backed event store.
     *
     * <p>If the file already exists, events are replayed into the in-memory store.
     * If the file does not exist, a new one is created with the initial capacity.
     *
     * @param sessionId the debug session identifier
     * @param directory the directory to store files in (will be created if absent)
     * @return a new MMapEventStore
     * @throws UncheckedIOException if file operations fail
     */
    public static MMapEventStore open(String sessionId, Path directory) {
        try {
            Files.createDirectories(directory);
            var filePath = directory.resolve(sessionId + ".events");
            var serializer = new NetEventSerializer();
            var store = new MMapEventStore(sessionId, filePath, serializer);
            store.initFile();
            return store;
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to open MMap event store for session: " + sessionId, e);
        }
    }

    private void initFile() throws IOException {
        boolean existing = Files.exists(filePath);

        channel = FileChannel.open(filePath,
            StandardOpenOption.CREATE, StandardOpenOption.READ, StandardOpenOption.WRITE);

        if (existing && channel.size() >= HEADER_SIZE) {
            fileSize = (int) channel.size();
            buffer = channel.map(FileChannel.MapMode.READ_WRITE, 0, fileSize);
            replayFromFile();
        } else {
            fileSize = INITIAL_SIZE;
            channel.truncate(fileSize); // pre-allocate but this may not extend, so write zeros
            // Force the file to the desired size
            channel.write(ByteBuffer.allocate(1), fileSize - 1);
            buffer = channel.map(FileChannel.MapMode.READ_WRITE, 0, fileSize);
            writePosition.set(HEADER_SIZE);
        }
    }

    private void replayFromFile() {
        long writePos = buffer.getLong(0);
        int pos = HEADER_SIZE;
        int recovered = 0;

        while (pos + 4 <= writePos && pos + 4 <= fileSize) {
            int length = buffer.getInt(pos);
            if (length <= 0 || pos + 4 + length > writePos) {
                int offset = pos;
                int count = recovered;
                LOG.log(Level.WARNING, () -> "Corrupt or truncated event at offset " + offset
                        + ", stopping replay (" + count + " events recovered)");
                break;
            }

            byte[] data = new byte[length];
            buffer.get(pos + 4, data);
            pos += 4 + length;

            try {
                NetEvent event = serializer.deserialize(data);
                super.append(event); // replay into in-memory store
                recovered++;
            } catch (Exception e) {
                int failedOffset = pos;
                LOG.log(Level.WARNING, () -> "Failed to deserialize event at offset " + failedOffset + ", stopping replay", e);
                break;
            }
        }

        // Initialize writePosition from file for continued appending
        writePosition.set(writePos);
    }

    @Override
    public void append(NetEvent event) {
        try {
            byte[] data = serializer.serialize(event);
            int required = 4 + data.length;

            // 1. Claim exclusive slot (lock-free, single atomic op)
            long pos = writePosition.getAndAdd(required);

            // 2. Ensure capacity (rare path — lock only when growing)
            MappedByteBuffer buf = this.buffer;
            if (pos + required > buf.capacity()) {
                buf = ensureCapacity(pos + required);
            }

            // 3. Write to claimed slot (lock-free — non-overlapping regions)
            buf.putInt((int) pos, data.length);
            buf.put((int) pos + 4, data);
        } catch (NetEventSerializer.NetEventSerializationException e) {
            LOG.log(Level.WARNING, () -> "Failed to serialize event to mmap, skipping persistence: "
                + event.getClass().getSimpleName(), e);
        }

        // Always store in-memory + broadcast, even if mmap persistence failed
        super.append(event);
    }

    /**
     * Ensures the buffer has at least {@code minSize} bytes of capacity.
     * Uses a lock since growth is rare and must be coordinated.
     *
     * @param minSize minimum required file/buffer size
     * @return the (possibly new) buffer with sufficient capacity
     */
    private MappedByteBuffer ensureCapacity(long minSize) {
        growLock.lock();
        try {
            // Another thread may have already grown
            if (minSize <= fileSize) {
                return buffer;
            }
            grow(minSize);
            return buffer;
        } finally {
            growLock.unlock();
        }
    }

    /**
     * Grows the backing file and remaps the buffer.
     *
     * <p><strong>Note:</strong> The old {@link MappedByteBuffer} is replaced without explicit unmap.
     * The JDK provides no public unmap API prior to Java 22's {@code MemorySegment}.
     * The old buffer remains valid (maps the same file pages via OS mmap coherence) until GC
     * reclaims it. This is acceptable for a debug tool where grows are rare.
     *
     * <!-- TODO: Migrate to MemorySegment (Java 22+) for deterministic unmap when the project
     *      moves to a MemorySegment-based API. This would also enable Arena-scoped lifecycle. -->
     */
    private void grow(long minSize) {
        try {
            int newSize = fileSize;
            while (newSize < minSize) {
                newSize *= 2;
            }

            // Force-flush existing buffer before remapping
            buffer.force();

            // Extend the file
            channel.write(ByteBuffer.allocate(1), newSize - 1);

            // Re-map (old MappedByteBuffer released by GC — see method Javadoc)
            buffer = channel.map(FileChannel.MapMode.READ_WRITE, 0, newSize);
            fileSize = newSize;
        } catch (IOException e) {
            throw new UncheckedIOException("Failed to grow MMap file", e);
        }
    }

    /**
     * Returns the path to the backing file.
     *
     * @return the file path
     */
    public Path filePath() {
        return filePath;
    }

    @Override
    public void close() {
        shutdownBroadcast();
        try {
            if (buffer != null) {
                // Flush final write position to header for replay on reopen
                buffer.putLong(0, writePosition.get());
                buffer.force();
            }
            if (channel != null && channel.isOpen()) {
                channel.close();
            }
        } catch (IOException e) {
            LOG.log(Level.WARNING, "Error closing MMap event store", e);
        }
    }
}
