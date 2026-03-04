package org.libpetri.debug.archive;

import org.libpetri.debug.archive.SessionArchiveStorage.ArchivedSessionSummary;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class FileSessionArchiveStorageTest {

    @ParameterizedTest
    @ValueSource(strings = {"../../../etc/passwd", "../../etc/shadow"})
    void shouldRejectPathTraversalInSessionId(String maliciousId, @TempDir Path dir) {
        var storage = new FileSessionArchiveStorage(dir);

        assertThrows(IllegalArgumentException.class, () -> storage.storeStreaming(maliciousId, out -> {}));
        assertThrows(IllegalArgumentException.class, () -> storage.retrieve(maliciousId));
    }

    @Test
    void shouldRejectBlankSessionId(@TempDir Path dir) {
        var storage = new FileSessionArchiveStorage(dir);

        assertThrows(IllegalArgumentException.class, () -> storage.storeStreaming("", out -> {}));
        assertThrows(IllegalArgumentException.class, () -> storage.storeStreaming("  ", out -> {}));
        assertThrows(IllegalArgumentException.class, () -> storage.storeStreaming(null, out -> {}));
    }

    @Test
    void shouldStoreAndRetrieveArchive(@TempDir Path dir) throws IOException {
        var storage = new FileSessionArchiveStorage(dir);
        byte[] testData = "hello archive".getBytes();

        storage.storeStreaming("abc-123", out -> out.write(testData));

        try (var in = storage.retrieve("abc-123")) {
            assertArrayEquals(testData, in.readAllBytes());
        }
    }

    @Test
    void shouldListStoredArchives(@TempDir Path dir) throws IOException {
        var storage = new FileSessionArchiveStorage(dir);

        storage.storeStreaming("aaa-111", out -> out.write(new byte[]{1}));
        storage.storeStreaming("bbb-222", out -> out.write(new byte[]{2, 3}));

        var list = storage.list(10);
        assertEquals(2, list.size());
        var sessionIds = list.stream().map(ArchivedSessionSummary::sessionId).toList();
        assertTrue(sessionIds.contains("aaa-111"));
        assertTrue(sessionIds.contains("bbb-222"));
    }

    @Test
    void shouldThrowWhenRetrievingNonExistentSession(@TempDir Path dir) {
        var storage = new FileSessionArchiveStorage(dir);

        assertThrows(IOException.class, () -> storage.retrieve("non-existent"));
    }

    @Test
    void shouldReturnEmptyListForNonExistentDirectory() throws IOException {
        var storage = new FileSessionArchiveStorage(Path.of("/tmp/does-not-exist-" + System.nanoTime()));
        assertEquals(0, storage.list(10).size());
    }

    @Test
    void shouldAlwaysBeAvailable(@TempDir Path dir) {
        var storage = new FileSessionArchiveStorage(dir);
        assertTrue(storage.isAvailable());
    }

    @Test
    void shouldLimitListResults(@TempDir Path dir) throws IOException {
        var storage = new FileSessionArchiveStorage(dir);

        storage.storeStreaming("aaa-111", out -> out.write(new byte[]{1}));
        storage.storeStreaming("bbb-222", out -> out.write(new byte[]{2}));
        storage.storeStreaming("ccc-333", out -> out.write(new byte[]{3}));

        var list = storage.list(2);
        assertEquals(2, list.size());
    }
}
