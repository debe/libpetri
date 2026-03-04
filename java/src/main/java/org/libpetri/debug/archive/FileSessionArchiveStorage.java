package org.libpetri.debug.archive;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * File-system backed storage for session archives.
 *
 * <p>Stores archives at {@code {directory}/{prefix}/{sessionId}.archive.lz4}
 * where prefix is the first character of the session ID (UUID hex digit -> 16 folders).
 */
public class FileSessionArchiveStorage implements SessionArchiveStorage {

    private static final String EXTENSION = ".archive.lz4";
    private final Path directory;

    public FileSessionArchiveStorage(Path directory) {
        this.directory = directory;
    }

    @Override
    public void storeStreaming(String sessionId, OutputStreamConsumer writer) throws IOException {
        var target = archivePath(sessionId);
        Files.createDirectories(target.getParent());
        try (var out = Files.newOutputStream(target)) {
            writer.writeTo(out);
        }
    }

    @Override
    public List<ArchivedSessionSummary> list(int limit) throws IOException {
        return list(limit, null);
    }

    @Override
    public List<ArchivedSessionSummary> list(int limit, String prefix) throws IOException {
        if (!Files.isDirectory(directory)) {
            return List.of();
        }

        var results = new ArrayList<ArchivedSessionSummary>();
        try (DirectoryStream<Path> prefixDirs = Files.newDirectoryStream(directory)) {
            for (Path prefixDir : prefixDirs) {
                if (!Files.isDirectory(prefixDir)) continue;
                // Skip subdirectories that can't contain matches
                if (prefix != null && !prefix.isBlank()) {
                    var dirName = prefixDir.getFileName().toString();
                    if (dirName.length() == 1 && dirName.charAt(0) != prefix.charAt(0)) continue;
                }
                try (DirectoryStream<Path> files = Files.newDirectoryStream(prefixDir, "*" + EXTENSION)) {
                    for (Path file : files) {
                        var fileName = file.getFileName().toString();
                        var sessionId = fileName.substring(0, fileName.length() - EXTENSION.length());
                        if (prefix != null && !prefix.isBlank() && !sessionId.startsWith(prefix)) continue;
                        var attrs = Files.readAttributes(file, java.nio.file.attribute.BasicFileAttributes.class);
                        results.add(new ArchivedSessionSummary(
                                sessionId,
                                directory.relativize(file).toString(),
                                attrs.size(),
                                attrs.lastModifiedTime().toInstant()
                        ));
                    }
                }
            }
        }

        results.sort(Comparator.comparing(ArchivedSessionSummary::lastModified).reversed());
        return results.size() > limit ? results.subList(0, limit) : results;
    }

    @Override
    public InputStream retrieve(String sessionId) throws IOException {
        var path = archivePath(sessionId);
        if (!Files.exists(path)) {
            throw new IOException("Archive not found for session: " + sessionId);
        }
        return Files.newInputStream(path);
    }

    @Override
    public boolean isAvailable() {
        return true;
    }

    private Path archivePath(String sessionId) {
        if (sessionId == null || sessionId.isBlank()) {
            throw new IllegalArgumentException("Invalid session ID: " + sessionId);
        }
        String prefix = sessionId.substring(0, 1);
        var resolved = directory.resolve(prefix).resolve(sessionId + EXTENSION).normalize();
        if (!resolved.startsWith(directory)) {
            throw new IllegalArgumentException("Session ID escapes archive directory: " + sessionId);
        }
        return resolved;
    }
}
