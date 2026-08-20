package org.libpetri.doclet;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Drift gate for the mirrored viewer bundle.
 *
 * <p>{@code typescript/src/viewer/} is the single source of truth, but three
 * consumers ship a <em>copy</em> of the built bundle as
 * {@code petrinet-diagrams.{js,css}}: this module's
 * {@code src/main/resources/javadoc/}, {@code rust/libpetri-docgen/resources/},
 * and {@code typescript/src/doclet/resources/}.
 * {@code scripts/build-viewer.sh} distributes all three and records the
 * canonical digests in {@code spec/viewer-bundle.sha256}.
 *
 * <p>Nothing forced a rebuild before, so a consumer could sit on an old bundle
 * indefinitely and quietly render an old viewer. That is how a generated doc
 * page ends up with Graphviz-routed diagonal edges long after the ELK
 * orthogonal routing shipped, with nothing on the page to say so.
 *
 * <p>When this fails, the fix is {@code scripts/build-viewer.sh}. The resource
 * files are build outputs and must never be hand-edited.
 */
class ViewerBundleDriftTest {

    @ParameterizedTest
    @ValueSource(strings = {"petrinet-diagrams.js", "petrinet-diagrams.css"})
    void classpathResourceMatchesCanonicalDigest(String filename) {
        String expected = canonicalDigests().get(filename);
        assertNotNull(expected, "spec/viewer-bundle.sha256 has no entry for " + filename);

        assertEquals(
            expected,
            sha256(readClasspathResource(filename)),
            filename + " is stale — run scripts/build-viewer.sh "
                + "(do not hand-edit build outputs)");
    }

    /**
     * Cheap canary independent of the digests: the orthogonal edge routing
     * draws ELK's own routes under Graphviz {@code nop2}. A bundle predating
     * that renders ELK-placed nodes joined by diagonal splines, which reads as
     * a styling preference rather than a stale build.
     */
    @Test
    void bundleShipsOrthogonalRouting() {
        String js = new String(readClasspathResource("petrinet-diagrams.js"), StandardCharsets.UTF_8);
        assertTrue(js.contains("nop2"), "viewer bundle predates orthogonal edge routing");
    }

    private static byte[] readClasspathResource(String filename) {
        // The classpath copy is what actually ships in the jar, so hashing it
        // catches a stale source file and a stale build alike.
        try (InputStream in = ViewerBundleDriftTest.class.getResourceAsStream("/javadoc/" + filename)) {
            assertNotNull(in, "missing classpath resource /javadoc/" + filename);
            return in.readAllBytes();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Parses the {@code <sha256>  <filename>} lines written by build-viewer.sh. */
    private static Map<String, String> canonicalDigests() {
        Map<String, String> digests = new HashMap<>();
        try {
            for (String line : Files.readAllLines(locateChecksums())) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                String[] parts = trimmed.split("\\s+", 2);
                if (parts.length != 2) {
                    throw new IllegalStateException(
                        "malformed line in spec/viewer-bundle.sha256: " + line);
                }
                digests.put(parts[1].trim(), parts[0]);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return digests;
    }

    /**
     * Resolves the checksum file upward from the module directory (surefire
     * runs with cwd {@code java/}, so the first hit is
     * {@code ../spec/viewer-bundle.sha256}).
     */
    private static Path locateChecksums() {
        Path dir = Path.of("").toAbsolutePath();
        for (int depth = 0; dir != null && depth < 8; depth++, dir = dir.getParent()) {
            Path candidate = dir.resolve("spec").resolve("viewer-bundle.sha256");
            if (Files.isRegularFile(candidate)) {
                return candidate;
            }
        }
        throw new IllegalStateException(
            "could not locate spec/viewer-bundle.sha256 upward from "
                + Path.of("").toAbsolutePath());
    }

    private static String sha256(byte[] bytes) {
        try {
            return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(bytes));
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 unavailable", e);
        }
    }
}
