package org.libpetri.smt.z3;

import java.util.regex.Pattern;

/**
 * A z3 release version, ordered numerically (VER-013).
 *
 * @param major major version
 * @param minor minor version
 * @param patch patch version ({@code 0} when the probe reported only two components)
 */
public record Z3Version(int major, int minor, int patch) implements Comparable<Z3Version> {

    private static final Pattern VERSION_LINE =
        Pattern.compile("Z3 version (\\d+)\\.(\\d+)(?:\\.(\\d+))?");

    /**
     * Parses the version out of a {@code z3 --version} reply
     * ({@code Z3 version 4.16.0 - 64 bit}); {@code null} when the text carries none.
     */
    public static Z3Version parse(String text) {
        if (text == null) {
            return null;
        }
        var m = VERSION_LINE.matcher(text);
        if (!m.find()) {
            return null;
        }
        try {
            int major = Integer.parseInt(m.group(1));
            int minor = Integer.parseInt(m.group(2));
            int patch = m.group(3) == null ? 0 : Integer.parseInt(m.group(3));
            return new Z3Version(major, minor, patch);
        } catch (NumberFormatException _) {
            return null;
        }
    }

    @Override
    public int compareTo(Z3Version other) {
        int c = Integer.compare(major, other.major);
        if (c != 0) {
            return c;
        }
        c = Integer.compare(minor, other.minor);
        if (c != 0) {
            return c;
        }
        return Integer.compare(patch, other.patch);
    }

    @Override
    public String toString() {
        return major + "." + minor + "." + patch;
    }
}
