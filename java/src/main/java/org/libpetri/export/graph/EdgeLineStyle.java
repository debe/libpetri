package org.libpetri.export.graph;

/** DOT edge line styles. */
public enum EdgeLineStyle {
    SOLID("solid"),
    DASHED("dashed"),
    BOLD("bold");

    private final String dotValue;

    EdgeLineStyle(String dotValue) {
        this.dotValue = dotValue;
    }

    /** Returns the DOT attribute value for this style. */
    public String dotValue() {
        return dotValue;
    }
}
