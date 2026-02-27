package org.libpetri.export.graph;

/** DOT arrowhead shapes. */
public enum ArrowHead {
    NORMAL("normal"),
    ODOT("odot"),
    NONE("none"),
    DIAMOND("diamond"),
    DOT("dot");

    private final String dotValue;

    ArrowHead(String dotValue) {
        this.dotValue = dotValue;
    }

    /** Returns the DOT attribute value for this arrowhead. */
    public String dotValue() {
        return dotValue;
    }
}
