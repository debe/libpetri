package org.libpetri.export.graph;

/** DOT node shapes. */
public enum NodeShape {
    CIRCLE("circle"),
    DOUBLECIRCLE("doublecircle"),
    BOX("box"),
    DIAMOND("diamond"),
    ELLIPSE("ellipse"),
    RECORD("record");

    private final String dotValue;

    NodeShape(String dotValue) {
        this.dotValue = dotValue;
    }

    /** Returns the DOT attribute value for this shape. */
    public String dotValue() {
        return dotValue;
    }
}
