package org.libpetri.examples.parser.compiler;

/**
 * Persistent linked-list stack for return addresses.
 * O(1) push/pop with structural sharing — tails are reused.
 * Uses int site IDs for O(1) dispatch on return.
 */
public record CallFrame(int returnSiteId, int astDepthAtCall, CallFrame parent) {

    public static final CallFrame EMPTY = null;

    public CallFrame push(int siteId, int astDepth) {
        return new CallFrame(siteId, astDepth, this);
    }

    public int peek() {
        return returnSiteId;
    }

    public CallFrame pop() {
        return parent;
    }

    public int depth() {
        int d = 0;
        CallFrame f = this;
        while (f != null) {
            d++;
            f = f.parent;
        }
        return d;
    }
}
