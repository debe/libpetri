package org.libpetri.examples.parser.compiler;

import org.libpetri.examples.parser.ast.AstNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Persistent linked-list stack for AST node accumulation.
 * O(1) push/pop with structural sharing.
 */
public record AstFrame(AstNode node, int depth, AstFrame parent) {

    public static final AstFrame EMPTY = null;

    static AstFrame of(AstNode node, AstFrame parent) {
        int d = (parent == null ? 0 : parent.depth) + 1;
        return new AstFrame(node, d, parent);
    }

    public AstFrame push(AstNode n) {
        return AstFrame.of(n, this);
    }

    public AstNode peek() {
        return node;
    }

    public AstFrame pop() {
        return parent;
    }

    /** Collect all nodes from top to bottom (most recently pushed first). */
    public List<AstNode> toList() {
        var result = new ArrayList<AstNode>();
        AstFrame f = this;
        while (f != null) {
            result.add(f.node);
            f = f.parent;
        }
        return result;
    }

    /** Collect all nodes in reverse (first pushed first). */
    public List<AstNode> toListReversed() {
        var list = toList();
        Collections.reverse(list);
        return list;
    }

    // depth is stored as a field — O(1) access
}
