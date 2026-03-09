package org.libpetri.examples.parser.compiler;

import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.lexer.LexToken;

import java.time.Instant;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The coloured token flowing through the parser Petri net.
 * Immutable record with persistent data structures for O(1) operations.
 *
 * <p>Per transition firing: 1 ParseState (~32 bytes) + 1 CallFrame or AstFrame (~16 bytes).
 * All short-lived, young-gen friendly. No array copying, no HashMap, no string allocation.
 */
public record ParseState(
    LexToken[] tokens,      // full token stream (shared array ref)
    int position,            // current index into tokens
    CallFrame callStack,     // persistent linked list for return addresses
    AstFrame astStack        // persistent linked list for AST accumulation
) {

    /** Fixed timestamp to avoid system clock calls on every transition. */
    public static final Instant EPOCH = Instant.EPOCH;

    /** Create initial parse state from a token stream. */
    public static ParseState initial(LexToken[] tokens) {
        return new ParseState(tokens, 0, null, null);
    }

    /** Current token (or EOF sentinel). */
    public LexToken current() {
        if (position >= tokens.length) {
            return tokens[tokens.length - 1]; // EOF
        }
        return tokens[position];
    }

    /** Whether we've consumed all tokens (at EOF). */
    public boolean atEnd() {
        return position >= tokens.length - 1; // last token is EOF
    }

    /** Advance position by 1. */
    public ParseState advance() {
        return new ParseState(tokens, position + 1, callStack, astStack);
    }

    /** Push a return site ID onto the call stack, capturing current AST depth. */
    public ParseState pushCall(int siteId) {
        return new ParseState(tokens, position, new CallFrame(siteId, astDepth(), callStack), astStack);
    }

    /** Pop the call stack and return the site ID. */
    public int peekReturnSite() {
        if (callStack == null) throw new IllegalStateException("Call stack is empty");
        return callStack.peek();
    }

    public ParseState popCall() {
        if (callStack == null) throw new IllegalStateException("Call stack is empty");
        return new ParseState(tokens, position, callStack.pop(), astStack);
    }

    /** Push an AST node. */
    public ParseState pushAst(AstNode node) {
        return new ParseState(tokens, position, callStack, AstFrame.of(node, astStack));
    }

    /** Pop an AST node. */
    public AstNode peekAst() {
        if (astStack == null) throw new IllegalStateException("AST stack is empty");
        return astStack.peek();
    }

    public ParseState popAst() {
        if (astStack == null) throw new IllegalStateException("AST stack is empty");
        return new ParseState(tokens, position, callStack, astStack.pop());
    }

    /** Replace the top AST node. */
    public ParseState replaceTopAst(AstNode node) {
        if (astStack == null) throw new IllegalStateException("AST stack is empty");
        return new ParseState(tokens, position, callStack, AstFrame.of(node, astStack.pop()));
    }

    /**
     * Reduce AST nodes pushed since the current call frame was entered.
     * Pops children from the stack and wraps them in a GenericNode.
     */
    public ParseState reduceAst(String productionName) {
        if (callStack == null) throw new IllegalStateException("Call stack is empty during reduce");
        int depthAtCall = callStack.astDepthAtCall();
        int currentDepth = astDepth();
        int childCount = currentDepth - depthAtCall;

        if (childCount == 0) {
            // No children pushed — push an empty GenericNode
            return pushAst(new AstNode.GenericNode(productionName, List.of()));
        }

        // Collect children (they are in reverse order on the stack)
        var children = new ArrayList<AstNode>(childCount);
        AstFrame frame = astStack;
        for (int i = 0; i < childCount; i++) {
            children.add(frame.peek());
            frame = frame.pop();
        }
        Collections.reverse(children);

        // Replace the children with a single GenericNode
        return new ParseState(tokens, position, callStack,
            AstFrame.of(new AstNode.GenericNode(productionName, children), frame));
    }

    /** Count AST stack depth — O(1) via cached depth in AstFrame. */
    public int astDepth() {
        return astStack == null ? 0 : astStack.depth();
    }

    @Override
    public String toString() {
        return "ParseState[pos=" + position + "/" + tokens.length +
               ", token=" + (position < tokens.length ? tokens[position] : "EOF") +
               ", callDepth=" + (callStack != null ? callStack.depth() : 0) +
               ", astDepth=" + astDepth() + "]";
    }
}
