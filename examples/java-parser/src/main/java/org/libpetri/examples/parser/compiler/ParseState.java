package org.libpetri.examples.parser.compiler;

import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.lexer.LexToken;

import java.time.Instant;

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

    /** Push a return site ID onto the call stack. */
    public ParseState pushCall(int siteId) {
        return new ParseState(tokens, position, new CallFrame(siteId, callStack), astStack);
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
        return new ParseState(tokens, position, callStack, new AstFrame(node, astStack));
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
        return new ParseState(tokens, position, callStack, new AstFrame(node, astStack.pop()));
    }

    /** Count AST stack depth. */
    public int astDepth() {
        int d = 0;
        AstFrame f = astStack;
        while (f != null) { d++; f = f.parent(); }
        return d;
    }

    @Override
    public String toString() {
        return "ParseState[pos=" + position + "/" + tokens.length +
               ", token=" + (position < tokens.length ? tokens[position] : "EOF") +
               ", callDepth=" + (callStack != null ? callStack.depth() : 0) +
               ", astDepth=" + astDepth() + "]";
    }
}
