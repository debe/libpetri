package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link TransitionContext}.
 */
class TransitionContextTest {

    record TestValue(String data) {}
    record AnotherValue(int count) {}

    private static final Place<TestValue> INPUT_PLACE = Place.of("Input", TestValue.class);
    private static final Place<TestValue> OUTPUT_PLACE = Place.of("Output", TestValue.class);
    private static final Place<TestValue> READ_PLACE = Place.of("Read", TestValue.class);

    private Transition createTestTransition() {
        return Transition.builder("TestTransition")
                .inputs(Arc.In.one(INPUT_PLACE))
                .outputs(Arc.Out.and(OUTPUT_PLACE))
                .read(READ_PLACE)
                .action(TransitionAction.passthrough())
                .build();
    }

    // ==================== Execution Context Tests ====================

    @Test
    void executionContext_withEmptyContext_returnsNull() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var ctx = new TransitionContext(transition, input, new TokenOutput());

        assertNull(ctx.executionContext(String.class));
    }

    @Test
    void executionContext_withContext_returnsValue() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var executionContext = Map.<Class<?>, Object>of(String.class, "test-value");
        var ctx = new TransitionContext(transition, input, new TokenOutput(), executionContext);

        assertEquals("test-value", ctx.executionContext(String.class));
    }

    @Test
    void executionContext_withMultipleContexts_returnsCorrectValue() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var executionContext = Map.<Class<?>, Object>of(
                String.class, "string-value",
                Integer.class, 42,
                TestValue.class, new TestValue("context-value")
        );
        var ctx = new TransitionContext(transition, input, new TokenOutput(), executionContext);

        assertEquals("string-value", ctx.executionContext(String.class));
        assertEquals(42, ctx.executionContext(Integer.class));
        assertEquals(new TestValue("context-value"), ctx.executionContext(TestValue.class));
    }

    @Test
    void hasExecutionContext_withEmptyContext_returnsFalse() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var ctx = new TransitionContext(transition, input, new TokenOutput());

        assertFalse(ctx.hasExecutionContext(String.class));
    }

    @Test
    void hasExecutionContext_withPresentContext_returnsTrue() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var executionContext = Map.<Class<?>, Object>of(String.class, "test-value");
        var ctx = new TransitionContext(transition, input, new TokenOutput(), executionContext);

        assertTrue(ctx.hasExecutionContext(String.class));
        assertFalse(ctx.hasExecutionContext(Integer.class));
    }

    @Test
    void executionContext_isImmutable() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));
        var mutableMap = new java.util.HashMap<Class<?>, Object>();
        mutableMap.put(String.class, "original");
        var ctx = new TransitionContext(transition, input, new TokenOutput(), mutableMap);

        // Modify the original map
        mutableMap.put(String.class, "modified");
        mutableMap.put(Integer.class, 123);

        // TransitionContext should still have the original value
        assertEquals("original", ctx.executionContext(String.class));
        assertFalse(ctx.hasExecutionContext(Integer.class));
    }

    @Test
    void constructor_withNullExecutionContext_throwsNullPointerException() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));

        assertThrows(NullPointerException.class, () ->
                new TransitionContext(transition, input, new TokenOutput(), null)
        );
    }

    // ==================== SpanContext Interface Tests ====================

    @Test
    void executionContext_withSpanContext_canBeRetrieved() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("test")));

        // Create a mock SpanContext implementation
        SpanContext mockSpanContext = new SpanContext() {
            @Override public void makeCurrent() {}
            @Override public void setAttribute(String key, String value) {}
            @Override public void setAttribute(String key, long value) {}
            @Override public void recordException(Throwable exception) {}
            @Override public void addEvent(String name) {}
            @Override public void closeScope() {}
        };

        var executionContext = Map.<Class<?>, Object>of(SpanContext.class, mockSpanContext);
        var ctx = new TransitionContext(transition, input, new TokenOutput(), executionContext);

        assertTrue(ctx.hasExecutionContext(SpanContext.class));
        assertSame(mockSpanContext, ctx.executionContext(SpanContext.class));
    }

    // ==================== Bulk Output Tests ====================

    @Test
    void output_varargs_addsAllValuesInOrder() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var output = new TokenOutput();
        var ctx = new TransitionContext(transition, input, output);

        ctx.output(OUTPUT_PLACE, new TestValue("a"), new TestValue("b"), new TestValue("c"));

        var entries = output.entries();
        assertEquals(3, entries.size());
        assertEquals(new TestValue("a"), entries.get(0).token().value());
        assertEquals(new TestValue("b"), entries.get(1).token().value());
        assertEquals(new TestValue("c"), entries.get(2).token().value());
        assertEquals(OUTPUT_PLACE, entries.get(0).place());
    }

    @Test
    void output_varargs_emptyIsNoOp() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var output = new TokenOutput();
        var ctx = new TransitionContext(transition, input, output);

        ctx.output(OUTPUT_PLACE, new TestValue[0]);

        assertTrue(output.entries().isEmpty());
    }

    @Test
    void output_varargs_undeclaredPlaceThrows() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var ctx = new TransitionContext(transition, input, new TokenOutput());
        var foreign = Place.of("Foreign", TestValue.class);

        assertThrows(IllegalArgumentException.class,
                () -> ctx.output(foreign, new TestValue("a"), new TestValue("b")));
    }

    @Test
    void output_iterable_addsAllValuesInOrder() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var output = new TokenOutput();
        var ctx = new TransitionContext(transition, input, output);

        ctx.output(OUTPUT_PLACE, List.of(
                new TestValue("x"),
                new TestValue("y"),
                new TestValue("z")));

        var entries = output.entries();
        assertEquals(3, entries.size());
        assertEquals(new TestValue("x"), entries.get(0).token().value());
        assertEquals(new TestValue("y"), entries.get(1).token().value());
        assertEquals(new TestValue("z"), entries.get(2).token().value());
    }

    @Test
    void output_iterable_emptyIsNoOp() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var output = new TokenOutput();
        var ctx = new TransitionContext(transition, input, output);

        ctx.output(OUTPUT_PLACE, List.<TestValue>of());

        assertTrue(output.entries().isEmpty());
    }

    @Test
    void output_iterable_undeclaredPlaceThrows() {
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var ctx = new TransitionContext(transition, input, new TokenOutput());
        var foreign = Place.of("Foreign", TestValue.class);

        assertThrows(IllegalArgumentException.class,
                () -> ctx.output(foreign, List.of(new TestValue("a"))));
    }

    @Test
    void output_singleValueOverloadStillPreferred() {
        // Strict-match resolution (JLS §15.12.2.5) should route single-value calls
        // to the non-varargs output(Place, T) overload unchanged.
        var transition = createTestTransition();
        var input = new TokenInput();
        input.add(INPUT_PLACE, Token.of(new TestValue("in")));
        var output = new TokenOutput();
        var ctx = new TransitionContext(transition, input, output);

        ctx.output(OUTPUT_PLACE, new TestValue("single"));

        assertEquals(1, output.entries().size());
        assertEquals(new TestValue("single"), output.entries().get(0).token().value());
    }
}
