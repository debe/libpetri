package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link Instance} — the materialised module instance produced by
 * {@link SubnetDef#instantiate(String, Object)}.
 *
 * <p>Covers MOD-010 (rename pass), MOD-011 (typed handle map), MOD-012
 * (per-instance state isolation), and MOD-030 (action binding —
 * share-by-default + per-instance override via {@link Instance#bindActions}).
 */
class InstanceTest {

    record Item(String tag) {}

    // ============================================================
    //  Constructor surface
    // ============================================================

    @Test
    void constructor_isPackagePrivate_notInvokableByUserCode() {
        var constructors = Instance.class.getDeclaredConstructors();
        assertEquals(1, constructors.length);
        assertFalse(java.lang.reflect.Modifier.isPublic(constructors[0].getModifiers()),
            "Instance constructor must NOT be public — instances are produced by SubnetDef.instantiate");
        assertFalse(java.lang.reflect.Modifier.isProtected(constructors[0].getModifiers()),
            "Instance constructor must NOT be protected");
    }

    @Test
    void accessors_returnConstructorValues() {
        var def = simpleDef();
        var inst = def.instantiate("p1");
        assertEquals("p1", inst.prefix());
        assertNull(inst.params(), "Void-parameterised instance carries null params");
        assertSame(def, inst.def());
        assertNotNull(inst.renamedBody());
        var descriptor = inst.descriptor();
        assertEquals("p1", descriptor.prefix());
        assertEquals(inst.def().name(), descriptor.defName());
    }

    // ============================================================
    //  MOD-010: rename pass
    // ============================================================

    @Test
    void instantiate_returnsRenamedBody() {
        var def = simpleDef();
        var inst = def.instantiate("buf1");

        // Every place name in renamedBody must start with "buf1/".
        for (var place : inst.renamedBody().places()) {
            assertTrue(place.name().startsWith("buf1/"),
                "place name '" + place.name() + "' must be prefixed with 'buf1/'");
        }
        // Every transition name in renamedBody must start with "buf1/".
        for (var t : inst.renamedBody().transitions()) {
            assertTrue(t.name().startsWith("buf1/"),
                "transition name '" + t.name() + "' must be prefixed with 'buf1/'");
        }
        // Renamed net's name itself follows the same convention.
        assertTrue(inst.renamedBody().name().startsWith("buf1/"));
    }

    @Test
    void instantiate_renamedArcsReferenceRenamedPlaces() {
        // Per MOD-010: arc topology preserved, but every place reference is rewritten.
        var def = simpleDef();
        var inst = def.instantiate("r1");

        for (var t : inst.renamedBody().transitions()) {
            for (var arc : t.inputSpecs()) {
                assertTrue(arc.place().name().startsWith("r1/"),
                    "arc place '" + arc.place().name() + "' must be prefixed");
            }
            if (t.outputSpec() != null) {
                for (var p : t.outputSpec().allPlaces()) {
                    assertTrue(p.name().startsWith("r1/"),
                        "output place '" + p.name() + "' must be prefixed");
                }
            }
        }
    }

    // ============================================================
    //  MOD-011: typed handle map
    // ============================================================

    @Test
    void instantiate_handleMap_returnsRenamedPort() {
        Place<String> input = Place.of("input", String.class);
        Place<String> output = Place.of("output", String.class);
        Transition fwd = Transition.builder("fwd")
            .inputs(Arc.In.one(input))
            .outputs(Arc.Out.and(output))
            .build();
        var def = SubnetDef.builder("Forwarder")
            .transition(fwd)
            .inputPort("input", input)
            .outputPort("output", output)
            .build();

        var inst = def.instantiate("r1");
        Place<String> renamedInput = inst.port("input", String.class);
        assertEquals("r1/input", renamedInput.name(), "port handle must point to renamed place");
        assertEquals(String.class, renamedInput.tokenType());

        // Channel handle similarly resolves to renamed transition.
        var def2 = SubnetDef.builder("WithCh")
            .transition(fwd)
            .channel("attempt", fwd)
            .build();
        var inst2 = def2.instantiate("c1");
        var renamedAttempt = inst2.channel("attempt");
        assertEquals("c1/fwd", renamedAttempt.name());
    }

    @Test
    void port_typeMismatch_isRejected() {
        Place<String> input = Place.of("input", String.class);
        Transition t = Transition.builder("t").read(input).build();
        var def = SubnetDef.builder("S")
            .transition(t)
            .inputPort("input", input)
            .build();

        var inst = def.instantiate("p1");
        var ex = assertThrows(IllegalArgumentException.class,
            () -> inst.port("input", Integer.class));
        assertTrue(ex.getMessage().contains("input"));
    }

    @Test
    void port_unknownName_isRejected() {
        var inst = simpleDef().instantiate("p1");
        var ex = assertThrows(IllegalArgumentException.class,
            () -> inst.port("missing", String.class));
        assertTrue(ex.getMessage().contains("missing"));
    }

    @Test
    void channel_unknownName_isRejected() {
        var inst = simpleDef().instantiate("p1");
        var ex = assertThrows(IllegalArgumentException.class, () -> inst.channel("missing"));
        assertTrue(ex.getMessage().contains("missing"));
    }

    // ============================================================
    //  MOD-012: per-instance state isolation
    // ============================================================

    @Test
    void instantiate_perInstanceStateIsolation() {
        // Two instances of the same SubnetDef must have disjoint place sets.
        var def = simpleDef();
        var a = def.instantiate("b1");
        var b = def.instantiate("b2");

        var aPlaces = a.renamedBody().places();
        var bPlaces = b.renamedBody().places();

        // Disjointness by record-equality (Place is a record, equals on (name, tokenType)).
        for (var p : aPlaces) {
            assertFalse(bPlaces.contains(p),
                "instance b1 place '" + p.name() + "' must not appear in instance b2's place set");
        }
        for (var p : bPlaces) {
            assertFalse(aPlaces.contains(p),
                "instance b2 place '" + p.name() + "' must not appear in instance b1's place set");
        }
    }

    // ============================================================
    //  MOD-030: actions shared by reference; per-instance override
    // ============================================================

    @Test
    void instantiate_actionsSharedByReference() {
        // Build a transition with an explicit (non-passthrough) action.
        Place<String> p = Place.of("p", String.class);
        TransitionAction sharedAction = ctx -> CompletableFuture.completedFuture(null);
        Transition t = Transition.builder("t").read(p).action(sharedAction).build();

        var def = SubnetDef.builder("S").transition(t).build();
        var i1 = def.instantiate("a");
        var i2 = def.instantiate("b");

        var t1 = onlyTransition(i1);
        var t2 = onlyTransition(i2);

        assertSame(sharedAction, t1.action(), "instance 1 transition must hold the shared action object");
        assertSame(sharedAction, t2.action(), "instance 2 transition must hold the shared action object");
        assertSame(t1.action(), t2.action(),
            "MOD-030: actions are share-by-default across instances of the same SubnetDef");
    }

    @Test
    void bindActions_overridesOnlyForThisInstance() {
        Place<String> p = Place.of("p", String.class);
        TransitionAction defaultAction = ctx -> CompletableFuture.completedFuture(null);
        Transition t = Transition.builder("produce").read(p).action(defaultAction).build();

        var def = SubnetDef.builder("S").transition(t).build();
        var i1 = def.instantiate("p1");
        var i2 = def.instantiate("p2");

        TransitionAction override = ctx -> CompletableFuture.completedFuture(null);
        var i1bound = i1.bindActions(Map.of("produce", override));

        // i1bound's transition has the override.
        assertSame(override, onlyTransition(i1bound).action(),
            "bindActions must replace the action on the named transition");

        // Original i1 unchanged (returned a new Instance).
        assertSame(defaultAction, onlyTransition(i1).action(),
            "bindActions must NOT mutate the original instance");

        // i2 (a sibling instance) is untouched.
        assertSame(defaultAction, onlyTransition(i2).action(),
            "bindActions on i1 must NOT affect i2");
    }

    @Test
    void bindActions_unknownOriginalName_isRejected() {
        var def = simpleDef();
        var inst = def.instantiate("p1");
        TransitionAction action = ctx -> CompletableFuture.completedFuture(null);
        var ex = assertThrows(IllegalArgumentException.class,
            () -> inst.bindActions(Map.of("ghost", action)));
        assertTrue(ex.getMessage().contains("ghost"));
    }

    @Test
    void bindActions_emptyMap_isNoop_returnsSameInstance() {
        var inst = simpleDef().instantiate("p1");
        var rebound = inst.bindActions(Map.of());
        assertSame(inst, rebound, "empty bindActions must short-circuit and return the same instance");
    }

    @Test
    void bindActions_partialOverride_leavesUnnamedTransitionsAlone() {
        Place<String> p = Place.of("p", String.class);
        TransitionAction shared = ctx -> CompletableFuture.completedFuture(null);
        Transition t1 = Transition.builder("t1").read(p).action(shared).build();
        Transition t2 = Transition.builder("t2").read(p).action(shared).build();

        var def = SubnetDef.builder("S").transitions(t1, t2).build();
        var inst = def.instantiate("i");

        TransitionAction override = ctx -> CompletableFuture.completedFuture(null);
        var rebound = inst.bindActions(Map.of("t1", override));

        Transition r1 = transitionByName(rebound, "i/t1");
        Transition r2 = transitionByName(rebound, "i/t2");
        assertSame(override, r1.action(), "t1 must carry override");
        assertSame(shared,   r2.action(), "t2 must retain shared default");
    }

    // ============================================================
    //  Prefix validation (MOD-010 separator reservation)
    // ============================================================

    @Test
    void instantiate_throwsOnPrefixWithSlash() {
        var def = simpleDef();
        var ex = assertThrows(IllegalArgumentException.class, () -> def.instantiate("a/b"));
        assertTrue(ex.getMessage().contains("/") || ex.getMessage().toLowerCase().contains("prefix"));
    }

    @Test
    void instantiate_throwsOnNullPrefix() {
        assertThrows(IllegalArgumentException.class, () -> simpleDef().instantiate(null));
    }

    @Test
    void instantiate_throwsOnEmptyPrefix() {
        assertThrows(IllegalArgumentException.class, () -> simpleDef().instantiate(""));
    }

    // ============================================================
    //  Parameterised instance
    // ============================================================

    record MyParams(int n, String tag) {}

    @Test
    void instantiate_paramsAreAccessible() {
        Place<String> p = Place.of("p", String.class);
        Transition t = Transition.builder("t").read(p).build();
        SubnetDef<MyParams> def = SubnetDef.builder("Param", MyParams.class)
            .transition(t)
            .build();
        var params = new MyParams(7, "x");
        Instance<MyParams> inst = def.instantiate("p1", params);
        assertSame(params, inst.params());
    }

    // ============================================================
    //  Side-effect verification: actions still wire through
    // ============================================================

    @Test
    void boundAction_isExecutedWhenActionInvoked() {
        // Smoke-check: the rebound action object is the one that runs when invoked
        // via TransitionAction.execute (we don't drag in the executor here; this just
        // verifies the indirection isn't lost across bindActions + Instance copy).
        Place<String> p = Place.of("p", String.class);
        AtomicInteger counter = new AtomicInteger(0);
        TransitionAction shared = ctx -> {
            counter.incrementAndGet();
            return CompletableFuture.completedFuture(null);
        };
        Transition t = Transition.builder("produce").read(p).action(shared).build();
        var def = SubnetDef.builder("S").transition(t).build();
        var inst = def.instantiate("p1");

        // Run the shared action directly through the renamed transition.
        // We pass null for the context — the lambda doesn't touch it, this only
        // proves the action object reference itself was carried through.
        var bound = onlyTransition(inst);
        bound.action().execute(null);
        assertEquals(1, counter.get(), "renamed transition's action must invoke the shared lambda");
    }

    // ============================================================
    //  Helpers
    // ============================================================

    private static SubnetDef<Void> simpleDef() {
        Place<String> p = Place.of("p", String.class);
        Transition t = Transition.builder("t").read(p).build();
        return SubnetDef.builder("S").transition(t).build();
    }

    private static Transition onlyTransition(Instance<?> inst) {
        var ts = inst.renamedBody().transitions();
        assertEquals(1, ts.size(), "test helper expects exactly one transition");
        return ts.iterator().next();
    }

    private static Transition transitionByName(Instance<?> inst, String name) {
        for (var t : inst.renamedBody().transitions()) {
            if (t.name().equals(name)) return t;
        }
        throw new AssertionError("no transition named '" + name + "' in instance");
    }
}
