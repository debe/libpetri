package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.fixtures.SubnetFixtures;
import org.libpetri.runtime.BitmapNetExecutor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link FusionSet} resolution at {@link PetriNet.Builder#build()}
 * per <b>MOD-061</b> (fusion resolution), exercising the structural rewrite
 * that substitutes non-canonical members with the canonical member in every
 * arc of every transition in the builder.
 *
 * <p>Coverage:
 * <ul>
 *   <li>Single-set substitution: arcs originally referencing non-canonical
 *       members now reference the canonical member; non-canonical members
 *       are absent from the built net's place set.</li>
 *   <li>Independence: places not in any fusion set are untouched.</li>
 *   <li>Overlap detection: a place appearing in two fusion sets is rejected
 *       at {@code build()}.</li>
 *   <li>Three-way fusion of leaky-bucket {@code slots} places: shared rate
 *       limiter behavior verified end-to-end via the executor.</li>
 *   <li>Order independence: {@code fuse(...)} BEFORE {@code compose(...)}
 *       produces the same result as {@code fuse(...)} AFTER.</li>
 *   <li>Orthogonality with channel composition: a fusion set + a channel
 *       binding both apply correctly in one builder.</li>
 *   <li>Compose-then-fuse equals fuse-then-compose (structural equivalence).</li>
 * </ul>
 */
class FusionTest {

    // ============================================================
    //  MOD-061: single fusion set substitutes non-canonical → canonical
    // ============================================================

    @Test
    void fuse_substitutesNonCanonicalInArcs() {
        Place<String> a = Place.of("A", String.class);  // canonical
        Place<String> b = Place.of("B", String.class);  // non-canonical
        Place<String> sink = Place.of("sink", String.class);

        // T1 reads from B (non-canonical) → after fuse, reads from A.
        Transition t1 = Transition.builder("readFromB")
            .read(b)
            .build();
        // T2 writes to B (non-canonical) → after fuse, writes to A.
        Transition t2 = Transition.builder("writeToB")
            .inputs(Arc.In.one(sink))
            .outputs(Arc.Out.place(b))
            .build();

        var net = PetriNet.builder("Fused")
            .transitions(t1, t2)
            .fuse(FusionSet.of("ab", a, b))
            .build();

        // Place set: A and sink survive; B does not.
        assertTrue(net.places().contains(a), "canonical place A must survive");
        assertTrue(net.places().contains(sink), "unrelated place sink must survive");
        assertFalse(net.places().contains(b),
            "non-canonical place B must be removed from the place set (MOD-061)");

        // Find the rewritten transitions and verify their arcs reference A.
        var readFromB = findTransition(net, "readFromB");
        assertTrue(readFromB.readPlaces().contains(a),
            "T1 must read from canonical A after fusion. Reads: " + readFromB.readPlaces());
        assertFalse(readFromB.readPlaces().contains(b),
            "T1 must not reference non-canonical B");

        var writeToB = findTransition(net, "writeToB");
        assertTrue(writeToB.outputPlaces().contains(a),
            "T2 must write to canonical A after fusion. Outputs: " + writeToB.outputPlaces());
        assertFalse(writeToB.outputPlaces().contains(b),
            "T2 must not reference non-canonical B");
    }

    // ============================================================
    //  Unrelated places are untouched
    // ============================================================

    @Test
    void fuse_unrelatedPlaces_unchanged() {
        Place<String> a = Place.of("A", String.class);
        Place<String> b = Place.of("B", String.class);
        Place<String> c = Place.of("C", String.class);  // unrelated to {A, B}

        Transition t1 = Transition.builder("usesC")
            .read(c)
            .build();

        var net = PetriNet.builder("Mixed")
            .transitions(t1)
            .place(c)
            .fuse(FusionSet.of("ab", a, b))
            .build();

        assertTrue(net.places().contains(c), "unrelated place C must survive");
        var rewritten = findTransition(net, "usesC");
        assertTrue(rewritten.readPlaces().contains(c),
            "transition must still reference C unchanged");
    }

    // ============================================================
    //  Overlap detection: a place in two fusion sets is rejected
    // ============================================================

    @Test
    void fuse_overlappingFusionSets_throws() {
        Place<String> a = Place.of("A", String.class);
        Place<String> b = Place.of("B", String.class);
        Place<String> c = Place.of("C", String.class);

        var s1 = FusionSet.of("set1", a, b);
        var s2 = FusionSet.of("set2", b, c);  // B is in both!

        var ex = assertThrows(IllegalStateException.class,
            () -> PetriNet.builder("Bad").fuse(s1, s2).build());
        assertTrue(ex.getMessage().contains("B"),
            "exception must name the offending place. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("set1"),
            "exception must name the first owning set. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("set2"),
            "exception must name the second owning set. Got: " + ex.getMessage());
    }

    // ============================================================
    //  MOD-061 acceptance: three-bucket shared rate limiter
    // ============================================================

    @Test
    void fuse_chained_threeBucketsShareLimiter() {
        // Three instances of leaky-bucket, each with its own internal "slots"
        // place. Compose all three; declare a fusion set across the three
        // slots places. The resulting net has a single canonical "slots".
        // Bind a forwarding action: consume request, emit a marker to the
        // sole output place. (The default passthrough() action emits no
        // outputs, so we must bind explicit forwarding to observe accept/reject.)
        TransitionAction forward = ctx -> {
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                ctx.output(p, "x");
            }
            return CompletableFuture.completedFuture(null);
        };
        Map<String, TransitionAction> actions = Map.of(
            "accept", forward,
            "reject", forward
        );

        var bucketDef = SubnetFixtures.leakyBucket(2);
        var b1 = bucketDef.instantiate("b1").bindActions(actions);
        var b2 = bucketDef.instantiate("b2").bindActions(actions);
        var b3 = bucketDef.instantiate("b3").bindActions(actions);

        // Each instance gets its own external request/accept/reject places.
        Place<String> req1 = Place.of("req1", String.class);
        Place<String> acc1 = Place.of("acc1", String.class);
        Place<String> rej1 = Place.of("rej1", String.class);
        Place<String> req2 = Place.of("req2", String.class);
        Place<String> acc2 = Place.of("acc2", String.class);
        Place<String> rej2 = Place.of("rej2", String.class);
        Place<String> req3 = Place.of("req3", String.class);
        Place<String> acc3 = Place.of("acc3", String.class);
        Place<String> rej3 = Place.of("rej3", String.class);

        // The leakyBucket fixture keeps slots as an INTERNAL place (not a
        // port — that is the whole point of fusion: shared cross-instance
        // state without exposing it as a port on every subnet). Resolve the
        // renamed slots places by name on the renamed body.
        Place<String> slotsB1 = renamedSlots(b1);
        Place<String> slotsB2 = renamedSlots(b2);
        Place<String> slotsB3 = renamedSlots(b3);

        var net = PetriNet.builder("ThreeBuckets")
            .compose(b1, m -> m.bindPort("request", req1)
                                 .bindPort("accept", acc1)
                                 .bindPort("reject", rej1))
            .compose(b2, m -> m.bindPort("request", req2)
                                 .bindPort("accept", acc2)
                                 .bindPort("reject", rej2))
            .compose(b3, m -> m.bindPort("request", req3)
                                 .bindPort("accept", acc3)
                                 .bindPort("reject", rej3))
            .fuse(FusionSet.of("sharedSlots", slotsB1, slotsB2, slotsB3))
            .build();

        // Assertion 1: only the canonical slotsB1 place survives; the other
        // two are gone from the built net's place set.
        assertTrue(net.places().contains(slotsB1),
            "canonical slots place must survive in the fused net");
        assertFalse(net.places().contains(slotsB2),
            "non-canonical slotsB2 must be substituted away");
        assertFalse(net.places().contains(slotsB3),
            "non-canonical slotsB3 must be substituted away");

        // Assertion 2: every transition that originally referenced any of the
        // three slots places now references only slotsB1. We sample the three
        // accept transitions (each consumed from its own slots).
        var b1AcceptT = findTransition(net, "b1/accept");
        assertTrue(b1AcceptT.inputPlaces().contains(slotsB1),
            "b1/accept must consume from canonical slots");

        var b2AcceptT = findTransition(net, "b2/accept");
        assertTrue(b2AcceptT.inputPlaces().contains(slotsB1),
            "b2/accept must now consume from canonical (shared) slots");
        assertFalse(b2AcceptT.inputPlaces().contains(slotsB2),
            "b2/accept must not reference non-canonical slotsB2");

        var b3AcceptT = findTransition(net, "b3/accept");
        assertTrue(b3AcceptT.inputPlaces().contains(slotsB1),
            "b3/accept must now consume from canonical (shared) slots");
        assertFalse(b3AcceptT.inputPlaces().contains(slotsB3),
            "b3/accept must not reference non-canonical slotsB3");

        // Assertion 3: dynamic behaviour — only 2 slots total are available
        // across all three buckets, even though each was declared with rate=2.
        // Send three requests (one per bucket); only 2 should accept.
        try (var executor = BitmapNetExecutor.create(net, Map.of(
            req1, List.of(Token.of("r1")),
            req2, List.of(Token.of("r2")),
            req3, List.of(Token.of("r3")),
            slotsB1, List.of(Token.of("s"), Token.of("s"))  // 2 shared slots
        ))) {
            var marking = executor.run();
            int totalAccepts = marking.tokenCount(acc1)
                + marking.tokenCount(acc2)
                + marking.tokenCount(acc3);
            int totalRejects = marking.tokenCount(rej1)
                + marking.tokenCount(rej2)
                + marking.tokenCount(rej3);
            assertEquals(2, totalAccepts,
                "exactly 2 requests should accept (shared 2-slot limiter). Marking: " + marking);
            assertEquals(1, totalRejects,
                "exactly 1 request should reject (3 in - 2 accepted). Marking: " + marking);
        }
    }

    // Helper: resolve a renamed internal "slots" place by name. Slots is an
    // internal (non-port) place of leakyBucket, so we look it up by name.
    @SuppressWarnings("unchecked")
    private static Place<String> renamedSlots(Instance<?> instance) {
        for (var p : instance.renamedBody().places()) {
            if (p.name().equals(instance.prefix() + "/slots")) {
                return (Place<String>) p;
            }
        }
        throw new AssertionError(
            "no renamed slots place for instance with prefix '" + instance.prefix() + "'");
    }

    // ============================================================
    //  Order independence: fuse before compose vs after compose
    // ============================================================

    @Test
    void fuse_runsAfterCompose() {
        // Declare a fusion set BEFORE the compose call. The fusion set
        // references places that only exist after the renamed body is merged
        // into the host. Builder accumulates fuse sets and applies at build().
        var bucketDef = SubnetFixtures.leakyBucket(1);
        var b1 = bucketDef.instantiate("b1");
        var b2 = bucketDef.instantiate("b2");

        Place<String> req1 = Place.of("req1", String.class);
        Place<String> acc1 = Place.of("acc1", String.class);
        Place<String> rej1 = Place.of("rej1", String.class);
        Place<String> req2 = Place.of("req2", String.class);
        Place<String> acc2 = Place.of("acc2", String.class);
        Place<String> rej2 = Place.of("rej2", String.class);

        Place<String> slotsB1 = renamedSlots(b1);
        Place<String> slotsB2 = renamedSlots(b2);

        // Note: fuse(...) called BEFORE the compose calls. This is allowed
        // because fuse only registers; the rewrite happens at build() AFTER
        // compose has flattened both instances.
        var net = PetriNet.builder("OrderIndependent")
            .fuse(FusionSet.of("shared", slotsB1, slotsB2))
            .compose(b1, m -> m.bindPort("request", req1)
                                 .bindPort("accept", acc1)
                                 .bindPort("reject", rej1))
            .compose(b2, m -> m.bindPort("request", req2)
                                 .bindPort("accept", acc2)
                                 .bindPort("reject", rej2))
            .build();

        // Assert the same outcome as if fuse came after compose.
        assertTrue(net.places().contains(slotsB1));
        assertFalse(net.places().contains(slotsB2));
        var b2AcceptT = findTransition(net, "b2/accept");
        assertTrue(b2AcceptT.inputPlaces().contains(slotsB1),
            "fuse-before-compose still resolves the post-compose place names");
    }

    // ============================================================
    //  Orthogonality with channel composition (MOD-021 + MOD-061)
    // ============================================================

    @Test
    void fuse_independentOfChannelComposition() {
        // Subnet with a channel "fire" and an internal place "shared".
        Place<String> shared = Place.of("shared", String.class);
        Place<String> tick = Place.of("tick", String.class);
        Transition fireT = Transition.builder("fire")
            .read(tick)
            .outputs(Arc.Out.place(shared))
            .build();
        var def = SubnetDef.builder("HasChannelAndInternal")
            .place(shared)
            .place(tick)
            .transition(fireT)
            .channel("fire", fireT)
            .build();

        var inst = def.instantiate("i1");

        // Caller-side place to fuse with the renamed shared place.
        Place<String> hostShared = Place.of("hostShared", String.class);

        // Caller-side transition for the channel binding.
        Place<String> hostTrigger = Place.of("hostTrigger", String.class);
        Transition callerSide = Transition.builder("callerFire")
            .read(hostTrigger)
            .build();

        Place<String> renamedShared = (Place<String>) findRenamedPlace(inst, "i1/shared");

        var net = PetriNet.builder("ChannelPlusFusion")
            .compose(inst, m -> m.bindChannel("fire", callerSide))
            .fuse(FusionSet.of("share", hostShared, renamedShared))
            .build();

        // Channel composition: the merged caller-side transition exists.
        var merged = findTransition(net, "callerFire");
        // Fusion: the renamed-instance "shared" place is gone; "hostShared"
        // is the canonical and lives in the place set + on the merged
        // transition's output.
        assertTrue(net.places().contains(hostShared));
        assertFalse(net.places().contains(renamedShared));
        assertTrue(merged.outputPlaces().contains(hostShared),
            "merged transition's output must reference fused canonical hostShared. "
                + "Outputs: " + merged.outputPlaces());
    }

    // ============================================================
    //  fuse + compose orthogonality: structural equivalence
    // ============================================================

    @Test
    void fuse_andCompose_orthogonality() {
        // We build two equivalent flat nets:
        //   netA: compose-then-fuse (fuse() called after compose())
        //   netB: fuse-then-compose (fuse() called before compose())
        // Both must produce structurally equivalent place + arc sets.
        var bucketDef = SubnetFixtures.leakyBucket(2);

        // ---- netA: compose-then-fuse ----
        var b1A = bucketDef.instantiate("b1");
        var b2A = bucketDef.instantiate("b2");
        Place<String> req1A = Place.of("req1", String.class);
        Place<String> acc1A = Place.of("acc1", String.class);
        Place<String> rej1A = Place.of("rej1", String.class);
        Place<String> req2A = Place.of("req2", String.class);
        Place<String> acc2A = Place.of("acc2", String.class);
        Place<String> rej2A = Place.of("rej2", String.class);
        Place<String> slotsB1A = renamedSlots(b1A);
        Place<String> slotsB2A = renamedSlots(b2A);

        var netA = PetriNet.builder("ComposeThenFuse")
            .compose(b1A, m -> m.bindPort("request", req1A)
                                  .bindPort("accept", acc1A)
                                  .bindPort("reject", rej1A))
            .compose(b2A, m -> m.bindPort("request", req2A)
                                  .bindPort("accept", acc2A)
                                  .bindPort("reject", rej2A))
            .fuse(FusionSet.of("shared", slotsB1A, slotsB2A))
            .build();

        // ---- netB: fuse-then-compose (the same SubnetDef + same prefix → same renamed slots place) ----
        var b1B = bucketDef.instantiate("b1");
        var b2B = bucketDef.instantiate("b2");
        Place<String> req1B = Place.of("req1", String.class);
        Place<String> acc1B = Place.of("acc1", String.class);
        Place<String> rej1B = Place.of("rej1", String.class);
        Place<String> req2B = Place.of("req2", String.class);
        Place<String> acc2B = Place.of("acc2", String.class);
        Place<String> rej2B = Place.of("rej2", String.class);
        Place<String> slotsB1B = renamedSlots(b1B);
        Place<String> slotsB2B = renamedSlots(b2B);

        var netB = PetriNet.builder("FuseThenCompose")
            .fuse(FusionSet.of("shared", slotsB1B, slotsB2B))
            .compose(b1B, m -> m.bindPort("request", req1B)
                                  .bindPort("accept", acc1B)
                                  .bindPort("reject", rej1B))
            .compose(b2B, m -> m.bindPort("request", req2B)
                                  .bindPort("accept", acc2B)
                                  .bindPort("reject", rej2B))
            .build();

        // Place sets must be structurally equal (Place is a record →
        // value equality on name+tokenType).
        assertEquals(netA.places(), netB.places(),
            "compose-then-fuse and fuse-then-compose must have equal place sets. "
                + "A: " + netA.places() + " B: " + netB.places());

        // Transition arc-sets, indexed by name, must match. We compare
        // by transition name + the set of place names referenced in arcs.
        var arcSummaryA = arcSummaryByTransitionName(netA);
        var arcSummaryB = arcSummaryByTransitionName(netB);
        assertEquals(arcSummaryA, arcSummaryB,
            "compose-then-fuse and fuse-then-compose must produce equivalent arc topologies");
    }

    // ============================================================
    //  Helpers
    // ============================================================

    /**
     * Returns a map keyed by transition name, valued by a set of "kind:place"
     * strings summarising every arc reference. Lets us compare two nets'
     * arc topologies regardless of transition identity.
     */
    private static Map<String, Set<String>> arcSummaryByTransitionName(PetriNet net) {
        var out = new java.util.HashMap<String, Set<String>>();
        for (var t : net.transitions()) {
            var refs = new HashSet<String>();
            for (var in : t.inputSpecs()) refs.add("in:" + in.place().name());
            if (t.outputSpec() != null) {
                for (var p : t.outputSpec().allPlaces()) refs.add("out:" + p.name());
            }
            for (var inh : t.inhibitors()) refs.add("inh:" + inh.place().name());
            for (var rd  : t.reads())      refs.add("read:" + rd.place().name());
            for (var rs  : t.resets())     refs.add("reset:" + rs.place().name());
            out.put(t.name(), refs);
        }
        return out;
    }

    private static Transition findTransition(PetriNet net, String name) {
        for (var t : net.transitions()) {
            if (t.name().equals(name)) return t;
        }
        var available = new ArrayList<String>();
        for (var t : net.transitions()) available.add(t.name());
        throw new AssertionError("no transition '" + name + "' in '" + net.name()
            + "'. Available: " + available);
    }

    private static Place<?> findRenamedPlace(Instance<?> inst, String renamedName) {
        for (var p : inst.renamedBody().places()) {
            if (p.name().equals(renamedName)) return p;
        }
        throw new AssertionError("no place '" + renamedName + "' in instance with prefix '"
            + inst.prefix() + "'. Places: " + inst.renamedBody().places());
    }
}
