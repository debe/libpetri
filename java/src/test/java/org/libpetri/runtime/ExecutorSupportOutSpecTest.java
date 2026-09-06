package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import org.libpetri.core.Arc.Out;
import org.libpetri.core.Place;

/**
 * [IO-015] {@link ExecutorSupport#validateOutSpec} — the exact-explanation search.
 *
 * <p>Mirrors the TypeScript reference suite (`executor-support.test.ts`), so the two runtimes
 * are diagnosable the same way: validation succeeds iff exactly one assignment of the spec tree
 * claims exactly the produced places the spec names.
 */
class ExecutorSupportOutSpecTest {

    private static final Place<String> pA = Place.of("A", String.class);
    private static final Place<String> pB = Place.of("B", String.class);
    private static final Place<String> pC = Place.of("C", String.class);
    private static final Place<String> pD = Place.of("D", String.class);

    private static Set<Place<?>> produced(Place<?>... places) {
        return new LinkedHashSet<>(List.of(places));
    }

    private static Set<String> names(Set<Place<?>> places) {
        var out = new java.util.TreeSet<String>();
        for (Place<?> p : places) out.add(p.name());
        return out;
    }

    // ==================== Leaves and the basic connectives ====================

    @Test
    void placeSpecSatisfied() {
        var claim = ExecutorSupport.validateOutSpec("T", Out.place(pA), produced(pA));
        assertEquals(Set.of("A"), names(claim));
    }

    @Test
    void placeSpecNotSatisfiedThrows() {
        var e = assertThrows(OutViolationException.class,
            () -> ExecutorSupport.validateOutSpec("T", Out.place(pA), produced()));
        assertTrue(e.getMessage().contains("output does not match the declared spec"), e.getMessage());
    }

    @Test
    void andSpecAllSatisfied() {
        var claim = ExecutorSupport.validateOutSpec("T", Out.and(pA, pB), produced(pA, pB));
        assertEquals(Set.of("A", "B"), names(claim));
    }

    @Test
    void andSpecPartiallySatisfiedIsAViolation() {
        var e = assertThrows(OutViolationException.class,
            () -> ExecutorSupport.validateOutSpec("T", Out.and(pA, pB), produced(pA)));
        assertTrue(e.getMessage().contains("output does not match the declared spec"), e.getMessage());
    }

    @Test
    void xorSpecExactlyOneSatisfied() {
        var claim = ExecutorSupport.validateOutSpec("T", Out.xor(pA, pB), produced(pB));
        assertEquals(Set.of("B"), names(claim));
    }

    @Test
    void xorSpecNoBranchThrows() {
        var e = assertThrows(OutViolationException.class,
            () -> ExecutorSupport.validateOutSpec("T", Out.xor(pA, pB), produced()));
        assertTrue(e.getMessage().contains("produced {}"), e.getMessage());
    }

    @Test
    @DisplayName("XOR with both branches written is unexplained output, not a double match")
    void xorSpecBothBranchesWrittenThrows() {
        // Neither branch CLAIMS {A, B}: one claims {A}, the other {B}. Under [IO-015]'s equality
        // rule that is unexplained output — the old code reported it as "multiple branches".
        var e = assertThrows(OutViolationException.class,
            () -> ExecutorSupport.validateOutSpec("T", Out.xor(pA, pB), produced(pA, pB)));
        assertTrue(e.getMessage().contains("output does not match the declared spec"), e.getMessage());
        assertTrue(e.getMessage().contains("produced {A, B}"), e.getMessage());
    }

    @Test
    void xorWithNestedAndSelectsTheProducedBranch() {
        var spec = Out.xor(Out.and(pA, pB), Out.and(pC, pD));
        var claim = ExecutorSupport.validateOutSpec("T", spec, produced(pC, pD));
        assertEquals(Set.of("C", "D"), names(claim));
    }

    @Test
    void timeoutChildIsValidated() {
        var timeoutPlace = Place.of("TIMEOUT", String.class);
        var spec = Out.timeout(Duration.ofMillis(100), Out.place(timeoutPlace));
        var claim = ExecutorSupport.validateOutSpec("T", spec, produced(timeoutPlace));
        assertEquals(Set.of("TIMEOUT"), names(claim));
    }

    @Test
    void forwardInputSatisfied() {
        var from = Place.of("FROM", String.class);
        var to = Place.of("TO", String.class);
        var claim = ExecutorSupport.validateOutSpec("T", Out.forwardInput(from, to), produced(to));
        assertEquals(Set.of("TO"), names(claim));
    }

    // ==================== The exact-explanation rules ====================

    @Nested
    @DisplayName("[IO-015] exact-explanation acceptance criteria")
    class ExactExplanation {

        @Test
        @DisplayName("AC5: overlapping branches resolve with no subsumption tie-break")
        void subsetBranchesResolveWithoutATieBreak() {
            // and(A,B,C) strictly contains and(A,B). With A, B and C produced only the wider
            // branch claims EXACTLY that set, so this resolves without the tie-break [IO-015]
            // used to need and no longer has.
            var spec = Out.xor(Out.and(pA, pB, pC), Out.and(pA, pB));
            var claim = ExecutorSupport.validateOutSpec("T", spec, produced(pA, pB, pC));
            assertEquals(Set.of("A", "B", "C"), names(claim));
        }

        @Test
        @DisplayName("genuinely overlapping branches still throw")
        void genuinelyOverlappingBranchesThrow() {
            // and(A,B) and and(B,C) each claim a strict subset of {A, B, C}, so neither explains
            // the write.
            var spec = Out.xor(Out.and(pA, pB), Out.and(pB, pC));
            var e = assertThrows(OutViolationException.class,
                () -> ExecutorSupport.validateOutSpec("T", spec, produced(pA, pB, pC)));
            assertTrue(e.getMessage().contains("output does not match the declared spec"), e.getMessage());
        }

        @Test
        @DisplayName("AC8: And is unordered — child order cannot change the verdict")
        void andIsUnordered() {
            var forward = Out.and(Out.place(pA), Out.xor(pC, pD));
            var reversed = Out.and(Out.xor(pC, pD), Out.place(pA));
            for (Set<Place<?>> write : List.of(produced(), produced(pA), produced(pA, pC))) {
                assertEquals(verdict(forward, write), verdict(reversed, write),
                    "verdict must not depend on And child order for " + names(write));
            }
        }

        private String verdict(Out spec, Set<Place<?>> write) {
            try {
                return "ok:" + names(ExecutorSupport.validateOutSpec("T", spec, write));
            } catch (OutViolationException e) {
                return e.getMessage().contains("ambiguous") ? "throw:ambiguous" : "throw:unmatched";
            }
        }

        @Test
        @DisplayName("AC9: a write outside the selected branch is a violation")
        void writeOutsideTheSelectedBranchIsAViolation() {
            // Selecting B explains B but leaves C unexplained; C used to be deposited silently
            // because validation only checked that obligations were satisfied.
            var spec = Out.xor(Out.and(pA, pC), Out.place(pB));
            var e = assertThrows(OutViolationException.class,
                () -> ExecutorSupport.validateOutSpec("T", spec, produced(pB, pC)));
            assertTrue(e.getMessage().contains("produced {B, C}"), e.getMessage());
        }

        @Test
        @DisplayName("AC10: an inner Xor does not pre-empt an outer one")
        void innerXorDoesNotPreEmptOuterXor() {
            // The second branch claims exactly {A}. The old eager walk threw inside the first
            // branch's inner xor before this one could be tried.
            var spec = Out.xor(Out.and(Out.place(pA), Out.xor(pC, pD)), Out.place(pA));
            var claim = ExecutorSupport.validateOutSpec("T", spec, produced(pA));
            assertEquals(Set.of("A"), names(claim));
        }

        @Test
        @DisplayName("AC4: two branches claiming the same set are ambiguous")
        void twoBranchesClaimingTheSameSetAreAmbiguous() {
            var spec = Out.xor(Out.and(Out.place(pA)), Out.place(pA));
            var e = assertThrows(OutViolationException.class,
                () -> ExecutorSupport.validateOutSpec("T", spec, produced(pA)));
            assertTrue(e.getMessage().contains("ambiguous output"), e.getMessage());
            assertTrue(e.getMessage().contains("{A} is claimed by more than one branch"), e.getMessage());
        }

        @Test
        @DisplayName("a token in a place the spec never names is [CORE-072]'s, not an IO-015 violation")
        void undeclaredPlaceIsNotAnOutViolation() {
            var undeclared = Place.of("UNDECLARED", String.class);
            var claim = ExecutorSupport.validateOutSpec("T", Out.place(pA), produced(pA, undeclared));
            assertEquals(Set.of("A"), names(claim));
        }
    }

    // ==================== Multiplicity cap ====================

    /**
     * The cap that keeps identical claims at multiplicity 2 is load-bearing, not an
     * optimisation: {@code And(Xor(A,B) x k)} with both A and B produced has 2^k assignments,
     * all of them claiming one of only three distinct sets. Uncapped, the {@code And} join
     * materialises every one of them on a path that runs on every firing.
     */
    @Test
    @DisplayName("And of 20 consistent Xor children stays fast (multiplicity cap)")
    void multiplicityCapBoundsTheAndJoin() {
        var children = new ArrayList<Out>();
        for (int i = 0; i < 20; i++) children.add(Out.xor(pA, pB));
        var spec = Out.and(children.toArray(new Out[0]));
        var write = produced(pA, pB);

        assertTimeoutPreemptively(Duration.ofSeconds(5), () -> {
            for (int i = 0; i < 100; i++) {
                // Ambiguous by construction (many assignments claim {A, B}) — the point is that
                // reaching that verdict costs microseconds rather than 2^20 allocated sets.
                assertThrows(OutViolationException.class,
                    () -> ExecutorSupport.validateOutSpec("T", spec, write));
            }
        });
    }
}
