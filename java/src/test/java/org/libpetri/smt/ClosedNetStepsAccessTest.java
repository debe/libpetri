package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.libpetri.smt.opennet.ClosedNetSteps;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The environment steps and reapable set an open-net route hands a verifier ([VER-022]) are out
 * of reach of every other caller: naming an environment step exempts a transition from the
 * in-flight split ([VER-004]) and naming the reapable set replaces the one read off the net
 * ([TIME-013]), both without a report line. This test lives outside
 * {@code org.libpetri.smt.opennet}, where a user's code lives.
 */
class ClosedNetStepsAccessTest {

    @Test
    void noPublicMethodOfTheVerifierTakesTheListsDirectly() {
        for (Method m : SmtVerifier.class.getMethods()) {
            boolean takesNames = Arrays.stream(m.getParameterTypes()).anyMatch(Set.class::equals);
            String name = m.getName().toLowerCase();
            assertTrue(!(takesNames && (name.contains("environmentstep") || name.contains("reapable"))),
                "public " + m + " sets the split's or the reaping's inputs without a ClosedNetSteps");
        }
    }

    @Test
    void onlyTheOpenNetPackageCanMakeClosedNetSteps() {
        assertEquals(0, ClosedNetSteps.class.getConstructors().length, "a public constructor");
        for (var c : ClosedNetSteps.class.getDeclaredConstructors()) {
            int mods = c.getModifiers();
            assertTrue(!Modifier.isPublic(mods) && !Modifier.isProtected(mods), c + " is reachable");
        }
        for (Method m : ClosedNetSteps.class.getMethods()) {
            assertTrue(!(Modifier.isStatic(m.getModifiers()) && m.getReturnType() == ClosedNetSteps.class),
                m + " makes one");
        }
        assertTrue(Modifier.isFinal(ClosedNetSteps.class.getModifiers()), "subclassable");
    }

    @Test
    void aNullGrantIsRefused() {
        var net = org.libpetri.core.PetriNet.builder("empty").build();
        assertThrows(NullPointerException.class, () -> SmtVerifier.forNet(net).closedNetSteps(null));
    }
}
