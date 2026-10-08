package org.libpetri.smt;

/**
 * The two name-alignment properties of [NU-055] as the routes see them: only Route B, the
 * name-partition state-class graph ([NU-050]), reads the name layer, so every other route gives
 * them no verdict.
 *
 * <p>Internal API: not part of the public contract.
 */
public final class NameAlignment {

    private NameAlignment() {}

    /** Whether {@code property} is {@code NameAligned} or {@code QuiescentNameAligned} ([NU-055]). */
    public static boolean isNameAlignment(SmtProperty property) {
        return property instanceof SmtProperty.NameAligned || property instanceof SmtProperty.QuiescentNameAligned;
    }

    /**
     * Why a route other than Route B gives {@code property} no verdict ([NU-055] AC4): the
     * name-blind routes do not see names. Also the closing clause of a Route B decline, after
     * which nothing else decides it.
     */
    public static String routeBOnlyReason(SmtProperty property) {
        return property.description() + " is decided only by the name-partition state-class graph "
            + "(NU-055, Route B)";
    }
}
