package org.libpetri.analysis;

/**
 * Selects the &nu;-name-correlation fragment the Route-B analyzer
 * ({@link NameFragment}/{@link NameStateClassGraph}) accepts (NU-050).
 *
 * <p>{@link #BASE} is the shipped mint&rarr;matched-join fragment: a <i>mint</i>
 * produces a fresh name into a coloured place, a <i>join</i> consumes one shared
 * name from every correlated input, everything else is <i>ordinary</i>; a non-match
 * transition consuming a coloured place puts the net out of fragment (returns
 * {@code null}). {@link #EXTENDED} additionally admits, opt-in, a name-blind
 * <i>consumer</i> that consumes exactly one coloured place at count exactly one
 * (NU-051): both a <b>drain</b> (the fired branch has no coloured output, so the
 * symbol is dead-lettered) and a <b>relay</b> (the fired branch re-emits the same
 * symbol into its coloured outputs, threading a minted name through declared carrier
 * places to the join inputs). This makes fork-threaded &nu;-correlations with
 * dead-letter drains decidable.
 *
 * <p>Both modes reject a net where any coloured place carries a reset, read, or
 * inhibitor arc (a soundness guard: such an arc would drift the name layer from the
 * base marking; rejection falls back to the sound over-approximation).
 *
 * <p>{@link #BASE} is the default: carrier declarations are ignored and
 * coloured-consumers still take the net out of fragment.
 */
public enum FragmentMode {
    /** The shipped mint&rarr;matched-join fragment (default; unchanged behavior). */
    BASE,
    /** BASE plus opt-in name-blind coloured-consumers (drain / relay) and carriers. */
    EXTENDED
}
