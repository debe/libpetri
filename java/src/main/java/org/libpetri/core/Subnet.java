package org.libpetri.core;

/**
 * Sealed sum-type abstraction over Petri nets, distinguishing closed
 * (runnable) nets from open (composable) subnet fragments per
 * {@code spec/11-modular-composition.md}, requirement <b>MOD-002</b>.
 *
 * <p>This abstraction is the bridge between the existing flat {@link PetriNet}
 * world and the modular composition extension. Code that wishes to accept
 * "any net" types its parameter as {@code Subnet}; code that needs a runnable
 * net continues to take {@link PetriNet} (or {@link Closed}); code that needs
 * an open fragment takes {@link Open} (or {@link SubnetDef}{@code <?>}).
 * Misuse is rejected at compile time wherever the language permits.
 *
 * <h2>Variants</h2>
 * <ul>
 *   <li>{@link Closed} — wraps a {@link PetriNet}, runnable by an executor per
 *       [CORE-040].</li>
 *   <li>{@link Open} — implemented by {@link SubnetDef}{@code <P>} for any
 *       parameter type {@code P}; an open fragment with a declared
 *       {@link Interface} but no executor binding.</li>
 * </ul>
 *
 * <h2>Example</h2>
 * <pre>{@code
 * Subnet asAny = new Subnet.Closed(myNet);
 * Subnet asOpen = SubnetDef.builder("Buffer").build();
 *
 * switch (asAny) {
 *     case Subnet.Closed(PetriNet net) -> runWithExecutor(net);
 *     case Subnet.Open open            -> compose(open);
 * }
 * }</pre>
 *
 * @see PetriNet
 * @see SubnetDef
 * @see Interface
 */
public sealed interface Subnet permits Subnet.Closed, Subnet.Open {

    /**
     * Closed (runnable) net variant. Wraps an existing {@link PetriNet}.
     *
     * @param net the underlying flat Petri net
     */
    record Closed(PetriNet net) implements Subnet {
        public Closed {
            if (net == null) {
                throw new IllegalArgumentException("Closed.net cannot be null");
            }
        }
    }

    /**
     * Open (composable) net variant. Implemented by {@link SubnetDef} —
     * the sealing of {@code Open} to a single permitted subtype is intentional:
     * subnet definitions are the sole open-net carrier in this design.
     */
    sealed interface Open extends Subnet permits SubnetDef { }
}
