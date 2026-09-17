package org.libpetri.smt.opennet;

/**
 * What an environment transition of the closure does, for the port trace ([VER-022]).
 */
public sealed interface EnvironmentStep {

    /** The step without its payload: what a port trace marks a firing as. */
    Kind kind();

    /**
     * Moves one token of arrival group {@code group} onto {@code place}.
     *
     * @param group the arrival group's index in {@link OpenNetContract#arrivals()}
     * @param place the name of the place the token arrives on
     */
    record Arrival(int group, String place) implements EnvironmentStep {
        @Override
        public Kind kind() {
            return Kind.ARRIVAL;
        }
    }

    /**
     * Declines one optional token of arrival group {@code group}.
     *
     * @param group the arrival group's index in {@link OpenNetContract#arrivals()}
     */
    record Decline(int group) implements EnvironmentStep {
        @Override
        public Kind kind() {
            return Kind.DECLINE;
        }
    }

    /** One of the contract's own environment transitions ({@link OpenNetContract#environment()}). */
    record Transition() implements EnvironmentStep {
        @Override
        public Kind kind() {
            return Kind.TRANSITION;
        }
    }

    /** {@code arrival}, {@code decline} or {@code transition}, as the report prints it. */
    enum Kind {
        ARRIVAL("arrival"),
        DECLINE("decline"),
        TRANSITION("transition");

        private final String label;

        Kind(String label) {
            this.label = label;
        }

        public String label() {
            return label;
        }
    }
}
