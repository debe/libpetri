package org.libpetri.smt.conformance;

import com.fasterxml.jackson.databind.JsonNode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtProperty;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;

/**
 * One net of the cross-language conformance corpus ({@code spec/verification-fixtures/conformance/
 * README.md}), parsed from {@code nets/<id>.json} exactly per the schema, and built into a real
 * {@link PetriNet} with the Java builder API.
 *
 * <p>The parsed description is kept alongside the built net: {@link ReferenceSemantics} replays a
 * verifier's counterexample on it, independently of the verifier's own encodings.
 */
public record ConformanceNet(
    String id,
    List<String> declaredPlaces,
    Map<String, Integer> marking,
    List<TSpec> transitions,
    List<PropSpec> properties
) {

    /** An input arc: {@code one} | {@code exactly} (n) | {@code all} | {@code atLeast} (n). */
    public record InSpec(String place, String kind, int n) {
        /** Tokens the input needs to enable its transition. */
        int required() {
            return switch (kind) {
                case "one", "all" -> 1;
                case "exactly", "atLeast" -> n;
                default -> throw new IllegalStateException(kind);
            };
        }
    }

    /** An output tree node ([IO-011]..[IO-016]). */
    public sealed interface OutSpec {
        record PlaceOut(String place) implements OutSpec {}
        record AndOut(List<OutSpec> children) implements OutSpec {}
        record XorOut(List<OutSpec> children) implements OutSpec {}
        record TimeoutOut(long afterMs, OutSpec child) implements OutSpec {}
        record ForwardOut(String from, String to) implements OutSpec {}
    }

    /**
     * A transition; {@code output} is {@code null} when it has none. {@code timing} is the
     * schema's {@code timing} object ([TIME-002]..[TIME-006]), {@link Timing#immediate()} when
     * absent.
     */
    public record TSpec(
        String name, List<InSpec> inputs, List<String> inhibitors, List<String> reads,
        List<String> resets, OutSpec output, int priority, Timing timing
    ) {
        /** Reapable ([TIME-013]): {@code deadline} or {@code window} timing. */
        boolean reapable() {
            return timing instanceof Timing.Deadline || timing instanceof Timing.Window;
        }
    }

    /**
     * A property of one of the six schema types. Fields a type does not use are empty /
     * {@code null}; {@code max} is {@code null} when unbounded.
     */
    public record PropSpec(
        String id, String type, List<String> sinks, String place, int bound,
        List<String> places, int min, Integer max
    ) {}

    // ======================================================================
    // Parsing
    // ======================================================================

    public static ConformanceNet parse(JsonNode root) {
        String id = text(root, "id");
        var declared = strings(root.get("places"));
        var marking = new LinkedHashMap<String, Integer>();
        if (root.hasNonNull("marking")) {
            for (var e : root.get("marking").properties()) {
                marking.put(e.getKey(), e.getValue().asInt());
            }
        }
        var transitions = new ArrayList<TSpec>();
        for (JsonNode t : root.get("transitions")) {
            var inputs = new ArrayList<InSpec>();
            if (t.hasNonNull("inputs")) {
                for (JsonNode in : t.get("inputs")) {
                    String kind = text(in, "kind");
                    int n = switch (kind) {
                        case "one", "all" -> 0;
                        case "exactly", "atLeast" -> positive(in, "n");
                        default -> throw new IllegalArgumentException(
                            "net " + id + ": unknown input kind '" + kind + "'");
                    };
                    inputs.add(new InSpec(text(in, "place"), kind, n));
                }
            }
            JsonNode out = t.get("output");
            transitions.add(new TSpec(
                text(t, "name"),
                List.copyOf(inputs),
                strings(t.get("inhibitors")),
                strings(t.get("reads")),
                strings(t.get("resets")),
                out == null || out.isNull() ? null : parseOut(id, out),
                t.hasNonNull("priority") ? t.get("priority").asInt() : 0,
                t.hasNonNull("timing") ? parseTiming(id, t.get("timing")) : Timing.immediate()));
        }
        var properties = new ArrayList<PropSpec>();
        for (JsonNode p : root.get("properties")) {
            properties.add(parseProperty(id, p));
        }
        return new ConformanceNet(id, declared, marking, List.copyOf(transitions), List.copyOf(properties));
    }

    private static Timing parseTiming(String id, JsonNode node) {
        String kind = text(node, "kind");
        return switch (kind) {
            case "immediate", "unconstrained" -> Timing.immediate();
            case "deadline" -> Timing.deadline(ms(id, node, "latestMs"));
            case "delayed" -> Timing.delayed(ms(id, node, "earliestMs"));
            case "window" -> Timing.window(ms(id, node, "earliestMs"), ms(id, node, "latestMs"));
            case "exact" -> Timing.exact(ms(id, node, "earliestMs"));
            default -> throw new IllegalArgumentException("net " + id + ": unknown timing kind '" + kind + "'");
        };
    }

    private static Duration ms(String id, JsonNode node, String key) {
        if (!node.hasNonNull(key) || !node.get(key).canConvertToLong() || node.get(key).asLong() < 0) {
            throw new IllegalArgumentException("net " + id + ": timing '" + key + "' must be a whole number");
        }
        return Duration.ofMillis(node.get(key).asLong());
    }

    private static OutSpec parseOut(String id, JsonNode node) {
        String type = text(node, "type");
        return switch (type) {
            case "place" -> new OutSpec.PlaceOut(text(node, "place"));
            case "and" -> new OutSpec.AndOut(children(id, node));
            case "xor" -> new OutSpec.XorOut(children(id, node));
            case "timeout" -> new OutSpec.TimeoutOut(node.get("afterMs").asLong(), parseOut(id, node.get("child")));
            case "forward" -> new OutSpec.ForwardOut(text(node, "from"), text(node, "to"));
            default -> throw new IllegalArgumentException("net " + id + ": unknown output type '" + type + "'");
        };
    }

    private static List<OutSpec> children(String id, JsonNode node) {
        var out = new ArrayList<OutSpec>();
        for (JsonNode c : node.get("children")) {
            out.add(parseOut(id, c));
        }
        return List.copyOf(out);
    }

    private static PropSpec parseProperty(String id, JsonNode p) {
        String type = text(p, "type");
        return switch (type) {
            case "deadlock-free", "terminates-at-sink" ->
                new PropSpec(text(p, "id"), type, strings(p.get("sinks")), null, 0, List.of(), 0, null);
            case "place-bound" ->
                new PropSpec(text(p, "id"), type, List.of(), text(p, "place"), p.get("bound").asInt(), List.of(), 0, null);
            case "mutual-exclusion", "unreachable" ->
                new PropSpec(text(p, "id"), type, List.of(), null, 0, strings(p.get("places")), 0, null);
            case "quiescent-count" -> new PropSpec(text(p, "id"), type, List.of(), null, 0,
                strings(p.get("places")), p.get("min").asInt(),
                p.hasNonNull("max") ? p.get("max").asInt() : null);
            default -> throw new IllegalArgumentException("net " + id + ": unknown property type '" + type + "'");
        };
    }

    private static String text(JsonNode node, String field) {
        JsonNode v = node.get(field);
        if (v == null || v.isNull()) {
            throw new IllegalArgumentException("missing field '" + field + "' in " + node);
        }
        return v.asText();
    }

    private static int positive(JsonNode node, String field) {
        JsonNode v = node.get(field);
        if (v == null || !v.canConvertToInt() || v.asInt() < 1) {
            throw new IllegalArgumentException("field '" + field + "' must be an integer >= 1 in " + node);
        }
        return v.asInt();
    }

    private static List<String> strings(JsonNode array) {
        var out = new ArrayList<String>();
        if (array != null && !array.isNull()) {
            for (JsonNode n : array) {
                out.add(n.asText());
            }
        }
        return List.copyOf(out);
    }

    // ======================================================================
    // Building
    // ======================================================================

    /**
     * Every corpus place is {@code Object}-typed: Java {@link Place} equality is structural on
     * {@code (name, tokenType)} (MOD-024), so one token type keeps name identity.
     */
    public static Place<Object> place(String name) {
        return Place.of(name, Object.class);
    }

    /** The net: declared places, every transition, and a structure-only action on each. */
    public PetriNet build() {
        var nb = PetriNet.builder(id);
        for (TSpec t : transitions) {
            var tb = Transition.builder(t.name());
            for (InSpec in : t.inputs()) {
                var p = place(in.place());
                tb.inputs(switch (in.kind()) {
                    case "one" -> In.one(p);
                    case "exactly" -> In.exactly(in.n(), p);
                    case "all" -> In.all(p);
                    case "atLeast" -> In.atLeast(in.n(), p);
                    default -> throw new IllegalStateException(in.kind());
                });
            }
            t.inhibitors().forEach(p -> tb.inhibitor(place(p)));
            t.reads().forEach(p -> tb.read(place(p)));
            t.resets().forEach(p -> tb.reset(place(p)));
            if (t.output() != null) {
                tb.outputs(toOut(t.output()));
            }
            tb.priority(t.priority());
            tb.timing(t.timing());
            nb.transition(tb.build());
        }
        for (String p : declaredPlaces) {
            nb.place(place(p));
        }
        return StructureOnly.bind(nb.build());
    }

    private Out toOut(OutSpec spec) {
        return switch (spec) {
            case OutSpec.PlaceOut p -> Out.place(place(p.place()));
            case OutSpec.AndOut a -> new Out.And(a.children().stream().map(this::toOut).toList());
            case OutSpec.XorOut x -> {
                if (x.children().size() < 2) {
                    throw new NotExpressible("net " + id + ": Java's Out.Xor needs at least 2 children, got "
                        + x.children().size());
                }
                yield new Out.Xor(x.children().stream().map(this::toOut).toList());
            }
            case OutSpec.TimeoutOut t -> Out.timeout(Duration.ofMillis(t.afterMs()), toOut(t.child()));
            case OutSpec.ForwardOut f -> Out.forwardInput(place(f.from()), place(f.to()));
        };
    }

    /** The initial marking; names no arc touches and the net does not declare are inert places. */
    public MarkingState initialMarking() {
        var b = MarkingState.builder();
        marking.forEach((name, n) -> {
            if (n > 0) {
                b.tokens(place(name), n);
            }
        });
        return b.build();
    }

    /** The Java property for a schema property; sinks are passed separately. */
    public SmtProperty toSmt(PropSpec p) {
        return switch (p.type()) {
            case "deadlock-free" -> SmtProperty.deadlockFree();
            case "terminates-at-sink" -> SmtProperty.terminatesAtSink();
            case "place-bound" -> SmtProperty.placeBound(place(p.place()), p.bound());
            case "mutual-exclusion" -> {
                if (p.places().size() != 2) {
                    throw new NotExpressible("net " + id + ", property " + p.id()
                        + ": Java's mutualExclusion takes exactly 2 places, got " + p.places());
                }
                yield SmtProperty.mutualExclusion(place(p.places().get(0)), place(p.places().get(1)));
            }
            case "unreachable" -> {
                var set = new LinkedHashSet<Place<?>>();
                p.places().forEach(n -> set.add(place(n)));
                yield SmtProperty.unreachable(set);
            }
            case "quiescent-count" -> SmtProperty.quiescentCount(
                p.places().stream().map(ConformanceNet::place).toList(), p.min(),
                p.max() == null ? OptionalInt.empty() : OptionalInt.of(p.max()));
            default -> throw new IllegalStateException(p.type());
        };
    }

    /**
     * Whether the property is a mutual exclusion over three or more places: pairwise in the spec
     * (VER-002), but Java's {@code mutualExclusion} takes exactly two, so the runner skips it
     * (README clarification 1). {@link #toSmt} still refuses it.
     */
    public static boolean beyondTwoPlaceApi(PropSpec p) {
        return p.type().equals("mutual-exclusion") && p.places().size() > 2;
    }

    /** The sink places the property carries (empty for the non-sink types). */
    public Place<?>[] sinks(PropSpec p) {
        return p.sinks().stream().map(ConformanceNet::place).toArray(Place<?>[]::new);
    }

    /** A schema construct the Java API cannot express. */
    public static final class NotExpressible extends RuntimeException {
        public NotExpressible(String message) {
            super(message);
        }
    }
}
