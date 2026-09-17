package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.core.internal.SubnetRewriter;
import org.libpetri.smt.encoding.NetFlattener;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * An open net closed by the environment its contract describes ([VER-022]).
 *
 * <p>Each arrival group becomes ordinary net structure. A source place holds the tokens the
 * group must deliver, with one transition per target place that moves a token across. The
 * part the group may withhold gets a second source, whose tokens can also be declined by a
 * transition with no output. The contract's environment transitions, the neighbours that
 * react to what the subnet sends, join unchanged but for their arcs, which resolve to the
 * net's places by name. Every interleaving of the environment's steps with the subnet's own
 * firings is then a run of the closed net. A run of the closed net is quiescent only once the
 * environment has delivered what it must and decided about the rest.
 *
 * <p>Nothing else changes. The closed net is a plain net, so the state-class graph and the
 * SMT pipeline verify it as they verify any other, and no route needs a notion of
 * environment.
 *
 * <p>The closure uses ordinary places rather than the environment places of [VER-006] on
 * purpose. Under {@code alwaysAvailable} or {@code bounded(k)} an environment place never runs
 * dry, so a net with one is never quiescent, and every quiescence property holds vacuously.
 * An arrival group that runs dry after {@code max} tokens is what a bounded contract means.
 */
public final class OpenNetClosure {

    private OpenNetClosure() {}

    /** The action an environment transition that declares outputs gets when it has none: it never runs. */
    private static final TransitionAction ENVIRONMENT_ACTION = TransitionAction.transform(_ -> null);

    /**
     * Closes {@code net} with the environment of {@code contract}: its environment transitions,
     * and for arrival group {@code i} a source {@code env:arrivals[i]} holding {@code min}
     * tokens and a source {@code env:optional[i]} holding {@code max − min}, with transitions
     * {@code env:arrive[i]:<place>} / {@code env:arrive?[i]:<place>} moving a token onto each of
     * the group's places, and {@code env:decline[i]} discarding an optional one.
     *
     * <p>Places are matched by <b>name</b>, as the TypeScript reference's closure matches them:
     * a contract place resolves to the net's place of that name whatever its token type. That
     * covers the arcs of the contract's environment transitions too, which join on the net's
     * places ({@link #onClosedPlaces}).
     *
     * @throws IllegalArgumentException when a name the closure would add is already taken in
     *     {@code net}
     */
    public static ClosedNet closeOpenNet(PetriNet net, OpenNetContract contract) {
        // Every place an arc declares, reset-only places included: the reference's net builder
        // registers those in `net.places`, Java's reaches them only through the transitions.
        var byName = new LinkedHashMap<String, Place<?>>();
        for (var p : NetFlattener.declaredPlaces(net)) {
            byName.putIfAbsent(p.name(), p);
        }
        var taken = new HashSet<String>(byName.keySet());
        for (var t : net.transitions()) {
            taken.add(t.name());
        }

        var environment = new LinkedHashMap<String, EnvironmentStep>();
        var environmentPlaces = new LinkedHashMap<String, Place<?>>();
        for (var t : contract.environment()) {
            environment.put(fresh(taken, t.name()), new EnvironmentStep.Transition());
            for (var p : OpenNetContract.transitionPlaces(t)) {
                if (!byName.containsKey(p.name())) {
                    environmentPlaces.putIfAbsent(p.name(), p);
                }
            }
        }
        // Before the undeclared sweep below, so an environment place is never also reported as a
        // place the contract named and nothing declares.
        for (var entry : environmentPlaces.entrySet()) {
            taken.add(entry.getKey());
            byName.put(entry.getKey(), entry.getValue());
        }

        // Every place the contract names joins the closed net, a terminal's excused places
        // included — `contract.places()` leaves those out. This is also what keeps the two routes
        // deciding the same rest set: the SMT encoder resolves each sink and marker through the
        // flat net's place index and silently drops what does not resolve, while the graph route
        // reads markings and drops nothing. An arc-less excused place that never got registered
        // here would therefore lose its excuse on the SMT route alone, and that route would
        // report a stranding the graph route proves cannot happen.
        var undeclared = new ArrayList<String>();
        var extra = new ArrayList<Place<?>>();
        var named = new ArrayList<Place<?>>(contract.places());
        for (var t : contract.terminals()) {
            named.addAll(t.excused());
        }
        for (var p : named) {
            if (byName.containsKey(p.name())) {
                continue;
            }
            undeclared.add(p.name());
            byName.put(p.name(), p);
            extra.add(p);
        }

        // Keyed by name through `byName`, so a contract place and the net's place of that name
        // hold the same tokens whatever their token types.
        var marking = MarkingState.builder();
        for (var p : contract.initialMarking().placesWithTokens()) {
            marking.tokens(byName.getOrDefault(p.name(), p), contract.initialMarking().tokens(p));
        }

        var envTransitions = new ArrayList<Transition>();
        for (int i = 0; i < contract.arrivals().size(); i++) {
            var group = contract.arrivals().get(i);
            if (group.min() > 0) {
                var source = Place.of(fresh(taken, "env:arrivals[" + i + "]"), Object.class);
                marking.tokens(source, group.min());
                for (var p : group.places()) {
                    inject(taken, envTransitions, environment, i, source, byName.getOrDefault(p.name(), p), false);
                }
            }
            if (group.max() > group.min()) {
                var source = Place.of(fresh(taken, "env:optional[" + i + "]"), Object.class);
                marking.tokens(source, group.max() - group.min());
                for (var p : group.places()) {
                    inject(taken, envTransitions, environment, i, source, byName.getOrDefault(p.name(), p), true);
                }
                var name = fresh(taken, "env:decline[" + i + "]");
                envTransitions.add(Transition.builder(name).inputs(Arc.In.one(source)).build());
                environment.put(name, new EnvironmentStep.Decline(i));
            }
        }

        // An environment transition's action never runs, so it need not produce: give one that
        // declares outputs a placeholder rather than refuse it under CORE-043.
        Set<String> placeholder = new HashSet<>();
        for (var t : contract.environment()) {
            if (t.outputSpec() != null && TransitionAction.isPassthrough(t.action())) {
                placeholder.add(t.name());
            }
        }
        var places = new ArrayList<Place<?>>(net.places());
        places.addAll(extra);
        var transitions = new ArrayList<Transition>(net.transitions());
        for (var t : contract.environment()) {
            transitions.add(onClosedPlaces(t, byName));
        }
        transitions.addAll(envTransitions);
        var closed = PetriNet.builder(net.name() + "+environment")
            .places(places.toArray(new Place<?>[0]))
            .transitions(transitions.toArray(new Transition[0]))
            .build()
            .bindActions(name -> placeholder.contains(name) ? ENVIRONMENT_ACTION : null);
        return new ClosedNet(
            closed, marking.build(), environment, List.copyOf(environmentPlaces.values()), undeclared, byName);
    }

    /**
     * {@code t} with every arc on the closed net's place of that name, or {@code t} itself when
     * its arcs already are.
     *
     * <p>The reference's places are equal by name, so its environment transitions join the net
     * as they are. Java's are equal by name and token type ({@link Place}), and the flattener and
     * the state-class graph key on that equality: an environment transition that reads a
     * {@code Place<String>} named like the subnet's {@code Place<Object>} would otherwise touch a
     * second place of that name, one the subnet never marks, and the verdict would flip.
     *
     * <p>Rebinding an arc to a place of another token type is sound only because an environment
     * transition never executes: no token of the arc's declared type is ever read through it,
     * and both routes read names and counts alone.
     */
    private static Transition onClosedPlaces(Transition t, Map<String, Place<?>> byName) {
        var remap = new HashMap<Place<?>, Place<?>>();
        for (var p : OpenNetContract.transitionPlaces(t)) {
            var resolved = byName.get(p.name());
            if (resolved != null && !resolved.equals(p)) {
                remap.put(p, resolved);
            }
        }
        return remap.isEmpty() ? t : SubnetRewriter.substitutePlaces(t, remap);
    }

    /** {@code name}, reserved; refused when the net or the closure already uses it. */
    private static String fresh(Set<String> taken, String name) {
        if (!taken.add(name)) {
            throw new IllegalArgumentException(
                "VER-022: closing the net would add '" + name + "', which the net already declares");
        }
        return name;
    }

    /** {@code env:arrive[group]:<target>} (or {@code env:arrive?…} when optional): one token from {@code source} onto {@code target}. */
    private static void inject(
            Set<String> taken,
            List<Transition> envTransitions,
            LinkedHashMap<String, EnvironmentStep> environment,
            int group,
            Place<?> source,
            Place<?> target,
            boolean optional
    ) {
        var name = fresh(taken, "env:arrive" + (optional ? "?" : "") + "[" + group + "]:" + target.name());
        envTransitions.add(Transition.builder(name)
            .inputs(Arc.In.one(source))
            .outputs(Arc.Out.place(target))
            .action(TransitionAction.fork())
            .build());
        environment.put(name, new EnvironmentStep.Arrival(group, target.name()));
    }
}
