package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Name-correlation fragment classifier for the &nu;-aware state class graph
 * (NU-050, Route B).
 *
 * <p>Identifies the <b>coloured</b> places (the correlated inputs of &nu;-joins)
 * and the role of each transition in the supported mint &rarr; matched-join
 * fragment: a <i>mint</i> (a declared one, NU-010) produces a freshly-named token into a
 * coloured place,
 * a <i>join</i> consumes one shared name from every correlated input, and
 * everything else is <i>ordinary</i>. {@link #classify} returns {@code null} when
 * the net is not a &nu;-net or falls outside the fragment (a non-match transition
 * consuming a coloured place, or a join writing a coloured place it does not declare
 * as a relay target, NU-054); the verifier then falls back to the SMT / Route A path.
 */
public final class NameFragment {

    /** A transition's role w.r.t. the coloured places. */
    public sealed interface Role {
        record Ordinary() implements Role {}
        record Mint() implements Role {}
        /**
         * A matched join (NU-020): correlated inputs (place name &rarr; required per-firing
         * count), sorted by name. {@code relayTo} (EXTENDED only, NU-054) holds the declared
         * relay targets: a firing on symbol {@code s} removes {@code s} from the keys, then
         * adds {@code s} once to each relay target in the fired branch. Empty under BASE and
         * for a join that drains the name.
         */
        record Join(List<Map.Entry<String, Integer>> colouredIn, Set<String> relayTo) implements Role {
            public Join(List<Map.Entry<String, Integer>> colouredIn) {
                this(colouredIn, Set.of());
            }
        }
        /**
         * A non-match transition that consumes exactly one coloured place at count
         * exactly one (EXTENDED fragment only, NU-051). The name-successor step
         * removes one resident symbol from {@code colouredInput} and re-emits it into
         * the fired branch's coloured outputs: a branch with no coloured output
         * <i>drains</i> the symbol (dead-letter), a branch with a coloured output
         * <i>relays</i> it (threads a carrier name to a join input). Because the
         * consumed count is fixed at one, the role carries only the input place name
         * (no count, no list).
         *
         * <p><b>Documented precondition</b> (NU-051): the action MUST thread the
         * consumed symbol (relay) or drop it (drain); it MUST NOT mint a fresh name
         * into a coloured output while consuming a coloured token. Such a
         * consume-and-remint transition is out of contract (the name layer would
         * thread the consumed symbol where the runtime mints a fresh one).
         */
        record Consume(String colouredInput) implements Role {}
    }

    final List<String> colouredOrder;
    private final Set<String> coloured;
    private final Map<String, Role> roles;
    private final List<String> mints;
    private final List<String> relays;

    private NameFragment(
            List<String> colouredOrder, Set<String> coloured, Map<String, Role> roles,
            List<String> mints, List<String> relays) {
        this.colouredOrder = colouredOrder;
        this.coloured = coloured;
        this.roles = roles;
        this.mints = List.copyOf(mints);
        this.relays = List.copyOf(relays);
    }

    /**
     * The transitions read as mints, in net order: the analysis trusts the mint contract of
     * NU-010 for them.
     */
    public List<String> mints() {
        return mints;
    }

    /**
     * The coloured consumers that write a coloured place, in net order: the analysis trusts the
     * relay contract of NU-051 for their action writes.
     */
    public List<String> relays() {
        return relays;
    }

    /**
     * The transitions of {@code net} declared to mint (NU-010): each one named in
     * {@code explicit} (the verifier's {@code mintTransitions}), plus each one that consumes a
     * declared budget place, since a budget token is what a fork consumes when it mints
     * (NU-040).
     */
    public static Set<String> declaredMints(PetriNet net, Set<String> budgetPlaces, Set<String> explicit) {
        var out = new TreeSet<String>(CodePointOrder.COMPARATOR);
        out.addAll(explicit);
        for (var t : net.transitions()) {
            if (t.inputSpecs().stream().anyMatch(in -> budgetPlaces.contains(in.place().name()))) {
                out.add(t.name());
            }
        }
        return out;
    }

    /**
     * Why {@code declared} names a mint transition that {@code net} does not have, or
     * {@code null}: {@code declared mint transition{s} 'a', 'b' not in the net (NU-010)}, the
     * unknown names deduplicated in code-point order. A typo'd declaration would silently leave a
     * real mint undeclared, so every entry point rejects it with this reason.
     */
    public static String unknownMintReason(PetriNet net, java.util.Collection<String> declared) {
        var inNet = new HashSet<String>();
        net.transitions().forEach(t -> inNet.add(t.name()));
        var unknown = new TreeSet<String>(CodePointOrder.COMPARATOR);
        for (var n : declared) {
            if (!inNet.contains(n)) {
                unknown.add(n);
            }
        }
        if (unknown.isEmpty()) {
            return null;
        }
        var quoted = new ArrayList<String>();
        unknown.forEach(n -> quoted.add("'" + n + "'"));
        return "declared mint transition" + (unknown.size() == 1 ? "" : "s") + " " + String.join(", ", quoted)
            + " not in the net (NU-010)";
    }

    /**
     * The transitions of {@code net} that write a coloured place of the fragment without consuming
     * one and are not in {@code mints}, in net order, when declaring them is all that keeps
     * {@code net} out of the fragment: {@link #classify} admits {@code net} with every transition
     * read as a mint and rejects it with {@code mints}. Empty otherwise. These are the undeclared
     * mints a Route B decline points at (NU-010).
     */
    public static List<String> undeclaredMints(
            PetriNet net, FragmentMode mode, Set<String> carriers, Set<String> mints) {
        if (classify(net, mode, carriers, mints) != null) {
            return List.of();
        }
        var every = new HashSet<String>();
        net.transitions().forEach(t -> every.add(t.name()));
        var fragment = classify(net, mode, carriers, every);
        if (fragment == null) {
            return List.of();
        }
        return fragment.mints().stream().filter(m -> !mints.contains(m)).toList();
    }

    /**
     * The sentence a Route B decline adds when {@link #undeclaredMints} names transitions: which
     * transitions to declare, and with what.
     */
    public static String undeclaredMintsPointer(List<String> undeclared) {
        var names = new ArrayList<String>();
        undeclared.forEach(t -> names.add("'" + t + "'"));
        boolean one = undeclared.size() == 1;
        return String.join(", ", names) + " " + (one ? "writes" : "write")
            + " a coloured place without consuming one and " + (one ? "is" : "are")
            + " not declared to mint (NU-010); if the action writes a name minted with freshName(), declare "
            + (one ? "it" : "them") + " with mintTransitions";
    }

    /**
     * The report lines naming the &nu; contracts a verdict rests on (NU-010, NU-051): the
     * transitions read as mints, and the coloured consumers whose action writes are read as
     * relays. Empty when there are none. The analyses cannot check what an action writes, so a
     * verdict holds only while these actions keep the contracts.
     */
    public static String contractNote(List<String> mints, List<String> relays) {
        var out = new StringBuilder();
        if (!mints.isEmpty()) {
            out.append("Mint contract (NU-010) assumed for ").append(String.join(", ", mints))
               .append(": each writes a freshly minted name into every coloured place it writes.\n");
        }
        if (!relays.isEmpty()) {
            out.append("Relay contract (NU-051) assumed for ").append(String.join(", ", relays))
               .append(": each writes the name it consumed into every coloured place it writes.\n");
        }
        return out.toString();
    }

    public boolean isColoured(String place) {
        return coloured.contains(place);
    }

    Role role(String transition) {
        return roles.getOrDefault(transition, new Role.Ordinary());
    }

    /**
     * Classifies {@code net} under {@code mode}. Returns {@code null} when the net
     * is not a &nu;-net (no match transition) or falls outside the admitted fragment
     * (the caller falls back to the SMT / Route A path).
     *
     * <p>Under {@link FragmentMode#BASE} the {@code carrierPlaces} are ignored and a
     * non-match transition consuming a coloured place takes the net out of fragment.
     * Under {@link FragmentMode#EXTENDED} the declared {@code carrierPlaces} are
     * unioned into the coloured set before role assignment (so a name minted at a
     * fork is threaded through them) and a non-match transition consuming exactly one
     * coloured place at count exactly one is admitted as a {@link Role.Consume}
     * (drain / relay), NU-051. EXTENDED also unions every join's declared relay targets
     * into the coloured set and lets a join write them (NU-054); BASE ignores relay
     * declarations, as it ignores carriers.
     *
     * <p>Both modes reject a net where any coloured place carries a reset, read, or
     * inhibitor arc: those arcs would be silently misclassified {@code Ordinary} and
     * the name layer would drift from the base marking (a soundness guard; rejection
     * just falls back to the sound over-approximation).
     *
     * <p>A transition that writes a coloured place without consuming one is read as a
     * <b>mint</b> only when it is named in {@code mintTransitions}, the declared mints
     * ({@link #declaredMints}). The declaration is the net's statement that the action writes
     * a name freshly minted by {@code freshName()} into each coloured place it writes (NU-010).
     * An action may write any value, a copied correlation id included, so without the
     * declaration the name layer cannot give the deposit a fresh symbol and the net is
     * rejected. A deposit the executor makes on timeout is never a mint, declared or not: a
     * forward copies a consumed value and an {@code Out.Place} writes a unit token with no name
     * (IO-013, IO-014). A join's timeout may write a relay target only by forwarding one of its
     * match keys, the one write that carries the matched name. The executor checks every relay
     * deposit (NU-054) and fails the firing on any other, so no timeout write relies on a
     * contract.
     */
    public static NameFragment classify(
            PetriNet net, FragmentMode mode, Set<String> carrierPlaces, Set<String> mintTransitions) {
        // Code-point order: the coloured order indexes the name layer in every implementation.
        var coloured = new TreeSet<String>(CodePointOrder.COMPARATOR);
        boolean anyMatch = false;
        for (var t : net.transitions()) {
            if (t.matchSpec() != null) {
                anyMatch = true;
                for (var key : t.matchSpec().keys()) {
                    coloured.add(key.place().name());
                }
            }
        }
        if (!anyMatch || coloured.isEmpty()) {
            return null;
        }
        if (mode == FragmentMode.EXTENDED) {
            // Declared carrier places thread a minted name from the fork to the join
            // inputs, so they are part of the coloured (name-partitioned) set.
            coloured.addAll(carrierPlaces);
            // A join's relay targets carry the name it matched onward (NU-054), so they are
            // coloured too — which also brings them under the arc exclusion below and the
            // off-key rule of the join role.
            for (var t : net.transitions()) {
                if (t.matchSpec() != null) {
                    for (var relay : t.matchSpec().relays()) {
                        coloured.add(relay.place().name());
                    }
                }
            }
        }

        // Soundness guard (BOTH modes): no coloured place may carry a reset, read, or
        // inhibitor arc on any transition. Such an arc would be silently misclassified
        // Ordinary and the name layer would drift from the base marking (e.g. a reset
        // zeroes the place while the name layer keeps its symbol, breaking the
        // count == name-total invariant). Checked after the coloured set is finalized
        // (a carrier could carry such an arc). Rejection just falls back to the sound
        // over-approximation.
        for (var t : net.transitions()) {
            if (t.resets().stream().anyMatch(r -> coloured.contains(r.place().name()))
                    || t.reads().stream().anyMatch(r -> coloured.contains(r.place().name()))
                    || t.inhibitors().stream().anyMatch(i -> coloured.contains(i.place().name()))) {
                return null;
            }
        }

        var roles = new HashMap<String, Role>();
        var mintNames = new ArrayList<String>();
        var relayNames = new ArrayList<String>();
        for (var t : net.transitions()) {
            boolean consumesColoured =
                t.inputSpecs().stream().anyMatch(in -> coloured.contains(in.place().name()));
            var outcomes = BranchOutcomes.outcomes(t);
            // The name layer adds one symbol per coloured output place of a firing, as the
            // base marking adds one token per place an action writes. A timeout forward
            // deposits one token per consumed token ([IO-014]); into a coloured place at any
            // count but one, the name layer would lose track of the base marking.
            for (var o : outcomes) {
                for (var e : o.deposits().entrySet()) {
                    if (coloured.contains(e.getKey().name())
                            && !e.getValue().equals(new BranchOutcomes.Deposit.Tokens(1))) {
                        return null;
                    }
                }
            }
            boolean producesColoured = false;
            for (var o : outcomes) {
                for (var p : o.places()) {
                    if (coloured.contains(p.name())) {
                        producesColoured = true;
                    }
                }
            }
            // What the executor itself writes into a coloured place on timeout: a copy of a
            // consumed value (forward) or a unit token (place). Neither is a fresh name.
            var timeoutColoured = new ArrayList<BranchOutcomes.TimeoutWrite>();
            for (var w : BranchOutcomes.timeoutWrites(t)) {
                if (coloured.contains(w.to())) {
                    timeoutColoured.add(w);
                }
            }

            Role role;
            if (t.matchSpec() != null) {
                // A join may write a coloured place only as a declared relay target (NU-054,
                // EXTENDED); any other coloured output is a re-mint — out of fragment.
                var relayTo = new HashSet<String>();
                if (mode == FragmentMode.EXTENDED) {
                    for (var relay : t.matchSpec().relays()) {
                        relayTo.add(relay.place().name());
                    }
                }
                if (producesColoured) {
                    for (var o : outcomes) {
                        for (var p : o.places()) {
                            if (coloured.contains(p.name()) && !relayTo.contains(p.name())) {
                                return null;
                            }
                        }
                    }
                }
                var keyPlaces = new HashSet<String>();
                for (var key : t.matchSpec().keys()) {
                    keyPlaces.add(key.place().name());
                }
                // What the executor writes into a relay target on timeout is checked like an
                // action's write (NU-054). Only a forward of a match key carries the matched
                // name. A unit token has none and a forward of another input carries that
                // input's name, so such a firing fails and deposits nothing, while the name
                // layer would relay the matched name.
                for (var w : timeoutColoured) {
                    if (w.from() == null || !keyPlaces.contains(w.from())) {
                        return null;
                    }
                }
                // A coloured place consumed off-key is taken FIFO, whatever its name; the
                // join step only removes the matched name from the keys, so the name layer
                // would keep a symbol the base marking has lost.
                for (var in : t.inputSpecs()) {
                    if (coloured.contains(in.place().name()) && !keyPlaces.contains(in.place().name())) {
                        return null;
                    }
                }
                var colouredIn = new ArrayList<Map.Entry<String, Integer>>();
                for (var key : t.matchSpec().keys()) {
                    var place = key.place().name();
                    // One/Exactly consume a fixed count of the matched name, which
                    // the SCG step removes faithfully. All/AtLeast consume ALL
                    // matching tokens at runtime — the fixed-count step would
                    // under-consume — so drop those to the sound over-approximation.
                    Integer required = fixedRequiredCount(t, place);
                    if (required == null) {
                        return null;
                    }
                    colouredIn.add(Map.entry(place, required));
                }
                colouredIn.sort(Map.Entry.comparingByKey(CodePointOrder.COMPARATOR));
                role = new Role.Join(colouredIn, Set.copyOf(relayTo));
            } else if (consumesColoured) {
                // A non-match transition consuming a coloured place. BASE: out of
                // fragment (the consumed name would be ambiguous). EXTENDED: a drain
                // (no coloured output) or relay (re-emits the same symbol into its
                // coloured outputs), admitted ONLY when it consumes exactly ONE
                // coloured place at count EXACTLY ONE (In.One or In.Exactly{count:1}).
                // More than one coloured input, or any higher / All / AtLeast count,
                // would over-count the name layer relative to the base marking (which
                // adds exactly one token per output place) — reject to the sound
                // over-approximation.
                if (mode != FragmentMode.EXTENDED) {
                    return null;
                }
                var colouredInputs = new ArrayList<Arc.In>();
                for (var in : t.inputSpecs()) {
                    if (coloured.contains(in.place().name())) {
                        colouredInputs.add(in);
                    }
                }
                if (colouredInputs.size() != 1) {
                    return null; // multi-coloured-input consumer — out of the supported fragment
                }
                var only = colouredInputs.get(0);
                boolean countOne = switch (only) {
                    case Arc.In.One _ -> true;
                    case Arc.In.Exactly e -> e.count() == 1;
                    default -> false;
                };
                if (!countOne) {
                    return null; // count != 1 — over-approx fallback (Blocker 1 & 2)
                }
                var inputPlace = only.place().name();
                // A timeout deposit relays the consumed name only when it forwards the coloured
                // input itself. A forward of another input copies a name the relay did not
                // consume, and a unit token has none.
                for (var w : timeoutColoured) {
                    if (!inputPlace.equals(w.from())) {
                        return null;
                    }
                }
                if (producesColoured) {
                    relayNames.add(t.name());
                }
                role = new Role.Consume(inputPlace);
            } else if (producesColoured) {
                // Minting fork: produces a coloured token, consumes none. Read as a mint only
                // when declared (NU-010), and never when the executor writes a coloured place on
                // timeout.
                if (!mintTransitions.contains(t.name()) || !timeoutColoured.isEmpty()) {
                    return null;
                }
                mintNames.add(t.name());
                role = new Role.Mint();
            } else {
                role = new Role.Ordinary();
            }
            roles.put(t.name(), role);
        }

        return new NameFragment(new ArrayList<>(coloured), coloured, roles, mintNames, relayNames);
    }

    /**
     * The fixed per-firing consumption of the matched name for {@code t}'s input
     * on {@code placeName}, or {@code null} when the cardinality consumes ALL
     * matching tokens (All/AtLeast) or no such input exists — neither of which the
     * fixed-count SCG step can model faithfully.
     */
    private static Integer fixedRequiredCount(Transition t, String placeName) {
        for (var in : t.inputSpecs()) {
            if (in.place().name().equals(placeName)) {
                return switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.All _ -> null;
                    case Arc.In.AtLeast _ -> null;
                };
            }
        }
        return null;
    }
}
