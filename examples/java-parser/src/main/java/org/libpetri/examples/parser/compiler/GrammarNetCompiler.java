package org.libpetri.examples.parser.compiler;

import org.libpetri.core.*;
import org.libpetri.examples.parser.ast.AstNode;
import org.libpetri.examples.parser.grammar.*;
import org.libpetri.examples.parser.lexer.LexToken;
import org.libpetri.examples.parser.lexer.TokenType;

import java.time.Instant;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.function.Predicate;

/**
 * Compiles a Grammar into a Petri net.
 *
 * <p>Each grammar element maps to a specific net pattern:
 * <ul>
 *   <li>Terminal → match token, advance or error</li>
 *   <li>TokenMatch → match by type, advance or error</li>
 *   <li>Sequence → chain subnets</li>
 *   <li>Choice → dispatch with XOR, FIRST-set predicates</li>
 *   <li>Repetition → loop subnet</li>
 *   <li>Optional → skip/enter dispatch</li>
 *   <li>NonTerminal → call with int site ID push, return via XOR dispatch</li>
 * </ul>
 */
public final class GrammarNetCompiler {

    private final Grammar grammar;
    private int placeCounter = 0;
    private int transitionCounter = 0;
    private int siteIdCounter = 0;

    // Production name → start/end places
    private final Map<String, Place<ParseState>> productionStartPlaces = new LinkedHashMap<>();
    private final Map<String, Place<ParseState>> productionEndPlaces = new LinkedHashMap<>();

    // Return dispatchers: production name → list of (siteId, returnPlace)
    private final Map<String, List<ReturnSite>> returnSites = new LinkedHashMap<>();

    // All transitions collected during compilation
    private final List<Transition> allTransitions = new ArrayList<>();

    // Error place for parse failures
    private final Place<ParseState> errorPlace = makePlace("error");

    private record ReturnSite(int siteId, Place<ParseState> returnPlace) {}

    private GrammarNetCompiler(Grammar grammar) {
        this.grammar = grammar;
    }

    /**
     * Compile a grammar into a Petri net parser.
     */
    public static CompiledParserNet compile(Grammar grammar) {
        var compiler = new GrammarNetCompiler(grammar);
        return compiler.doCompile();
    }

    private CompiledParserNet doCompile() {
        // Phase 1: Create start/end places for each production
        for (var name : grammar.productionNames()) {
            productionStartPlaces.put(name, makePlace(name + "_start"));
            productionEndPlaces.put(name, makePlace(name + "_end"));
        }

        // Phase 2: Compile each production body
        for (var prod : grammar.productions()) {
            var startPlace = productionStartPlaces.get(prod.name());
            var endPlace = productionEndPlaces.get(prod.name());
            var subnet = compileElement(prod.body(), prod.name());

            // Connect production start → subnet start
            allTransitions.add(makePassthrough(
                prod.name() + "_enter", startPlace, subnet.startPlace()));

            // Connect subnet end → production end
            allTransitions.add(makePassthrough(
                prod.name() + "_exit", subnet.endPlace(), endPlace));
        }

        // Phase 3: Build return dispatchers
        finalizeReturns();

        // Phase 4: Build the net
        var globalStart = makePlace("parse_start");
        var globalEnd = makePlace("parse_end");

        // Connect global start → start production
        var startProdPlace = productionStartPlaces.get(grammar.startProduction());
        allTransitions.add(makePassthrough("global_enter", globalStart, startProdPlace));

        // Connect start production end → global end
        var startProdEnd = productionEndPlaces.get(grammar.startProduction());
        allTransitions.add(makePassthrough("global_exit", startProdEnd, globalEnd));

        var builder = PetriNet.builder("JavaParser");
        for (var t : allTransitions) {
            builder.transition(t);
        }
        // Ensure error place is in the net
        builder.place(errorPlace);
        builder.place(globalStart);
        builder.place(globalEnd);

        var net = builder.build();

        return new CompiledParserNet(
            net, globalStart, globalEnd, errorPlace,
            productionStartPlaces, productionEndPlaces,
            net.places().size(), net.transitions().size(),
            grammar.productions().size()
        );
    }

    // ==================== Element Compilation ====================

    private SubNet compileElement(GrammarElement element, String context) {
        return switch (element) {
            case GrammarElement.Terminal t -> compileTerminal(t, context);
            case GrammarElement.TokenMatch t -> compileTokenMatch(t, context);
            case GrammarElement.NonTerminal nt -> compileNonTerminal(nt, context);
            case GrammarElement.Sequence seq -> compileSequence(seq, context);
            case GrammarElement.Choice ch -> compileChoice(ch, context);
            case GrammarElement.Repetition rep -> compileRepetition(rep, context);
            case GrammarElement.Optional opt -> compileOptional(opt, context);
        };
    }

    /**
     * Terminal: consume token, check value, advance position or route to error.
     * Pattern: start → [match_terminal] → end | error
     */
    private SubNet compileTerminal(GrammarElement.Terminal terminal, String context) {
        var start = makePlace(context + "_t_" + sanitize(terminal.value()) + "_in");
        var end = makePlace(context + "_t_" + sanitize(terminal.value()) + "_out");

        var transition = Transition.builder(context + "_match_" + sanitize(terminal.value()))
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.xor(end, errorPlace))
            .action(ctx -> {
                var state = ctx.input(start);
                var current = state.current();
                if (current.value().equals(terminal.value())) {
                    var next = state.advance().pushAst(
                        new AstNode.Literal(terminal.value(), AstNode.LiteralKind.STRING));
                    ctx.output(end, next);
                } else {
                    ctx.output(errorPlace, state);
                }
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(transition);
        return new SubNet(start, end, List.of(transition));
    }

    /**
     * TokenMatch: consume token by type, advance position or route to error.
     * Pattern: start → [match_type] → end | error
     */
    private SubNet compileTokenMatch(GrammarElement.TokenMatch match, String context) {
        var start = makePlace(context + "_tm_" + match.type().name() + "_in");
        var end = makePlace(context + "_tm_" + match.type().name() + "_out");
        var type = match.type();

        var transition = Transition.builder(context + "_match_" + match.type().name())
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.xor(end, errorPlace))
            .action(ctx -> {
                var state = ctx.input(start);
                var current = state.current();
                if (current.type() == type) {
                    var kind = tokenTypeToLiteralKind(type);
                    var next = state.advance().pushAst(
                        kind != null
                            ? new AstNode.Literal(current.value(), kind)
                            : new AstNode.Identifier(current.value()));
                    ctx.output(end, next);
                } else {
                    ctx.output(errorPlace, state);
                }
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(transition);
        return new SubNet(start, end, List.of(transition));
    }

    /**
     * NonTerminal: push return site ID, route to production start.
     * Return handled by finalizeReturns().
     * Pattern: start → [call_prod] → prod_start ... prod_end → [return] → end
     */
    private SubNet compileNonTerminal(GrammarElement.NonTerminal nt, String context) {
        var start = makePlace(context + "_call_" + nt.name() + "_in");
        var end = makePlace(context + "_call_" + nt.name() + "_out");
        int siteId = siteIdCounter++;

        var prodStart = productionStartPlaces.get(nt.name());
        if (prodStart == null) {
            throw new IllegalStateException("Unknown production: " + nt.name());
        }

        // Call transition: push return site ID, route to production start
        var callTransition = Transition.builder(context + "_call_" + nt.name())
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.place(prodStart))
            .action(ctx -> {
                var state = ctx.input(start);
                ctx.output(prodStart, state.pushCall(siteId));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(callTransition);

        // Register return site
        returnSites.computeIfAbsent(nt.name(), k -> new ArrayList<>())
            .add(new ReturnSite(siteId, end));

        return new SubNet(start, end, List.of(callTransition));
    }

    /**
     * Sequence: chain subnets together.
     * Pattern: → [A] → mid → [B] → mid → [C] →
     */
    private SubNet compileSequence(GrammarElement.Sequence sequence, String context) {
        var elements = sequence.elements();
        var subnets = new ArrayList<SubNet>();

        for (int i = 0; i < elements.size(); i++) {
            subnets.add(compileElement(elements.get(i), context + "_s" + i));
        }

        // Chain: connect end of each to start of next
        var transitions = new ArrayList<Transition>();
        for (int i = 0; i < subnets.size() - 1; i++) {
            var from = subnets.get(i).endPlace();
            var to = subnets.get(i + 1).startPlace();
            var t = makePassthrough(context + "_chain_" + i, from, to);
            transitions.add(t);
            allTransitions.add(t);
        }

        transitions.addAll(subnets.stream().flatMap(s -> s.transitions().stream()).toList());

        return new SubNet(
            subnets.getFirst().startPlace(),
            subnets.getLast().endPlace(),
            transitions
        );
    }

    /**
     * Choice: dispatch with XOR based on FIRST set lookahead.
     * Pattern: start → [dispatch] → branch_1_start | branch_2_start | ...
     */
    private SubNet compileChoice(GrammarElement.Choice choice, String context) {
        var start = makePlace(context + "_choice_in");
        var end = makePlace(context + "_choice_out");
        var alternatives = choice.alternatives();

        // Compile each alternative
        var branchSubnets = new ArrayList<SubNet>();
        var branchPredicates = new ArrayList<Predicate<LexToken>>();

        for (int i = 0; i < alternatives.size(); i++) {
            var subnet = compileElement(alternatives.get(i), context + "_alt" + i);
            branchSubnets.add(subnet);
            branchPredicates.add(grammar.firstPredicate(alternatives.get(i)));

            // Connect branch end → choice end
            var merge = makePassthrough(context + "_merge_" + i, subnet.endPlace(), end);
            allTransitions.add(merge);
        }

        // Build XOR output places (include errorPlace for fallback)
        var xorPlacesList = new ArrayList<Place<?>>();
        branchSubnets.forEach(s -> xorPlacesList.add(s.startPlace()));
        xorPlacesList.add(errorPlace);
        var xorPlaces = xorPlacesList.toArray(Place[]::new);

        // Dispatch transition with XOR
        // Safe unchecked cast: Place<ParseState> erases to raw Place; all places in this compiler carry ParseState tokens
        @SuppressWarnings("unchecked")
        var dispatch = Transition.builder(context + "_dispatch")
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.xor(xorPlaces))
            .action(ctx -> {
                var state = ctx.input(start);
                var current = state.current();

                for (int i = 0; i < branchPredicates.size(); i++) {
                    if (branchPredicates.get(i).test(current)) {
                        ctx.output(branchSubnets.get(i).startPlace(), state);
                        return CompletableFuture.completedFuture(null);
                    }
                }

                // No match — route to error
                ctx.output(errorPlace, state);
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(dispatch);

        var transitions = new ArrayList<Transition>();
        transitions.add(dispatch);
        branchSubnets.forEach(s -> transitions.addAll(s.transitions()));

        return new SubNet(start, end, transitions);
    }

    /**
     * Repetition: loop body zero or more times.
     * Pattern: start → [decide] → body_start → body_end → loop back; or → exit
     */
    private SubNet compileRepetition(GrammarElement.Repetition rep, String context) {
        var start = makePlace(context + "_rep_in");
        var end = makePlace(context + "_rep_out");

        var bodySubnet = compileElement(rep.body(), context + "_rep_body");
        var bodyPredicate = grammar.firstPredicate(rep.body());

        // Decision transition: enter body or exit
        var decide = Transition.builder(context + "_rep_decide")
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.xor(bodySubnet.startPlace(), end))
            .action(ctx -> {
                var state = ctx.input(start);
                if (bodyPredicate.test(state.current())) {
                    ctx.output(bodySubnet.startPlace(), state);
                } else {
                    ctx.output(end, state);
                }
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(decide);

        // Loop back: body end → start (for another iteration)
        var loopBack = makePassthrough(context + "_rep_loop", bodySubnet.endPlace(), start);
        allTransitions.add(loopBack);

        var transitions = new ArrayList<Transition>();
        transitions.add(decide);
        transitions.add(loopBack);
        transitions.addAll(bodySubnet.transitions());

        return new SubNet(start, end, transitions);
    }

    /**
     * Optional: enter body or skip.
     * Pattern: start → [decide] → body_start | skip → end
     */
    private SubNet compileOptional(GrammarElement.Optional opt, String context) {
        var start = makePlace(context + "_opt_in");
        var end = makePlace(context + "_opt_out");

        var bodySubnet = compileElement(opt.body(), context + "_opt_body");
        var bodyPredicate = grammar.firstPredicate(opt.body());

        // Decision: enter body or skip
        var decide = Transition.builder(context + "_opt_decide")
            .inputs(Arc.In.one(start))
            .outputs(Arc.Out.xor(bodySubnet.startPlace(), end))
            .action(ctx -> {
                var state = ctx.input(start);
                if (bodyPredicate.test(state.current())) {
                    ctx.output(bodySubnet.startPlace(), state);
                } else {
                    ctx.output(end, state);
                }
                return CompletableFuture.completedFuture(null);
            })
            .build();

        allTransitions.add(decide);

        // Connect body end → end
        var merge = makePassthrough(context + "_opt_merge", bodySubnet.endPlace(), end);
        allTransitions.add(merge);

        var transitions = new ArrayList<Transition>();
        transitions.add(decide);
        transitions.add(merge);
        transitions.addAll(bodySubnet.transitions());

        return new SubNet(start, end, transitions);
    }

    // ==================== Return Dispatchers ====================

    /**
     * Build return dispatchers for all productions that are called as non-terminals.
     * Each production end gets a transition that pops the call stack and routes to
     * the correct return site via XOR dispatch.
     */
    private void finalizeReturns() {
        for (var entry : returnSites.entrySet()) {
            var prodName = entry.getKey();
            var sites = entry.getValue();
            var prodEnd = productionEndPlaces.get(prodName);

            if (sites.isEmpty()) continue;

            if (sites.size() == 1) {
                // Single call site — direct route, no XOR needed
                var site = sites.getFirst();
                var returnTransition = Transition.builder(prodName + "_return")
                    .inputs(Arc.In.one(prodEnd))
                    .outputs(Arc.Out.place(site.returnPlace()))
                    .action(ctx -> {
                        var state = ctx.input(prodEnd);
                        ctx.output(site.returnPlace(), state.popCall());
                        return CompletableFuture.completedFuture(null);
                    })
                    .build();
                allTransitions.add(returnTransition);
            } else {
                // Multiple call sites — XOR dispatch based on call stack top
                var returnPlacesList = new ArrayList<Place<?>>();
                sites.forEach(s -> returnPlacesList.add(s.returnPlace()));
                returnPlacesList.add(errorPlace);
                var returnPlaces = returnPlacesList.toArray(Place[]::new);

                // Build site ID → index lookup array for O(1) dispatch
                int maxSiteId = sites.stream().mapToInt(ReturnSite::siteId).max().orElse(0);
                var siteIdToIndex = new int[maxSiteId + 1];
                Arrays.fill(siteIdToIndex, -1);
                for (int i = 0; i < sites.size(); i++) {
                    siteIdToIndex[sites.get(i).siteId()] = i;
                }

                // Safe unchecked cast: Place<ParseState> erases to raw Place; all places in this compiler carry ParseState tokens
                @SuppressWarnings("unchecked")
                var returnTransition = Transition.builder(prodName + "_return")
                    .inputs(Arc.In.one(prodEnd))
                    .outputs(Arc.Out.xor(returnPlaces))
                    .action(ctx -> {
                        var state = ctx.input(prodEnd);
                        int returnSiteId = state.peekReturnSite();
                        var popped = state.popCall();

                        int index = (returnSiteId >= 0 && returnSiteId < siteIdToIndex.length)
                            ? siteIdToIndex[returnSiteId] : -1;

                        if (index >= 0) {
                            ctx.output(returnPlaces[index], popped);
                        } else {
                            ctx.output(errorPlace, popped);
                        }
                        return CompletableFuture.completedFuture(null);
                    })
                    .build();
                allTransitions.add(returnTransition);
            }
        }
    }

    // ==================== Helpers ====================

    // Safe unchecked cast: Place.of requires Class<T> but ParseState.class erases to Class<ParseState> via raw type
    @SuppressWarnings("unchecked")
    private Place<ParseState> makePlace(String name) {
        placeCounter++;
        return Place.of(name, (Class<ParseState>) (Class<?>) ParseState.class);
    }

    private Transition makePassthrough(String name, Place<ParseState> from, Place<ParseState> to) {
        return Transition.builder(name)
            .inputs(Arc.In.one(from))
            .outputs(Arc.Out.place(to))
            .action(ctx -> {
                ctx.output(to, ctx.input(from));
                return CompletableFuture.completedFuture(null);
            })
            .build();
    }

    private String sanitize(String s) {
        return s.replaceAll("[^a-zA-Z0-9_]", "_");
    }

    private AstNode.LiteralKind tokenTypeToLiteralKind(TokenType type) {
        return switch (type) {
            case INT_LITERAL -> AstNode.LiteralKind.INT;
            case LONG_LITERAL -> AstNode.LiteralKind.LONG;
            case FLOAT_LITERAL -> AstNode.LiteralKind.FLOAT;
            case DOUBLE_LITERAL -> AstNode.LiteralKind.DOUBLE;
            case CHAR_LITERAL -> AstNode.LiteralKind.CHAR;
            case STRING_LITERAL -> AstNode.LiteralKind.STRING;
            case TEXT_BLOCK -> AstNode.LiteralKind.TEXT_BLOCK;
            case BOOLEAN_LITERAL -> AstNode.LiteralKind.BOOLEAN;
            case NULL_LITERAL -> AstNode.LiteralKind.NULL;
            default -> null;
        };
    }
}
