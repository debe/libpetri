package org.libpetri.core.internal;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.libpetri.core.Arc;
import org.libpetri.core.Place;

/**
 * The [IO-012] build-time ambiguity check: the first pair of output branches of a spec that
 * claim the same set of places.
 *
 * <p>The result is defined by enumeration: number the branches as [IO-016] lists them (the
 * {@code <t>_b<i>} numbering of [VER-001]), read each as a set of places, and report the first
 * {@code j} whose set equals that of an earlier branch, with {@code i} the smallest such earlier
 * index. This class computes the same {@code i} and {@code j} without listing every branch, so a
 * spec with exponentially many branches (an {@code And} of many two-way {@code Xor}s) is checked
 * in time linear in its size. The cross-child search below is exponential only when two
 * alternatives of one {@code Xor} have exponentially many branches inside each other's places
 * without ever claiming the same set:
 *
 * <ul>
 *   <li>An {@code And}'s children name pairwise disjoint places, because [IO-011] has already
 *       passed, so two of its branches are equal exactly when they are equal child by child. Its
 *       first duplicate therefore sits in its last child that has one, with every other child at
 *       its branch 0.</li>
 *   <li>A {@code Xor}'s branches are its children's, concatenated. Its first duplicate is in the
 *       first child that either repeats a set internally or produces a set an earlier child also
 *       produces; only that cross-child search enumerates, pruned to the places both sides can
 *       name and done from whichever side has fewer candidates.</li>
 * </ul>
 *
 * <p>Must run after the [IO-011] check: it relies on no branch naming a place twice.
 *
 * <p>Internal API: not part of the public contract.
 */
public final class OutputBranchAmbiguity {

    /**
     * Branches {@code first} and {@code second} claim the same set; {@code places} lists branch
     * {@code first} in leaf order.
     */
    public record Ambiguity(BigInteger first, BigInteger second, List<Place<?>> places) {}

    private record Pair(BigInteger i, BigInteger j) {}

    @FunctionalInterface
    private interface Visitor {
        /** Returns {@code true} to stop the enumeration. */
        boolean visit(BigInteger index, List<Place<?>> places);
    }

    private final Map<Arc.Out, BigInteger> counts = new IdentityHashMap<>();
    private final Map<Arc.Out, Set<Place<?>>> universes = new IdentityHashMap<>();

    private OutputBranchAmbiguity() {}

    /** The first ambiguous pair of output branches of {@code spec}, or {@code null}. */
    public static Ambiguity find(Arc.Out spec) {
        var self = new OutputBranchAmbiguity();
        var pair = self.firstDuplicate(spec);
        return pair == null ? null : new Ambiguity(pair.i(), pair.j(), self.branchAt(spec, pair.i()));
    }

    /** Number of output branches of {@code x} ([IO-016]). */
    private BigInteger count(Arc.Out x) {
        var known = counts.get(x);
        if (known != null) return known;
        BigInteger n = switch (x) {
            case Arc.Out.Place _, Arc.Out.ForwardInput _ -> BigInteger.ONE;
            case Arc.Out.Timeout t -> count(t.child());
            case Arc.Out.Xor xor -> xor.children().stream().map(this::count).reduce(BigInteger.ZERO, BigInteger::add);
            case Arc.Out.And and -> and.children().stream().map(this::count).reduce(BigInteger.ONE, BigInteger::multiply);
        };
        counts.put(x, n);
        return n;
    }

    /** Every place some branch of {@code x} names. */
    private Set<Place<?>> universe(Arc.Out x) {
        var known = universes.get(x);
        if (known != null) return known;
        Set<Place<?>> u = switch (x) {
            case Arc.Out.Place p -> Set.of(p.place());
            case Arc.Out.ForwardInput f -> Set.of(f.to());
            case Arc.Out.Timeout t -> universe(t.child());
            case Arc.Out.Xor xor -> union(xor.children());
            case Arc.Out.And and -> union(and.children());
        };
        universes.put(x, u);
        return u;
    }

    private Set<Place<?>> union(List<Arc.Out> children) {
        var u = new HashSet<Place<?>>();
        for (var c : children) u.addAll(universe(c));
        return u;
    }

    /** The places branch {@code q} of {@code x} names, in leaf order. */
    private List<Place<?>> branchAt(Arc.Out x, BigInteger q) {
        return switch (x) {
            case Arc.Out.Place p -> List.of(p.place());
            case Arc.Out.ForwardInput f -> List.of(f.to());
            case Arc.Out.Timeout t -> branchAt(t.child(), q);
            case Arc.Out.Xor xor -> {
                var rest = q;
                for (var c : xor.children()) {
                    var n = count(c);
                    if (rest.compareTo(n) < 0) yield branchAt(c, rest);
                    rest = rest.subtract(n);
                }
                throw new IllegalArgumentException("branch index out of range");
            }
            case Arc.Out.And and -> {
                var children = and.children();
                var digits = new BigInteger[children.size()];
                var rest = q;
                for (int k = children.size() - 1; k >= 0; k--) {
                    var qr = rest.divideAndRemainder(count(children.get(k)));
                    digits[k] = qr[1];
                    rest = qr[0];
                }
                var out = new ArrayList<Place<?>>();
                for (int k = 0; k < children.size(); k++) out.addAll(branchAt(children.get(k), digits[k]));
                yield out;
            }
        };
    }

    /** The smallest index of a branch of {@code x} claiming exactly {@code s}, or {@code null}. */
    private BigInteger indexOf(Arc.Out x, Set<Place<?>> s) {
        return switch (x) {
            case Arc.Out.Place p -> s.size() == 1 && s.contains(p.place()) ? BigInteger.ZERO : null;
            case Arc.Out.ForwardInput f -> s.size() == 1 && s.contains(f.to()) ? BigInteger.ZERO : null;
            case Arc.Out.Timeout t -> indexOf(t.child(), s);
            case Arc.Out.Xor xor -> {
                var offset = BigInteger.ZERO;
                for (var c : xor.children()) {
                    var r = indexOf(c, s);
                    if (r != null) yield offset.add(r);
                    offset = offset.add(count(c));
                }
                yield null;
            }
            case Arc.Out.And and -> {
                // Children name disjoint places, so each claims exactly its share of s.
                var idx = BigInteger.ZERO;
                int covered = 0;
                for (var c : and.children()) {
                    var share = new HashSet<Place<?>>(s);
                    share.retainAll(universe(c));
                    covered += share.size();
                    var r = indexOf(c, share);
                    if (r == null) yield null;
                    idx = idx.multiply(count(c)).add(r);
                }
                yield covered == s.size() ? idx : null;
            }
        };
    }

    /** The first duplicate pair among the branches of {@code x}, or {@code null}. */
    private Pair firstDuplicate(Arc.Out x) {
        return switch (x) {
            case Arc.Out.Place _, Arc.Out.ForwardInput _ -> null;
            case Arc.Out.Timeout t -> firstDuplicate(t.child());
            case Arc.Out.And and -> {
                var children = and.children();
                var suffix = BigInteger.ONE;
                for (int k = children.size() - 1; k >= 0; k--) {
                    var inner = firstDuplicate(children.get(k));
                    if (inner != null) yield new Pair(inner.i().multiply(suffix), inner.j().multiply(suffix));
                    suffix = suffix.multiply(count(children.get(k)));
                }
                yield null;
            }
            case Arc.Out.Xor xor -> {
                var children = xor.children();
                var offset = BigInteger.ZERO;
                for (int k = 0; k < children.size(); k++) {
                    var c = children.get(k);
                    var earlier = children.subList(0, k);
                    var inner = firstDuplicate(c);
                    var cross = earlier.isEmpty() ? null : firstIndexIn(c, earlier);
                    if (cross != null && (inner == null || cross.compareTo(inner.j()) <= 0)) {
                        var s = new HashSet<Place<?>>(branchAt(c, cross));
                        var before = BigInteger.ZERO;
                        for (var m : earlier) {
                            var r = indexOf(m, s);
                            if (r != null) yield new Pair(before.add(r), offset.add(cross));
                            before = before.add(count(m));
                        }
                        throw new IllegalStateException("cross duplicate without an earlier branch");
                    }
                    if (inner != null) yield new Pair(offset.add(inner.i()), offset.add(inner.j()));
                    offset = offset.add(count(c));
                }
                yield null;
            }
        };
    }

    /**
     * The smallest index of a branch of {@code x} whose set some branch of {@code earlier} also
     * claims, or {@code null}. Enumerates from the side with fewer candidates, each side pruned
     * to the places the other can name.
     */
    private BigInteger firstIndexIn(Arc.Out x, List<Arc.Out> earlier) {
        var ux = universe(x);
        var ue = union(earlier);
        var fromX = restrictedCount(x, ue);
        var fromEarlier = BigInteger.ZERO;
        for (var g : earlier) fromEarlier = fromEarlier.add(restrictedCount(g, ux));
        if (fromX.signum() == 0 || fromEarlier.signum() == 0) return null;
        if (fromX.compareTo(fromEarlier) <= 0) {
            // x's candidates in index order: the first one an earlier sibling claims wins.
            BigInteger[] found = {null};
            enumerate(x, ue, (q, places) -> {
                var s = new HashSet<Place<?>>(places);
                for (var g : earlier) {
                    if (indexOf(g, s) != null) {
                        found[0] = q;
                        return true;
                    }
                }
                return false;
            });
            return found[0];
        }
        BigInteger[] best = {null};
        for (var g : earlier) {
            enumerate(g, ux, (q, places) -> {
                var r = indexOf(x, new HashSet<>(places));
                if (r != null && (best[0] == null || r.compareTo(best[0]) < 0)) best[0] = r;
                return false;
            });
        }
        return best[0];
    }

    /** Number of branches of {@code x} naming only places in {@code allowed}. */
    private BigInteger restrictedCount(Arc.Out x, Set<Place<?>> allowed) {
        return switch (x) {
            case Arc.Out.Place p -> allowed.contains(p.place()) ? BigInteger.ONE : BigInteger.ZERO;
            case Arc.Out.ForwardInput f -> allowed.contains(f.to()) ? BigInteger.ONE : BigInteger.ZERO;
            case Arc.Out.Timeout t -> restrictedCount(t.child(), allowed);
            case Arc.Out.Xor xor -> {
                var n = BigInteger.ZERO;
                for (var c : xor.children()) n = n.add(restrictedCount(c, allowed));
                yield n;
            }
            case Arc.Out.And and -> {
                var n = BigInteger.ONE;
                for (var c : and.children()) {
                    n = n.multiply(restrictedCount(c, allowed));
                    if (n.signum() == 0) break;
                }
                yield n;
            }
        };
    }

    /**
     * Visits, in index order, the branches of {@code x} naming only places in {@code allowed},
     * with their index among all branches of {@code x}. Returns {@code true} if stopped.
     */
    private boolean enumerate(Arc.Out x, Set<Place<?>> allowed, Visitor v) {
        return switch (x) {
            case Arc.Out.Place p -> allowed.contains(p.place()) && v.visit(BigInteger.ZERO, List.of(p.place()));
            case Arc.Out.ForwardInput f -> allowed.contains(f.to()) && v.visit(BigInteger.ZERO, List.of(f.to()));
            case Arc.Out.Timeout t -> enumerate(t.child(), allowed, v);
            case Arc.Out.Xor xor -> {
                var offset = BigInteger.ZERO;
                for (var c : xor.children()) {
                    var base = offset;
                    if (enumerate(c, allowed, (q, places) -> v.visit(base.add(q), places))) yield true;
                    offset = offset.add(count(c));
                }
                yield false;
            }
            case Arc.Out.And and -> restrictedCount(and, allowed).signum() != 0
                && enumerateAnd(and.children(), 0, allowed, BigInteger.ZERO, List.of(), v);
        };
    }

    private boolean enumerateAnd(
            List<Arc.Out> children, int k, Set<Place<?>> allowed,
            BigInteger index, List<Place<?>> places, Visitor v) {
        if (k == children.size()) return v.visit(index, places);
        var c = children.get(k);
        var n = count(c);
        return enumerate(c, allowed, (q, own) -> {
            var joined = new ArrayList<Place<?>>(places.size() + own.size());
            joined.addAll(places);
            joined.addAll(own);
            return enumerateAnd(children, k + 1, allowed, index.multiply(n).add(q), joined, v);
        });
    }

    /** {@code places} as the message lists them: names in order, separated by {@code ", "}. */
    public static String names(List<Place<?>> places) {
        return String.join(", ", places.stream().map(Place::name).toList());
    }
}
