/**
 * Formal verification for Time Petri Nets using the State Class Graph method.
 *
 * <h2>Overview</h2>
 * <p>
 * This package implements the Berthomieu-Diaz (1991) algorithm for formal
 * verification of Time Petri Nets. It provides mathematical guarantees about
 * liveness properties through exhaustive state class graph exploration.
 *
 * <h2>Class Hierarchy</h2>
 * <pre>
 * Analysis Package
 * +-- Core Data Structures
 * |   +-- {@link org.libpetri.analysis.MarkingState}     - Token distribution (immutable)
 * |   +-- {@link org.libpetri.analysis.DBM}              - Difference Bound Matrix
 * |   +-- {@link org.libpetri.analysis.StateClass}       - (Marking, DBM) pair
 * |
 * +-- Graph Construction
 * |   +-- {@link org.libpetri.analysis.StateClassGraph}  - State class graph builder
 * |   +-- {@link org.libpetri.analysis.SCCAnalyzer}      - Tarjan's SCC algorithm
 * |
 * +-- Analyzer
 *     +-- {@link org.libpetri.analysis.TimePetriNetAnalyzer}  - Formal TPN analyzer
 * </pre>
 *
 * <h2>Mathematical Foundation (Berthomieu-Diaz 1991)</h2>
 * <p>
 * A Time Petri Net configuration is (M, v) where:
 * <ul>
 *   <li>M is the current marking (token distribution)</li>
 *   <li>v: enabled(M) -> R>=0 assigns a clock value to each enabled transition</li>
 * </ul>
 * <p>
 * A <b>state class</b> C = (M, D) represents all configurations (M, v) where
 * the clock values v satisfy the constraints in the firing domain D.
 *
 * <h2>Key Concepts</h2>
 * <ul>
 *   <li><b>State Class</b> - A pair (M, D) where M is a marking and D is a
 *       firing domain (DBM) representing all valid clock valuations</li>
 *   <li><b>Firing Domain</b> - A convex polyhedron of valid firing times,
 *       represented as a Difference Bound Matrix (DBM)</li>
 *   <li><b>DBM</b> - Matrix where bounds[i][j] = upper bound on (x_i - x_j),
 *       canonicalized via Floyd-Warshall</li>
 *   <li><b>Successor Computation</b> - Berthomieu-Diaz formula:
 *       intersect -> substitute -> eliminate -> add fresh clocks -> canonicalize</li>
 * </ul>
 *
 * <h2>Correctness Theorems</h2>
 * <ul>
 *   <li><b>Reachability</b>: Marking M is reachable iff exists (M, D) in SCG</li>
 *   <li><b>Goal Liveness</b>: Goal reachable from all states iff all terminal
 *       SCCs contain goal states</li>
 *   <li><b>Boundedness</b>: For bounded TPNs, the state class graph is finite</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * var result = TimePetriNetAnalyzer.forNet(exampleNet)
 *     .initialMarking(m -> m.tokens(INPUT_QUEUE, 1))
 *     .goalPlaces(CLOSED)
 *     .maxClasses(10_000)
 *     .build()
 *     .analyze();
 *
 * if (result.isGoalLive() && result.isComplete()) {
 *     System.out.println("FORMAL PROOF: Net is goal-live");
 * }
 *
 * // Print detailed report
 * System.out.println(result.report());
 * }</pre>
 *
 * <h2>SCC Analysis (Tarjan 1972)</h2>
 * <p>
 * The {@link org.libpetri.analysis.SCCAnalyzer} implements Tarjan's
 * algorithm for finding Strongly Connected Components in O(V + E) time.
 * <p>
 * Terminal SCCs (bottom SCCs) represent the "final behaviors" of the system.
 * For goal liveness, all terminal SCCs must contain goal states.
 *
 * <h2>References</h2>
 * <ul>
 *   <li>Berthomieu, Diaz (1991): "Modeling and verification of time dependent
 *       systems using Time Petri Nets", IEEE Transactions on Software Engineering</li>
 *   <li>Gardey, Roux, Roux (2006): "State Space Computation and Analysis of
 *       Time Petri Nets", STTT</li>
 *   <li>Tarjan (1972): "Depth-first search and linear graph algorithms",
 *       SIAM Journal on Computing</li>
 * </ul>
 *
 * @see org.libpetri.core Core Petri net types
 * @see org.libpetri.runtime Runtime execution
 */
package org.libpetri.analysis;
