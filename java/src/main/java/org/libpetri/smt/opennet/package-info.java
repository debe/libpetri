/**
 * Open-net verification: a subnet checked in isolation against a contract, with its ports
 * played by the environment ([VER-022]). Entry point:
 * {@link org.libpetri.smt.opennet.OpenNetVerifier#verifyOpenNet}.
 *
 * <p>A caller that builds its nets from a fixed vocabulary of subnets can prove each subnet
 * once. A proof then costs what the subnet costs rather than what the interleavings of the
 * composed net cost; the composition argument stays the caller's own.
 *
 * <p>The package is split the way the TypeScript reference ({@code verification/open-net}) is,
 * so the two can be read side by side: the contract and its builder
 * ({@link org.libpetri.smt.opennet.OpenNetContract}), the closure that turns the contract's
 * environment into net structure ({@link org.libpetri.smt.opennet.OpenNetClosure}), the one
 * predicate both routes judge a quiescent marking by, the graph route, the SMT route, the
 * result types and the report. Only the contract, the closure, the options, the entry point
 * and the result types are public; the routes and the predicate are package-private, because
 * a second caller of them is exactly how the two routes would stop judging the same sets.
 */
package org.libpetri.smt.opennet;
