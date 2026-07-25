package org.libpetri.runtime;

/**
 * Package-private test seam for lengthening the orchestrator's completion-wait poll fallback.
 *
 * <p>When an action completes it does {@code completionQueue.offer(t); wakeUp()}, so the
 * semaphore is the <em>direct</em> wake-up and the poll is only a safety re-check. A test that
 * wants to prove the direct wake-up (rather than the poll tick) sets the poll far beyond its own
 * run timeout: a working handoff still wakes immediately via the semaphore, while a regressed one
 * parks until the (now huge) poll and the run times out — a deterministic hang instead of a
 * masked latency. Not part of the public API; the interface is package-private so only in-package
 * tests can reach it.
 */
interface AwaitPollTunable {

    /**
     * Sets the maximum time {@code awaitCompletionOrEvent} parks before falling back to a poll
     * re-check. The default (50ms) is fine in production; tests raise it to neutralize the poll.
     *
     * @param millis the poll fallback interval in milliseconds
     */
    void awaitPollMillisForTesting(long millis);
}
