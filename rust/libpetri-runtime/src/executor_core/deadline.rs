use std::time::Instant;

/// Tolerance for deadline enforcement to account for timer jitter.
pub(crate) const DEADLINE_TOLERANCE_MS: f64 = 5.0;

/// Wall-clock milliseconds since the Unix epoch. Used for `created_at`
/// timestamps on tokens and events.
pub(crate) fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

/// Milliseconds elapsed since `start`. The monotonic clock backing
/// [`Instant`] is the one the executor measures relative time against
/// (deadlines, windows, action latency).
#[inline]
pub(crate) fn elapsed_ms_since(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}
