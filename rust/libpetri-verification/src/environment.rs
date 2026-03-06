/// How environment places should be treated during verification.
/// Controls how environment places (external event sources) are treated
/// during formal analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentAnalysisMode {
    /// Environment places are always considered to have tokens available.
    /// Transitions reading from environment places are always enabled.
    AlwaysAvailable,
    /// Environment places are treated as having at most `max_tokens` tokens.
    /// Explores states where 0..=max_tokens tokens are injected.
    Bounded { max_tokens: usize },
    /// Environment places are treated as regular places (no special handling).
    Ignore,
}

/// Creates an `AlwaysAvailable` environment mode.
pub fn always_available() -> EnvironmentAnalysisMode {
    EnvironmentAnalysisMode::AlwaysAvailable
}

/// Creates a `Bounded` environment mode with the given max token count.
pub fn bounded(max_tokens: usize) -> EnvironmentAnalysisMode {
    EnvironmentAnalysisMode::Bounded { max_tokens }
}

/// Creates an `Ignore` environment mode (treats env places as regular).
pub fn ignore() -> EnvironmentAnalysisMode {
    EnvironmentAnalysisMode::Ignore
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mode_constructors() {
        assert_eq!(always_available(), EnvironmentAnalysisMode::AlwaysAvailable);
        assert_eq!(bounded(3), EnvironmentAnalysisMode::Bounded { max_tokens: 3 });
        assert_eq!(ignore(), EnvironmentAnalysisMode::Ignore);
    }
}
