/// How environment places should be treated during verification.
/// Controls how environment places (external event sources) are treated
/// during formal analysis ([VER-006]).
///
/// `#[non_exhaustive]`: a mode added later is not a breaking change for a
/// caller that matches on it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum EnvironmentAnalysisMode {
    /// Environment places are always considered to have tokens available.
    /// Transitions reading from environment places are always enabled.
    AlwaysAvailable,
    /// At most `max_tokens` tokens **resident** in each environment place at a
    /// time: injection refills the place up to `max_tokens`, forever, so a
    /// transition can take at most `max_tokens` from it per firing, but the total
    /// injected over a run is unbounded. For a total, see [`Self::Arrivals`].
    ///
    /// Every route reads the place as a source that holds at most `max_tokens`,
    /// which is the executor only when no transition deposits into an environment
    /// place and the initial marking holds at most `max_tokens` on each one
    /// ([VER-006] AC3). `SmtVerifier` checks both and answers `Unknown`, naming
    /// the place, when either fails.
    Bounded { max_tokens: usize },
    /// Environment places are treated as regular places (no special handling).
    Ignore,
    /// At most `max_tokens` tokens injected into each environment place **in
    /// total**, over the whole run.
    ///
    /// A net rewrite, not an encoding: before any route runs, `SmtVerifier`
    /// closes the net with the [VER-022] construction for an optional arrival
    /// group (`open_net::close_arrivals`) — environment place `P`, the `i`-th
    /// registered, gets a source place `env:optional[i]` holding `max_tokens`
    /// tokens, an injection transition `env:arrive?[i]:P`, and `env:decline[i]`,
    /// which discards an undelivered arrival. A run may rest after any number of
    /// arrivals up to `max_tokens`, so "at most" holds for quiescence too. The
    /// rewritten net has no environment places, so the enumeration route,
    /// P-invariants and quiescence apply to it as to any closed net;
    /// counterexample traces name the injection transitions, one firing per
    /// arrival, and the declines. An injection into a coloured place ([NU-051]) is
    /// not a mint, so the ν routes decline such a net by name.
    ///
    /// Only `SmtVerifier` (and `SubnetDef` verification through it) applies the
    /// rewrite: a state-class graph built directly with environment places under
    /// this mode panics.
    Arrivals { max_tokens: usize },
    /// Between `min_tokens` and `max_tokens` tokens injected into each environment
    /// place **in total**, over the whole run: [`Self::Arrivals`] with a mandatory
    /// part. `Arrivals { max_tokens: k }` is `ArrivalsBetween { min_tokens: 0,
    /// max_tokens: k }`, and [`arrivals_between`] returns it in that form, so the two
    /// compare equal; exact accounting is `ArrivalsBetween { min_tokens: k, max_tokens:
    /// k }`.
    ///
    /// The same net rewrite, with the full [VER-022] arrival group (`min_tokens`,
    /// `max_tokens`): environment place `P`, the `i`-th registered, gets a mandatory
    /// source `env:arrivals[i]` holding `min_tokens` with `env:arrive[i]:P`, and an
    /// optional source `env:optional[i]` holding `max_tokens − min_tokens` with
    /// `env:arrive?[i]:P` and `env:decline[i]`; a source whose count is `0` is left out
    /// with its transitions. A run is quiescent only once every mandatory arrival has
    /// been delivered.
    ///
    /// `SmtVerifier` panics on `max_tokens < min_tokens`.
    ArrivalsBetween { min_tokens: usize, max_tokens: usize },
}

impl EnvironmentAnalysisMode {
    /// Panics when a component that models injection itself is handed environment
    /// places under [`Self::Arrivals`], which only `SmtVerifier` applies.
    pub(crate) fn reject_arrivals(&self, env_places: usize, component: &str) {
        if env_places > 0 && matches!(self, Self::Arrivals { .. } | Self::ArrivalsBetween { .. }) {
            panic!(
                "{component}: EnvironmentAnalysisMode::Arrivals is a net rewrite applied by \
                 SmtVerifier (VER-006); close the net first (open_net::close_arrivals) and \
                 analyse it without environment places"
            );
        }
    }
}

/// [VER-006] AC3: why the `Bounded(k)` model does not describe the executor on this
/// net, or `None` when it does. Every route models a `Bounded(k)` environment place
/// as a source holding at most `k`: the flat encoding caps each successor there at
/// `k`, the state-class graphs enable an environment input exactly when it demands at
/// most `k`, and the quiescence clause calls a demand above `k` permanently disabled.
/// That holds only when the initial marking holds at most `k` on each environment
/// place and no transition deposits into one. Environment places are checked in
/// code-point order, the initial marking first; the depositing transition named is
/// the first in code-point order. Any other mode, or no environment place, is `None`.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn bounded_premise_violation(
    net: &libpetri_core::petri_net::PetriNet,
    initial_marking: &crate::marking_state::MarkingState,
    env_places: &std::collections::BTreeSet<String>,
    mode: &EnvironmentAnalysisMode,
) -> Option<String> {
    let EnvironmentAnalysisMode::Bounded { max_tokens: k } = *mode else {
        return None;
    };
    let outside = |place: &str, what: String| {
        format!(
            "environment place '{place}' is outside the Bounded({k}) premises (VER-006 AC3): \
             {what}. Every route models it as a source holding at most {k}, so a verdict \
             would not describe the executor"
        )
    };
    for place in env_places {
        let held = initial_marking.count(place);
        if held > k {
            return Some(outside(place, format!("the initial marking holds {held} tokens there, more than {k}")));
        }
    }
    for place in env_places {
        let depositor = net
            .transitions()
            .iter()
            .filter(|t| t.output_places().iter().any(|p| p.name() == place.as_str()))
            // [VER-004]: a split net deposits through `complete:<t>`; name `t`.
            .map(|t| crate::in_flight::source_transition(net, t.name()))
            .min();
        if let Some(t) = depositor {
            return Some(outside(place, format!("transition '{t}' deposits into it")));
        }
    }
    None
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

/// Creates an `Arrivals` environment mode: at most `max_tokens` tokens injected
/// into each environment place over the whole run ([VER-006]).
pub fn arrivals(max_tokens: usize) -> EnvironmentAnalysisMode {
    EnvironmentAnalysisMode::Arrivals { max_tokens }
}

/// Creates an environment mode injecting between `min_tokens` and `max_tokens` tokens
/// into each environment place over the whole run ([VER-006]). `arrivals_between(0, k)`
/// is [`arrivals`]`(k)`; `arrivals_between(k, k)` delivers exactly `k`.
///
/// # Panics
/// When `max_tokens < min_tokens`.
pub fn arrivals_between(min_tokens: usize, max_tokens: usize) -> EnvironmentAnalysisMode {
    if max_tokens < min_tokens {
        panic!(
            "arrivals_between: needs min_tokens <= max_tokens, got {min_tokens}..{max_tokens} (VER-006)"
        );
    }
    if min_tokens == 0 {
        return EnvironmentAnalysisMode::Arrivals { max_tokens };
    }
    EnvironmentAnalysisMode::ArrivalsBetween { min_tokens, max_tokens }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mode_constructors() {
        assert_eq!(always_available(), EnvironmentAnalysisMode::AlwaysAvailable);
        assert_eq!(
            bounded(3),
            EnvironmentAnalysisMode::Bounded { max_tokens: 3 }
        );
        assert_eq!(ignore(), EnvironmentAnalysisMode::Ignore);
        assert_eq!(arrivals(2), EnvironmentAnalysisMode::Arrivals { max_tokens: 2 });
        assert_eq!(arrivals_between(0, 2), arrivals(2));
        assert_eq!(
            arrivals_between(2, 3),
            EnvironmentAnalysisMode::ArrivalsBetween { min_tokens: 2, max_tokens: 3 }
        );
    }

    #[test]
    #[should_panic(expected = "min_tokens <= max_tokens")]
    fn arrivals_between_rejects_max_below_min() {
        arrivals_between(3, 2);
    }
}
