//! What a subnet promises when it is verified on its own, with its ports played by the
//! environment ([VER-022]).
//!
//! The **assumption** half says what the environment does: which tokens the subnet holds
//! before anything arrives, and the arrival groups, each delivering between `min` and `max`
//! tokens onto its places at any point of the run. Every bound is finite. A bound is both
//! the runtime cap and the width of the claim, so an environment that delivers without
//! limit is not something a contract can assume.
//!
//! The **guarantee** half says what every quiescent marking holds: the count clauses, the
//! rest places, and the designed terminals under which a run may stop short. A place the
//! contract does not name is internal to the subnet and must be empty at quiescence. Every
//! run must also come to rest, unless [`OpenNetContractBuilder::require_termination`] is
//! turned off.
//!
//! Places are named by string, as everywhere else in this crate: a contract is read
//! against markings and flat nets, which know places by name only.

use std::collections::HashSet;

use libpetri_core::output::Out;
use libpetri_core::transition::Transition;

use crate::marking_state::{MarkingState, MarkingStateBuilder};
use crate::property::count_phrase;

use super::report::marking_text;

/// The environment delivers between `min` and `max` tokens in total, each onto one of
/// `places`, each at any point of the run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArrivalGroup {
    pub places: Vec<String>,
    pub min: usize,
    pub max: usize,
}

/// At every quiescent marking the tokens across `places` number between `min` and `max`
/// (`None` is unbounded). A marked designed terminal waives `min`, never `max`: a halt
/// stops progress, it does not license a token too many.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CountClause {
    pub name: String,
    pub places: Vec<String>,
    pub min: usize,
    pub max: Option<usize>,
}

/// While `marker` holds a token, the clauses' lower bounds are waived and tokens may rest
/// on `excused`: the places where the work the marker interrupted was delivered. The
/// marker itself may always rest, as a conditional-sink marker may ([VER-014]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DesignedTerminal {
    pub marker: String,
    pub excused: Vec<String>,
}

/// A subnet's contract: the environment it assumes and what it guarantees at quiescence
/// ([VER-022]). Build one with [`OpenNetContract::builder`]; check it with
/// [`verify_open_net`](super::verify_open_net).
///
/// ```ignore
/// let contract = OpenNetContract::builder()
///     .initial_tokens("idle", 1)
///     .initial_tokens("budget", k)
///     .arrive(1, ["in/data", "in/empty"])       // exactly one arrival on the input edge
///     .arrive_at_most(1, ["halt"])              // never or once
///     .expect("e3", 1, ["e3/data", "e3/empty"]) // one of data / empty per outgoing edge, once it runs
///     .expect("idle", 1, ["idle"])
///     .expect("budget", k, ["budget"])
///     .expect("history", 1, ["done", "skipped"])
///     .terminal("halt", ["in/data", "in/empty"]) // a halted run leaves the arrival where it was delivered
///     .terminal("skipped", [] as [&str; 0])      // a skipped run writes no output edge at all
///     .build();
/// ```
///
/// **A node that can skip needs its edge clauses conditional.** `expect("e3", 1, …)` alone
/// says every quiescent marking writes that edge exactly once, which a node that
/// legitimately skips does not: it comes to rest having written the edge zero times, and
/// the clause reports it. Whether that is a defect or a design is the contract's to say, so
/// name the place that marks a skip as a [`terminal`](OpenNetContractBuilder::terminal).
/// That waives the clauses' lower bounds while it is marked and leaves every upper bound in
/// force, so a run that writes an edge twice is still caught.
///
/// **A subnet that asks something of its neighbours needs an environment.** Verified alone,
/// a node that dispatches a request and waits has nobody to answer it: it quiesces with the
/// request outstanding, which is correct for an open net whose environment does nothing and
/// rarely what was meant. Give the contract the transitions the neighbours would fire
/// ([`environment`](OpenNetContractBuilder::environment)), and their own places stay theirs
/// — never counted as the subnet stranding a token. An environment transition is never
/// executed, so it needs no action.
#[derive(Debug, Clone)]
pub struct OpenNetContract {
    initial_tokens: Vec<(String, usize)>,
    arrivals: Vec<ArrivalGroup>,
    clauses: Vec<CountClause>,
    rest: Vec<String>,
    terminals: Vec<DesignedTerminal>,
    environment: Vec<Transition>,
    requires_termination: bool,
}

impl OpenNetContract {
    pub fn builder() -> OpenNetContractBuilder {
        OpenNetContractBuilder::new()
    }

    /// Tokens the subnet holds before anything arrives: its own resources and any shared
    /// pool it borrows from.
    pub fn initial_marking(&self) -> MarkingState {
        let mut builder = MarkingStateBuilder::new();
        for (place, count) in &self.initial_tokens {
            builder = builder.tokens(place.as_str(), *count);
        }
        builder.build()
    }

    /// The initial marking's places with their counts, in the order they were first named:
    /// the order [`OpenNetContract::places`] and a violation's port trace list them in.
    pub fn initial_tokens(&self) -> &[(String, usize)] {
        &self.initial_tokens
    }

    pub fn arrivals(&self) -> &[ArrivalGroup] {
        &self.arrivals
    }

    pub fn clauses(&self) -> &[CountClause] {
        &self.clauses
    }

    /// Places that may hold any number of tokens at quiescence.
    pub fn rest(&self) -> &[String] {
        &self.rest
    }

    pub fn terminals(&self) -> &[DesignedTerminal] {
        &self.terminals
    }

    /// Transitions the environment fires: neighbours that react to what the subnet sends.
    pub fn environment(&self) -> &[Transition] {
        &self.environment
    }

    /// Whether every run must come to rest.
    pub fn requires_termination(&self) -> bool {
        self.requires_termination
    }

    /// Every place the initial marking, an arrival group, a clause, the rest set or a
    /// terminal marker names, then every place an environment transition touches, in
    /// first-mention order. A violation's port trace reports the token changes on these
    /// places.
    ///
    /// A terminal's *excused* places are **not** included, so a place that only ever
    /// appears as an excuse is absent here; [`close_open_net`](super::close_open_net) adds
    /// those separately, because every place the contract names has to join the closed net
    /// for both routes to resolve it.
    pub fn places(&self) -> Vec<String> {
        let environment_places: Vec<String> =
            self.environment.iter().flat_map(transition_places).collect();
        let mut named: Vec<&str> = Vec::new();
        named.extend(self.initial_tokens.iter().map(|(p, _)| p.as_str()));
        for g in &self.arrivals {
            named.extend(g.places.iter().map(String::as_str));
        }
        for c in &self.clauses {
            named.extend(c.places.iter().map(String::as_str));
        }
        named.extend(self.rest.iter().map(String::as_str));
        named.extend(self.terminals.iter().map(|t| t.marker.as_str()));
        named.extend(environment_places.iter().map(String::as_str));
        let mut seen: HashSet<&str> = HashSet::new();
        let mut places: Vec<String> = Vec::new();
        for p in named {
            if seen.insert(p) {
                places.push(p.to_string());
            }
        }
        places
    }

    /// The contract as the report prints it, one line per part.
    pub fn describe(&self) -> Vec<String> {
        let mut lines = vec![format!("  Initial marking: {}", marking_text(&self.initial_marking()))];
        lines.push(if self.arrivals.is_empty() {
            "  Arrivals: none".to_string()
        } else {
            let groups: Vec<String> = self
                .arrivals
                .iter()
                .map(|g| format!("{} onto {{{}}}", count_phrase(g.min, Some(g.max)), g.places.join(", ")))
                .collect();
            format!("  Arrivals: {}", groups.join("; "))
        });
        lines.push(if self.clauses.is_empty() {
            "  At quiescence: no count clauses".to_string()
        } else {
            let clauses: Vec<String> = self
                .clauses
                .iter()
                .map(|c| {
                    format!("{} = {} across {{{}}}", c.name, count_phrase(c.min, c.max), c.places.join(", "))
                })
                .collect();
            format!("  At quiescence: {}", clauses.join("; "))
        });
        if !self.rest.is_empty() {
            lines.push(format!("  Rest: {}", self.rest.join(", ")));
        }
        for t in &self.terminals {
            lines.push(if t.excused.is_empty() {
                format!("  Terminal: when {}", t.marker)
            } else {
                format!("  Terminal: when {}: {}", t.marker, t.excused.join(", "))
            });
        }
        if !self.environment.is_empty() {
            let names: Vec<&str> = self.environment.iter().map(Transition::name).collect();
            lines.push(format!("  Environment transitions: {}", names.join(", ")));
        }
        lines.push(format!(
            "  Termination: {}",
            if self.requires_termination { "every run comes to rest" } else { "not required" }
        ));
        lines
    }
}

/// Every place an arc of `t` touches: inputs, reads, inhibitors, resets, then outputs, the
/// outputs in the order the spec names them (first occurrence).
///
/// The order reaches the report through [`OpenNetContract::places`], so it is read off the
/// spec tree rather than [`Transition::output_places`], a hash set with no order.
pub(super) fn transition_places(t: &Transition) -> Vec<String> {
    let mut places: Vec<String> = Vec::new();
    places.extend(t.input_specs().iter().map(|s| s.place_name().to_string()));
    places.extend(t.reads().iter().map(|a| a.place.name().to_string()));
    places.extend(t.inhibitors().iter().map(|a| a.place.name().to_string()));
    places.extend(t.resets().iter().map(|a| a.place.name().to_string()));
    if let Some(out) = t.output_spec() {
        let mut outputs: Vec<String> = Vec::new();
        collect_output_places(out, &mut outputs);
        places.extend(outputs);
    }
    places
}

fn collect_output_places(out: &Out, into: &mut Vec<String>) {
    fn push(name: &str, into: &mut Vec<String>) {
        if !into.iter().any(|p| p == name) {
            into.push(name.to_string());
        }
    }
    match out {
        Out::Place(p) => push(p.name(), into),
        Out::ForwardInput { to, .. } => push(to.name(), into),
        Out::And(children) | Out::Xor(children) => {
            for child in children {
                collect_output_places(child, into);
            }
        }
        Out::Timeout { child, .. } => collect_output_places(child, into),
    }
}

/// Builds an [`OpenNetContract`]. Every method validates as it goes and panics on a
/// contract that cannot mean anything, with the message the TypeScript reference throws:
/// a malformed contract is the caller's error, reported where it is built rather than as a
/// verdict about the net.
#[derive(Debug, Clone)]
pub struct OpenNetContractBuilder {
    initial_tokens: Vec<(String, usize)>,
    arrivals: Vec<ArrivalGroup>,
    clauses: Vec<CountClause>,
    rest: Vec<String>,
    terminals: Vec<DesignedTerminal>,
    environment: Vec<Transition>,
    requires_termination: bool,
}

impl Default for OpenNetContractBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl OpenNetContractBuilder {
    pub fn new() -> Self {
        Self {
            initial_tokens: Vec::new(),
            arrivals: Vec::new(),
            clauses: Vec::new(),
            rest: Vec::new(),
            terminals: Vec::new(),
            environment: Vec::new(),
            requires_termination: true,
        }
    }

    /// Replaces the tokens the subnet holds before anything arrives with `marking`. Its
    /// places are taken in the order [`MarkingState::places`] lists them, which for a
    /// marking from [`MarkingStateBuilder`] is the order its builder first saw them: the
    /// order a violation's port trace lists their changes in.
    pub fn initial_marking(mut self, marking: &MarkingState) -> Self {
        self.initial_tokens = marking.places().map(|(p, n)| (p.to_string(), n)).collect();
        self
    }

    /// Sets the tokens `place` holds before anything arrives; `0` removes it. A place set
    /// again keeps the position it was first named at, as a marking builder's map does.
    pub fn initial_tokens(mut self, place: impl AsRef<str>, count: usize) -> Self {
        let place = place.as_ref();
        match self.initial_tokens.iter().position(|(p, _)| p == place) {
            Some(i) if count == 0 => {
                self.initial_tokens.remove(i);
            }
            Some(i) => self.initial_tokens[i].1 = count,
            None if count == 0 => {}
            None => self.initial_tokens.push((place.to_string(), count)),
        }
        self
    }

    /// The environment delivers exactly `count` tokens, each onto one of `places`, at any
    /// point of the run.
    pub fn arrive<I, S>(self, count: usize, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.arrive_between(count, count, places)
    }

    /// The environment delivers at most `max` tokens, possibly none. `arrive_at_most(1,
    /// ["halt"])` is "never or once".
    pub fn arrive_at_most<I, S>(self, max: usize, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.arrive_between(0, max, places)
    }

    /// The environment delivers between `min` and `max` tokens in total, each onto one of
    /// `places`, at any point of the run.
    ///
    /// # Panics
    /// When `max < min`, when `max` is `0`, or when `places` is empty.
    pub fn arrive_between<I, S>(mut self, min: usize, max: usize, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        if max < min || max < 1 {
            panic!(
                "OpenNetContract: an arrival group needs whole bounds with 0 <= min <= max and max >= 1, \
                 got {min}..{max}. A bound is both the runtime cap and the width of the claim, so it is finite."
            );
        }
        let places = distinct(places, "an arrival group");
        self.arrivals.push(ArrivalGroup { places, min, max });
        self
    }

    /// At every quiescent marking, exactly `count` tokens across `places`.
    pub fn expect<I, S>(self, name: impl Into<String>, count: usize, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.expect_between(name, count, Some(count), places)
    }

    /// At every quiescent marking, between `min` and `max` tokens across `places`; `max`
    /// of `None` is unbounded.
    ///
    /// # Panics
    /// When `name` is empty or already taken, when `max < min`, or when `places` is empty.
    pub fn expect_between<I, S>(
        mut self,
        name: impl Into<String>,
        min: usize,
        max: Option<usize>,
        places: I,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let name = name.into();
        if name.is_empty() {
            panic!("OpenNetContract: a clause needs a name");
        }
        if self.clauses.iter().any(|c| c.name == name) {
            panic!("OpenNetContract: duplicate clause name '{name}'");
        }
        if let Some(max) = max {
            if max < min {
                panic!("OpenNetContract: clause '{name}' needs whole bounds with 0 <= min <= max, got {min}..{max}");
            }
        }
        let places = distinct(places, &format!("clause '{name}'"));
        self.clauses.push(CountClause { name, places, min, max });
        self
    }

    /// Places that may hold any number of tokens at quiescence.
    pub fn rest<I, S>(mut self, places: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        for p in places {
            let p = p.as_ref();
            if !self.rest.iter().any(|r| r == p) {
                self.rest.push(p.to_string());
            }
        }
        self
    }

    /// A designed terminal: while `marker` holds a token, lower bounds are waived and tokens
    /// may rest on `excused`. Repeated calls for one marker accumulate.
    pub fn terminal<I, S>(mut self, marker: impl AsRef<str>, excused: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let marker = marker.as_ref();
        let index = match self.terminals.iter().position(|t| t.marker == marker) {
            Some(i) => i,
            None => {
                self.terminals.push(DesignedTerminal { marker: marker.to_string(), excused: Vec::new() });
                self.terminals.len() - 1
            }
        };
        let entry = &mut self.terminals[index];
        for p in excused {
            let p = p.as_ref();
            if !entry.excused.iter().any(|e| e == p) {
                entry.excused.push(p.to_string());
            }
        }
        self
    }

    /// Transitions the environment fires: a neighbour that reacts to what the subnet sends,
    /// such as a tool that answers a request, or a loop body that sends an item back at most
    /// as often as a budget of its own allows. An arrival group cannot say that, because its
    /// tokens do not wait for a request.
    ///
    /// They join the closed net unchanged, and their firings are marked as environment
    /// steps in the port trace. A place only they touch belongs to the environment: it may
    /// hold tokens at quiescence, and the internal-place check never reports it. A place
    /// they share with the subnet is a port and is judged like any other. Their actions
    /// never run, so one that declares outputs may keep `passthrough()`.
    ///
    /// # Panics
    /// When a transition's name is already one of the contract's environment transitions.
    pub fn environment(mut self, transitions: impl IntoIterator<Item = Transition>) -> Self {
        for t in transitions {
            if self.environment.iter().any(|e| e.name() == t.name()) {
                panic!("OpenNetContract: duplicate environment transition '{}'", t.name());
            }
            self.environment.push(t);
        }
        self
    }

    /// Whether every run must come to rest (default `true`).
    pub fn require_termination(mut self, required: bool) -> Self {
        self.requires_termination = required;
        self
    }

    pub fn build(self) -> OpenNetContract {
        OpenNetContract {
            initial_tokens: self.initial_tokens,
            arrivals: self.arrivals,
            clauses: self.clauses,
            rest: self.rest,
            terminals: self.terminals,
            environment: self.environment,
            requires_termination: self.requires_termination,
        }
    }
}

/// `places` without repeats, in the order given.
///
/// # Panics
/// When `places` is empty: a group or clause over nothing is a contract that says nothing.
fn distinct<I, S>(places: I, what: &str) -> Vec<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut out: Vec<String> = Vec::new();
    for p in places {
        let p = p.as_ref();
        if !out.iter().any(|q| q == p) {
            out.push(p.to_string());
        }
    }
    if out.is_empty() {
        panic!("OpenNetContract: {what} names no place");
    }
    out
}
