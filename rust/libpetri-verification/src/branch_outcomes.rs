//! What one firing of a transition can deposit, for every analysis that expands a
//! transition's output spec: the flattener behind the SMT routes, the state-class
//! graph (the enumeration route, [VER-017]), the ν name-partition graph (Route B) and
//! everything built on those.
//!
//! A firing ends one of two ways, and they deposit differently:
//!
//! * **The action completes** and writes a branch of the spec ([IO-015]). A branch is a
//!   set of places and the analyses model one token per place of it ([IO-016]); a
//!   `ForwardInput` leaf is then an ordinary claim on its `to` place.
//! * **The action's `Timeout` fires** ([IO-013]). The marking receives the timeout
//!   child's tokens *and nothing else* — no sibling of the `Timeout` — and a
//!   `ForwardInput(from, to)` leaf deposits one token in `to` **per token the firing
//!   consumed from `from`** ([IO-014]): `n` for `Exactly(n)`, the whole drained batch for
//!   `All` / `AtLeast`.
//!
//! Every analysis used to read the timeout child as if the action had written it: one
//! token per named place, siblings included. On `exactly(2, a) -> xor(c, timeout(50,
//! forward_input(a, b)))` that deposits one token in `b` where the executor deposits two,
//! and `placeBound(b, 1)` was proven by the linear bound, the state-equation phase, the
//! fixpoint query and the enumeration route alike.
//!
//! [`outcomes`] lists the action outcomes first, in [`enumerate_branches`] order — so a
//! flat transition keeps its `_b<i>` name and a graph edge its `branch_index` — then the
//! timeout outcome when it differs from every action outcome. It can differ only when the
//! child forwards a batch that is not one token, or the `Timeout` has a sibling in its
//! branch; on every other spec the list is the one the analyses always used.
//!
//! A forward of an `All` / `AtLeast` input deposits a marking-dependent count
//! ([`Deposit::Drained`]) — a transfer. The graphs resolve it from the marking they fire
//! in, so the state-space enumeration ([VER-017]), the timed state-class graph and Route B
//! decide such a net exactly; the flat encodings cannot express it, so the verifier
//! refuses it on the linear routes only ([`drained_forward`]).

use std::collections::{BTreeMap, HashSet};

use libpetri_core::input::{self, In};
use libpetri_core::output::{Out, enumerate_branches, find_timeout};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::transition::Transition;

/// Tokens one outcome deposits into one place.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum Deposit {
    /// A fixed count: 1 for a place an action writes ([IO-016]) or a timeout mints, `n`
    /// for a timeout forward from an `One` / `Exactly(n)` input ([IO-014]).
    Tokens(usize),
    /// A timeout forward from an `All` / `AtLeast` input: every token the firing drained
    /// from the named place ([IO-014]), which depends on the marking it fires in.
    Drained(String),
}

/// One way a firing of a transition can end: the places it deposits into, each once, in
/// name order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    /// Each place this outcome deposits into, with how many tokens, sorted by place name.
    pub deposits: Vec<(String, Deposit)>,
    /// The same places as a set: the ν name layer reads which places receive a token,
    /// and rejects from its fragment a coloured place that receives any count but one.
    pub places: HashSet<String>,
}

impl Outcome {
    fn new(deposits: BTreeMap<String, Deposit>) -> Self {
        let places = deposits.keys().cloned().collect();
        Outcome {
            deposits: deposits.into_iter().collect(),
            places,
        }
    }

    /// The outcome of a transition with no output spec: nothing is deposited.
    pub fn empty() -> Self {
        Outcome::new(BTreeMap::new())
    }

    /// The count this outcome deposits into each place, with a `Drained` forward resolved
    /// by `drained(from)`.
    pub fn resolved<'a>(
        &'a self,
        drained: impl Fn(&str) -> usize + 'a,
    ) -> impl Iterator<Item = (&'a str, usize)> + 'a {
        self.deposits.iter().map(move |(place, deposit)| {
            let n = match deposit {
                Deposit::Tokens(n) => *n,
                Deposit::Drained(from) => drained(from),
            };
            (place.as_str(), n)
        })
    }
}

/// The ways one firing of `t` can deposit (module docs). Never empty: a transition with
/// no output spec has the one empty outcome.
pub fn outcomes(t: &Transition) -> Vec<Outcome> {
    let Some(out) = t.output_spec() else {
        return vec![Outcome::empty()];
    };
    let mut result: Vec<Outcome> = enumerate_branches(out)
        .into_iter()
        .map(|branch| {
            Outcome::new(
                branch
                    .into_iter()
                    .map(|p| (p.name().to_string(), Deposit::Tokens(1)))
                    .collect(),
            )
        })
        .collect();
    if result.is_empty() {
        result.push(Outcome::empty());
    }
    // The executor takes the first `Timeout` of the spec ([IO-013]), and so do we.
    if let Some((_, child)) = find_timeout(out) {
        for deposits in timeout_deposits(child, t) {
            let outcome = Outcome::new(deposits);
            if !result.contains(&outcome) {
                result.push(outcome);
            }
        }
    }
    result
}

/// The deposits of a `Timeout` child, one map per branch of it. The executors reject a
/// `Xor` under a `Timeout` when it fires; reading it as alternatives here keeps the
/// enumeration total.
fn timeout_deposits(out: &Out, t: &Transition) -> Vec<BTreeMap<String, Deposit>> {
    match out {
        Out::Place(p) => vec![BTreeMap::from([(p.name().to_string(), Deposit::Tokens(1))])],
        Out::ForwardInput { from, to } => {
            let deposit = forward_deposit(t, from.name());
            if deposit == Deposit::Tokens(0) {
                vec![BTreeMap::new()]
            } else {
                vec![BTreeMap::from([(to.name().to_string(), deposit)])]
            }
        }
        Out::Timeout { child, .. } => timeout_deposits(child, t),
        Out::Xor(children) => children.iter().flat_map(|c| timeout_deposits(c, t)).collect(),
        Out::And(children) => {
            let mut acc = vec![BTreeMap::new()];
            for child in children {
                let next = timeout_deposits(child, t);
                acc = acc
                    .iter()
                    .flat_map(|left| {
                        next.iter().map(move |right| {
                            let mut merged: BTreeMap<String, Deposit> = left.clone();
                            for (place, deposit) in right {
                                // A place twice in one branch is rejected at build
                                // ([IO-011]); summing keeps this total regardless.
                                let sum = match (merged.remove(place), deposit) {
                                    (None, d) => d.clone(),
                                    (Some(Deposit::Tokens(a)), Deposit::Tokens(b)) => {
                                        Deposit::Tokens(a + b)
                                    }
                                    (Some(_), d) => d.clone(),
                                };
                                merged.insert(place.clone(), sum);
                            }
                            merged
                        })
                    })
                    .collect();
            }
            acc
        }
    }
}

/// What a timeout forward from `from` deposits ([IO-014]): one token per token the firing
/// consumed from `from`. A place that is not an input of `t` (the builder rejects it)
/// consumes nothing and forwards nothing.
fn forward_deposit(t: &Transition, from: &str) -> Deposit {
    match t.input_specs().iter().find(|s| s.place_name() == from) {
        Some(spec @ (In::One { .. } | In::Exactly { .. })) => {
            Deposit::Tokens(input::required_count(spec))
        }
        Some(In::All { .. } | In::AtLeast { .. }) => Deposit::Drained(from.to_string()),
        None => Deposit::Tokens(0),
    }
}

/// Where a token the executor writes on timeout comes from ([IO-013], [IO-014]). The
/// action writes nothing on that path, so the value is fixed by the spec alone.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TimeoutWrite {
    /// An `Out::Place` leaf: a unit token with no value, so a ν key projects no name
    /// from it.
    Unit,
    /// A `ForwardInput(from, to)` leaf: the tokens consumed from `from`, values
    /// unchanged, so each carries the name it had in `from`.
    Forward(String),
}

/// Every place the first `Timeout` of `t`'s output spec writes into, with where the
/// token comes from. Empty when the spec has no `Timeout`. The ν analyses read this to
/// tell a timeout deposit, which the executor makes by copying or by writing a unit
/// token, from an action write, which the ν contracts cover ([NU-010], [NU-051]).
pub fn timeout_writes(t: &Transition) -> Vec<(String, TimeoutWrite)> {
    fn walk(out: &Out, acc: &mut Vec<(String, TimeoutWrite)>) {
        match out {
            Out::Place(p) => acc.push((p.name().to_string(), TimeoutWrite::Unit)),
            Out::ForwardInput { from, to } => {
                acc.push((to.name().to_string(), TimeoutWrite::Forward(from.name().to_string())))
            }
            Out::Timeout { child, .. } => walk(child, acc),
            Out::And(children) | Out::Xor(children) => {
                for c in children {
                    walk(c, acc);
                }
            }
        }
    }
    let mut acc = Vec::new();
    if let Some((_, child)) = t.output_spec().and_then(find_timeout) {
        walk(child, &mut acc);
    }
    acc
}

/// A timeout forward whose count the flat encodings cannot express ([`drained_forward`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DrainedForward {
    /// The transition declaring it.
    pub transition: String,
    /// The drained input place (`All` / `AtLeast`).
    pub from: String,
    /// The place it forwards to.
    pub to: String,
}

impl DrainedForward {
    /// The `Unknown` reason the verifier gives for this net ([VER-003]).
    pub fn reason(&self) -> String {
        format!(
            "transition '{}' forwards its All/AtLeast input '{}' to '{}' on timeout, which \
             deposits one token per token drained (IO-014), a marking-dependent count the \
             flat encodings cannot express; refusing to certify on the linear routes (the \
             state-space graphs decide it exactly: VER-017 enumeration, Route B)",
            self.transition, self.from, self.to
        )
    }
}

/// The first timeout forward, in transition order, from an `All` / `AtLeast` input: its
/// deposit is the drained batch ([`Deposit::Drained`]), a transfer the incidence-matrix
/// analyses (P-invariants, the linear bound, the state equation, the firing bound, the CHC
/// transition rule, Route A) have no column for. The verifier lets the graph routes decide
/// such a net and refuses it before the first linear route.
pub fn drained_forward(net: &PetriNet) -> Option<DrainedForward> {
    net.transitions().iter().find_map(|t| {
        outcomes(t).into_iter().find_map(|o| {
            o.deposits.into_iter().find_map(|(to, d)| match d {
                Deposit::Drained(from) => Some(DrainedForward {
                    transition: t.name().to_string(),
                    from,
                    to,
                }),
                Deposit::Tokens(_) => None,
            })
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::input::{all, at_least, exactly, one};
    use libpetri_core::output::{and, forward_input, out_place, timeout, xor};
    use libpetri_core::place::Place;

    fn places() -> (Place<i32>, Place<i32>, Place<i32>) {
        (Place::new("a"), Place::new("b"), Place::new("c"))
    }

    fn deposits(o: &Outcome) -> Vec<(&str, Deposit)> {
        o.deposits.iter().map(|(p, d)| (p.as_str(), d.clone())).collect()
    }

    /// The repro of the wrong `Proven`: the timeout forwards both consumed tokens.
    #[test]
    fn an_exactly_two_forward_deposits_two() {
        let (a, b, c) = places();
        let t = Transition::builder("t")
            .input(exactly(2, &a))
            .output(xor(vec![out_place(&c), timeout(50, forward_input(&a, &b))]))
            .action(fork())
            .build();
        let got = outcomes(&t);
        assert_eq!(got.len(), 3);
        assert_eq!(deposits(&got[0]), vec![("c", Deposit::Tokens(1))]);
        // The action may write the forward's target itself: one token ([IO-016]).
        assert_eq!(deposits(&got[1]), vec![("b", Deposit::Tokens(1))]);
        // The timeout forwards both consumed tokens ([IO-014]).
        assert_eq!(deposits(&got[2]), vec![("b", Deposit::Tokens(2))]);
    }

    /// A `One` forward deposits one token, which the action branch already models:
    /// the list is the one the analyses always used.
    #[test]
    fn a_one_forward_adds_no_outcome() {
        let (a, b, c) = places();
        let t = Transition::builder("t")
            .input(one(&a))
            .output(xor(vec![out_place(&c), timeout(50, forward_input(&a, &b))]))
            .action(fork())
            .build();
        assert_eq!(outcomes(&t).len(), 2);
    }

    /// On timeout the marking receives the child's tokens and nothing else ([IO-013]
    /// AC5): a sibling of the `Timeout` is not written.
    #[test]
    fn a_timeout_does_not_write_its_siblings() {
        let (a, b, c) = places();
        let t = Transition::builder("t")
            .input(one(&a))
            .output(and(vec![out_place(&c), timeout(50, out_place(&b))]))
            .action(fork())
            .build();
        let got = outcomes(&t);
        assert_eq!(got.len(), 2);
        assert_eq!(deposits(&got[0]), vec![("b", Deposit::Tokens(1)), ("c", Deposit::Tokens(1))]);
        assert_eq!(deposits(&got[1]), vec![("b", Deposit::Tokens(1))]);
    }

    #[test]
    fn a_drained_forward_is_marking_dependent_and_found() {
        let (a, b, c) = places();
        for input in [all(&a), at_least(2, &a)] {
            let t = Transition::builder("t")
                .input(input)
                .output(xor(vec![out_place(&c), timeout(50, forward_input(&a, &b))]))
                .action(fork())
                .build();
            let got = outcomes(&t);
            assert_eq!(deposits(&got[2]), vec![("b", Deposit::Drained("a".into()))]);
            let net = PetriNet::builder("n").transition(t).build();
            let found = drained_forward(&net).expect("the drained forward");
            assert_eq!((found.from.as_str(), found.to.as_str()), ("a", "b"));
        }
    }

    #[test]
    fn no_output_spec_is_one_empty_outcome() {
        let (a, _, _) = places();
        let t = Transition::builder("t").input(one(&a)).build();
        assert_eq!(outcomes(&t), vec![Outcome::empty()]);
    }
}
