//! `Bounded(k)` premises ([VER-006] AC3). Every route models a `Bounded(k)` environment place
//! as a source that holds at most `k` tokens: the flat encoding caps each successor at `k`,
//! the state-class graphs answer an environment input with `required <= k` whatever the
//! place holds, and the quiescence clause calls a transition demanding more than `k`
//! permanently disabled. That is the executor only when no transition deposits into an
//! environment place and the initial marking holds at most `k` on each one. Outside those
//! premises the verifier answers `Unknown` and names the place, on every route.
//! Lean: `bounded_initial_overflow_wrong_proven`, `bounded_producer_overflow_wrong_proven`,
//! `supplied_bounded_deposit_wrong_proven`, `supplied_bounded_initial_wrong_proven`,
//! `quiescence_bounded_initial_spurious`.

#![cfg(feature = "z3")]

use libpetri_core::action::fork;
use libpetri_core::input::{exactly, one};
use libpetri_core::output::{and, out_place};
use libpetri_core::petri_net::{PetriNet, PetriNetBuilder};
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::environment::EnvironmentAnalysisMode;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{Verdict, VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

macro_rules! require_z3 {
    ($name:literal) => {
        if !z3_available() {
            eprintln!(concat!("skipping ", $name, ": z3 binary not on PATH"));
            return;
        }
    };
}

fn place(name: &str) -> Place<()> {
    Place::new(name)
}

fn transition(name: &str, inputs: Vec<libpetri_core::input::In>, output: &Place<()>) -> Transition {
    let mut b = Transition::builder(name);
    for i in inputs {
        b = b.input(i);
    }
    b.output(out_place(output)).action(fork()).build()
}

fn verify(
    net: &PetriNet,
    m0: MarkingState,
    property: SmtProperty,
    budget: usize,
) -> VerificationResult {
    SmtVerifier::for_net(net)
        .initial_marking(m0)
        .environment_places(vec!["E".into()])
        .environment_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 1 })
        .mint_transition_if_present(net)
        .property(property)
        .enumeration_max_classes(budget)
        .timeout(15_000)
        .verify()
}

/// The declared mint of [`with_join`], when the net has it.
trait MintIfPresent {
    fn mint_transition_if_present(self, net: &PetriNet) -> Self;
}

impl MintIfPresent for SmtVerifier<'_> {
    fn mint_transition_if_present(self, net: &PetriNet) -> Self {
        if net.transitions().iter().any(|t| t.name() == "fork") {
            self.mint_transition("fork")
        } else {
            self
        }
    }
}

/// Adds a same-mint ν-join beside the net, so the query runs on Route B.
fn with_join(builder: PetriNetBuilder) -> PetriNetBuilder {
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    let source = place("source");
    let branch_a = Place::<String>::new("branchA");
    let branch_b = Place::<String>::new("branchB");
    let merged = Place::<String>::new("merged");
    let fork_t = Transition::builder("fork")
        .input(one(&source))
        .output(and(vec![out_place(&branch_a), out_place(&branch_b)]))
        .action(fork())
        .build();
    let join = Transition::builder("join")
        .input(one(&branch_a))
        .input(one(&branch_b))
        .match_spec(
            MatchSpec::builder()
                .key(&branch_a, |s: &String| NameId::new(s.clone()))
                .key(&branch_b, |s: &String| NameId::new(s.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(fork())
        .build();
    builder.transition(fork_t).transition(join)
}

fn assert_refused(result: &VerificationResult, place: &str, cause: &str) {
    let Verdict::Unknown { reason } = &result.verdict else {
        panic!("expected Unknown, got {:?}\n{}", result.verdict, result.report);
    };
    assert!(reason.contains(&format!("'{place}'")), "{reason}");
    assert!(reason.contains(cause), "{reason}");
    assert!(reason.contains("VER-006"), "{reason}");
}

/// (A) `M0(E) = 2 > k = 1`: the flat encoding capped every successor at `k`, so no
/// transition could fire and `b` looked unreachable, although the executor fires `t` from
/// `M0` with no injection at all.
#[test]
fn an_initial_marking_above_k_is_refused() {
    require_z3!("an_initial_marking_above_k_is_refused");
    let (a, b, c, d, e) = (place("a"), place("b"), place("c"), place("d"), place("E"));
    let net = PetriNet::builder("capA")
        .transition(transition("t", vec![one(&a)], &b))
        .transition(transition("u", vec![one(&e), one(&d)], &c))
        .build();
    let m0 = MarkingStateBuilder::new().tokens("a", 1).tokens("E", 2).build();
    for budget in [0, 50_000] {
        let result = verify(&net, m0.clone(), SmtProperty::place_bound("b", 0), budget);
        assert_refused(&result, "E", "initial marking holds 2");
    }
}

/// (B) `t` deposits into `E`: the executor fires it twice and marks `E` with 2, the cap
/// kept `E` at 1.
#[test]
fn a_deposit_into_an_environment_place_is_refused() {
    require_z3!("a_deposit_into_an_environment_place_is_refused");
    let (a, e) = (place("a"), place("E"));
    let net = PetriNet::builder("capB").transition(transition("t", vec![one(&a)], &e)).build();
    let m0 = MarkingStateBuilder::new().tokens("a", 2).build();
    let result = verify(&net, m0, SmtProperty::place_bound("E", 1), 50_000);
    assert_refused(&result, "E", "transition 't' deposits into it");
}

/// The state-class graph read an environment input as `required <= k`, so `exactly(2, E)`
/// was never enabled; the executor fires `t0` twice and then `t1`. On the flat path and on
/// Route B.
#[test]
fn a_demand_above_k_met_by_a_deposit_is_refused_on_every_route() {
    require_z3!("a_demand_above_k_met_by_a_deposit_is_refused_on_every_route");
    let (a, e, out) = (place("a"), place("E"), place("out"));
    let base = || {
        PetriNet::builder("supplied")
            .transition(transition("t0", vec![one(&a)], &e))
            .transition(transition("t1", vec![exactly(2, &e)], &out))
    };
    let flat = base().build();
    let nu = with_join(base()).build();
    let m0 = MarkingStateBuilder::new().tokens("a", 2).tokens("source", 1).build();
    let result = verify(&flat, m0.clone(), SmtProperty::place_bound("out", 0), 50_000);
    assert_refused(&result, "E", "transition 't0' deposits into it");
    let result = verify(&nu, m0, SmtProperty::place_bound("out", 0), 50_000);
    assert_refused(&result, "E", "transition 't0' deposits into it");
}

/// The quiescence clause called `tQ1` (demanding 2 > k) permanently disabled, so the
/// initial marking looked quiescent: a spurious `Violated`. The executor fires `tQ1` and
/// then loops on `tQ2` forever.
#[test]
fn a_spurious_deadlock_from_an_initial_marking_above_k_is_refused() {
    require_z3!("a_spurious_deadlock_from_an_initial_marking_above_k_is_refused");
    let (e, out) = (place("E"), place("out"));
    let base = || {
        PetriNet::builder("quiescent")
            .transition(transition("tQ1", vec![exactly(2, &e)], &out))
            .transition(transition("tQ2", vec![one(&out)], &out))
    };
    let m0 = MarkingStateBuilder::new().tokens("E", 2).build();
    for net in [base().build(), with_join(base()).build()] {
        let result = verify(&net, m0.clone(), SmtProperty::DeadlockFree, 50_000);
        assert_refused(&result, "E", "initial marking holds 2");
    }
}

/// Within the premises nothing changes: `M0(E) = k` and no deposit, the verdict stands.
#[test]
fn within_the_premises_the_verdict_stands() {
    require_z3!("within_the_premises_the_verdict_stands");
    let (a, b, e, out) = (place("a"), place("b"), place("E"), place("out"));
    let net = PetriNet::builder("within")
        .transition(transition("t", vec![one(&a)], &b))
        .transition(transition("u", vec![one(&e)], &out))
        .build();
    let m0 = MarkingStateBuilder::new().tokens("a", 1).tokens("E", 1).build();
    let result = verify(&net, m0.clone(), SmtProperty::place_bound("b", 0), 0);
    assert!(result.is_violated(), "{}", result.report);
    let result = verify(&net, m0, SmtProperty::place_bound("b", 1), 0);
    assert!(result.is_proven(), "{}", result.report);
    assert_ne!(result.route, VerificationRoute::Unavailable, "{}", result.report);
}

/// (B) on a split net ([VER-004]): `u` inhibited by `E` splits `t`, whose deposit into `E`
/// is then made by `complete:t`. The refusal names `t`, the caller's transition; it
/// used to name the synthetic `complete:t`.
#[test]
fn a_deposit_by_a_split_transition_is_refused_naming_it() {
    require_z3!("a_deposit_by_a_split_transition_is_refused_naming_it");
    let (a, e, q, r) = (place("a"), place("E"), place("q"), place("r"));
    let watch = Transition::builder("u")
        .input(one(&q))
        .inhibitor(libpetri_core::arc::inhibitor(&e))
        .output(out_place(&r))
        .action(fork())
        .build();
    let net = PetriNet::builder("capSplit").transition(transition("t", vec![one(&a)], &e)).transition(watch).build();
    let m0 = MarkingStateBuilder::new().tokens("a", 2).tokens("q", 1).build();
    let result = verify(&net, m0, SmtProperty::place_bound("E", 1), 50_000);
    assert_refused(&result, "E", "transition 't' deposits into it");
    let Verdict::Unknown { reason } = &result.verdict else { unreachable!() };
    assert!(!reason.contains("complete:"), "{reason}");
}
