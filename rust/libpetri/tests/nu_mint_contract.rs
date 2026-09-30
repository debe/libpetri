//! The ν mint and relay contracts ([NU-010], [NU-051]) against what the executor
//! does, for both ν routes of [NU-050] (Route A, the name-coloured CHC encoding, and
//! Route B, the name-partition state-class graph).
//!
//! Each net here has a run that the executor takes and that the ν routes used to rule
//! out, because they read a coloured write as a fresh name when it was not one:
//!
//! - a timeout forward into a match key deposits the consumed token, whose name is
//!   its payload's ([IO-014]), not a fresh one;
//! - the stock `fork()` copies its input, so two "mints" fed one correlation id write
//!   one name;
//! - an EXTENDED coloured consumer whose timeout forwards another input writes that
//!   input's name, not the one it consumed;
//! - a coloured consumer that relays back into its own input keeps its colour there.
//!
//! Every test runs the executor to the run it takes, then checks that no route
//! proves the run impossible.
//!
//! Lives in the umbrella crate so it can run the executor and the verifier together.

use libpetri::core::action::{async_action, fork, sync_action};
use libpetri::core::input::one;
use libpetri::core::match_spec::MatchSpec;
use libpetri::core::name::NameId;
use libpetri::core::output::{and, forward_input, out_place, timeout, xor};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;
use libpetri::verification::marking_state::MarkingStateBuilder;
use libpetri::verification::name_fragment::FragmentMode;
use libpetri::verification::property::SmtProperty;
use libpetri::verification::result::{Verdict, VerificationResult, VerificationRoute};
use libpetri::verification::smt_verifier::SmtVerifier;

fn key(s: &String) -> NameId {
    NameId::new(s.clone())
}

fn join(name: &str, a: &Place<String>, b: &Place<String>, out: &Place<String>) -> Transition {
    let (from, to) = (a.name().to_string(), out.name().to_string());
    Transition::builder(name)
        .input(one(a))
        .input(one(b))
        .match_spec(MatchSpec::builder().key(a, key).key(b, key).build())
        .output(out_place(out))
        .action(sync_action(move |ctx| {
            let v: String = (*ctx.input::<String>(&from)?).clone();
            ctx.output(&to, v)?;
            Ok(())
        }))
        .build()
}

fn marking(tokens: &[(&str, &str)]) -> Marking {
    let mut m = Marking::new();
    for (place, value) in tokens {
        m.add(&Place::<String>::new(*place), Token::at(value.to_string(), 0));
    }
    m
}

fn not_proven(r: &VerificationResult, what: &str) {
    assert!(
        !matches!(r.verdict, Verdict::Proven { .. }),
        "{what}: the executor reaches the bad marking, so no route may prove it\n{}",
        r.report
    );
}

// ── Copying "mints" ([NU-010]) ───────────────────────────────────────────────

/// `mA: S1 → A` and `mB: S2 → B`, both with the stock `fork()`, which copies the
/// input value; `J` joins `A` and `B` by name into `DONE`.
fn copying_mints() -> PetriNet {
    let (s1, s2) = (Place::<String>::new("S1"), Place::<String>::new("S2"));
    let (a, b, done) = (
        Place::<String>::new("A"),
        Place::<String>::new("B"),
        Place::<String>::new("DONE"),
    );
    let ma = Transition::builder("mA").input(one(&s1)).output(out_place(&a)).action(fork()).build();
    let mb = Transition::builder("mB").input(one(&s2)).output(out_place(&b)).action(fork()).build();
    PetriNet::builder("copying_mints")
        .transitions([ma, mb, join("J", &a, &b, &done)])
        .build()
}

#[test]
fn a_copying_producer_is_not_read_as_a_mint_unless_declared() {
    let net = copying_mints();
    // One correlation id in both sources: the executor joins it.
    let mut ex = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking(&[("S1", "order-7"), ("S2", "order-7")]),
        ExecutorOptions::default(),
    );
    assert_eq!(ex.run_sync().count("DONE"), 1);

    let m0 = || MarkingStateBuilder::new().tokens("S1", 1).tokens("S2", 1).build();
    // Route B used to read `mA` and `mB` as mints of two distinct names and prove
    // `DONE` unreachable.
    let r = SmtVerifier::for_net(&net)
        .initial_marking(m0())
        .property(SmtProperty::place_bound("DONE", 0))
        .verify();
    not_proven(&r, "undeclared copying producers");
    assert_ne!(r.route, VerificationRoute::NuScg, "{}", r.report);

    // Declared, the verdict rests on the mint contract, and the report says so.
    let declared = SmtVerifier::for_net(&net)
        .initial_marking(m0())
        .property(SmtProperty::place_bound("DONE", 0))
        .mint_transitions(["mA".to_string(), "mB".to_string()])
        .verify();
    assert!(declared.is_proven(), "{}", declared.report);
    assert_eq!(declared.route, VerificationRoute::NuScg);
    assert!(
        declared.report.contains(
            "Mint contract (NU-010) assumed for mA, mB: each writes a freshly minted name into every coloured place it writes."
        ),
        "{}",
        declared.report
    );
}

#[test]
fn a_declared_mint_that_is_not_in_the_net_is_unknown() {
    let r = SmtVerifier::for_net(&copying_mints())
        .initial_marking(MarkingStateBuilder::new().tokens("S1", 1).tokens("S2", 1).build())
        .property(SmtProperty::place_bound("DONE", 0))
        .mint_transition("mA")
        .mint_transition("mC")
        .verify();
    assert_eq!(
        r.verdict,
        Verdict::Unknown { reason: "declared mint transition 'mC' not in the net (NU-010)".into() },
        "{}",
        r.report
    );
}

// ── Timeout forwards ([IO-014]) ──────────────────────────────────────────────

/// A 200 ms action, so a 20 ms `Timeout` always fires first.
#[cfg(feature = "tokio")]
fn slow() -> libpetri::core::action::BoxedAction {
    async_action(|ctx| async move {
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
        Ok(ctx)
    })
}

/// `t1: budget, reqA → xor(okA, timeout(20, forward(reqA, a)))`, the twin `t2` into
/// `b`, and `join: a, b → done`. Both timeouts forward the request token itself.
#[cfg(feature = "tokio")]
fn forward_mints() -> PetriNet {
    let budget = Place::<String>::new("budget");
    let p = |n: &str| Place::<String>::new(n);
    let (a, b, done) = (p("a"), p("b"), p("done"));
    let twin = |name: &str, req: &Place<String>, ok: &Place<String>, key_place: &Place<String>| {
        Transition::builder(name)
            .input(one(&budget))
            .input(one(req))
            .output(xor(vec![out_place(ok), timeout(20, forward_input(req, key_place))]))
            .action(slow())
            .build()
    };
    PetriNet::builder("forward_mints")
        .transitions([
            twin("t1", &p("reqA"), &p("okA"), &a),
            twin("t2", &p("reqB"), &p("okB"), &b),
            join("join", &a, &b, &done),
        ])
        .build()
}

#[cfg(feature = "tokio")]
async fn run_async(net: &PetriNet, m: Marking) -> Marking {
    let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, m, ExecutorOptions::default());
    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel();
    ex.run_async(rx).await;
    ex.marking().into_owned()
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_timeout_forward_into_a_match_key_is_never_a_mint() {
    let net = forward_mints();
    let end = run_async(
        &net,
        marking(&[("budget", "b"), ("budget", "b"), ("reqA", "x"), ("reqB", "x")]),
    )
    .await;
    assert_eq!(end.count("done"), 1, "both timeouts forward 'x', and the join matches it");

    let m0 = || {
        MarkingStateBuilder::new()
            .tokens("budget", 2)
            .tokens("reqA", 1)
            .tokens("reqB", 1)
            .build()
    };
    // Route B, even with t1 and t2 declared: the executor, not the action, writes `a`.
    let b = SmtVerifier::for_net(&net)
        .initial_marking(m0())
        .property(SmtProperty::place_bound("done", 0))
        .mint_transitions(["t1".to_string(), "t2".to_string()])
        .verify();
    not_proven(&b, "Route B");
    assert_ne!(b.route, VerificationRoute::NuScg, "{}", b.report);

    // Route A: the budget declares t1 and t2, and still the timeout write is no mint.
    #[cfg(feature = "z3")]
    if libpetri::verification::smt_verifier::z3_available() {
        let a = SmtVerifier::for_net(&net)
            .initial_marking(m0())
            .property(SmtProperty::place_bound("done", 0))
            .budget_places(["budget".to_string()])
            .verify();
        not_proven(&a, "Route A");
        assert!(!a.report.contains("ν-encoding: name-coloured"), "{}", a.report);
    }
}

// ── EXTENDED coloured consumers ([NU-051]) ───────────────────────────────────

/// `m1: budget → A1` and `m2: budget → A2` mint (fresh names, carriers `A1`, `A2`);
/// the consumers `r1: A1, reqA → xor(okA, timeout(20, forward(reqA, KA)))` and its
/// twin `r2` into `KB` time out and forward the request, not the name they consumed;
/// `join: KA, KB → done`.
#[cfg(feature = "tokio")]
fn forwarding_consumers() -> PetriNet {
    let p = |n: &str| Place::<String>::new(n);
    let budget = p("budget");
    let mint = |name: &str, out: &Place<String>| {
        let target = out.name().to_string();
        Transition::builder(name)
            .input(one(&budget))
            .output(out_place(out))
            .action(sync_action(move |ctx| {
                let n = ctx.fresh_name().to_string();
                ctx.output(&target, n)?;
                Ok(())
            }))
            .build()
    };
    let consumer = |name: &str, carrier: &Place<String>, req: &Place<String>, ok: &Place<String>, k: &Place<String>| {
        Transition::builder(name)
            .input(one(carrier))
            .input(one(req))
            .output(xor(vec![out_place(ok), timeout(20, forward_input(req, k))]))
            .action(slow())
            .build()
    };
    let (ka, kb) = (p("KA"), p("KB"));
    PetriNet::builder("forwarding_consumers")
        .transitions([
            mint("m1", &p("A1")),
            mint("m2", &p("A2")),
            consumer("r1", &p("A1"), &p("reqA"), &p("okA"), &ka),
            consumer("r2", &p("A2"), &p("reqB"), &p("okB"), &kb),
            join("join", &ka, &kb, &p("done")),
        ])
        .build()
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_consumer_timeout_forwarding_another_input_is_not_a_relay() {
    let net = forwarding_consumers();
    let end = run_async(
        &net,
        marking(&[("budget", "b"), ("budget", "b"), ("reqA", "x"), ("reqB", "x")]),
    )
    .await;
    assert_eq!(end.count("done"), 1, "both consumers forward 'x', and the join matches it");

    let verifier = || {
        SmtVerifier::for_net(&net)
            .initial_marking(
                MarkingStateBuilder::new()
                    .tokens("budget", 2)
                    .tokens("reqA", 1)
                    .tokens("reqB", 1)
                    .build(),
            )
            .property(SmtProperty::place_bound("done", 0))
            .fragment_mode(FragmentMode::Extended)
            .carrier_places(["A1".to_string(), "A2".to_string()])
    };
    let b = verifier().mint_transitions(["m1".to_string(), "m2".to_string()]).verify();
    not_proven(&b, "Route B");
    assert_ne!(b.route, VerificationRoute::NuScg, "{}", b.report);

    #[cfg(feature = "z3")]
    if libpetri::verification::smt_verifier::z3_available() {
        let a = verifier().budget_places(["budget".to_string()]).verify();
        not_proven(&a, "Route A");
        assert!(!a.report.contains("ν-encoding: name-coloured"), "{}", a.report);
    }
}

// ── A consumer relaying into its own input (Route A) ─────────────────────────

/// `mint: budget → a, b` (one fresh name in both); `spin: a, tick → a, tock` relays
/// the name back into `a`; `join: a, b → done`. `spin` can fire, so `tock` is
/// reachable.
fn self_loop() -> PetriNet {
    let p = |n: &str| Place::<String>::new(n);
    let (a, b) = (p("a"), p("b"));
    let mint = Transition::builder("mint")
        .input(one(&p("budget")))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let n = ctx.fresh_name().to_string();
            ctx.output("a", n.clone())?;
            ctx.output("b", n)?;
            Ok(())
        }))
        .build();
    let spin = Transition::builder("spin")
        .input(one(&a))
        .input(one(&p("tick")))
        .output(and(vec![out_place(&a), out_place(&p("tock"))]))
        .action(sync_action(|ctx| {
            let v: String = (*ctx.input::<String>("a")?).clone();
            ctx.output("a", v)?;
            ctx.output("tock", "t".to_string())?;
            Ok(())
        }))
        .build();
    PetriNet::builder("self_loop")
        .transitions([mint, spin, join("join", &a, &b, &p("done"))])
        .build()
}

#[test]
fn a_consumer_relaying_into_its_own_input_keeps_the_colour_there() {
    let net = self_loop();
    let mut ex = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking(&[("budget", "b"), ("tick", "t")]),
        ExecutorOptions::default(),
    );
    let end = ex.run_sync();
    assert_eq!((end.count("tock"), end.count("done")), (1, 1));

    #[cfg(feature = "z3")]
    if libpetri::verification::smt_verifier::z3_available() {
        let r = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("budget", 1).tokens("tick", 1).build())
            .property(SmtProperty::place_bound("tock", 0))
            .budget_places(["budget".to_string()])
            .fragment_mode(FragmentMode::Extended)
            .verify();
        // Route A decides it (budgeted reachability-safety), and must find `spin`.
        assert!(r.report.contains("ν-encoding: name-coloured"), "{}", r.report);
        assert!(r.is_violated(), "{}", r.report);
        assert!(
            r.report.contains(
                "Relay contract (NU-051) assumed for spin: each writes the name it consumed into every coloured place it writes."
            ),
            "{}",
            r.report
        );
    }
}
