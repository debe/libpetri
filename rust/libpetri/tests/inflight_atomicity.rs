//! In-flight actions and the atomic-firing premise of verification ([VER-004],
//! [EXEC-001], [CONC-001]).
//!
//! The executor consumes a firing's inputs when the action starts and deposits
//! its outputs when the action completes. With an asynchronous action other
//! transitions fire in between. For monotone arcs that interleaving is one of
//! the atomic model's own runs. It is not when another transition tests one of
//! the in-flight transition's input places with an inhibitor, reset, `all` or
//! `at_least` arc: it sees the place emptier than any atomic marking leaves it.

#![cfg(feature = "tokio")]

use std::time::Duration;

use libpetri::core::action::{BoxedAction, async_action, sync_action};
use libpetri::core::arc::{inhibitor, reset};
use libpetri::core::input::{In, all, at_least, one};
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::token::Token;
use libpetri::core::transition::{Transition, TransitionBuilder};
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::compiled_net::CompiledNet;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;
use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
use libpetri::runtime::precompiled_net::PrecompiledNet;

#[derive(Debug, Clone, Copy)]
enum Backend {
    Bitmap,
    Precompiled,
}

const BACKENDS: [Backend; 2] = [Backend::Bitmap, Backend::Precompiled];

fn p() -> Place<()> {
    Place::new("p")
}

fn marking(tokens: &[(&str, usize)]) -> Marking {
    let mut m = Marking::new();
    for (name, n) in tokens {
        for _ in 0..*n {
            m.add(&Place::<()>::new(*name), Token::at((), 0));
        }
    }
    m
}

/// `t` forwards its `p` token after a 50 ms sleep.
fn slow() -> BoxedAction {
    async_action(|mut ctx| async move {
        tokio::time::sleep(Duration::from_millis(50)).await;
        ctx.output("p", ())?;
        Ok(ctx)
    })
}

/// `t` forwards its `p` token inline.
fn inline() -> BoxedAction {
    sync_action(|ctx| {
        ctx.output("p", ())?;
        Ok(())
    })
}

/// `t: p + go → p`, priority 1, so it starts before `u`. It fires once and leaves `p`
/// as it found it: atomically `t` never changes how many tokens `p` holds.
fn t(action: BoxedAction) -> Transition {
    Transition::builder("t")
        .priority(1)
        .input(one(&p()))
        .input(one(&Place::<()>::new("go")))
        .output(out_place(&p()))
        .action(action)
        .build()
}

/// `u: q + <test of p> → r`.
fn u(test: impl FnOnce(TransitionBuilder) -> TransitionBuilder) -> Transition {
    let q = Place::<()>::new("q");
    let r = Place::<()>::new("r");
    test(Transition::builder("u").input(one(&q)))
        .output(out_place(&r))
        .action(sync_action(|ctx| {
            ctx.output("r", ())?;
            Ok(())
        }))
        .build()
}

fn net(name: &str, action: BoxedAction, test: impl FnOnce(TransitionBuilder) -> TransitionBuilder) -> PetriNet {
    PetriNet::builder(name).transition(t(action)).transition(u(test)).build()
}

/// `u` inhibited by `p`. From `{p, q, go}` `p` is never empty, so `r` is unreachable.
fn inhibitor_net(action: BoxedAction) -> PetriNet {
    net("inflight-inhibitor", action, |b| b.inhibitor(inhibitor(&p())))
}

/// `u` resets `p`. Once `u` has fired `p` is empty and `t` is dead, so `p` and `r` are
/// never marked together.
fn reset_net(action: BoxedAction) -> PetriNet {
    net("inflight-reset", action, |b| b.reset(reset(&p())))
}

/// `u` consumes `all(p)` (or `at_least(2, p)`), which drains `p`: `p` and `r` are never
/// marked together.
fn drain_net(name: &str, action: BoxedAction, input: In) -> PetriNet {
    net(name, action, |b| b.input(input))
}

async fn run_async(backend: Backend, net: &PetriNet, initial: Marking) -> Marking {
    let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
    drop(tx);
    match backend {
        Backend::Bitmap => {
            let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, initial, ExecutorOptions::default());
            ex.run_async(rx).await.into_owned()
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut ex = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, initial).build();
            ex.run_async(rx).await.into_owned()
        }
    }
}

fn run_sync(backend: Backend, net: &PetriNet, initial: Marking) -> Marking {
    match backend {
        Backend::Bitmap => {
            let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, initial, ExecutorOptions::default());
            ex.run_sync().into_owned()
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut ex = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, initial).build();
            ex.run_sync().into_owned()
        }
    }
}

fn count(m: &Marking, place: &str) -> usize {
    m.queue(place).map(|q| q.len()).unwrap_or(0)
}

type Case = (&'static str, fn(BoxedAction) -> PetriNet, &'static [(&'static str, usize)]);

fn cases() -> Vec<Case> {
    vec![
        ("inhibitor", inhibitor_net, &[("p", 1), ("q", 1), ("go", 1)]),
        ("reset", reset_net, &[("p", 1), ("q", 1), ("go", 1)]),
        ("all", |a| drain_net("inflight-all", a, all(&p())), &[("p", 2), ("q", 1), ("go", 1)]),
        ("at_least", |a| drain_net("inflight-at-least", a, at_least(2, &p())), &[("p", 3), ("q", 1), ("go", 1)]),
    ]
}

/// The atomic model's answer for every case: `r` is marked only with `p` empty (the
/// inhibitor case never marks `r` at all).
fn atomic_ok(m: &Marking) -> bool {
    !(count(m, "r") > 0 && count(m, "p") > 0)
}

/// An asynchronous `t` lets `u` fire while `t` holds `p`'s token: the executor ends
/// at `{p, r}`, a marking no atomic run reaches (and, for the inhibitor, at a marked
/// `r` the atomic model says is unreachable).
#[tokio::test]
async fn an_async_action_lets_a_non_monotone_test_see_its_input_empty() {
    for backend in BACKENDS {
        for (name, build, initial) in cases() {
            let m = run_async(backend, &build(slow()), marking(initial)).await;
            assert_eq!(count(&m, "r"), 1, "{backend:?} {name}: u fired while t was in flight");
            assert_eq!(count(&m, "p"), 1, "{backend:?} {name}: t deposited after u");
            assert!(!atomic_ok(&m), "{backend:?} {name}: the final marking is not atomic");
        }
    }
}

/// A synchronous `t` deposits inside the firing pass, but a drain later in the same pass
/// does not see the deposit ([EXEC-003] AC5): it takes what the pass began with, minus
/// what `t` consumed. So reset, `all` and `at_least` reach `{p, r}` without any
/// asynchronous action. The inhibitor does not: `u` was not ready when the pass began.
#[tokio::test]
async fn a_sync_action_interleaves_with_a_drain_in_the_same_pass() {
    for backend in BACKENDS {
        for (name, build, initial) in cases() {
            for m in [
                run_sync(backend, &build(inline()), marking(initial)),
                run_async(backend, &build(inline()), marking(initial)).await,
            ] {
                let atomic = atomic_ok(&m);
                assert_eq!(atomic, name == "inhibitor", "{backend:?} {name}: {:?}", (count(&m, "p"), count(&m, "r")));
            }
        }
    }
}

/// `start: req + inhibitor(busy) → busy`, the usual one-at-a-time guard, with an
/// asynchronous action. Atomically `busy` never holds two tokens. The executor starts the
/// second request while the first is in flight, since `busy` is still empty.
fn guard_net(action: BoxedAction) -> PetriNet {
    let req = Place::<()>::new("req");
    let busy = Place::<()>::new("busy");
    PetriNet::builder("inflight-guard")
        .transition(
            Transition::builder("start")
                .input(one(&req))
                .inhibitor(inhibitor(&busy))
                .output(out_place(&busy))
                .action(action)
                .build(),
        )
        .build()
}

fn slow_busy() -> BoxedAction {
    async_action(|mut ctx| async move {
        tokio::time::sleep(Duration::from_millis(50)).await;
        ctx.output("busy", ())?;
        Ok(ctx)
    })
}

fn inline_busy() -> BoxedAction {
    sync_action(|ctx| {
        ctx.output("busy", ())?;
        Ok(())
    })
}

/// Rust starts a transition again while it is in flight, so the second request starts before
/// the first deposits. Java and TypeScript do not (which of the two an executor does is not
/// specified); two guarded transitions sharing `busy` diverge on every executor. The split
/// covers both.
#[tokio::test]
async fn an_async_guarded_start_runs_twice() {
    for backend in BACKENDS {
        let m = run_async(backend, &guard_net(slow_busy()), marking(&[("req", 2)])).await;
        assert_eq!(count(&m, "busy"), 2, "{backend:?}: both requests started");
        let m = run_sync(backend, &guard_net(inline_busy()), marking(&[("req", 2)]));
        assert_eq!(count(&m, "busy"), 1, "{backend:?}: sync starts one");
        let m = run_async(backend, &two_guards_net(), marking(&[("req", 1), ("req2", 1)])).await;
        assert_eq!(count(&m, "busy"), 2, "{backend:?}: both guarded transitions started");
    }
}

/// `start` and `start2`, each guarded by `inhibitor(busy)`, sharing `busy`.
fn two_guards_net() -> PetriNet {
    let busy = Place::<()>::new("busy");
    let guarded = |name: &str, req: &str| {
        Transition::builder(name)
            .input(one(&Place::<()>::new(req)))
            .inhibitor(inhibitor(&busy))
            .output(out_place(&busy))
            .action(slow_busy())
            .build()
    };
    PetriNet::builder("inflight-two-guards")
        .transition(guarded("start", "req"))
        .transition(guarded("start2", "req2"))
        .build()
}

// ============================================================
//  Witnesses of the fix round (2026-09-30)
// ============================================================

/// An action that sleeps `ms`, then writes `()` to `out`.
fn slow_to(out: &'static str, ms: u64) -> BoxedAction {
    async_action(move |mut ctx| async move {
        tokio::time::sleep(Duration::from_millis(ms)).await;
        ctx.output(out, ())?;
        Ok(ctx)
    })
}

/// An action that writes `()` to `out` inline.
fn inline_to(out: &'static str) -> BoxedAction {
    sync_action(move |ctx| {
        ctx.output(out, ())?;
        Ok(())
    })
}

fn unit(name: &str) -> Place<()> {
    Place::new(name)
}

/// F1. `t: a → ok` (100 ms) and `f: s → done` (10 ms), `done` terminal. `f` completes
/// first and the terminal stop abandons `t` in flight: `a` and `ok` both end empty.
fn terminal_abandon_net() -> PetriNet {
    PetriNet::builder("terminal-abandon")
        .transition(Transition::builder("t").input(one(&unit("a"))).output(out_place(&unit("ok"))).action(slow_to("ok", 100)).build())
        .transition(Transition::builder("f").input(one(&unit("s"))).output(out_place(&unit("done"))).action(slow_to("done", 10)).build())
        .terminal(&unit("done"))
        .build()
}

#[tokio::test]
async fn a_terminal_stop_abandons_an_action_in_flight() {
    for backend in BACKENDS {
        let m = run_async(backend, &terminal_abandon_net(), marking(&[("a", 1), ("s", 1)])).await;
        assert_eq!((count(&m, "a"), count(&m, "ok"), count(&m, "done")), (0, 0, 1), "{backend:?}");
    }
}

/// The ν pair every conflict witness carries, so Route B decides it: `MINT: SEED → X, Y`
/// writes one fresh name into both, and `JOIN` joins `X` and `Y` by name into `J`.
fn nu_pair() -> [Transition; 2] {
    nu_pair_with(0)
}

/// [`nu_pair`] with `JOIN` at `join_priority`.
fn nu_pair_with(join_priority: i32) -> [Transition; 2] {
    use libpetri::core::match_spec::MatchSpec;
    use libpetri::core::name::NameId;
    use libpetri::core::output::and;
    let (x, y, j) = (Place::<String>::new("X"), Place::<String>::new("Y"), Place::<String>::new("J"));
    let mint = Transition::builder("MINT")
        .input(one(&unit("SEED")))
        .output(and(vec![out_place(&x), out_place(&y)]))
        .action(sync_action(|ctx| {
            let n = ctx.fresh_name().to_string();
            ctx.output("X", n.clone())?;
            ctx.output("Y", n)?;
            Ok(())
        }))
        .build();
    let key = |v: &String| NameId::new(v.clone());
    let join = Transition::builder("JOIN")
        .priority(join_priority)
        .input(one(&x))
        .input(one(&y))
        .match_spec(MatchSpec::builder().key(&x, key).key(&y, key).build())
        .output(out_place(&j))
        .action(sync_action(|ctx| {
            let v: String = (*ctx.input::<String>("X")?).clone();
            ctx.output("J", v)?;
            Ok(())
        }))
        .build();
    [mint, join]
}

fn nu_marking(tokens: &[(&str, usize)]) -> Marking {
    let mut m = marking(tokens);
    m.add(&unit("SEED"), Token::at((), 0));
    m
}

/// F2 (a). `t: a → p` (50 ms), `H: p + b → ok` priority 10, `L: b + inhibitor(a) → bad`
/// priority 0. While `t` is in flight `a` is empty and `p` not yet marked, so `L` fires.
fn conflict_feeder_net() -> PetriNet {
    PetriNet::builder("conflict-feeder")
        .transition(Transition::builder("t").input(one(&unit("a"))).output(out_place(&unit("p"))).action(slow_to("p", 50)).build())
        .transition(
            Transition::builder("H")
                .priority(10)
                .input(one(&unit("p")))
                .input(one(&unit("b")))
                .output(out_place(&unit("ok")))
                .action(inline_to("ok"))
                .build(),
        )
        .transition(
            Transition::builder("L")
                .input(one(&unit("b")))
                .inhibitor(inhibitor(&unit("a")))
                .output(out_place(&unit("bad")))
                .action(inline_to("bad"))
                .build(),
        )
        .transitions(nu_pair())
        .build()
}

#[tokio::test]
async fn a_conflict_pruner_fed_by_an_action_in_flight_does_not_pre_empt() {
    for backend in BACKENDS {
        let m = run_async(backend, &conflict_feeder_net(), nu_marking(&[("a", 1), ("b", 1)])).await;
        assert_eq!(count(&m, "bad"), 1, "{backend:?}: L fired while t was in flight");
    }
}

/// F2 (b). `H: c → ok` priority 10 (100 ms), `L: c → bad` priority 0,
/// `g: s + inhibitor(c) → c`. `H` takes `c`, `g` refills it while `H` is in flight. The
/// Java and TypeScript executors do not start `H` again then, so `L` takes the refill and
/// marks `bad`. Rust starts `H` again, which pre-empts `L`: the split model allows both.
fn conflict_restart_net() -> PetriNet {
    PetriNet::builder("conflict-restart")
        .transition(
            Transition::builder("H")
                .priority(10)
                .input(one(&unit("c")))
                .output(out_place(&unit("ok")))
                .action(slow_to("ok", 100))
                .build(),
        )
        .transition(Transition::builder("L").input(one(&unit("c"))).output(out_place(&unit("bad"))).action(inline_to("bad")).build())
        .transition(
            Transition::builder("g")
                .input(one(&unit("s")))
                .inhibitor(inhibitor(&unit("c")))
                .output(out_place(&unit("c")))
                .action(inline_to("c"))
                .build(),
        )
        .transitions(nu_pair())
        .build()
}

#[tokio::test]
async fn rust_restarts_a_pruner_in_flight() {
    for backend in BACKENDS {
        let m = run_async(backend, &conflict_restart_net(), nu_marking(&[("c", 1), ("s", 1)])).await;
        assert_eq!((count(&m, "ok"), count(&m, "bad")), (2, 0), "{backend:?}: H started twice");
    }
}

/// F3. `t: a → p` `deadline(20)` (150 ms), `h: p + b → ok` `deadline(20)`,
/// `v: b → bad` `delayed(60)`. `t` is still running at 60 ms, so `v` takes `b`.
fn long_action_net() -> PetriNet {
    use libpetri::core::timing::{deadline, delayed};
    PetriNet::builder("long-action")
        .transition(
            Transition::builder("t")
                .input(one(&unit("a")))
                .output(out_place(&unit("p")))
                .timing(deadline(20))
                .action(slow_to("p", 150))
                .build(),
        )
        .transition(
            Transition::builder("h")
                .input(one(&unit("p")))
                .input(one(&unit("b")))
                .output(out_place(&unit("ok")))
                .timing(deadline(20))
                .action(inline_to("ok"))
                .build(),
        )
        .transition(
            Transition::builder("v")
                .input(one(&unit("b")))
                .output(out_place(&unit("bad")))
                .timing(delayed(60))
                .action(inline_to("bad"))
                .build(),
        )
        .transitions(nu_pair())
        .build()
}

#[tokio::test]
async fn a_long_action_lets_a_delayed_transition_win() {
    for backend in BACKENDS {
        let m = run_async(backend, &long_action_net(), nu_marking(&[("a", 1), ("b", 1)])).await;
        assert_eq!(count(&m, "bad"), 1, "{backend:?}");
    }
}

// ============================================================
//  The verifier's verdict on the same nets
// ============================================================

#[cfg(feature = "z3")]
mod verdicts {
    use super::*;
    use libpetri::verification::marking_state::{MarkingState, MarkingStateBuilder};
    use libpetri::verification::property::SmtProperty;
    use libpetri::verification::result::VerificationResult;
    use libpetri::verification::smt_verifier::{SmtVerifier, z3_available};

    fn state(tokens: &[(&str, usize)]) -> MarkingState {
        let mut b = MarkingStateBuilder::new();
        for (p, n) in tokens {
            b = b.tokens(*p, *n);
        }
        b.build()
    }

    fn verify(net: &PetriNet, initial: &[(&str, usize)], property: SmtProperty) -> VerificationResult {
        SmtVerifier::for_net(net).initial_marking(state(initial)).property(property).timeout(30_000).verify()
    }

    fn verify_smt_only(net: &PetriNet, initial: &[(&str, usize)], property: SmtProperty) -> VerificationResult {
        SmtVerifier::for_net(net)
            .initial_marking(state(initial))
            .property(property)
            .enumeration_max_classes(0)
            .timeout(30_000)
            .verify()
    }

    /// What the executor reaches must not be proven unreachable, on the enumeration
    /// route and on the SMT pipeline alone.
    #[test]
    fn the_in_flight_interleaving_is_not_proven_away() {
        if !z3_available() {
            eprintln!("skipping: z3 binary not on PATH");
            return;
        }
        for (name, build, initial) in cases() {
            let net = build(slow());
            let property = if name == "inhibitor" {
                SmtProperty::Unreachable { places: vec!["r".into()] }
            } else {
                SmtProperty::MutualExclusion { places: vec!["p".into(), "r".into()] }
            };
            for result in [verify(&net, initial, property.clone()), verify_smt_only(&net, initial, property.clone())] {
                assert!(result.is_violated(), "{name}: {:?} via {:?}\n{}", result.verdict, result.route, result.report);
            }
        }
        let bound = SmtProperty::PlaceBound { place: "busy".into(), bound: 1 };
        for result in [
            verify(&guard_net(slow_busy()), &[("req", 2)], bound.clone()),
            verify_smt_only(&guard_net(slow_busy()), &[("req", 2)], bound),
        ] {
            assert!(result.is_violated(), "guard: {:?} via {:?}\n{}", result.verdict, result.route, result.report);
        }
        // The counterexample is the executor's run: two starts, then two completions.
        let result = verify(&guard_net(slow_busy()), &[("req", 2)], SmtProperty::PlaceBound { place: "busy".into(), bound: 1 });
        assert_eq!(result.counterexample_transitions, ["start", "start", "complete:start", "complete:start"], "{}", result.report);
        assert!(result.report.contains("In-flight actions (VER-004): start is verified in two steps"), "{}", result.report);
    }

    /// `assume_atomic_firing` reads every firing as one step again, and the report says
    /// the verdict rests on it.
    #[test]
    fn assume_atomic_firing_restores_the_atomic_verdict() {
        if !z3_available() {
            eprintln!("skipping: z3 binary not on PATH");
            return;
        }
        let net = guard_net(slow_busy());
        for scg in [0, 50_000] {
            let result = SmtVerifier::for_net(&net)
                .initial_marking(state(&[("req", 2)]))
                .property(SmtProperty::PlaceBound { place: "busy".into(), bound: 1 })
                .enumeration_max_classes(scg)
                .assume_atomic_firing(true)
                .timeout(30_000)
                .verify();
            assert!(result.is_proven(), "{}", result.report);
            assert!(
                result.report.contains("ASSUMPTION: every firing is atomic (the assume-atomic-firing option)"),
                "{}",
                result.report
            );
        }
    }

    /// A net where no transition tests another's output non-monotonically is not
    /// rewritten: same scripts with and without the option, and no report line.
    #[test]
    fn a_net_without_non_monotone_tests_of_outputs_is_unchanged() {
        let p = Place::<()>::new("p");
        let q = Place::<()>::new("q");
        let net = PetriNet::builder("plain")
            .transition(Transition::builder("t").input(one(&p)).output(out_place(&q)).action(inline_q()).build())
            .build();
        let scripts = |atomic: bool| {
            SmtVerifier::for_net(&net)
                .initial_marking(state(&[("p", 1)]))
                .property(SmtProperty::PlaceBound { place: "q".into(), bound: 1 })
                .assume_atomic_firing(atomic)
                .encode_scripts()
                .horn
        };
        assert_eq!(scripts(false), scripts(true));
    }

    fn inline_q() -> BoxedAction {
        sync_action(|ctx| {
            ctx.output("q", ())?;
            Ok(())
        })
    }

    /// A ν-join the split would have to cut in two is refused on every route.
    #[test]
    fn a_nu_join_that_needs_the_split_is_refused() {
        use libpetri::core::match_spec::MatchSpec;
        use libpetri::core::name::NameId;
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let joined = Place::<String>::new("joined");
        let late = Place::<()>::new("late");
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |v: &String| NameId::new(v.clone()))
                    .key(&b, |v: &String| NameId::new(v.clone()))
                    .build(),
            )
            .output(out_place(&joined))
            .action(sync_action(|ctx| {
                ctx.output("joined", String::new())?;
                Ok(())
            }))
            .build();
        let watch = Transition::builder("watch")
            .input(one(&late))
            .inhibitor(inhibitor(&joined))
            .action(sync_action(|_| Ok(())))
            .build();
        let net = PetriNet::builder("nu-in-flight").transition(join).transition(watch).build();
        let result = SmtVerifier::for_net(&net)
            .initial_marking(state(&[("late", 1)]))
            .property(SmtProperty::PlaceBound { place: "joined".into(), bound: 1 })
            .verify();
        match &result.verdict {
            libpetri::verification::result::Verdict::Unknown { reason } => {
                assert!(reason.contains("transition 'join'") && reason.contains("ν-join"), "{reason}")
            }
            other => panic!("expected the refusal, got {other:?}\n{}", result.report),
        }
        // Under the opt-out the atomic net is verified as before.
        let atomic = SmtVerifier::for_net(&net)
            .initial_marking(state(&[("late", 1)]))
            .property(SmtProperty::PlaceBound { place: "joined".into(), bound: 1 })
            .assume_atomic_firing(true)
            .verify();
        assert!(!matches!(atomic.verdict, libpetri::verification::result::Verdict::Unknown { .. }), "{}", atomic.report);
    }

    /// The open-net verifier ([VER-022]) splits the same transitions, on both routes.
    #[test]
    fn the_open_net_verifier_splits_too() {
        use libpetri::verification::open_net::{OpenNetContract, OpenNetOptions, verify_open_net};
        let net = guard_net(slow_busy());
        let contract = OpenNetContract::builder()
            .initial_tokens("req", 2)
            .expect("busy", 1, ["busy"])
            .rest(["req"])
            .build();
        for max_classes in [50_000, 0] {
            if max_classes == 0 && !z3_available() {
                continue;
            }
            let split = verify_open_net(&net, &contract, &OpenNetOptions::default().with_max_classes(max_classes));
            assert!(split.verdict.is_violated(), "{}", split.report);
            assert!(split.report.contains("In-flight actions (VER-004): start is verified in two steps"), "{}", split.report);
            let atomic = verify_open_net(
                &net,
                &contract,
                &OpenNetOptions::default().with_max_classes(max_classes).with_assume_atomic_firing(true),
            );
            assert!(atomic.verdict.is_proven(), "{}", atomic.report);
            assert!(atomic.report.contains("ASSUMPTION: every firing is atomic"), "{}", atomic.report);
        }
    }

    // ------------------------------------------------------------
    //  Witnesses of the fix round (2026-09-30)
    // ------------------------------------------------------------

    fn verdict_word(r: &VerificationResult) -> &'static str {
        match r.verdict {
            libpetri::verification::result::Verdict::Proven { .. } => "proven",
            libpetri::verification::result::Verdict::Violated => "violated",
            _ => "unknown",
        }
    }

    /// F1: the terminal stop abandons `t`, so `QuiescentCount([a, ok], 1, 1)` is violated,
    /// on the enumeration route and on the SMT pipeline alone. Without the terminal-demand
    /// split, `t` stayed atomic and the count was proven.
    #[test]
    fn a_quiescent_count_sees_the_action_a_terminal_stop_abandons() {
        if !z3_available() {
            eprintln!("skipping: z3 binary not on PATH");
            return;
        }
        let net = terminal_abandon_net();
        let property = SmtProperty::quiescent_count(vec!["a".into(), "ok".into()], 1, Some(1), vec![]);
        for result in [
            verify(&net, &[("a", 1), ("s", 1)], property.clone()),
            verify_smt_only(&net, &[("a", 1), ("s", 1)], property.clone()),
        ] {
            assert!(result.is_violated(), "{:?} via {:?}\n{}", result.verdict, result.route, result.report);
            assert!(
                result.report.contains(
                    "a terminal place stops the net without waiting for an action in flight (EXEC-042) \
                     and the property's lower bound counts a place one of them deposits into"
                ),
                "{}",
                result.report
            );
        }
        // A lower bound the terminal waives needs no split: the terminal rest is excused.
        let waived = SmtProperty::quiescent_count(vec!["a".into(), "ok".into()], 1, Some(1), vec!["done".into()]);
        let result = verify(&net, &[("a", 1), ("s", 1)], waived);
        assert!(result.is_proven(), "{}", result.report);
    }

    fn verify_conflict(net: &PetriNet, initial: &[(&str, usize)], atomic: bool) -> VerificationResult {
        use libpetri::verification::priority_semantics::PrioritySemantics;
        let mut tokens = initial.to_vec();
        tokens.push(("SEED", 1));
        SmtVerifier::for_net(net)
            .initial_marking(state(&tokens))
            .property(SmtProperty::Unreachable { places: vec!["bad".into()] })
            .mint_transition("MINT")
            .priority_semantics(PrioritySemantics::Conflict)
            .assume_atomic_firing(atomic)
            .timeout(30_000)
            .verify()
    }

    /// F2 (a): `t` feeds the pruner `H`, so `t` is split, and `L` fires while `t` is in
    /// flight. Before, `t` stayed atomic and conflict priority proved `bad` unreachable.
    #[test]
    fn conflict_priority_splits_the_feeder_of_a_pruner() {
        let result = verify_conflict(&conflict_feeder_net(), &[("a", 1), ("b", 1)], false);
        assert!(result.is_violated(), "{}\n{}", verdict_word(&result), result.report);
        assert!(
            result.report.contains("In-flight actions (VER-004): t, H are verified in two steps"),
            "{}",
            result.report
        );
        assert!(
            result.report.contains("conflict priority (NU-052) reads whether a pruning transition is enabled"),
            "{}",
            result.report
        );
        // The atomic reading keeps the old answer and names the assumption.
        let atomic = verify_conflict(&conflict_feeder_net(), &[("a", 1), ("b", 1)], true);
        assert!(atomic.is_proven(), "{}", atomic.report);
        assert!(atomic.report.contains("ASSUMPTION: every firing is atomic"), "{}", atomic.report);
    }

    /// F2 (b): `H` in flight pre-empts nothing, so `L` takes the refill. Before, the
    /// atomic `H` fired again at once and pruned `L` for ever.
    #[test]
    fn a_pruner_in_flight_pre_empts_nothing() {
        let result = verify_conflict(&conflict_restart_net(), &[("c", 1), ("s", 1)], false);
        assert!(result.is_violated(), "{}\n{}", verdict_word(&result), result.report);
        assert!(result.counterexample_transitions.iter().any(|t| t == "L"), "{:?}", result.counterexample_transitions);
    }

    /// F2 fallback: a ν-join pruner cannot be split, so the pruning is off and the report
    /// says why; the verdict is the one of `PrioritySemantics::None`.
    #[test]
    fn conflict_priority_is_off_when_a_pruner_cannot_be_split() {
        use libpetri::verification::name_fragment::FragmentMode;
        use libpetri::verification::priority_semantics::PrioritySemantics;
        let x = Place::<String>::new("X");
        let drain = Transition::builder("DRAIN")
            .priority(-10)
            .input(one(&x))
            .output(out_place(&unit("DEAD")))
            .action(inline_to("DEAD"))
            .build();
        let [mint, join] = nu_pair_with(10);
        let net = PetriNet::builder("conflict-join").transitions([mint, join, drain]).build();
        let run = |semantics: PrioritySemantics| {
            SmtVerifier::for_net(&net)
                .initial_marking(state(&[("SEED", 1)]))
                .property(SmtProperty::Unreachable { places: vec!["DEAD".into()] })
                .mint_transition("MINT")
                .fragment_mode(FragmentMode::Extended)
                .priority_semantics(semantics)
                .verify()
        };
        let conflict = run(PrioritySemantics::Conflict);
        let none = run(PrioritySemantics::None);
        assert!(conflict.report.contains("Conflict priority (NU-052) is off:"), "{}", conflict.report);
        assert!(conflict.report.contains("cannot be split: it"), "{}", conflict.report);
        assert_eq!(verdict_word(&conflict), verdict_word(&none), "{}\n{}", conflict.report, none.report);
    }

    /// F3: under `assume_no_reaping` Route B keeps the latest bounds and gives an action no
    /// duration, so it proves `bad` unreachable while the executor marks it. The verdict is
    /// labelled so: the assumption names the instant actions, and the sound-and-complete
    /// claim is gone. Read reap-aware, the default, it is violated.
    #[test]
    fn route_b_under_assume_no_reaping_names_its_instant_actions() {
        let net = long_action_net();
        let run = |strict: bool| {
            SmtVerifier::for_net(&net)
                .initial_marking(state(&[("a", 1), ("b", 1), ("SEED", 1)]))
                .property(SmtProperty::Unreachable { places: vec!["bad".into()] })
                .mint_transition("MINT")
                .assume_no_reaping(strict)
                .verify()
        };
        let strict = run(true);
        assert!(strict.is_proven(), "{}", strict.report);
        assert!(
            strict.report.contains(
                "ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its \
                 latest bound, and an action takes no time, i.e. an on-time executor with atomic firings."
            ),
            "{}",
            strict.report
        );
        assert!(!strict.report.contains("sound AND complete"), "{}", strict.report);
        assert!(strict.report.contains("exact only for an on-time executor whose actions take no time"), "{}", strict.report);
        let default = run(false);
        assert!(default.is_violated(), "{}", default.report);
    }

    /// F5 and F7 on the guard net: a split verdict says `ctx.flush()` is not modelled,
    /// and a counterexample that starts `start` twice says only Rust does that.
    #[test]
    fn a_split_verdict_names_flush_and_a_restart() {
        if !z3_available() {
            eprintln!("skipping: z3 binary not on PATH");
            return;
        }
        let result = verify(&guard_net(slow_busy()), &[("req", 2)], SmtProperty::PlaceBound { place: "busy".into(), bound: 1 });
        assert!(result.is_violated(), "{}", result.report);
        assert!(result.report.contains("an action that calls ctx.flush() publishes"), "{}", result.report);
        assert!(
            result.report.contains(
                "NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is \
                 still in flight (inflight:start marked)."
            ),
            "{}",
            result.report
        );
        // A counterexample without a restart carries no such note.
        let result = verify(&inhibitor_net(slow()), &[("p", 1), ("q", 1), ("go", 1)], SmtProperty::Unreachable { places: vec!["r".into()] });
        assert!(result.is_violated(), "{}", result.report);
        assert!(!result.report.contains("NOTE (CONC-002)"), "{}", result.report);
    }
}
