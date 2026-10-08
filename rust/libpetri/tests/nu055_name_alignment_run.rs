//! \[NU-055\] AC5: the search-as-you-type net of the worked example, run with names minted in
//! the default scope and in a pinned one ([NU-010], [NU-011]) on both executors. The fixed net
//! rests with `box` and `list` holding one name (`QuiescentNameAligned` is `Proven`); the buggy
//! variant rests on the old results (`Violated`, 12 firings), and the minting scope changes
//! neither. The verifier answers the same on these executable nets as on the fixtures of
//! `spec/verification-fixtures/nu-aligned-fixtures.json`.
//!
//! `fetchA` answers only once `show` has shown a result, so the reply to the first keystroke
//! lands after the reply to the second, deterministically: the run the buggy variant's
//! counterexample describes. Lives in the umbrella crate so it can run the executors and the
//! verifier together. The same runs as TypeScript's `tests/verification/nu-name-alignment.test.ts`.

#![cfg(all(feature = "tokio", feature = "z3"))]

use std::sync::Arc;

use libpetri::core::action::{BoxedAction, async_action, sync_action};
use libpetri::core::input::one;
use libpetri::core::match_spec::MatchSpec;
use libpetri::core::name::NameId;
use libpetri::core::output::{and, out_place};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::compiled_net::CompiledNet;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;
use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
use libpetri::runtime::precompiled_net::PrecompiledNet;
use libpetri::verification::marking_state::MarkingStateBuilder;
use libpetri::verification::name_fragment::FragmentMode;
use libpetri::verification::property::SmtProperty;
use libpetri::verification::result::VerificationRoute;
use libpetri::verification::smt_verifier::SmtVerifier;
use tokio::sync::Notify;

const INITIAL: [(&str, usize); 4] = [("typed", 2), ("idle", 1), ("listEmpty", 1), ("slot", 1)];
const SCOPE: &str = "nu055-scope";

fn p(name: &str) -> Place<String> {
    Place::new(name)
}

fn key(s: &String) -> NameId {
    NameId::new(s.clone())
}

/// Writes a unit token into `to`.
fn unit(to: &'static str) -> BoxedAction {
    sync_action(move |ctx| {
        ctx.output(to, "unit".to_string())?;
        Ok(())
    })
}

/// Writes the name consumed from `from` into each of `to`, and a unit token into `unit_to`.
fn relay(from: &'static str, to: &'static [&'static str], unit_to: Option<&'static str>) -> BoxedAction {
    sync_action(move |ctx| {
        let n: String = (*ctx.input::<String>(from)?).clone();
        for place in to {
            ctx.output(place, n.clone())?;
        }
        if let Some(place) = unit_to {
            ctx.output(place, "unit".to_string())?;
        }
        Ok(())
    })
}

/// Mints a fresh name into `box` and `inflight` ([NU-010]).
fn mint(inflight: &'static str) -> BoxedAction {
    sync_action(move |ctx| {
        let n = ctx.fresh_name().as_str().to_string();
        ctx.output("box", n.clone())?;
        ctx.output(inflight, n)?;
        Ok(())
    })
}

fn step(name: &str, ins: &[&str], outs: &[&str], action: BoxedAction) -> Transition {
    let mut b = Transition::builder(name);
    for i in ins {
        b = b.input(one(&p(i)));
    }
    let out = if outs.len() == 1 {
        out_place(&p(outs[0]))
    } else {
        and(outs.iter().map(|o| out_place(&p(o))).collect())
    };
    b.output(out).action(action).build()
}

/// The search-as-you-type net with executable actions: each token of a coloured place is
/// its name. `fetchA` waits for `show`, so it answers last.
fn search_as_you_type(bug: bool) -> PetriNet {
    let shown = Arc::new(Notify::new());
    let gate = Arc::clone(&shown);
    let fetch_a = async_action(move |mut ctx| {
        let gate = Arc::clone(&gate);
        async move {
            let n: String = (*ctx.input::<String>("inflightA")?).clone();
            gate.notified().await;
            ctx.output("reply", n)?;
            Ok(ctx)
        }
    });
    let show = sync_action(move |ctx| {
        let n: String = (*ctx.input::<String>("staged")?).clone();
        ctx.output("list", n)?;
        ctx.output("slot", "unit".to_string())?;
        shown.notify_one();
        Ok(())
    });
    let apply = if bug {
        step("apply_bug", &["reply", "slot"], &["staged", "clr"], relay("reply", &["staged"], Some("clr")))
    } else {
        Transition::builder("apply")
            .input(one(&p("reply")))
            .input(one(&p("box")))
            .input(one(&p("slot")))
            .match_spec(
                MatchSpec::builder()
                    .key(&p("reply"), key)
                    .key(&p("box"), key)
                    .relay_to(&p("box"), key)
                    .relay_to(&p("staged"), key)
                    .build(),
            )
            .output(and(vec![out_place(&p("box")), out_place(&p("staged")), out_place(&p("clr"))]))
            .action(relay("reply", &["box", "staged"], Some("clr")))
            .build()
    };
    PetriNet::builder(if bug { "searchAsYouTypeBug" } else { "searchAsYouType" })
        .transitions([
            step("first", &["idle", "typed"], &["armedA"], unit("armedA")),
            step("retire", &["box", "typed"], &["armedB"], unit("armedB")),
            step("sendA", &["armedA"], &["box", "inflightA"], mint("inflightA")),
            step("sendB", &["armedB"], &["box", "inflightB"], mint("inflightB")),
            step("fetchA", &["inflightA"], &["reply"], fetch_a),
            step("fetchB", &["inflightB"], &["reply"], relay("inflightB", &["reply"], None)),
            apply,
            step("clearNone", &["listEmpty", "clr"], &["ready"], unit("ready")),
            step("clear", &["list", "clr"], &["ready"], unit("ready")),
            step("show", &["staged", "ready"], &["list", "slot"], show),
        ])
        .build()
}

fn initial_tokens() -> Marking {
    let mut m = Marking::new();
    for (name, k) in INITIAL {
        for _ in 0..k {
            m.add(&p(name), Token::at("unit".to_string(), 0));
        }
    }
    m
}

fn names(m: &Marking, place: &str) -> Vec<String> {
    m.queue(place)
        .map(|q| q.iter().map(|t| t.downcast::<String>().expect("a String token").value().clone()).collect())
        .unwrap_or_default()
}

#[derive(Debug, Clone, Copy)]
enum Backend {
    Bitmap,
    Precompiled,
}

async fn run(backend: Backend, net: &PetriNet, scope: Option<&str>) -> Marking {
    let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
    drop(tx);
    match backend {
        Backend::Bitmap => {
            let mut options = ExecutorOptions::default();
            if let Some(scope) = scope {
                options = options.execution_scope(scope);
            }
            let mut ex = BitmapNetExecutor::<NoopEventStore>::new(net, initial_tokens(), options);
            ex.run_async(rx).await.into_owned()
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut builder = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, initial_tokens());
            if let Some(scope) = scope {
                builder = builder.execution_scope(scope);
            }
            let mut ex = builder.build();
            ex.run_async(rx).await.into_owned()
        }
    }
}

/// [NU-055] AC5: on both executors and in both minting scopes the fixed net rests aligned
/// and the buggy variant, with the first reply answered last, rests on the old results.
#[tokio::test]
async fn nu055_ac5_runs_rest_as_the_verdicts_say_in_every_minting_scope() {
    for backend in [Backend::Bitmap, Backend::Precompiled] {
        for scope in [None, Some(SCOPE)] {
            for bug in [false, true] {
                let at_rest = run(backend, &search_as_you_type(bug), scope).await;
                let what = format!("{backend:?}, scope {scope:?}, bug {bug}");
                let in_box = names(&at_rest, "box");
                let in_list = names(&at_rest, "list");
                assert_eq!(in_box.len(), 1, "{what}: {in_box:?}");
                assert_eq!(in_list.len(), 1, "{what}: {in_list:?}");
                if let Some(scope) = scope {
                    assert!(in_box[0].contains(&format!("#{scope}:")), "{what}: {in_box:?}");
                }
                if bug {
                    assert_ne!(in_list[0], in_box[0], "{what}");
                } else {
                    assert_eq!(in_list[0], in_box[0], "{what}");
                }
            }
        }
    }
}

/// [NU-055] AC5: the verdicts on the executable nets are those of the fixtures.
#[test]
fn nu055_ac5_the_verdicts_on_the_executable_nets_match_the_fixtures() {
    for bug in [false, true] {
        let net = search_as_you_type(bug);
        let carriers: &[&str] = if bug {
            &["box", "inflightA", "inflightB", "reply", "staged", "list"]
        } else {
            &["inflightA", "inflightB", "list"]
        };
        let mut m0 = MarkingStateBuilder::new();
        for (name, k) in INITIAL {
            m0 = m0.tokens(name, k);
        }
        let r = SmtVerifier::for_net(&net)
            .initial_marking(m0.build())
            .property(SmtProperty::quiescent_name_aligned(["box", "list"]))
            .mint_transitions(["sendA", "sendB"].map(String::from))
            .carrier_places(carriers.iter().map(|c| c.to_string()))
            .fragment_mode(FragmentMode::Extended)
            .verify();
        assert_eq!(r.route, VerificationRoute::NuScg, "{}", r.report);
        if bug {
            assert!(r.is_violated(), "{}", r.report);
            assert_eq!(r.counterexample_transitions.len(), 12);
        } else {
            assert!(r.is_proven(), "{}", r.report);
        }
    }
}
