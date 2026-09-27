//! \[NU-054\] join relay: the runtime check that every token a join writes
//! into a relay target carries the name it matched (AC2), on both executor
//! backends, on the sync path, the async completion path, the `Out::Timeout`
//! branch (forwarded input included) and a batch published mid-action.

#![cfg(test)]

use libpetri_core::action::{BoxedAction, sync_action};
use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{Out, and, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::token::Token;
use libpetri_core::transition::Transition;
use libpetri_event::event_store::{EventStore, InMemoryEventStore};
use libpetri_event::net_event::NetEvent;

use crate::compiled_net::CompiledNet;
use crate::executor::{BitmapNetExecutor, ExecutorOptions};
use crate::marking::Marking;
use crate::precompiled_executor::PrecompiledNetExecutor;
use crate::precompiled_net::PrecompiledNet;

#[derive(Clone, Debug)]
struct Msg {
    cid: String,
}

fn msg(cid: &str) -> Msg {
    Msg { cid: cid.into() }
}

fn by_cid(m: &Msg) -> NameId {
    NameId::new(m.cid.clone())
}

#[derive(Clone, Copy, Debug)]
enum Backend {
    Bitmap,
    Precompiled,
}

const BACKENDS: [Backend; 2] = [Backend::Bitmap, Backend::Precompiled];

struct Outcome {
    marking: Marking,
    events: Vec<NetEvent>,
}

impl Outcome {
    fn failures(&self) -> Vec<String> {
        self.events
            .iter()
            .filter_map(|e| match e {
                NetEvent::TransitionFailed { error, .. } => Some(error.clone()),
                _ => None,
            })
            .collect()
    }

    fn completed(&self) -> usize {
        self.events
            .iter()
            .filter(|e| matches!(e, NetEvent::TransitionCompleted { .. }))
            .count()
    }

    fn cids(&self, place: &str) -> Vec<String> {
        self.marking
            .queue(place)
            .map(|q| {
                q.iter()
                    .filter_map(|t| t.value.downcast_ref::<Msg>().map(|m| m.cid.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }
}

/// `A`, `B` hold one token named `x` each (plus whatever `extra` adds).
fn initial(extra: &[(&Place<Msg>, &str)]) -> Marking {
    let mut marking = Marking::new();
    marking.add(&Place::<Msg>::new("A"), Token::at(msg("x"), 0));
    marking.add(&Place::<Msg>::new("B"), Token::at(msg("x"), 0));
    for (p, cid) in extra {
        marking.add(*p, Token::at(msg(cid), 0));
    }
    marking
}

fn run_sync(backend: Backend, net: &PetriNet, marking: Marking, skip: bool) -> Outcome {
    match backend {
        Backend::Bitmap => {
            assert!(!skip, "the bitmap executor has no validation escape hatch");
            let mut ex = BitmapNetExecutor::<InMemoryEventStore>::new(
                net,
                marking,
                ExecutorOptions::default(),
            );
            let marking = ex.run_sync().into_owned();
            Outcome {
                marking,
                events: ex.event_store().events().to_vec(),
            }
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut ex = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
                .event_store(InMemoryEventStore::new())
                .skip_output_validation(skip)
                .build();
            let marking = ex.run_sync().into_owned();
            Outcome {
                marking,
                events: ex.event_store().events().to_vec(),
            }
        }
    }
}

#[cfg(feature = "tokio")]
async fn run_async(backend: Backend, net: &PetriNet, marking: Marking) -> Outcome {
    let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
    drop(tx);
    match backend {
        Backend::Bitmap => {
            let mut ex = BitmapNetExecutor::<InMemoryEventStore>::new(
                net,
                marking,
                ExecutorOptions::default(),
            );
            let marking = ex.run_async(rx).await.into_owned();
            Outcome {
                marking,
                events: ex.event_store().events().to_vec(),
            }
        }
        Backend::Precompiled => {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut ex = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
                .event_store(InMemoryEventStore::new())
                .build();
            let marking = ex.run_async(rx).await.into_owned();
            Outcome {
                marking,
                events: ex.event_store().events().to_vec(),
            }
        }
    }
}

/// A join on `A`, `B` relaying to `C`; `action` decides what lands in `C`.
fn relay_net(out: Out, action: BoxedAction) -> PetriNet {
    let a = Place::<Msg>::new("A");
    let b = Place::<Msg>::new("B");
    let c = Place::<Msg>::new("C");
    let j = Transition::builder("j")
        .input(one(&a))
        .input(one(&b))
        .output(out)
        .match_spec(
            MatchSpec::builder()
                .key(&a, by_cid)
                .key(&b, by_cid)
                .relay_to(&c, by_cid)
                .build(),
        )
        .action(action)
        .build();
    PetriNet::builder("relay").transition(j).build()
}

/// Writes `A`'s name (or `cid`, when given) into `C`.
fn write_c(cid: Option<&'static str>) -> BoxedAction {
    sync_action(move |ctx| {
        let a = ctx.input::<Msg>("A")?;
        let v = cid.map_or_else(|| a.cid.clone(), str::to_string);
        ctx.output("C", Msg { cid: v })?;
        Ok(())
    })
}

fn c_out() -> Out {
    out_place(&Place::<Msg>::new("C"))
}

const OTHER_NAME: &str =
    "'j': relay target 'C' received a token with name 'y', but the join matched name 'x' (NU-054)";
const NO_NAME: &str =
    "'j': relay target 'C' received a token with no name, but the join matched name 'x' (NU-054)";

#[test]
fn conforming_action_fires_normally() {
    for backend in BACKENDS {
        let out = run_sync(backend, &relay_net(c_out(), write_c(None)), initial(&[]), false);
        assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
        assert_eq!(out.cids("C"), vec!["x"], "{backend:?}");
    }
}

#[test]
fn token_of_another_name_fails_the_firing() {
    for backend in BACKENDS {
        let out = run_sync(backend, &relay_net(c_out(), write_c(Some("y"))), initial(&[]), false);
        assert_eq!(out.failures(), vec![OTHER_NAME.to_string()], "{backend:?}");
        assert!(out.cids("C").is_empty(), "{backend:?}: a failed firing deposits nothing");
        assert_eq!(out.completed(), 0, "{backend:?}");
    }
}

#[test]
fn token_projecting_to_no_name_fails_the_firing() {
    // A value of another type projects to no name, as it does for a match key.
    for backend in BACKENDS {
        let action = sync_action(|ctx| {
            ctx.output("C", "not a Msg".to_string())?;
            Ok(())
        });
        let out = run_sync(backend, &relay_net(c_out(), action), initial(&[]), false);
        assert_eq!(out.failures(), vec![NO_NAME.to_string()], "{backend:?}");
    }
}

#[test]
fn absent_value_has_no_name_and_the_projection_is_not_called() {
    // A unit relay target: the projection accepts `()`, so only the absent-value
    // rule keeps it from being called on the unit token.
    for backend in BACKENDS {
        let a = Place::<Msg>::new("A");
        let b = Place::<Msg>::new("B");
        let u = Place::<()>::new("U");
        let j = Transition::builder("j")
            .input(one(&a))
            .input(one(&b))
            .output(out_place(&u))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, by_cid)
                    .key(&b, by_cid)
                    .relay_to(&u, |_: &()| panic!("the projection must not see an absent value"))
                    .build(),
            )
            .action(sync_action(|ctx| {
                ctx.output("U", ())?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("unit").transition(j).build();
        let out = run_sync(backend, &net, initial(&[]), false);
        assert_eq!(
            out.failures(),
            vec![
                "'j': relay target 'U' received a token with no name, but the join matched name 'x' (NU-054)"
                    .to_string()
            ],
            "{backend:?}"
        );
    }
}

#[test]
fn every_token_in_the_target_is_checked() {
    for backend in BACKENDS {
        let log = Place::<String>::new("log");
        let action = sync_action(|ctx| {
            ctx.output("C", msg("x"))?;
            ctx.output("C", msg("z"))?;
            ctx.output("log", "done".to_string())?;
            Ok(())
        });
        let out = run_sync(
            backend,
            &relay_net(and(vec![c_out(), out_place(&log)]), action),
            initial(&[]),
            false,
        );
        let failures = out.failures();
        assert_eq!(failures.len(), 1, "{backend:?}");
        assert!(failures[0].contains("name 'z'"), "{backend:?}: {}", failures[0]);
    }
}

#[test]
fn a_place_that_is_not_a_relay_target_is_not_checked() {
    for backend in BACKENDS {
        let log = Place::<String>::new("log");
        let action = sync_action(|ctx| {
            ctx.output("C", msg("x"))?;
            ctx.output("log", "anything".to_string())?;
            Ok(())
        });
        let out = run_sync(
            backend,
            &relay_net(and(vec![c_out(), out_place(&log)]), action),
            initial(&[]),
            false,
        );
        assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
    }
}

#[test]
fn skipped_exactly_where_output_validation_is() {
    // CONC-026: the precompiled executor's escape hatch skips the relay check too.
    let out = run_sync(
        Backend::Precompiled,
        &relay_net(c_out(), write_c(Some("y"))),
        initial(&[]),
        true,
    );
    assert_eq!(out.failures(), Vec::<String>::new());
    assert_eq!(out.cids("C"), vec!["y"]);
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn async_completion_is_checked() {
    for backend in BACKENDS {
        let action = libpetri_core::action::async_action(|mut ctx| async move {
            ctx.output("C", msg("y"))?;
            Ok(ctx)
        });
        let out = run_async(backend, &relay_net(c_out(), action), initial(&[])).await;
        assert_eq!(out.failures(), vec![OTHER_NAME.to_string()], "{backend:?}");
        assert!(out.cids("C").is_empty(), "{backend:?}");
    }
}

/// A sync action fired by the async loop completes inline, on its own path.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_sync_action_under_the_async_loop_is_checked() {
    for backend in BACKENDS {
        let out = run_async(backend, &relay_net(c_out(), write_c(Some("y"))), initial(&[])).await;
        assert_eq!(out.failures(), vec![OTHER_NAME.to_string()], "{backend:?}");
        assert!(out.cids("C").is_empty(), "{backend:?}");
        let out = run_async(backend, &relay_net(c_out(), write_c(None)), initial(&[])).await;
        assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
        assert_eq!(out.cids("C"), vec!["x"], "{backend:?}");
    }
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn timeout_branch_is_checked_forwarded_input_included() {
    // IO-013/IO-014: what an `Out::Timeout` branch deposits is checked like an
    // action's write. Forwarding the matched key token conforms; forwarding the
    // non-key input's token (name `q`) does not.
    let z = Place::<Msg>::new("Z");
    for backend in BACKENDS {
        for (from, expect_fail) in [("A", false), ("Z", true)] {
            let a = Place::<Msg>::new("A");
            let b = Place::<Msg>::new("B");
            let c = Place::<Msg>::new("C");
            let from_place = Place::<Msg>::new(from);
            let j = Transition::builder("j")
                .input(one(&a))
                .input(one(&b))
                .input(one(&z))
                .output(libpetri_core::output::timeout(
                    10,
                    libpetri_core::output::forward_input(&from_place, &c),
                ))
                .match_spec(
                    MatchSpec::builder()
                        .key(&a, by_cid)
                        .key(&b, by_cid)
                        .relay_to(&c, by_cid)
                        .build(),
                )
                .action(libpetri_core::action::async_action(|ctx| async move {
                    tokio::time::sleep(std::time::Duration::from_millis(500)).await;
                    Ok(ctx)
                }))
                .build();
            let net = PetriNet::builder("slow").transition(j).build();
            let out = run_async(backend, &net, initial(&[(&z, "q")])).await;
            if expect_fail {
                assert_eq!(
                    out.failures(),
                    vec![
                        "'j': relay target 'C' received a token with name 'q', but the join matched name 'x' (NU-054)"
                            .to_string()
                    ],
                    "{backend:?}"
                );
                assert!(out.cids("C").is_empty(), "{backend:?}");
            } else {
                assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
                assert_eq!(out.cids("C"), vec!["x"], "{backend:?}");
            }
        }
    }
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_flushed_batch_is_checked_when_it_is_published() {
    // IO-015: a batch published mid-action is checked when it is published. The
    // violating batch is not deposited and the firing fails; the conforming
    // token written after it does not rescue the firing.
    for backend in BACKENDS {
        let action = libpetri_core::action::async_action(|mut ctx| async move {
            ctx.output("C", msg("y"))?;
            ctx.flush()?;
            ctx.output("C", msg("x"))?;
            Ok(ctx)
        });
        let out = run_async(backend, &relay_net(c_out(), action), initial(&[])).await;
        assert_eq!(out.failures(), vec![OTHER_NAME.to_string()], "{backend:?}");
        assert!(out.cids("C").is_empty(), "{backend:?}: {:?}", out.cids("C"));
        assert_eq!(out.completed(), 0, "{backend:?}");
    }
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_refused_flush_returns_err_with_the_relay_message() {
    // NU-054: the violation reaches the action as `flush()`'s `Err`, not only at
    // completion. An action that swallows the `Err` still fails the firing, and a
    // later flush is refused with the same message.
    for backend in BACKENDS {
        use std::sync::{Arc, Mutex};
        let seen: Arc<Mutex<Vec<Result<(), String>>>> = Arc::default();
        let record = Arc::clone(&seen);
        let action = libpetri_core::action::async_action(move |mut ctx| {
            let record = Arc::clone(&record);
            async move {
                ctx.output("C", msg("y"))?;
                let first = ctx.flush().map_err(|e| e.message);
                ctx.output("C", msg("x"))?;
                let second = ctx.flush().map_err(|e| e.message);
                record.lock().unwrap().extend([first, second]);
                Ok(ctx)
            }
        });
        let out = run_async(backend, &relay_net(c_out(), action), initial(&[])).await;
        assert_eq!(
            *seen.lock().unwrap(),
            vec![Err(OTHER_NAME.to_string()), Err(OTHER_NAME.to_string())],
            "{backend:?}"
        );
        assert_eq!(out.failures(), vec![OTHER_NAME.to_string()], "{backend:?}");
        assert!(out.cids("C").is_empty(), "{backend:?}: {:?}", out.cids("C"));
    }
}

#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_conforming_flushed_batch_is_deposited() {
    for backend in BACKENDS {
        let action = libpetri_core::action::async_action(|mut ctx| async move {
            ctx.output("C", msg("x"))?;
            ctx.flush()?;
            Ok(ctx)
        });
        let out = run_async(backend, &relay_net(c_out(), action), initial(&[])).await;
        assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
        assert_eq!(out.cids("C"), vec!["x"], "{backend:?}");
    }
}

#[test]
fn the_join_without_relays_writes_freely() {
    // A join without a relay declaration is not checked: the check is
    // declaration-driven.
    for backend in BACKENDS {
        let a = Place::<Msg>::new("A");
        let b = Place::<Msg>::new("B");
        let c = Place::<Msg>::new("C");
        let j = Transition::builder("j")
            .input(one(&a))
            .input(one(&b))
            .output(out_place(&c))
            .match_spec(MatchSpec::builder().key(&a, by_cid).key(&b, by_cid).build())
            .action(write_c(Some("y")))
            .build();
        let net = PetriNet::builder("plain").transition(j).build();
        let out = run_sync(backend, &net, initial(&[]), false);
        assert_eq!(out.failures(), Vec::<String>::new(), "{backend:?}");
        assert_eq!(out.cids("C"), vec!["y"], "{backend:?}");
    }
}
