//! \[CORE-073\] snapshot / restore, \[ENV-014\] AC5–AC8, and \[NU-011\].
//!
//! The three land together on purpose: restore is what makes a resumed
//! execution possible, ENV-014 is what tells a caller whether a snapshot is
//! safe to resume *from*, and NU-011 is what stops the resumed segment
//! re-minting ν-names the restored marking already holds.

use std::sync::{Arc, Mutex};

use libpetri::core::action::{ActionError, fork, sync_action};
use libpetri::core::context::TransitionContext;
use libpetri::core::input::one;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::core::match_spec::MatchSpec;
use libpetri::core::name::NameId;
use libpetri::core::output::and;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::compiled_net::CompiledNet;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::{Marking, MarkingSnapshot};
use libpetri::runtime::owned_precompiled::OwnedPrecompiledNet;
use libpetri::runtime::precompiled_executor::PrecompiledNetExecutor;
use libpetri::runtime::precompiled_net::PrecompiledNet;

// ============================================================
//  Every executor entry point, from one source
// ============================================================

/// The three ways a host reaches an executor. Bitmap is the reference and
/// Precompiled the production backend, and they must agree; `Owned` is the
/// cached-program entry point, which forwards every option by hand through
/// its own builder — so an option it forgets is a bug only a test that names
/// it can see.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Backend {
    Bitmap,
    Precompiled,
    Owned,
}

const BACKENDS: [Backend; 3] = [Backend::Bitmap, Backend::Precompiled, Backend::Owned];

/// Runs `net` to sync completion on `backend`, optionally under a pinned
/// \[NU-011\] scope, and returns the final marking.
fn run_sync_on(backend: Backend, net: &PetriNet, marking: Marking, scope: Option<&str>) -> Marking {
    match backend {
        Backend::Bitmap => {
            let mut options = ExecutorOptions::default();
            if let Some(scope) = scope {
                options = options.execution_scope(scope);
            }
            let mut executor = BitmapNetExecutor::<NoopEventStore>::new(net, marking, options);
            executor.run_sync().into_owned()
        }
        Backend::Precompiled => {
            let program = PrecompiledNet::from_compiled(CompiledNet::compile(net));
            let mut builder = PrecompiledNetExecutor::<NoopEventStore>::builder(&program, marking);
            if let Some(scope) = scope {
                builder = builder.execution_scope(scope);
            }
            let mut executor = builder.build();
            executor.run_sync().into_owned()
        }
        Backend::Owned => {
            let owned = OwnedPrecompiledNet::compile(net);
            let mut builder = owned.builder::<NoopEventStore>(marking);
            if let Some(scope) = scope {
                builder = builder.execution_scope(scope);
            }
            builder.run_sync()
        }
    }
}

fn strings_at(marking: &Marking, place: &str) -> Vec<String> {
    marking
        .queue(place)
        .map(|q| {
            q.iter()
                .map(|t| t.value.downcast_ref::<String>().expect("String").clone())
                .collect()
        })
        .unwrap_or_default()
}

// ============================================================
//  CORE-073 — the normative form
// ============================================================

/// AC#1, AC#6, AC#9: values, `created_at`, and FIFO order all survive.
#[test]
fn round_trip_preserves_values_timestamps_and_fifo_order() {
    let p = Place::<String>::new("p");
    let mut marking = Marking::new();
    for (value, stamp) in [("A", 10u64), ("B", 20), ("C", 30)] {
        marking.add(&p, Token::at(value.to_string(), stamp));
    }

    let restored = Marking::from_snapshot(&marking.snapshot());
    let queue = restored.queue("p").expect("place restored");

    let values: Vec<&String> = queue
        .iter()
        .map(|t| t.value.downcast_ref::<String>().expect("String"))
        .collect();
    assert_eq!(values, vec!["A", "B", "C"], "FIFO order is part of the data");
    assert_eq!(
        queue.iter().map(|t| t.created_at).collect::<Vec<_>>(),
        vec![10, 20, 30],
        "created_at survives verbatim — the engine never re-stamps a restore"
    );
}

/// AC#7, the **accept** half. Worth testing directly: `snapshot()` never
/// emits an empty sequence, so a round-trip can never exercise this.
#[test]
fn an_explicitly_empty_sequence_restores_identically_to_an_omitted_one() {
    let p = Place::<String>::new("present");

    let mut with_empty: MarkingSnapshot = MarkingSnapshot::new();
    with_empty.insert(Arc::from("present"), vec![]);
    with_empty.insert(
        Arc::from("other"),
        vec![libpetri::core::token::ErasedToken::from_typed(&Token::at(
            "x".to_string(),
            5,
        ))],
    );

    let mut omitted: MarkingSnapshot = MarkingSnapshot::new();
    omitted.insert(
        Arc::from("other"),
        vec![libpetri::core::token::ErasedToken::from_typed(&Token::at(
            "x".to_string(),
            5,
        ))],
    );

    let a = Marking::from_snapshot(&with_empty);
    let b = Marking::from_snapshot(&omitted);

    assert_eq!(a.count("present"), 0);
    assert_eq!(b.count("present"), 0);
    assert_eq!(a.count("other"), b.count("other"));
    assert_eq!(
        a.non_empty_places().len(),
        b.non_empty_places().len(),
        "present-but-empty and omitted must restore identically"
    );
    let _ = p;
}

/// AC#7: a place the receiving net does not declare is retained, not dropped.
#[test]
fn a_place_the_net_does_not_declare_is_retained() {
    let p_in = Place::<String>::new("in");
    let p_out = Place::<String>::new("out");
    let net = PetriNet::builder("n")
        .transition(
            Transition::builder("t")
                .input(one(&p_in))
                .output(out_place(&p_out))
                .action(fork())
                .build(),
        )
        .build();

    for backend in BACKENDS {
        let mut marking = Marking::new();
        marking.add(&p_in, Token::at("a".to_string(), 1));
        marking.add(&Place::<String>::new("ghost"), Token::at("g".to_string(), 2));

        // Through the snapshot form on the way in as well: on the precompiled
        // backend an undeclared place has no ring buffer to live in, so this
        // is where a restore could lose it.
        let restored = Marking::from_snapshot(&marking.snapshot());
        let snapshot = run_sync_on(backend, &net, restored, None).snapshot();

        let ghost = snapshot
            .get("ghost")
            .unwrap_or_else(|| panic!("{backend:?}: unknown place must be retained"));
        assert_eq!(ghost.len(), 1, "{backend:?}");
        assert_eq!(ghost[0].created_at, 2, "{backend:?}: and keep its original stamp");
        assert_eq!(
            snapshot.keys().map(|k| k.as_ref()).collect::<Vec<_>>(),
            vec!["ghost", "out"],
            "{backend:?}: emitted form is sorted and omits the now-empty `in`"
        );
    }
}

/// \[CORE-072\] AC#4 for a **restored** seed: an undeclared place that arrives
/// through [`Marking::from_snapshot`] is warned about exactly as one added by
/// hand is — once per place, on the log-message event, with no transition
/// named. A restore is where an undeclared place is most likely to come from
/// (the snapshot was taken against an older net), so it is the case that
/// most needs the diagnostic.
///
/// The owned entry point consumes its builder, store included, so the store
/// here shares its buffer with the test.
#[test]
fn an_undeclared_place_in_a_restored_seed_is_warned_about_once() {
    use libpetri::event::event_store::{EventStore, InMemoryEventStore};
    use libpetri::event::net_event::NetEvent;

    #[derive(Default)]
    struct SharedStore(Arc<Mutex<Vec<NetEvent>>>);
    impl EventStore for SharedStore {
        const ENABLED: bool = true;
        fn append(&mut self, event: NetEvent) {
            self.0.lock().unwrap().push(event);
        }
        fn events(&self) -> &[NetEvent] {
            &[]
        }
        fn size(&self) -> usize {
            self.0.lock().unwrap().len()
        }
        fn is_empty(&self) -> bool {
            self.0.lock().unwrap().is_empty()
        }
    }

    let p_in = Place::<String>::new("in");
    let p_out = Place::<String>::new("out");
    let net = PetriNet::builder("n")
        .transition(
            Transition::builder("t")
                .input(one(&p_in))
                .output(out_place(&p_out))
                .action(fork())
                .build(),
        )
        .build();

    for backend in BACKENDS {
        let mut source = Marking::new();
        source.add(&p_in, Token::at("a".to_string(), 1));
        let ghost = Place::<String>::new("ghost");
        for v in ["g1", "g2", "g3"] {
            source.add(&ghost, Token::at(v.to_string(), 2));
        }
        let seed = Marking::from_snapshot(&source.snapshot());

        let events: Vec<NetEvent> = match backend {
            Backend::Bitmap => {
                let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
                    &net,
                    seed,
                    ExecutorOptions::default(),
                );
                executor.run_sync();
                executor.event_store().events().to_vec()
            }
            Backend::Precompiled => {
                let program = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
                let mut executor =
                    PrecompiledNetExecutor::<InMemoryEventStore>::builder(&program, seed).build();
                executor.run_sync();
                executor.event_store().events().to_vec()
            }
            Backend::Owned => {
                let shared = Arc::new(Mutex::new(Vec::new()));
                OwnedPrecompiledNet::compile(&net)
                    .builder::<SharedStore>(seed)
                    .event_store(SharedStore(Arc::clone(&shared)))
                    .run_sync();
                let events = shared.lock().unwrap().clone();
                events
            }
        };

        let warnings: Vec<(&str, &str, &str)> = events
            .iter()
            .filter_map(|e| match e {
                NetEvent::LogMessage { transition_name, level, message, .. } => {
                    Some((transition_name.as_ref(), level.as_str(), message.as_str()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(warnings.len(), 1, "{backend:?}: one per place, not per token: {warnings:?}");
        let (transition, level, message) = warnings[0];
        assert_eq!(transition, "", "{backend:?}: no transition fires at the seed");
        assert_eq!(level, "WARN", "{backend:?}");
        assert!(message.contains("unknown place 'ghost'"), "{backend:?}: {message}");
    }
}

/// AC#6 / AC#9 through an executor: a restored queue is consumed in the order
/// it was captured, and tokens the net never touches keep their `created_at`.
/// On the precompiled backend the restored marking is copied into ring
/// buffers and materialised back out, so this is where FIFO could be lost.
#[test]
fn a_restored_queue_is_consumed_in_fifo_order_on_every_backend() {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let net = {
        let seen = Arc::clone(&seen);
        let src = Place::<String>::new("src");
        let sink = Place::<String>::new("sink");
        PetriNet::builder("fifo")
            .transition(
                Transition::builder("move")
                    .input(one(&src))
                    .output(out_place(&sink))
                    .action(sync_action(
                        move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
                            let v = ctx.input::<String>("src")?;
                            seen.lock().unwrap().push((*v).clone());
                            ctx.output("sink", (*v).clone())?;
                            Ok(())
                        },
                    ))
                    .build(),
            )
            .build()
    };

    for backend in BACKENDS {
        seen.lock().unwrap().clear();
        let mut original = Marking::new();
        for (value, stamp) in [("A", 10u64), ("B", 20), ("C", 30)] {
            original.add(&Place::<String>::new("src"), Token::at(value.to_string(), stamp));
        }
        for (value, stamp) in [("k1", 7u64), ("k2", 8)] {
            original.add(&Place::<String>::new("kept"), Token::at(value.to_string(), stamp));
        }
        let restored = Marking::from_snapshot(&original.snapshot());

        let end = run_sync_on(backend, &net, restored, None);

        assert_eq!(*seen.lock().unwrap(), vec!["A", "B", "C"], "{backend:?}: firing order");
        assert_eq!(strings_at(&end, "sink"), vec!["A", "B", "C"], "{backend:?}");
        assert_eq!(strings_at(&end, "kept"), vec!["k1", "k2"], "{backend:?}");
        assert_eq!(
            end.queue("kept").expect("kept").iter().map(|t| t.created_at).collect::<Vec<_>>(),
            vec![7, 8],
            "{backend:?}: untouched tokens are never re-stamped"
        );
    }
}

/// AC#8: no codec is imposed. A value nothing could serialize round-trips.
#[test]
fn a_value_no_codec_could_encode_round_trips() {
    /// Deliberately neither `Serialize` nor `Clone`-of-anything-meaningful:
    /// a boxed closure is the case an imposed codec could not handle.
    struct NativeHandle(Box<dyn Fn(u32) -> u32 + Send + Sync>);

    let p = Place::<NativeHandle>::new("handles");
    let mut marking = Marking::new();
    marking.add(&p, Token::at(NativeHandle(Box::new(|x| x * 3)), 7));

    let restored = Marking::from_snapshot(&marking.snapshot());
    let queue = restored.queue("handles").expect("restored");
    let handle = queue[0]
        .value
        .downcast_ref::<NativeHandle>()
        .expect("value survives untouched");

    assert_eq!((handle.0)(14), 42, "the closure is still callable");
    assert_eq!(queue[0].created_at, 7);
}

/// AC#12, first half: place order is deterministic. Not semantic — a restore
/// must not depend on it — but a host that persists a snapshot will diff or
/// hash it.
///
/// Discriminating by construction: the places are *inserted* in an order
/// that is not the sorted one, so an implementation that merely preserved
/// insertion order would fail. Note that `MarkingSnapshot` being a
/// `BTreeMap` makes this unfalsifiable *for this type* — the value of the
/// test is that it fails loudly if the type is ever changed back to a
/// `HashMap`, which is where this started.
#[test]
fn place_order_is_deterministic() {
    let mut marking = Marking::new();
    for name in ["zebra", "alpha", "mike", "bravo"] {
        marking.add(&Place::<String>::new(name), Token::at(name.to_string(), 1));
    }

    let snapshot = marking.snapshot();
    let order: Vec<&str> = snapshot.keys().map(|k| k.as_ref()).collect();
    assert_eq!(
        order,
        vec!["alpha", "bravo", "mike", "zebra"],
        "sorted by place name, so a serialized snapshot is stable across runs"
    );

    // And stable across repeated captures of the same marking.
    for _ in 0..8 {
        let again = marking.snapshot();
        let again: Vec<&str> = again.keys().map(|k| k.as_ref()).collect();
        assert_eq!(again, order);
    }
}

// ============================================================
//  NU-011 — resume-safe minting
// ============================================================

/// Records every ν-name an action mints.
fn minting_net(seen: Arc<Mutex<Vec<String>>>) -> PetriNet {
    minting_net_named("fork", seen)
}

fn minting_net_named(transition: &str, seen: Arc<Mutex<Vec<String>>>) -> PetriNet {
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    PetriNet::builder("mint")
        .transition(
            Transition::builder(transition)
                .input(one(&src))
                .output(out_place(&sink))
                .action(sync_action(
                    move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
                        let name = ctx.fresh_name();
                        seen.lock().unwrap().push(name.as_str().to_string());
                        let v = ctx.input::<String>("src")?;
                        ctx.output("sink", (*v).clone())?;
                        Ok(())
                    },
                ))
                .build(),
        )
        .build()
}

fn run_minting(backend: Backend, seed: &[&str], scope: Option<&str>) -> Vec<String> {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let net = minting_net(Arc::clone(&seen));
    let mut marking = Marking::new();
    let src = Place::<String>::new("src");
    for v in seed {
        marking.add(&src, Token::at((*v).to_string(), 0));
    }
    run_sync_on(backend, &net, marking, scope);
    let names = seen.lock().unwrap().clone();
    names
}

/// Splits a minted name by the rule NU-011 states: the **last** `':'` splits
/// off the counter, then the **last** `'#'` before it splits off the scope.
/// Unique because a scope may hold neither character — a transition name may
/// hold both.
fn split_minted(name: &str) -> (&str, &str, u64) {
    let (head, n) = name.rsplit_once(':').expect("minted name has a counter");
    let (transition, scope) = head.rsplit_once('#').expect("minted name has a scope");
    (transition, scope, n.parse().expect("counter is decimal"))
}

fn is_default_scope(scope: &str) -> bool {
    scope.len() == 32 && scope.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

/// \[NU-011\] AC#5: the default scope is a process-unique random token — exactly 32 lowercase
/// hex characters — and is **not** the execution id. The id stays the
/// reproducible per-process counter (\[TIME-015\] AC#14), which is precisely
/// why it cannot be the scope: the first executor of *every* process is `0`.
#[test]
fn the_default_scope_is_32_lowercase_hex_and_is_not_the_execution_id() {
    let net = minting_net(Arc::new(Mutex::new(Vec::new())));
    let program = PrecompiledNet::from_compiled(CompiledNet::compile(&net));

    let bitmap =
        BitmapNetExecutor::<NoopEventStore>::new(&net, Marking::new(), ExecutorOptions::default());
    let precompiled =
        PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new()).build();

    for (backend, scope, id) in [
        ("bitmap", bitmap.execution_scope(), bitmap.execution_id()),
        ("precompiled", precompiled.execution_scope(), precompiled.execution_id()),
    ] {
        assert!(
            is_default_scope(scope),
            "{backend}: default scope must be 32 lowercase hex chars (128 bits), got {scope:?}"
        );
        assert_ne!(scope, id, "{backend}: the scope is no longer the execution id");
        assert!(
            !is_default_scope(id),
            "{backend}: the execution id stays the reproducible counter, got {id:?}"
        );
    }
    assert_ne!(bitmap.execution_scope(), precompiled.execution_scope());
    assert_eq!(
        bitmap.execution_scope(),
        bitmap.execution_scope(),
        "drawn once, then stable for the executor's lifetime"
    );
}

/// \[NU-011\] AC#5 — names minted under the default scope, on every entry point: the agreed
/// `<transition>#<scope>:<n>` with the random scope in the middle and `<n>`
/// still a plain per-executor counter from 0 — randomness is allowed in the
/// default scope and nowhere else.
#[test]
fn default_scope_names_keep_the_format_and_a_counter_from_zero() {
    for backend in BACKENDS {
        let names = run_minting(backend, &["a", "b", "c"], None);
        let parts: Vec<_> = names.iter().map(|n| split_minted(n)).collect();
        assert_eq!(parts.len(), 3, "{backend:?}: {names:?}");
        for (i, (transition, scope, n)) in parts.iter().enumerate() {
            assert_eq!(*transition, "fork", "{backend:?}: {names:?}");
            assert!(is_default_scope(scope), "{backend:?}: {names:?}");
            assert_eq!(*scope, parts[0].1, "{backend:?}: one scope per executor");
            assert_eq!(*n, i as u64, "{backend:?}: counter runs from 0: {names:?}");
        }
    }
}

/// AC#1 / AC#4 inside one process: two executions from one snapshot mint
/// disjoint sets by default, without the host pinning anything.
#[test]
fn two_executions_from_one_snapshot_mint_disjoint_names() {
    for backend in BACKENDS {
        let first = run_minting(backend, &["a", "b"], None);
        let second = run_minting(backend, &["a", "b"], None);
        assert_eq!(first.len(), 2);
        assert_eq!(second.len(), 2);
        for name in &second {
            assert!(
                !first.contains(name),
                "{backend:?}: resumed segment re-minted {name}.\n\
                 first: {first:?}\nsecond: {second:?}"
            );
        }
        // AC#5: not merely disjoint — each executor drew its own scope.
        assert_ne!(
            split_minted(&first[0]).1,
            split_minted(&second[0]).1,
            "{backend:?}: two default-scope executors shared a scope"
        );
    }
}

/// AC#3: for a fixed scope and firing order the minted sequence is
/// reproducible — which is what makes this a *scope* rather than a random
/// suffix, and what keeps NU-010 AC3 replay stability inside a segment.
///
/// Exact names, on every entry point: this is the only thing that pins the
/// three places a builder forwards the scope by hand
/// (`PrecompiledExecutorBuilder::build`, and the owned builder's two `run_*`).
#[test]
fn a_pinned_scope_reproduces_the_minted_sequence() {
    for backend in BACKENDS {
        let a = run_minting(backend, &["x", "y", "z"], Some("seg1"));
        let b = run_minting(backend, &["x", "y", "z"], Some("seg1"));
        assert_eq!(a, b, "{backend:?}: same scope + same firing order => same names");
        assert_eq!(
            a,
            vec!["fork#seg1:0", "fork#seg1:1", "fork#seg1:2"],
            "{backend:?}: agreed format is <transition>#<scope>:<n>, n from 0"
        );
    }
}

/// The owned builder forwards the scope separately on its async entry point.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_pinned_scope_reaches_the_owned_async_entry_point() {
    use libpetri::runtime::environment::ExecutorSignal;

    let seen = Arc::new(Mutex::new(Vec::new()));
    let net = minting_net(Arc::clone(&seen));
    let mut marking = Marking::new();
    for v in ["x", "y"] {
        marking.add(&Place::<String>::new("src"), Token::at(v.to_string(), 0));
    }
    let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
    OwnedPrecompiledNet::compile(&net)
        .builder::<NoopEventStore>(marking)
        .execution_scope("seg-async")
        .run_async(rx)
        .await;
    assert_eq!(
        *seen.lock().unwrap(),
        vec!["fork#seg-async:0", "fork#seg-async:1"]
    );
}

/// \[NU-011\] AC#6: the scope is validated, not escaped — identically in all four languages:
/// length 0 is rejected (**not** blank: whitespace is a legal scope), and so
/// is any `':'` or `'#'`. Checked on every entry point, because each builder
/// only carries the value and the panic fires where the executor is built.
#[test]
fn an_invalid_scope_is_rejected_on_every_entry_point() {
    let quiet = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut failures = Vec::new();
    for backend in BACKENDS {
        for (scope, expected) in [
            ("", "must not be empty"),
            ("bad:scope", "must not contain ':'"),
            (":", "must not contain ':'"),
            ("bad#scope", "must not contain '#'"),
        ] {
            let outcome =
                std::panic::catch_unwind(|| run_minting(backend, &["x"], Some(scope)));
            match outcome {
                Ok(names) => failures.push(format!("{backend:?} accepted {scope:?}: {names:?}")),
                Err(payload) => {
                    let message = payload
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_default();
                    if !message.contains(expected) {
                        failures.push(format!(
                            "{backend:?} rejected {scope:?} with {message:?}, expected {expected:?}"
                        ));
                    }
                }
            }
        }
    }
    std::panic::set_hook(quiet);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// \[NU-011\] AC#6, the accept half of the same rule: whitespace-only and non-ASCII scopes are
/// legal everywhere (the rule is *empty*, not *blank*).
#[test]
fn a_blank_or_non_ascii_scope_is_accepted() {
    for backend in BACKENDS {
        assert_eq!(run_minting(backend, &["x"], Some(" ")), vec!["fork# :0"]);
        assert_eq!(run_minting(backend, &["x"], Some("läuf-7")), vec!["fork#läuf-7:0"]);
    }
}

/// \[NU-011\] AC#6, the parse rule. Why `'#'` is banned from a scope: with it gone a minted name parses
/// uniquely even when the *transition* name holds both separators — last
/// `':'` splits the counter, then the last `'#'` before it splits the scope.
#[test]
fn a_minted_name_parses_uniquely_even_under_a_hostile_transition_name() {
    for backend in BACKENDS {
        let seen = Arc::new(Mutex::new(Vec::new()));
        let net = minting_net_named("a#b:c", Arc::clone(&seen));
        let mut marking = Marking::new();
        marking.add(&Place::<String>::new("src"), Token::at("x".to_string(), 0));
        run_sync_on(backend, &net, marking, Some("seg"));
        let names = seen.lock().unwrap().clone();
        assert_eq!(names, vec!["a#b:c#seg:0"], "{backend:?}");
        assert_eq!(split_minted(&names[0]), ("a#b:c", "seg", 0), "{backend:?}");
    }
}

// ------------------------------------------------------------
//  NU-011 AC#2 — a restored name must not correlate with a fresh one
// ------------------------------------------------------------

/// A token stamped with a ν-name, plus where it came from.
struct Stamped {
    cid: String,
    origin: &'static str,
}

/// `source → fork → (branchA, branchB)`, re-merged by a \[NU-020\] join that
/// correlates on the minted name alone. `merged` records *whose* halves were
/// joined, which is the only place a mis-correlation is visible: the join
/// itself raises nothing.
fn fork_join_net() -> PetriNet {
    let source = Place::<String>::new("source");
    let a = Place::<Stamped>::new("branchA");
    let b = Place::<Stamped>::new("branchB");
    let merged = Place::<String>::new("merged");

    let fork = Transition::builder("fork")
        .input(one(&source))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx: &mut TransitionContext| -> Result<(), ActionError> {
            let id = ctx.fresh_name().as_str().to_string();
            ctx.output("branchA", Stamped { cid: id.clone(), origin: "fresh" })?;
            ctx.output("branchB", Stamped { cid: id, origin: "fresh" })?;
            Ok(())
        }))
        .build();

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &Stamped| NameId::new(m.cid.clone()))
                .key(&b, |m: &Stamped| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(sync_action(|ctx: &mut TransitionContext| -> Result<(), ActionError> {
            let ma = ctx.input::<Stamped>("branchA")?;
            let mb = ctx.input::<Stamped>("branchB")?;
            ctx.output("merged", format!("{}+{}", ma.origin, mb.origin))?;
            Ok(())
        }))
        .build();

    PetriNet::builder("fork-join").transitions([fork, join]).build()
}

/// Resumes the fork/join net from a snapshot holding one half of a group the
/// *previous* segment minted as `restored_name`, then forks one fresh group.
/// Returns what the join merged and how many halves were left at `branchA`.
fn resume_into_join(
    backend: Backend,
    restored_name: &str,
    scope: Option<&str>,
) -> (Vec<String>, usize) {
    let mut persisted = Marking::new();
    persisted.add(
        &Place::<Stamped>::new("branchA"),
        Token::at(Stamped { cid: restored_name.to_string(), origin: "restored" }, 1),
    );
    persisted.add(&Place::<String>::new("source"), Token::at("go".to_string(), 2));
    let restored = Marking::from_snapshot(&persisted.snapshot());

    let end = run_sync_on(backend, &fork_join_net(), restored, scope);
    (strings_at(&end, "merged"), end.count("branchA"))
}

/// AC#2 inside one process, by default: the restored half waits for its own
/// sibling and the fresh group joins itself.
#[test]
fn a_restored_name_does_not_correlate_with_a_freshly_minted_one() {
    for backend in BACKENDS {
        let earlier = run_minting(backend, &["a"], None);
        let (merged, left_at_a) = resume_into_join(backend, &earlier[0], None);
        assert_eq!(merged, vec!["fresh+fresh"], "{backend:?}");
        assert_eq!(left_at_a, 1, "{backend:?}: the restored half is still waiting");
    }
}

/// The hazard itself, so the test above is known to be able to fail: two
/// executions in one restore lineage that **share** a scope re-mint the
/// restored name, and the join silently merges a restored half with a fresh
/// one. This is what "MUST NOT share a scope" means in practice.
#[test]
fn sharing_a_scope_across_a_restore_lineage_is_the_collision_nu011_forbids() {
    for backend in BACKENDS {
        let earlier = run_minting(backend, &["a"], Some("shared"));
        assert_eq!(earlier, vec!["fork#shared:0"]);
        let (merged, _) = resume_into_join(backend, &earlier[0], Some("shared"));
        assert_eq!(
            merged,
            vec!["restored+fresh"],
            "{backend:?}: a shared scope is expected to mis-correlate — if this stops \
             happening the AC#2 tests have lost their detector"
        );
    }
}

// ------------------------------------------------------------
//  NU-011 across processes — where a persisted snapshot actually goes
// ------------------------------------------------------------

/// Set only on the re-executed test binary; see [`run_child`].
const CHILD_ENV: &str = "LIBPETRI_NU011_CHILD";
const CHILD_MARK: &str = "NU011-CHILD ";

fn backend_named(name: &str) -> Backend {
    match name {
        "bitmap" => Backend::Bitmap,
        "precompiled" => Backend::Precompiled,
        "owned" => Backend::Owned,
        other => panic!("unknown backend {other}"),
    }
}

/// Body of the child process. A no-op in an ordinary test run.
///
/// Re-executed by [`run_child`] with `--exact`, so whatever it builds is the
/// **first executor of a brand-new process** — the situation a host is in
/// after a restart, and the one a per-process counter cannot tell apart from
/// the process that wrote the snapshot.
#[test]
fn nu011_child_process_entry() {
    let Ok(spec) = std::env::var(CHILD_ENV) else {
        return;
    };
    let fields: Vec<&str> = spec.split('|').collect();
    let backend = backend_named(fields[0]);
    match fields[1] {
        "mint" => {
            for name in run_minting(backend, &["a"], None) {
                println!("{CHILD_MARK}{name}");
            }
        }
        "resume" => {
            let (merged, left_at_a) = resume_into_join(backend, fields[2], None);
            println!("{CHILD_MARK}{}|{left_at_a}", merged.join(","));
        }
        other => panic!("unknown child mode {other}"),
    }
}

/// Runs [`nu011_child_process_entry`] alone in a fresh process and returns
/// the lines it reported.
fn run_child(spec: &str) -> Vec<String> {
    let exe = std::env::current_exe().expect("test binary path");
    let out = std::process::Command::new(exe)
        .args(["--exact", "nu011_child_process_entry", "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, spec)
        .output()
        .expect("spawn child test process");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(
        out.status.success(),
        "child {spec} failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let lines: Vec<String> = stdout
        .lines()
        // libtest prints `test <name> ... ` without a newline first, so the
        // mark is not necessarily at the start of its line.
        .filter_map(|l| l.find(CHILD_MARK).map(|at| l[at + CHILD_MARK.len()..].to_string()))
        .collect();
    assert!(!lines.is_empty(), "child {spec} reported nothing:\n{stdout}");
    lines
}

/// AC#1 across a process boundary: the first executor of two separate
/// processes must not mint the same name. Under a per-process counter both
/// mint `fork#0:0`, which is the whole defect.
#[test]
fn the_first_executor_of_two_processes_mints_different_names() {
    for backend in ["bitmap", "precompiled", "owned"] {
        let a = run_child(&format!("{backend}|mint"));
        let b = run_child(&format!("{backend}|mint"));
        assert_ne!(
            a, b,
            "{backend}: two processes minted the same default-scope name — a snapshot \
             persisted by one and restored by the other collides"
        );
    }
}

/// AC#2 across a process boundary, end to end: process A mints a name and
/// persists a half-joined group; process B restores it as *its* first
/// executor and forks a fresh group. The join must not pair the restored half
/// with the fresh one.
#[test]
fn a_snapshot_restored_in_a_new_process_does_not_correlate_with_fresh_names() {
    for backend in ["bitmap", "precompiled", "owned"] {
        let minted_by_a = run_child(&format!("{backend}|mint")).remove(0);
        let report = run_child(&format!("{backend}|resume|{minted_by_a}")).remove(0);
        assert_eq!(
            report, "fresh+fresh|1",
            "{backend}: process B re-minted {minted_by_a} and the join silently merged a \
             restored token with an unrelated fresh one"
        );
    }
}

// ============================================================
//  ENV-014 AC5/AC6 — a snapshot taken mid-flight says so
// ============================================================

/// AC#5 and AC#6 together, on the case AC#6 names exactly: the only marked
/// place feeds a transition whose action is in flight.
///
/// The consumed tokens are in **neither** place at that instant — taken from
/// `src` (\[EXEC-031\]) and not yet produced to `sink` — so the marking is
/// missing them. That marking is a perfectly good *observation* and a
/// catastrophic *restore point*: resume from it and the work is gone with no
/// error anywhere. The caller must be able to tell, and `action_in_flight`
/// is how.
///
/// On every entry point: the flag is computed by the shared loop, but the
/// marking beside it is materialised from ring buffers on the precompiled
/// backend, and "in neither place" has to hold there too.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_snapshot_taken_mid_flight_reports_that_it_is_not_a_restore_point() {
    for backend in BACKENDS {
        snapshot_mid_flight_on(backend).await;
    }
}

#[cfg(feature = "tokio")]
async fn snapshot_mid_flight_on(backend: Backend) {
    use libpetri::core::action::async_action;
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::environment::ExecutorSignal;
    use libpetri::runtime::executor_handle::ExecutorHandle;

    // The action parks until released, so it is provably still in flight
    // when the snapshot is served — no sleeping and hoping.
    let (started_tx, mut started_rx) = tokio::sync::mpsc::unbounded_channel::<()>();
    let release = Arc::new(tokio::sync::Notify::new());
    let release_in_action = Arc::clone(&release);

    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    let net = PetriNet::builder("inflight")
        .transition(
            Transition::builder("slow")
                .input(one(&src))
                .output(out_place(&sink))
                .action(async_action(move |mut ctx: TransitionContext| {
                    let started = started_tx.clone();
                    let release = Arc::clone(&release_in_action);
                    async move {
                        let v = ctx.input::<String>("src")?;
                        let _ = started.send(());
                        release.notified().await;
                        ctx.output("sink", (*v).clone())?;
                        Ok(ctx)
                    }
                }))
                .build(),
        )
        .build();

    let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
    let mut handle = ExecutorHandle::new(tx);

    let env: std::collections::HashSet<Arc<str>> = [Arc::from("src")].into_iter().collect();
    let run = match backend {
        Backend::Bitmap => tokio::spawn(async move {
            let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                &net,
                Marking::new(),
                ExecutorOptions::default().environment_places(env),
            );
            executor.run_async(rx).await.into_owned()
        }),
        Backend::Precompiled => tokio::spawn(async move {
            let program = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
            let mut executor =
                PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new())
                    .environment_places(env)
                    .build();
            executor.run_async(rx).await.into_owned()
        }),
        Backend::Owned => tokio::spawn(async move {
            OwnedPrecompiledNet::compile(&net)
                .builder::<NoopEventStore>(Marking::new())
                .environment_places(env)
                .run_async(rx)
                .await
        }),
    };

    handle.inject(
        Arc::from("src"),
        ErasedToken::from_typed(&Token::at("payload".to_string(), 99)),
    );
    started_rx.recv().await.expect("action must start");

    let snapshot = handle
        .snapshot()
        .expect("snapshot on a live handle")
        .await
        .expect("snapshot delivered");

    assert!(
        snapshot.action_in_flight,
        "{backend:?} AC#5: the caller must be able to tell an action was in flight"
    );
    assert!(
        !snapshot.is_restore_point(),
        "{backend:?} AC#6: and therefore that this is not a valid restore point"
    );
    assert!(
        snapshot.marking.get("src").is_none_or(Vec::is_empty),
        "AC#6: the consumed token is gone from src — {:?}",
        snapshot.marking
    );
    assert!(
        snapshot.marking.get("sink").is_none_or(Vec::is_empty),
        "AC#6: and has not yet arrived at sink, so it is in neither place — {:?}",
        snapshot.marking
    );

    // Let the run finish, and confirm the token was never actually lost —
    // the snapshot was misleading, the execution was not.
    release.notify_waiters();
    handle.close();
    std::mem::forget(handle);
    let final_marking = tokio::time::timeout(std::time::Duration::from_secs(5), run)
        .await
        .expect("run must terminate")
        .expect("run task");
    assert_eq!(final_marking.count("sink"), 1, "{backend:?}");
}

/// \[ENV-014\] AC#7: an accepted external event is never missing from a
/// snapshot taken after it. Other implementations queue accepted events and must fold "queue not
/// empty" into the flag; here an inject and a snapshot request share one FIFO
/// channel and an inject is applied on receipt, so every event accepted
/// before the request is already **in** the marking — with no yield between
/// the sends for the executor to have caught up in.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn events_accepted_before_a_snapshot_are_already_in_its_marking() {
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::environment::ExecutorSignal;
    use libpetri::runtime::executor_handle::ExecutorHandle;

    for backend in BACKENDS {
        let inbox = Place::<u32>::new("inbox");
        let net = PetriNet::builder("idle").place(inbox.as_ref()).build();
        let env: std::collections::HashSet<Arc<str>> = [Arc::from("inbox")].into_iter().collect();

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let mut handle = ExecutorHandle::new(tx);
        let run = match backend {
            Backend::Bitmap => tokio::spawn(async move {
                let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                    &net,
                    Marking::new(),
                    ExecutorOptions::default().environment_places(env),
                );
                executor.run_async(rx).await.into_owned()
            }),
            Backend::Precompiled => tokio::spawn(async move {
                let program = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
                let mut executor =
                    PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new())
                        .environment_places(env)
                        .build();
                executor.run_async(rx).await.into_owned()
            }),
            Backend::Owned => tokio::spawn(async move {
                OwnedPrecompiledNet::compile(&net)
                    .builder::<NoopEventStore>(Marking::new())
                    .environment_places(env)
                    .run_async(rx)
                    .await
            }),
        };

        for i in 0..50u32 {
            handle.inject(Arc::from("inbox"), ErasedToken::from_typed(&Token::at(i, 0)));
        }
        let snapshot = handle.snapshot().expect("live handle").await.expect("delivered");

        let seen: Vec<u32> = snapshot.marking["inbox"]
            .iter()
            .map(|t| *t.value.downcast_ref::<u32>().expect("u32"))
            .collect();
        assert_eq!(seen, (0..50).collect::<Vec<_>>(), "{backend:?}: all accepted, in order");
        assert!(snapshot.is_restore_point(), "{backend:?}: nothing is in flight");

        handle.close();
        std::mem::forget(handle);
        tokio::time::timeout(std::time::Duration::from_secs(5), run)
            .await
            .expect("run must terminate")
            .expect("run task");
    }
}

// ------------------------------------------------------------
//  ENV-014 AC#8 — a snapshot requested from inside an action
// ------------------------------------------------------------

/// Spawns `net` on `backend`'s async entry point and returns the run.
#[cfg(feature = "tokio")]
fn spawn_async_on(
    backend: Backend,
    net: PetriNet,
    env: std::collections::HashSet<Arc<str>>,
    rx: tokio::sync::mpsc::UnboundedReceiver<libpetri::runtime::environment::ExecutorSignal>,
) -> tokio::task::JoinHandle<Marking> {
    match backend {
        Backend::Bitmap => tokio::spawn(async move {
            let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
                &net,
                Marking::new(),
                ExecutorOptions::default().environment_places(env),
            );
            executor.run_async(rx).await.into_owned()
        }),
        Backend::Precompiled => tokio::spawn(async move {
            let program = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
            let mut executor =
                PrecompiledNetExecutor::<NoopEventStore>::builder(&program, Marking::new())
                    .environment_places(env)
                    .build();
            executor.run_async(rx).await.into_owned()
        }),
        Backend::Owned => tokio::spawn(async move {
            OwnedPrecompiledNet::compile(&net)
                .builder::<NoopEventStore>(Marking::new())
                .environment_places(env)
                .run_async(rx)
                .await
        }),
    }
}

/// \[ENV-014\] AC#8, the async half: an action that requests a snapshot as
/// its **first statement** and awaits the reply gets one — flagged — instead
/// of parking the orchestrator against itself.
///
/// The request is a non-blocking send and an async action runs as its own
/// task, so the orchestrator stays free to serve it. What the reply must say
/// is that the requester's own firing is in flight: its input is consumed
/// and its output not yet deposited, so the token is in neither place.
///
/// Bounded by the reply arriving, not by patience — the failure mode is a
/// self-deadlock.
#[cfg(feature = "tokio")]
#[tokio::test]
async fn a_snapshot_awaited_from_inside_an_action_returns_and_is_flagged() {
    use libpetri::core::action::async_action;
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::environment::ExecutorSignal;
    use libpetri::runtime::executor_handle::ExecutorHandle;
    use libpetri::runtime::marking::SnapshotResult;

    for backend in BACKENDS {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let from_action = tx.clone();
        let (seen_tx, mut seen_rx) = tokio::sync::mpsc::unbounded_channel::<SnapshotResult>();

        let src = Place::<String>::new("src");
        let sink = Place::<String>::new("sink");
        let net = PetriNet::builder("self-snapshot")
            .transition(
                Transition::builder("observer")
                    .input(one(&src))
                    .output(out_place(&sink))
                    .action(async_action(move |mut ctx: TransitionContext| {
                        let signal = from_action.clone();
                        let seen = seen_tx.clone();
                        async move {
                            // First statement: nothing has suspended yet.
                            let (reply_tx, reply_rx) = tokio::sync::oneshot::channel();
                            signal
                                .send(ExecutorSignal::Snapshot(reply_tx))
                                .map_err(|_| ActionError::new("executor gone"))?;
                            let snapshot = reply_rx
                                .await
                                .map_err(|_| ActionError::new("snapshot dropped"))?;
                            let _ = seen.send(snapshot);
                            let v = ctx.input::<String>("src")?;
                            ctx.output("sink", (*v).clone())?;
                            Ok(ctx)
                        }
                    }))
                    .build(),
            )
            .build();

        let env: std::collections::HashSet<Arc<str>> = [Arc::from("src")].into_iter().collect();
        let mut handle = ExecutorHandle::new(tx);
        let run = spawn_async_on(backend, net, env, rx);

        handle.inject(
            Arc::from("src"),
            ErasedToken::from_typed(&Token::at("payload".to_string(), 0)),
        );

        let snapshot = tokio::time::timeout(std::time::Duration::from_secs(5), seen_rx.recv())
            .await
            .unwrap_or_else(|_| {
                panic!("{backend:?} AC#8: the action never got its snapshot — the orchestrator parked")
            })
            .expect("the action reports what it saw");

        assert!(
            snapshot.action_in_flight && !snapshot.is_restore_point(),
            "{backend:?} AC#8: the requesting firing is itself in flight"
        );
        assert!(
            snapshot.marking.get("src").is_none_or(Vec::is_empty)
                && snapshot.marking.get("sink").is_none_or(Vec::is_empty),
            "{backend:?}: consumed and not yet deposited — {:?}",
            snapshot.marking
        );

        handle.close();
        std::mem::forget(handle);
        let final_marking = tokio::time::timeout(std::time::Duration::from_secs(5), run)
            .await
            .expect("run must terminate")
            .expect("run task");
        assert_eq!(final_marking.count("sink"), 1, "{backend:?}: and the run carried on");
    }
}

/// \[ENV-014\] AC#8, the inline half: a **sync** action runs on the
/// orchestrator's own thread of control, so a snapshot it requests cannot be
/// served until it returns.
///
/// Requesting is safe — the send does not block. *Blocking on the reply* from
/// there is the self-deadlock `ExecutorHandle::snapshot` documents, and this
/// is that deadlock in bounded form: for as long as the action keeps running
/// the reply does not arrive, however long it looks. There is nothing the
/// executor could detect — the reply is a plain oneshot the action holds, not
/// a call back into the executor — so the rule is documented, not enforced.
///
/// Once the action returns, the request is served on the next cycle and is
/// *truthful for that instant*: the firing has finished, its output is in
/// the marking, and nothing is in flight.
#[cfg(feature = "tokio")]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_snapshot_requested_by_an_inline_sync_action_is_served_only_after_it_returns() {
    use libpetri::core::token::ErasedToken;
    use libpetri::runtime::environment::ExecutorSignal;
    use libpetri::runtime::executor_handle::ExecutorHandle;
    use libpetri::runtime::marking::SnapshotResult;
    use tokio::sync::oneshot;

    for backend in BACKENDS {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        let from_action = tx.clone();
        let (reply_out_tx, reply_out_rx) =
            std::sync::mpsc::channel::<(bool, oneshot::Receiver<SnapshotResult>)>();
        let reply_out_tx = Mutex::new(reply_out_tx);

        let src = Place::<String>::new("src");
        let sink = Place::<String>::new("sink");
        let net = PetriNet::builder("inline-snapshot")
            .transition(
                Transition::builder("observer")
                    .input(one(&src))
                    .output(out_place(&sink))
                    .action(sync_action(
                        move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
                            let (reply_tx, mut reply_rx) = oneshot::channel();
                            from_action
                                .send(ExecutorSignal::Snapshot(reply_tx))
                                .map_err(|_| ActionError::new("executor gone"))?;
                            // Keep the orchestrator's thread for 150ms and
                            // watch for a reply that cannot come.
                            let mut served_while_running = false;
                            for _ in 0..30 {
                                std::thread::sleep(std::time::Duration::from_millis(5));
                                if reply_rx.try_recv().is_ok() {
                                    served_while_running = true;
                                    break;
                                }
                            }
                            let v = ctx.input::<String>("src")?;
                            ctx.output("sink", (*v).clone())?;
                            let _ = reply_out_tx
                                .lock()
                                .unwrap()
                                .send((served_while_running, reply_rx));
                            Ok(())
                        },
                    ))
                    .build(),
            )
            .build();

        let env: std::collections::HashSet<Arc<str>> = [Arc::from("src")].into_iter().collect();
        let mut handle = ExecutorHandle::new(tx);
        let run = spawn_async_on(backend, net, env, rx);
        handle.inject(
            Arc::from("src"),
            ErasedToken::from_typed(&Token::at("payload".to_string(), 0)),
        );

        let (served_while_running, reply_rx) = tokio::task::spawn_blocking(move || {
            reply_out_rx.recv_timeout(std::time::Duration::from_secs(5))
        })
        .await
        .expect("join")
        .unwrap_or_else(|_| panic!("{backend:?}: the sync action never ran"));

        assert!(
            !served_while_running,
            "{backend:?}: a reply arrived while the inline action still held the orchestrator"
        );

        let snapshot = tokio::time::timeout(std::time::Duration::from_secs(5), reply_rx)
            .await
            .unwrap_or_else(|_| panic!("{backend:?}: the request was never served after the action"))
            .expect("snapshot delivered");
        assert!(
            snapshot.is_restore_point(),
            "{backend:?}: served after the firing finished, so nothing is in flight"
        );
        assert!(snapshot.marking.get("src").is_none_or(Vec::is_empty), "{backend:?}");
        assert_eq!(
            snapshot.marking.get("sink").map(Vec::len),
            Some(1),
            "{backend:?}: and the firing's output is in the marking — no token is missing \
             from a snapshot that calls itself a restore point"
        );

        handle.close();
        std::mem::forget(handle);
        tokio::time::timeout(std::time::Duration::from_secs(5), run)
            .await
            .expect("run must terminate")
            .expect("run task");
    }
}

/// AC#10: a restored marking is **visible to the executor** — the net's own
/// transitions consume those tokens, rather than merely having them present
/// in the marking.
///
/// The assertion that matters is that the source place is **empty
/// afterwards**: "the tokens are in the marking" and "the net can act on
/// them" are different claims, and only the second is what restore is for.
#[test]
fn a_restored_marking_is_consumed_by_the_nets_own_transitions() {
    let src = Place::<String>::new("src");
    let sink = Place::<String>::new("sink");
    let net = PetriNet::builder("resume")
        .transition(
            Transition::builder("move")
                .input(one(&src))
                .output(out_place(&sink))
                .action(fork())
                .build(),
        )
        .build();

    // Build the marking through the snapshot form, not directly — the point
    // is that a name resolved out of a snapshot reaches the same place the
    // net's arcs refer to.
    for backend in BACKENDS {
        let mut original = Marking::new();
        original.add(&src, Token::at("carried".to_string(), 1234));
        let restored = Marking::from_snapshot(&original.snapshot());

        let final_marking = run_sync_on(backend, &net, restored, None);

        assert_eq!(
            final_marking.count("src"),
            0,
            "{backend:?} AC#10: the restored token must be CONSUMED, not merely present"
        );
        assert_eq!(final_marking.count("sink"), 1, "{backend:?}: and produced onward");
    }
}

/// AC#11: supplying a restored marking *and* an explicit initial marking must
/// be an error rather than a merge or a silent preference.
///
/// **Rust satisfies this structurally: there is exactly one marking input.**
/// `BitmapNetExecutor::new(net, marking, options)` and
/// `PrecompiledNetExecutor::builder(program, marking)` each take one, and
/// `ExecutorOptions` carries no marking of its own — a restore is simply
/// `Marking::from_snapshot(&s)` passed as *that* argument. So there is no
/// combination to reject, and none can be constructed.
///
/// This test pins that property rather than an error path, because adding a
/// second marking input purely so it could be rejected would build the hazard
/// in order to guard it. If a restore-specific entry point is ever added to
/// `ExecutorOptions`, this test is the reminder that AC#11 stops being free.
#[test]
fn there_is_exactly_one_marking_input_so_both_cannot_be_supplied() {
    let p = Place::<String>::new("p");
    let net = PetriNet::builder("one-input").place(p.as_ref()).build();

    for backend in BACKENDS {
        let mut snapshot_source = Marking::new();
        snapshot_source.add(&p, Token::at("restored".to_string(), 42));
        let restored = Marking::from_snapshot(&snapshot_source.snapshot());

        // The restored marking IS the initial marking — one parameter, one
        // meaning. Neither `ExecutorOptions` nor a builder contributes tokens.
        let final_marking = run_sync_on(backend, &net, restored, None);

        assert_eq!(final_marking.count("p"), 1, "{backend:?}");
        assert_eq!(
            final_marking.queue("p").expect("place")[0].created_at,
            42,
            "{backend:?}: the restored stamp survives, confirming this is the restored \
             marking and not some merged or defaulted one"
        );
    }
}

/// AC#12, second half: a restore is unaffected by the order the places are
/// presented in.
///
/// In Rust this is guaranteed by the type — `MarkingSnapshot` is a
/// `BTreeMap`, so a caller *cannot* present the places in another order
/// through the typed API, and the property holds by construction rather than
/// by care. The test states the property so the guarantee is visible; the
/// place where it can actually be violated is the binding, where
/// `marking_from_python` accepts an arbitrary insertion-ordered dict — see
/// `python/tests/test_marking_snapshot.py`.
#[test]
fn restore_is_unaffected_by_the_order_places_are_presented_in() {
    let mut original = Marking::new();
    for (name, value) in [("zeta", "z"), ("alpha", "a"), ("mid", "m")] {
        original.add(&Place::<String>::new(name), Token::at(value.to_string(), 7));
    }
    let snapshot = original.snapshot();

    // Rebuild the same logical snapshot by inserting in reverse order. The
    // BTreeMap re-sorts, which is exactly the guarantee.
    let mut reversed: MarkingSnapshot = MarkingSnapshot::new();
    for (place, entries) in snapshot.iter().rev() {
        reversed.insert(Arc::clone(place), entries.clone());
    }
    assert_eq!(
        reversed.keys().collect::<Vec<_>>(),
        snapshot.keys().collect::<Vec<_>>(),
        "insertion order cannot survive into the snapshot form"
    );

    let a = Marking::from_snapshot(&snapshot);
    let b = Marking::from_snapshot(&reversed);
    for place in ["zeta", "alpha", "mid"] {
        assert_eq!(a.count(place), b.count(place));
        assert_eq!(
            a.queue(place).expect("place")[0].created_at,
            b.queue(place).expect("place")[0].created_at,
        );
    }
}

// ============================================================
//  Umbrella surface
// ============================================================

/// `ExecutorHandle::snapshot` is re-exported at the crate root, so the type it
/// returns — and the clock seam `ExecutorOptions::clock` takes — must be
/// nameable from there too, not only through `libpetri::runtime::…`.
#[test]
fn the_umbrella_root_names_the_snapshot_clock_and_scope_types() {
    use libpetri::{
        ExecutorClock, InvalidExecutionScope, ManualClock, MarkingSnapshot as RootSnapshot,
        SnapshotResult, SystemClock, validate_execution_scope,
    };

    let result = SnapshotResult {
        marking: RootSnapshot::new(),
        action_in_flight: false,
    };
    assert!(result.is_restore_point());
    let _clocks: [Arc<dyn ExecutorClock>; 2] =
        [Arc::new(ManualClock::new()), Arc::new(SystemClock::new())];
    assert_eq!(validate_execution_scope(""), Err(InvalidExecutionScope::Empty));
    assert_eq!(validate_execution_scope("seg"), Ok(()));
}
