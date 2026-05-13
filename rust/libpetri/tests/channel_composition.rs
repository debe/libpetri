//! End-to-end integration tests for synchronous-channel composition per
//! **MOD-021**. Mirrors `typescript/tests/core/channel-composition.test.ts`
//! and `java/src/test/java/org/libpetri/core/ChannelCompositionTest.java`.
//!
//! Lives in the umbrella `libpetri` crate because `libpetri-core` does not
//! (and cannot) depend on `libpetri-runtime` — the runtime crate already
//! depends on core.

use std::sync::{Arc, Mutex};

use libpetri::core::action::{ActionError, BoxedAction, sync_action};
use libpetri::core::context::TransitionContext;
use libpetri::core::input::one;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;

// ============================================================
//  retry_policy fixture (mirrors TS retryPolicy / Java retryPolicy)
// ============================================================
//
// A subnet with a single channel "attempt" exposed on a transition that
// emits to its internal "attemptCount" sink. Composing it into a host with
// `bind_channel("attempt", host_t)` fuses the host's transition with the
// retry-policy's instance-side transition into a single merged firing.

fn retry_policy() -> SubnetDef<()> {
    let attempt_count = Place::<String>::new("attemptCount");
    let attempt = Transition::builder("attempt")
        .output(out_place(&attempt_count))
        .build();

    SubnetDef::<()>::builder("RetryPolicy")
        .place(&attempt_count)
        .transition(attempt.clone())
        .channel("attempt", &attempt)
        .build()
}

// ============================================================
//  Tests
// ============================================================

#[test]
fn channel_merge_end_to_end_retry_policy() {
    // Bind an instance-side action that increments a counter and emits a
    // synthetic value to the retry-policy's attemptCount sink. The merged
    // transition runs both the host action and the instance-side action
    // atomically (single transition firing per [EXEC-001]).
    let retry_def = retry_policy();

    let attempt_count: Arc<Mutex<i32>> = Arc::new(Mutex::new(0));
    let attempt_count_inner = Arc::clone(&attempt_count);
    let attempt_action: BoxedAction =
        sync_action(move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
            *attempt_count_inner.lock().unwrap() += 1;
            // Produce a synthetic value to the retry-policy's attemptCount
            // sink so the merged firing is well-formed.
            for op in ctx.output_place_names() {
                if op.ends_with("/attemptCount") {
                    ctx.output(&op, "tick".to_string())?;
                }
            }
            Ok(())
        });

    let mut bindings = std::collections::HashMap::new();
    bindings.insert(Arc::<str>::from("attempt"), attempt_action);
    let retry_inst = retry_def.instantiate("rp", ()).bind_actions(bindings);

    // Host net: a "trigger" place enables the "attemptHttp" transition.
    let trigger = Place::<String>::new("trigger");
    let host_result = Place::<String>::new("hostResult");

    let host_calls: Arc<Mutex<i32>> = Arc::new(Mutex::new(0));
    let host_calls_inner = Arc::clone(&host_calls);
    let host_action: BoxedAction =
        sync_action(move |ctx: &mut TransitionContext| -> Result<(), ActionError> {
            *host_calls_inner.lock().unwrap() += 1;
            for op in ctx.output_place_names() {
                if op.as_ref() == "hostResult" {
                    ctx.output(&op, "ok".to_string())?;
                }
            }
            Ok(())
        });

    let attempt_http = Transition::builder("attemptHttp")
        .input(one(&trigger))
        .output(out_place(&host_result))
        .action(host_action)
        .build();

    let host = PetriNet::builder("HostWithRetry")
        .compose_with(&retry_inst, |b| {
            b.bind_channel("attempt", &attempt_http);
        })
        .build();

    // After compose, the host net contains the merged "attemptHttp"
    // transition (caller-wins identity) and NOT the renamed "rp/attempt".
    let t_names: std::collections::HashSet<&str> =
        host.transitions().iter().map(|t| t.name()).collect();
    assert!(
        !t_names.contains("rp/attempt"),
        "renamed instance-side transition must be replaced by merged"
    );
    assert!(
        t_names.contains("attemptHttp"),
        "merged transition must carry the caller's name"
    );

    // The renamed instance-side internal place flows through unchanged so
    // we can observe the increment via the executor's marking.
    let attempt_count_place: Place<String> = Place::<String>::new("rp/attemptCount");
    assert!(
        host.places().contains(&attempt_count_place.as_ref()),
        "renamed instance-side internal place must flow through unchanged"
    );

    // Seed initial marking and run.
    let mut marking = Marking::new();
    marking.add(&trigger, Token::at("go".to_string(), 0));

    let mut executor =
        BitmapNetExecutor::<NoopEventStore>::new(&host, marking, ExecutorOptions::default());
    let final_marking = executor.run_sync();

    // The merged transition fires once for the single trigger token — both
    // the host action and the instance-side action increment.
    assert_eq!(*host_calls.lock().unwrap(), 1, "host action ran once");
    assert_eq!(
        *attempt_count.lock().unwrap(),
        1,
        "instance-side retry-policy action ran once (atomic merged firing)"
    );

    // Tokens land in both the host's result place and the retry-policy's
    // attemptCount sink.
    assert_eq!(
        final_marking.count("hostResult"),
        1,
        "host result place must hold the host's output"
    );
    assert_eq!(
        final_marking.count("rp/attemptCount"),
        1,
        "instance-side attemptCount sink must hold the merged output"
    );
}

#[test]
fn channel_merge_unbound_channel_flows_through_as_renamed_transition() {
    // Channels declared in iface but not bound flow through as ordinary
    // renamed transitions per MOD-021 (unchanged from pre-task-#21 behaviour).
    let def = retry_policy();
    let inst = def.instantiate("rp1", ());

    // No channel binding recorded — compose succeeds.
    let built = PetriNet::builder("host").compose_with(&inst, |_| {}).build();

    let t_names: std::collections::HashSet<&str> =
        built.transitions().iter().map(|t| t.name()).collect();
    assert!(
        t_names.contains("rp1/attempt"),
        "unbound channel transition must flow through with prefix"
    );
}
