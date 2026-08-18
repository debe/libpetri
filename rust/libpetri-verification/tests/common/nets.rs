//! Fixture net builders for the cross-language verdict-parity suite (C4).
//!
//! Each builder implements the normative `netDescription` contract of the
//! same-named entry in `spec/verification-fixtures/fixtures.json` (the shared
//! expectations all four language implementations run against, per the
//! cross-lang-dot-parity.sh pattern: shared expectations, per-language
//! builders). Divergence from a fixture's `expected` verdict is a parity
//! FINDING to report — the fixture is never adjusted to match.

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::{all, at_least, one};
use libpetri_core::output::{and, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::environment::EnvironmentAnalysisMode;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};

/// A built fixture: the net, its initial marking, and the environment
/// configuration the fixture's `netDescription` prescribes (VER-006 for
/// `envSingleFeed`; `Ignore` with no env places everywhere else).
pub struct FixtureNet {
    pub net: PetriNet,
    pub initial: MarkingState,
    pub env_places: Vec<String>,
    pub env_mode: EnvironmentAnalysisMode,
}

impl FixtureNet {
    fn closed(net: PetriNet, initial: MarkingState) -> Self {
        Self {
            net,
            initial,
            env_places: Vec::new(),
            env_mode: EnvironmentAnalysisMode::Ignore,
        }
    }
}

/// Builds the named fixture net. Panics on an unknown name so a new fixture
/// in the shared JSON fails loudly here until its builder lands.
pub fn build(name: &str) -> FixtureNet {
    match name {
        // p0(1) -> p1 -> p2 -> p0: the token circulates forever.
        "circularChain" => {
            let p0 = Place::<i32>::new("p0");
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");
            let t01 = Transition::builder("t01")
                .input(one(&p0))
                .output(out_place(&p1))
                .action(fork())
                .build();
            let t12 = Transition::builder("t12")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();
            let t20 = Transition::builder("t20")
                .input(one(&p2))
                .output(out_place(&p0))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("circularChain")
                    .transitions([t01, t12, t20])
                    .build(),
                MarkingStateBuilder::new().tokens("p0", 1).build(),
            )
        }
        // p0(1) -> p1 -> p2, and nothing consumes p2: a genuine dead marking
        // (p2 is a normal place, NOT a declared sink).
        "deadEndChain" => {
            let p0 = Place::<i32>::new("p0");
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");
            let t01 = Transition::builder("t01")
                .input(one(&p0))
                .output(out_place(&p1))
                .action(fork())
                .build();
            let t12 = Transition::builder("t12")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("deadEndChain")
                    .transitions([t01, t12])
                    .build(),
                MarkingStateBuilder::new().tokens("p0", 1).build(),
            )
        }
        // Binary semaphore: enter_i consumes idle_i + lock, exit_i returns both.
        "mutexLocked" => {
            let idle1 = Place::<i32>::new("idle1");
            let idle2 = Place::<i32>::new("idle2");
            let lock = Place::<i32>::new("lock");
            let crit1 = Place::<i32>::new("crit1");
            let crit2 = Place::<i32>::new("crit2");
            let enter1 = Transition::builder("enter1")
                .input(one(&idle1))
                .input(one(&lock))
                .output(out_place(&crit1))
                .action(fork())
                .build();
            let exit1 = Transition::builder("exit1")
                .input(one(&crit1))
                .output(and(vec![out_place(&idle1), out_place(&lock)]))
                .action(fork())
                .build();
            let enter2 = Transition::builder("enter2")
                .input(one(&idle2))
                .input(one(&lock))
                .output(out_place(&crit2))
                .action(fork())
                .build();
            let exit2 = Transition::builder("exit2")
                .input(one(&crit2))
                .output(and(vec![out_place(&idle2), out_place(&lock)]))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("mutexLocked")
                    .transitions([enter1, exit1, enter2, exit2])
                    .build(),
                MarkingStateBuilder::new()
                    .tokens("idle1", 1)
                    .tokens("idle2", 1)
                    .tokens("lock", 1)
                    .build(),
            )
        }
        // Same shape but no lock place at all: both criticals reachable
        // simultaneously.
        "mutexUnlocked" => {
            let idle1 = Place::<i32>::new("idle1");
            let idle2 = Place::<i32>::new("idle2");
            let crit1 = Place::<i32>::new("crit1");
            let crit2 = Place::<i32>::new("crit2");
            let enter1 = Transition::builder("enter1")
                .input(one(&idle1))
                .output(out_place(&crit1))
                .action(fork())
                .build();
            let exit1 = Transition::builder("exit1")
                .input(one(&crit1))
                .output(out_place(&idle1))
                .action(fork())
                .build();
            let enter2 = Transition::builder("enter2")
                .input(one(&idle2))
                .output(out_place(&crit2))
                .action(fork())
                .build();
            let exit2 = Transition::builder("exit2")
                .input(one(&crit2))
                .output(out_place(&idle2))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("mutexUnlocked")
                    .transitions([enter1, exit1, enter2, exit2])
                    .build(),
                MarkingStateBuilder::new()
                    .tokens("idle1", 1)
                    .tokens("idle2", 1)
                    .build(),
            )
        }
        // p0(3) -> p1 with conservation p0 + p1 = 3: the bound-3 proof needs
        // the P-invariant strengthening (exercises the R'-candidate
        // certificate check).
        "conservedPair" => {
            let p0 = Place::<i32>::new("p0");
            let p1 = Place::<i32>::new("p1");
            let t = Transition::builder("t")
                .input(one(&p0))
                .output(out_place(&p1))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("conservedPair").transition(t).build(),
                MarkingStateBuilder::new().tokens("p0", 3).build(),
            )
        }
        // Environment place e in always-available injection mode (VER-006):
        // injection makes p1 exceed any bound.
        "envSingleFeed" => {
            let e = Place::<i32>::new("e");
            let p1 = Place::<i32>::new("p1");
            let t = Transition::builder("t")
                .input(one(&e))
                .output(out_place(&p1))
                .action(fork())
                .build();
            FixtureNet {
                net: PetriNet::builder("envSingleFeed").transition(t).build(),
                initial: MarkingStateBuilder::new().build(),
                env_places: vec!["e".to_string()],
                env_mode: EnvironmentAnalysisMode::AlwaysAvailable,
            }
        }
        // Nothing ever drains blocker(1), so the inhibitor keeps t frozen and
        // p1 stays empty forever.
        "inhibitorFrozen" => {
            let p0 = Place::<i32>::new("p0");
            let blocker = Place::<i32>::new("blocker");
            let p1 = Place::<i32>::new("p1");
            let t = Transition::builder("t")
                .input(one(&p0))
                .inhibitor(inhibitor(&blocker))
                .output(out_place(&p1))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("inhibitorFrozen").transition(t).build(),
                MarkingStateBuilder::new()
                    .tokens("p0", 1)
                    .tokens("blocker", 1)
                    .build(),
            )
        }
        // The Strengthening.lean H1 witness: t: all(p0) -> p1 with p0(2).
        "h1ConsumeAll" => {
            let p0 = Place::<i32>::new("p0");
            let p1 = Place::<i32>::new("p1");
            let t = Transition::builder("t")
                .input(all(&p0))
                .output(out_place(&p1))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("h1ConsumeAll").transition(t).build(),
                MarkingStateBuilder::new().tokens("p0", 2).build(),
            )
        }
        // t: atLeast(2)(p0) -> p1 with p0(3): the drain empties p0 on the
        // first firing, so t fires at most once and p1 <= 1. Its invariant is
        // H1-dropped; the proof must come from the consume-all arm alone.
        "atLeastDrain" => {
            let p0 = Place::<i32>::new("p0");
            let p1 = Place::<i32>::new("p1");
            let t = Transition::builder("t")
                .input(at_least(2, &p0))
                .output(out_place(&p1))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("atLeastDrain").transition(t).build(),
                MarkingStateBuilder::new().tokens("p0", 3).build(),
            )
        }
        // p0(1) -> done + stuck in one shot. The only quiescent marking holds a
        // token in the declared sink `done` AND one in the non-sink `stuck`;
        // [VER-002] excuses it because a sink is marked.
        "sinkPartialTerminal" => {
            let p0 = Place::<i32>::new("p0");
            let done = Place::<i32>::new("done");
            let stuck = Place::<i32>::new("stuck");
            let t = Transition::builder("t")
                .input(one(&p0))
                .output(and(vec![out_place(&done), out_place(&stuck)]))
                .action(fork())
                .build();
            FixtureNet::closed(
                PetriNet::builder("sinkPartialTerminal").transition(t).build(),
                MarkingStateBuilder::new().tokens("p0", 1).build(),
            )
        }
        // p0(1) drained by a sink transition (no output spec, [CORE-042]); the
        // declared sink `done` never receives anything, so the quiescent marking
        // is empty and [VER-002]'s "no sink place has a token" holds. `done`
        // touches no arc, so it is declared explicitly on the builder.
        "sinkDrainedTerminal" => {
            let p0 = Place::<i32>::new("p0");
            let done = Place::<i32>::new("done");
            let t = Transition::builder("t").input(one(&p0)).build();
            FixtureNet::closed(
                PetriNet::builder("sinkDrainedTerminal")
                    .place((&done).into())
                    .transition(t)
                    .build(),
                MarkingStateBuilder::new().tokens("p0", 1).build(),
            )
        }
        other => panic!(
            "unknown fixture net '{other}' — add its builder to tests/common/nets.rs \
             (the shared fixtures.json gained a net this implementation does not build yet)"
        ),
    }
}
