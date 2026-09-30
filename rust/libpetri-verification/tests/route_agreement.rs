//! Route-agreement differential test for the verifier ([VER-003], [VER-017]).
//!
//! Every route that can decide a query is run on the same random small net, the
//! same initial marking and the same property, and each verdict is held against
//! an **independent reference** — an explicit-state explorer written in this file
//! straight from the spec's firing rules ([CORE-022], [CORE-030]–[CORE-036],
//! [IO-001]–[IO-004], [IO-014], [IO-016]), sharing no code with the verifier's
//! flattener, state-class graph or encoders:
//!
//! * `enum`   — the default pipeline, bounded enumeration first ([VER-017]);
//! * `smt+lb` — enumeration off, linear bound on ([VER-015]; Commoner and the
//!   bound are the structural route), VER-018/019 phases on;
//! * `smt-lb` — enumeration off, linear bound off, phases on;
//! * `ic3`    — enumeration off, linear bound and both phases off: IC3/PDR alone.
//!
//! Asserted, per (net, property): no route says `Proven` where the reference or
//! another route finds a violation; every `Violated` trace replays on the
//! reference; a `Violated` the reference refutes (closed state space, no
//! violation) is reported. `Unknown` is neutral.
//!
//! The reference models the untimed abstraction the verifier claims ([VER-004]):
//! atomic firings, every output branch possible, priority-blind. It is faithful
//! to [IO-014]: a `ForwardInput(from, to)` deposits one token into `to` per token
//! the firing consumed from `from`. A second, deliberately *unit* semantics (one
//! token per forward leaf, what the pre-fix flattener did) is used only to
//! classify a disagreement as the known ForwardInput bug (R1 in
//! `research/net-metrics/review/lean-gaps/ANALYSIS.md`).
//!
//! Runtime knobs (all optional):
//! * `ROUTE_AGREEMENT_NETS`    — number of random nets (default [`DEFAULT_NETS`]);
//! * `ROUTE_AGREEMENT_SEED`    — base seed (default 0x5EED);
//! * `ROUTE_AGREEMENT_THREADS` — worker threads (default: available parallelism);
//! * `ROUTE_AGREEMENT_STRICT=0` — tolerate disagreements classified as the
//!   ForwardInput bug (R1, now fixed): report them without failing. For bisecting
//!   against a pre-fix revision only; the default fails on them.
//! * `ROUTE_AGREEMENT_VERBOSE=1` — print every finding in full.

#![cfg(feature = "z3")]

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use libpetri_core::action::fork;
use libpetri_core::arc::{inhibitor, read, reset};
use libpetri_core::input as input;
use libpetri_core::output::{self as output, Out};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::{Place, PlaceRef};
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{Verdict, VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

/// Random nets in the default (CI) run. Sized to finish well under a minute on
/// a laptop-class machine; raise with `ROUTE_AGREEMENT_NETS` for long runs.
const DEFAULT_NETS: usize = 60;

/// Reference exploration caps: a marking with more tokens than this in one place,
/// or more states than this overall, leaves the reference *incomplete* — it then
/// still witnesses violations (every explored state is reachable) but proves nothing.
const REF_MAX_STATES: usize = 20_000;
const REF_MAX_TOKENS: u16 = 24;

/// Class budget of the enumeration route in the `enum` configuration. Smaller than
/// the default so an unbounded net truncates quickly and falls through to SMT.
const ENUM_BUDGET: usize = 5_000;

// ======================================================================
// Deterministic PRNG (splitmix64) — no external crate
// ======================================================================

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn range(&mut self, lo: usize, hi_incl: usize) -> usize {
        lo + self.below(hi_incl - lo + 1)
    }
    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len())]
    }
    /// `k` distinct values from `0..n` (k <= n).
    fn distinct(&mut self, n: usize, k: usize) -> Vec<usize> {
        let mut pool: Vec<usize> = (0..n).collect();
        for i in 0..k {
            let j = i + self.below(n - i);
            pool.swap(i, j);
        }
        pool.truncate(k);
        pool
    }
}

// ======================================================================
// Net model (the test's own description; built into a real PetriNet)
// ======================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Card {
    One,
    Exactly(usize),
    All,
    AtLeast(usize),
}

#[derive(Clone, Debug)]
enum OSpec {
    Place(usize),
    And(Vec<OSpec>),
    Xor(Vec<OSpec>),
    Timeout(Box<OSpec>),
    Forward { from: usize, to: usize },
}

#[derive(Clone, Debug)]
struct TSpec {
    name: String,
    inputs: Vec<(usize, Card)>,
    reads: Vec<usize>,
    inhibitors: Vec<usize>,
    resets: Vec<usize>,
    out: Option<OSpec>,
}

/// Places are indexed in one universe: `p0..p{n-1}` (arc places), then the
/// optional declared-but-arc-less `q0`, then the optional undeclared `s0`,
/// which only the initial marking names ([CORE-072]: inert).
#[derive(Clone, Debug)]
struct NetSpec {
    names: Vec<String>,
    arc_places: usize,
    /// `q0` is declared on the net builder with no arcs.
    declared_extra: Option<usize>,
    /// `s0` appears only in the initial marking.
    undeclared: Option<usize>,
    transitions: Vec<TSpec>,
    initial: Vec<u16>,
}

#[derive(Clone, Debug)]
enum Prop {
    Deadlock { sinks: Vec<String> },
    Bound { place: String, bound: usize },
    Mutex { a: String, b: String },
    Unreach { places: Vec<String> },
    QCount { places: Vec<String>, min: usize, max: Option<usize>, waived: Vec<String> },
}

impl Prop {
    fn to_smt(&self) -> SmtProperty {
        match self {
            Prop::Deadlock { .. } => SmtProperty::DeadlockFree,
            Prop::Bound { place, bound } => SmtProperty::place_bound(place.clone(), *bound),
            Prop::Mutex { a, b } => SmtProperty::mutual_exclusion(vec![a.clone(), b.clone()]),
            Prop::Unreach { places } => SmtProperty::unreachable(places.clone()),
            Prop::QCount { places, min, max, waived } => {
                SmtProperty::quiescent_count(places.clone(), *min, *max, waived.clone())
            }
        }
    }
    fn sinks(&self) -> &[String] {
        match self {
            Prop::Deadlock { sinks } => sinks,
            _ => &[],
        }
    }
    fn describe(&self) -> String {
        match self {
            Prop::Deadlock { sinks } if sinks.is_empty() => "DeadlockFree".into(),
            Prop::Deadlock { sinks } => format!("DeadlockFree(sinks {sinks:?})"),
            Prop::Bound { place, bound } => format!("PlaceBound({place}, {bound})"),
            Prop::Mutex { a, b } => format!("MutualExclusion({a}, {b})"),
            Prop::Unreach { places } => format!("Unreachable({places:?})"),
            Prop::QCount { places, min, max, waived } => {
                format!("QuiescentCount({places:?}, {min}, {max:?}, waived {waived:?})")
            }
        }
    }
}

impl NetSpec {
    fn index(&self) -> HashMap<&str, usize> {
        self.names.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect()
    }

    fn initial_marking(&self) -> MarkingState {
        let mut b = MarkingStateBuilder::new();
        for (i, &n) in self.initial.iter().enumerate() {
            if n > 0 {
                b = b.tokens(self.names[i].clone(), n as usize);
            }
        }
        b.build()
    }

    /// A forward whose `from` input can consume more than one token: the R1 shape.
    fn has_multi_forward(&self) -> bool {
        self.transitions.iter().any(|t| {
            let mut fw = Vec::new();
            if let Some(o) = &t.out {
                forwards(o, &mut fw);
            }
            fw.iter().any(|from| {
                t.inputs
                    .iter()
                    .any(|(p, c)| p == from && !matches!(c, Card::One | Card::Exactly(1)))
            })
        })
    }

    fn build(&self) -> PetriNet {
        let places: Vec<Place<i32>> = self.names.iter().map(|n| Place::<i32>::new(n.as_str())).collect();
        let mut nb = PetriNet::builder("route-agreement");
        for t in &self.transitions {
            let mut tb = Transition::builder(t.name.as_str());
            for &(p, card) in &t.inputs {
                tb = tb.input(match card {
                    Card::One => input::one(&places[p]),
                    Card::Exactly(n) => input::exactly(n, &places[p]),
                    Card::All => input::all(&places[p]),
                    Card::AtLeast(n) => input::at_least(n, &places[p]),
                });
            }
            for &p in &t.reads {
                tb = tb.read(read(&places[p]));
            }
            for &p in &t.inhibitors {
                tb = tb.inhibitor(inhibitor(&places[p]));
            }
            for &p in &t.resets {
                tb = tb.reset(reset(&places[p]));
            }
            if let Some(o) = &t.out {
                tb = tb.output(to_out(o, &places));
            }
            nb = nb.transition(tb.action(fork()).build());
        }
        // Every arc place is declared, touched or not (an untouched `p` is a
        // declared place no transition names); `q0` likewise. `s0` never is.
        for i in 0..self.arc_places {
            nb = nb.place(PlaceRef::new(self.names[i].as_str()));
        }
        if let Some(q) = self.declared_extra {
            nb = nb.place(PlaceRef::new(self.names[q].as_str()));
        }
        nb.build()
    }

    fn describe(&self) -> String {
        let mut s = String::new();
        for t in &self.transitions {
            let ins: Vec<String> = t
                .inputs
                .iter()
                .map(|(p, c)| match c {
                    Card::One => format!("one({})", self.names[*p]),
                    Card::Exactly(n) => format!("exactly({n}, {})", self.names[*p]),
                    Card::All => format!("all({})", self.names[*p]),
                    Card::AtLeast(n) => format!("at_least({n}, {})", self.names[*p]),
                })
                .collect();
            s.push_str(&format!("  {}: [{}]", t.name, ins.join(", ")));
            for &r in &t.reads {
                s.push_str(&format!(" read({})", self.names[r]));
            }
            for &r in &t.inhibitors {
                s.push_str(&format!(" inhibit({})", self.names[r]));
            }
            for &r in &t.resets {
                s.push_str(&format!(" reset({})", self.names[r]));
            }
            match &t.out {
                None => s.push_str(" -> (none)\n"),
                Some(o) => s.push_str(&format!(" -> {}\n", self.show_out(o))),
            }
        }
        let m0: Vec<String> = self
            .initial
            .iter()
            .enumerate()
            .filter(|(_, n)| **n > 0)
            .map(|(i, n)| format!("{}:{n}", self.names[i]))
            .collect();
        s.push_str(&format!("  M0 = {{{}}}", m0.join(", ")));
        if let Some(q) = self.declared_extra {
            s.push_str(&format!("  (declared arc-less: {})", self.names[q]));
        }
        if let Some(u) = self.undeclared {
            s.push_str(&format!("  (undeclared: {})", self.names[u]));
        }
        s
    }

    fn show_out(&self, o: &OSpec) -> String {
        match o {
            OSpec::Place(p) => self.names[*p].clone(),
            OSpec::And(c) => format!("and({})", c.iter().map(|x| self.show_out(x)).collect::<Vec<_>>().join(", ")),
            OSpec::Xor(c) => format!("xor({})", c.iter().map(|x| self.show_out(x)).collect::<Vec<_>>().join(", ")),
            OSpec::Timeout(c) => format!("timeout(50, {})", self.show_out(c)),
            OSpec::Forward { from, to } => {
                format!("forward_input({}, {})", self.names[*from], self.names[*to])
            }
        }
    }
}

fn forwards(o: &OSpec, acc: &mut Vec<usize>) {
    match o {
        OSpec::Place(_) => {}
        OSpec::And(c) | OSpec::Xor(c) => c.iter().for_each(|x| forwards(x, acc)),
        OSpec::Timeout(c) => forwards(c, acc),
        OSpec::Forward { from, .. } => acc.push(*from),
    }
}

fn to_out(o: &OSpec, places: &[Place<i32>]) -> Out {
    match o {
        OSpec::Place(p) => output::out_place(&places[*p]),
        OSpec::And(c) => output::and(c.iter().map(|x| to_out(x, places)).collect()),
        OSpec::Xor(c) => output::xor(c.iter().map(|x| to_out(x, places)).collect()),
        OSpec::Timeout(c) => output::timeout(50, to_out(c, places)),
        OSpec::Forward { from, to } => output::forward_input(&places[*from], &places[*to]),
    }
}

// ======================================================================
// Generator
// ======================================================================

fn gen_card(rng: &mut Rng) -> Card {
    match rng.below(100) {
        0..=44 => Card::One,
        45..=69 => Card::Exactly(rng.range(2, 3)),
        70..=84 => Card::All,
        _ => Card::AtLeast(rng.range(1, 2)),
    }
}

fn gen_normal(rng: &mut Rng, n: usize) -> OSpec {
    if n >= 2 && rng.chance(35) {
        let v = rng.distinct(n, 2);
        OSpec::And(vec![OSpec::Place(v[0]), OSpec::Place(v[1])])
    } else {
        OSpec::Place(rng.below(n))
    }
}

/// A timeout child ([IO-013]): a forward of a consumed input, optionally with a
/// sibling place; never an `Xor` or nested `Timeout` (the runtime rejects both).
fn gen_timeout_child(rng: &mut Rng, n: usize, inputs: &[(usize, Card)]) -> OSpec {
    // Mostly a one / exactly input: a forward of a draining input deposits a
    // marking-dependent count, which the flat encodings refuse (Unknown on every
    // route), so it is kept rarer to leave most forward nets decidable.
    let fixed: Vec<usize> = inputs
        .iter()
        .filter(|(_, c)| matches!(c, Card::One | Card::Exactly(_)))
        .map(|(p, _)| *p)
        .collect();
    let from = if !fixed.is_empty() && rng.chance(80) {
        rng.pick(&fixed)
    } else {
        inputs[rng.below(inputs.len())].0
    };
    let to = rng.below(n);
    let fw = OSpec::Forward { from, to };
    if n >= 2 && rng.chance(25) {
        let mut z = rng.below(n);
        if z == to {
            z = (z + 1) % n;
        }
        OSpec::And(vec![fw, OSpec::Place(z)])
    } else {
        fw
    }
}

fn gen_out(rng: &mut Rng, n: usize, inputs: &[(usize, Card)]) -> Option<OSpec> {
    let r = rng.below(100);
    let spec = match r {
        0..=7 => return None,
        8..=35 => OSpec::Place(rng.below(n)),
        36..=50 => {
            if n < 2 {
                OSpec::Place(0)
            } else {
                let v = rng.distinct(n, 2);
                OSpec::And(vec![OSpec::Place(v[0]), OSpec::Place(v[1])])
            }
        }
        51..=64 => {
            let a = gen_normal(rng, n);
            let b = OSpec::Place(rng.below(n));
            OSpec::Xor(vec![a, b])
        }
        65..=89 if !inputs.is_empty() => {
            let normal = gen_normal(rng, n);
            OSpec::Xor(vec![normal, OSpec::Timeout(Box::new(gen_timeout_child(rng, n, inputs)))])
        }
        _ if !inputs.is_empty() => OSpec::Timeout(Box::new(gen_timeout_child(rng, n, inputs))),
        _ => OSpec::Place(rng.below(n)),
    };
    Some(spec)
}

fn gen_net(seed: u64) -> NetSpec {
    let mut rng = Rng::new(seed);
    let n = rng.range(2, 6);
    let mut names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let declared_extra = if rng.chance(20) {
        names.push("q0".into());
        Some(names.len() - 1)
    } else {
        None
    };
    let undeclared = if rng.chance(30) {
        names.push("s0".into());
        Some(names.len() - 1)
    } else {
        None
    };
    let t_count = rng.range(1, 6);
    let places: Vec<Place<i32>> = (0..n).map(|i| Place::<i32>::new(format!("p{i}"))).collect();
    let mut transitions = Vec::new();
    for ti in 0..t_count {
        let k_in = match rng.below(100) {
            0..=4 => 0,
            5..=69 => 1,
            _ => 2.min(n),
        };
        let inputs: Vec<(usize, Card)> =
            rng.distinct(n, k_in).into_iter().map(|p| (p, gen_card(&mut rng))).collect();
        let in_set: HashSet<usize> = inputs.iter().map(|(p, _)| *p).collect();
        let mut reads = Vec::new();
        if rng.chance(15) {
            let cands: Vec<usize> = (0..n).filter(|p| !in_set.contains(p)).collect();
            if !cands.is_empty() {
                reads.push(rng.pick(&cands));
            }
        }
        let mut inhibitors = Vec::new();
        // A source transition mostly gets an inhibitor, which can bound it.
        if rng.chance(if k_in == 0 { 70 } else { 20 }) {
            inhibitors.push(rng.below(n));
        }
        let mut resets = Vec::new();
        if rng.chance(12) {
            resets.push(rng.below(n));
        }
        let mut out = gen_out(&mut rng, n, &inputs);
        // [IO-011]: the builder rejects a branch naming a place twice.
        if out.as_ref().is_some_and(|o| output::duplicate_in_branch(&to_out(o, &places)).is_some()) {
            out = Some(OSpec::Place(rng.below(n)));
        }
        transitions.push(TSpec { name: format!("t{ti}"), inputs, reads, inhibitors, resets, out });
    }
    let mut initial = vec![0u16; names.len()];
    for slot in initial.iter_mut().take(n) {
        *slot = match rng.below(100) {
            0..=49 => 0,
            50..=79 => 1,
            80..=94 => 2,
            _ => 3,
        };
    }
    // Multi-token inputs mostly need more than the 0-3 drawn above; give half of
    // them enough to fire at least once, so their forwards are exercised.
    for t in &transitions {
        for &(p, c) in &t.inputs {
            if matches!(c, Card::Exactly(_) | Card::AtLeast(_)) && rng.chance(50) {
                initial[p] = initial[p].max(required(c));
            }
        }
    }
    if let Some(q) = declared_extra {
        if rng.chance(50) {
            initial[q] = rng.range(1, 2) as u16;
        }
    }
    if let Some(s) = undeclared {
        initial[s] = rng.range(1, 2) as u16;
    }
    NetSpec { names, arc_places: n, declared_extra, undeclared, transitions, initial }
}

fn gen_props(seed: u64, net: &NetSpec) -> Vec<Prop> {
    let mut rng = Rng::new(seed.wrapping_mul(31).wrapping_add(7));
    let u = net.names.len();
    let name = |i: usize| net.names[i].clone();
    let mut props = vec![Prop::Deadlock { sinks: Vec::new() }];
    let k = rng.range(1, 2.min(u));
    props.push(Prop::Deadlock { sinks: rng.distinct(u, k).into_iter().map(name).collect() });
    // Bias the bound towards forward targets, where R1 lives.
    let mut fw_targets = Vec::new();
    for t in &net.transitions {
        if let Some(o) = &t.out {
            collect_forward_targets(o, &mut fw_targets);
        }
    }
    // Tight bounds find off-by-some deposits: on a closed reference state space the
    // bound is half the time the place's reachable maximum (or one less).
    let rnet = RefNet::new(net);
    let spaces = [
        explore(&rnet, &net.initial, ForwardSemantics::Faithful),
        explore(&rnet, &net.initial, ForwardSemantics::Unit),
    ];
    let max_of = |sem: ForwardSemantics, p: usize| -> Option<usize> {
        let ex = &spaces[(sem == ForwardSemantics::Unit) as usize];
        ex.complete.then(|| ex.states.iter().map(|m| m[p] as usize).max().unwrap_or(0))
    };
    let bound_place = rng.below(u);
    let bound = match max_of(ForwardSemantics::Faithful, bound_place) {
        Some(max) if rng.chance(50) => max.saturating_sub(rng.below(2)),
        _ => rng.range(0, 2),
    };
    props.push(Prop::Bound { place: name(bound_place), bound });
    // A forward target, bounded by its maximum under one-token-per-forward
    // semantics: holds there, and fails under [IO-014] exactly when a multi-token
    // forward can fire — the R1 shape.
    if !fw_targets.is_empty() {
        let target = rng.pick(&fw_targets);
        let bound = max_of(ForwardSemantics::Unit, target).unwrap_or_else(|| rng.range(0, 2));
        props.push(Prop::Bound { place: name(target), bound });
    }
    let v = rng.distinct(u, 2);
    props.push(Prop::Mutex { a: name(v[0]), b: name(v[1]) });
    let k = rng.range(1, 2.min(u));
    props.push(Prop::Unreach { places: rng.distinct(u, k).into_iter().map(name).collect() });
    let k = rng.range(1, 3.min(u));
    let places: Vec<String> = rng.distinct(u, k).into_iter().map(name).collect();
    let min = rng.range(0, 2);
    let max = if rng.chance(30) { None } else { Some(min + rng.range(0, 2)) };
    let waived: Vec<String> = if rng.chance(40) { vec![name(rng.below(u))] } else { Vec::new() };
    props.push(Prop::QCount { places, min, max, waived });
    props
}

fn collect_forward_targets(o: &OSpec, acc: &mut Vec<usize>) {
    match o {
        OSpec::Place(_) => {}
        OSpec::And(c) | OSpec::Xor(c) => c.iter().for_each(|x| collect_forward_targets(x, acc)),
        OSpec::Timeout(c) => collect_forward_targets(c, acc),
        OSpec::Forward { to, .. } => acc.push(*to),
    }
}

// ======================================================================
// Reference semantics — independent of the verifier
// ======================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ForwardSemantics {
    /// [IO-014]: one token into `to` per token consumed from `from`.
    Faithful,
    /// One token per forward leaf (the pre-fix flattener). Classification only.
    Unit,
}

type M = Vec<u16>;

/// A leaf of an output spec, kept as a leaf so a forward can carry its multiplicity.
#[derive(Clone, Debug)]
enum Leaf {
    Place(usize),
    Forward { from: usize, to: usize },
}

/// The claims an action that **completes** can write ([IO-015]): one per assignment
/// of every `Xor`; a `Timeout` claims its child's claim and a `ForwardInput` claims
/// its `to` place. The analyses model one token per claimed place ([IO-016]), so a
/// forward leaf here is an ordinary place.
fn alternatives(o: &OSpec) -> Vec<Vec<Leaf>> {
    match o {
        OSpec::Place(p) => vec![vec![Leaf::Place(*p)]],
        OSpec::Forward { to, .. } => vec![vec![Leaf::Place(*to)]],
        OSpec::Timeout(c) => alternatives(c),
        OSpec::Xor(cs) => cs.iter().flat_map(alternatives).collect(),
        OSpec::And(cs) => {
            let mut acc: Vec<Vec<Leaf>> = vec![Vec::new()];
            for c in cs {
                let alts = alternatives(c);
                let mut next = Vec::new();
                for a in &acc {
                    for b in &alts {
                        let mut v = a.clone();
                        v.extend(b.iter().cloned());
                        next.push(v);
                    }
                }
                acc = next;
            }
            acc
        }
    }
}

struct RefNet {
    transitions: Vec<RefT>,
}

struct RefT {
    name: String,
    inputs: Vec<(usize, Card)>,
    reads: Vec<usize>,
    inhibitors: Vec<usize>,
    resets: Vec<usize>,
    /// What a completing action can write; `[[]]` without an output spec.
    alts: Vec<Vec<Leaf>>,
    /// The leaves of the `Timeout` child, if the spec has one: what the marking
    /// receives when the budget expires ([IO-013] AC5: the child's tokens and
    /// nothing else). The generator never puts an `Xor` under a `Timeout` (the
    /// runtime rejects it), so the child is one conjunction of leaves.
    timeout: Option<Vec<Leaf>>,
}

fn timeout_leaves(o: &OSpec) -> Option<Vec<Leaf>> {
    fn leaves(o: &OSpec, acc: &mut Vec<Leaf>) {
        match o {
            OSpec::Place(p) => acc.push(Leaf::Place(*p)),
            OSpec::Forward { from, to } => acc.push(Leaf::Forward { from: *from, to: *to }),
            OSpec::And(c) => c.iter().for_each(|x| leaves(x, acc)),
            OSpec::Xor(_) | OSpec::Timeout(_) => panic!("generator put Xor/Timeout under a Timeout"),
        }
    }
    match o {
        OSpec::Timeout(c) => {
            let mut acc = Vec::new();
            leaves(c, &mut acc);
            Some(acc)
        }
        OSpec::And(cs) | OSpec::Xor(cs) => cs.iter().find_map(timeout_leaves),
        OSpec::Place(_) | OSpec::Forward { .. } => None,
    }
}

impl RefNet {
    fn new(net: &NetSpec) -> Self {
        RefNet {
            transitions: net
                .transitions
                .iter()
                .map(|t| RefT {
                    name: t.name.clone(),
                    inputs: t.inputs.clone(),
                    reads: t.reads.clone(),
                    inhibitors: t.inhibitors.clone(),
                    resets: t.resets.clone(),
                    alts: t.out.as_ref().map(alternatives).unwrap_or_else(|| vec![Vec::new()]),
                    timeout: t.out.as_ref().and_then(timeout_leaves),
                })
                .collect(),
        }
    }
}

fn required(c: Card) -> u16 {
    match c {
        Card::One => 1,
        Card::Exactly(n) => n as u16,
        Card::All => 1,
        Card::AtLeast(n) => n as u16,
    }
}

/// [CORE-022]: every input holds its required count, every read place is
/// marked, every inhibitor place is empty. A reset place contributes nothing.
fn enabled(t: &RefT, m: &M) -> bool {
    t.inputs.iter().all(|&(p, c)| m[p] >= required(c))
        && t.reads.iter().all(|&p| m[p] >= 1)
        && t.inhibitors.iter().all(|&p| m[p] == 0)
}

/// The markings one firing of `t` can produce: one per claim a completing action
/// can write, plus the timeout outcome when the spec has a `Timeout`.
/// Consumption per [IO-007] (`all` / `at_least` drain the place), then reset arcs
/// clear their places ([CORE-034]), then the deposit: one token per claimed place,
/// and for a forward on timeout the consumed multiplicity ([IO-014]).
fn fire(t: &RefT, m: &M, sem: ForwardSemantics) -> Vec<M> {
    let mut base = m.clone();
    let mut consumed: HashMap<usize, u16> = HashMap::new();
    for &(p, c) in &t.inputs {
        let n = match c {
            Card::One => 1,
            Card::Exactly(k) => k as u16,
            Card::All | Card::AtLeast(_) => m[p],
        };
        base[p] -= n;
        consumed.insert(p, n);
    }
    for &p in &t.resets {
        base[p] = 0;
    }
    t.alts
        .iter()
        .chain(t.timeout.iter())
        .map(|alt| {
            let mut next = base.clone();
            for leaf in alt {
                match *leaf {
                    Leaf::Place(p) => next[p] = next[p].saturating_add(1),
                    Leaf::Forward { from, to } => {
                        let k = match sem {
                            ForwardSemantics::Faithful => consumed.get(&from).copied().unwrap_or(0),
                            ForwardSemantics::Unit => 1,
                        };
                        next[to] = next[to].saturating_add(k);
                    }
                }
            }
            next
        })
        .collect()
}

fn quiescent(net: &RefNet, m: &M) -> bool {
    !net.transitions.iter().any(|t| enabled(t, m))
}

/// The property's bad-state predicate ([VER-002]), stated here from the spec.
fn bad(prop: &Prop, idx: &HashMap<&str, usize>, net: &RefNet, m: &M) -> bool {
    let count = |p: &String| idx.get(p.as_str()).map_or(0, |&i| m[i] as usize);
    match prop {
        Prop::Bound { place, bound } => count(place) > *bound,
        Prop::Mutex { a, b } => count(a) >= 1 && count(b) >= 1,
        Prop::Unreach { places } => places.iter().all(|p| count(p) >= 1),
        Prop::Deadlock { sinks } => {
            quiescent(net, m)
                && m.iter().enumerate().any(|(i, &n)| {
                    n > 0 && !sinks.iter().any(|s| idx.get(s.as_str()) == Some(&i))
                })
        }
        Prop::QCount { places, min, max, waived } => {
            if !quiescent(net, m) {
                return false;
            }
            let mut seen = HashSet::new();
            let total: usize = places.iter().filter(|p| seen.insert(p.as_str())).map(count).sum();
            max.is_some_and(|mx| total > mx)
                || (total < *min && !waived.iter().any(|w| count(w) > 0))
        }
    }
}

struct Explored {
    states: Vec<M>,
    complete: bool,
}

fn explore(net: &RefNet, m0: &M, sem: ForwardSemantics) -> Explored {
    let mut seen: HashMap<M, usize> = HashMap::new();
    let mut states = vec![m0.clone()];
    seen.insert(m0.clone(), 0);
    let mut queue = VecDeque::from([0usize]);
    let mut complete = true;
    while let Some(i) = queue.pop_front() {
        let m = states[i].clone();
        for t in &net.transitions {
            if !enabled(t, &m) {
                continue;
            }
            for next in fire(t, &m, sem) {
                if seen.contains_key(&next) {
                    continue;
                }
                if next.iter().any(|&n| n > REF_MAX_TOKENS) || states.len() >= REF_MAX_STATES {
                    complete = false;
                    continue;
                }
                seen.insert(next.clone(), states.len());
                queue.push_back(states.len());
                states.push(next);
            }
        }
    }
    Explored { states, complete }
}

/// What the reference says about a property: a witness exists, none exists (closed
/// state space), or it cannot tell (truncated, no witness in the explored part).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RefVerdict {
    Violated,
    Holds,
    Undecided,
}

fn ref_verdict(ex: &Explored, prop: &Prop, idx: &HashMap<&str, usize>, net: &RefNet) -> RefVerdict {
    if ex.states.iter().any(|m| bad(prop, idx, net, m)) {
        RefVerdict::Violated
    } else if ex.complete {
        RefVerdict::Holds
    } else {
        RefVerdict::Undecided
    }
}

/// Replays a verifier counterexample on the reference: from M0, each named
/// transition must be enabled and one of its alternatives must produce the next
/// trace marking (when the trace lists markings), and the last state must be bad.
fn replay(
    net: &RefNet,
    idx: &HashMap<&str, usize>,
    universe: usize,
    m0: &M,
    prop: &Prop,
    r: &VerificationResult,
    sem: ForwardSemantics,
) -> Result<(), String> {
    let to_m = |ms: &MarkingState| -> Result<M, String> {
        let mut v = vec![0u16; universe];
        for (p, n) in ms.places() {
            match idx.get(p) {
                Some(&i) => v[i] = n as u16,
                None if n == 0 => {}
                None => return Err(format!("trace marks unknown place '{p}'")),
            }
        }
        Ok(v)
    };
    let trace: Vec<M> =
        r.counterexample_trace.iter().map(to_m).collect::<Result<_, _>>()?;
    let names = &r.counterexample_transitions;
    let with_markings = !trace.is_empty() && trace.len() == names.len() + 1;
    if trace.is_empty() && names.is_empty() {
        return Err("no trace to replay".into());
    }
    if !trace.is_empty() && !with_markings && trace.len() != 1 {
        // A marking-only witness (no transitions): only its last state is checked.
        let last = trace.last().unwrap();
        let ex = explore(net, m0, sem);
        return if ex.states.contains(last) && bad(prop, idx, net, last) {
            Ok(())
        } else {
            Err(format!("witness {last:?} not a reachable bad state ({} markings, {} names)", trace.len(), names.len()))
        };
    }
    if with_markings && &trace[0] != m0 {
        return Err(format!("trace starts at {:?}, M0 is {m0:?}", trace[0]));
    }
    let mut states: Vec<M> = vec![m0.clone()];
    for (step, name) in names.iter().enumerate() {
        let base = strip_branch(name);
        let Some(t) = net.transitions.iter().find(|t| t.name == base) else {
            return Err(format!("step {step}: unknown transition '{name}'"));
        };
        let mut next: Vec<M> = Vec::new();
        for s in &states {
            if !enabled(t, s) {
                continue;
            }
            for n in fire(t, s, sem) {
                if !next.contains(&n) {
                    next.push(n);
                }
            }
        }
        if with_markings {
            let want = &trace[step + 1];
            if !next.contains(want) {
                return Err(format!(
                    "step {step}: '{name}' from {states:?} cannot reach trace marking {want:?} (reference gives {next:?})"
                ));
            }
            next = vec![want.clone()];
        }
        if next.is_empty() {
            return Err(format!("step {step}: '{name}' not enabled in {states:?}"));
        }
        states = next;
    }
    if states.iter().any(|s| bad(prop, idx, net, s)) {
        Ok(())
    } else {
        Err(format!("final state(s) {states:?} do not violate {}", prop.describe()))
    }
}

fn strip_branch(name: &str) -> &str {
    if let Some(pos) = name.rfind("_b") {
        if name[pos + 2..].chars().all(|c| c.is_ascii_digit()) && pos + 2 < name.len() {
            return &name[..pos];
        }
    }
    name
}

// ======================================================================
// Verifier configurations
// ======================================================================

#[derive(Clone, Copy)]
struct Config {
    name: &'static str,
    enum_budget: usize,
    linear_bound: bool,
    phases: bool,
}

const CONFIGS: [Config; 4] = [
    Config { name: "enum", enum_budget: ENUM_BUDGET, linear_bound: true, phases: true },
    Config { name: "smt+lb", enum_budget: 0, linear_bound: true, phases: true },
    Config { name: "smt-lb", enum_budget: 0, linear_bound: false, phases: true },
    Config { name: "ic3", enum_budget: 0, linear_bound: false, phases: false },
];

/// Runs one configuration. A verifier panic is not caught (the crate's policy,
/// `the_verification_crate_never_catches_a_panic`): it fails the net's own thread,
/// which is named after the seed, so the panic message names the net.
fn run_config(net: &PetriNet, m0: &MarkingState, prop: &Prop, cfg: Config) -> VerificationResult {
    SmtVerifier::for_net(net)
        // The Lean reference fires atomically; the in-flight split of VER-004 is not
        // modelled there yet, so the corpus is compared on the atomic reading.
        .assume_atomic_firing(true)
        .initial_marking(m0.clone())
        .property(prop.to_smt())
        .sink_places(prop.sinks().iter().cloned())
        .enumeration_max_classes(cfg.enum_budget)
        .linear_bound(cfg.linear_bound)
        .state_equation_phase(cfg.phases)
        .firing_bound(cfg.phases)
        .certificate_check(true)
        .counterexample_replay(true)
        .timeout(4_000)
        .total_budget(12_000)
        .verify()
}

// ======================================================================
// The differential check
// ======================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    /// Explained by the ForwardInput deposit bug (R1): the unit reference agrees.
    KnownForward,
    New,
}

#[derive(Debug)]
struct Finding {
    class: Class,
    kind: &'static str,
    config: &'static str,
    property: String,
    detail: String,
}

#[derive(Default)]
struct Stats {
    nets: usize,
    queries: usize,
    undeclared_marked: usize,
    declared_arcless: usize,
    untouched_arc_place: usize,
    multi_forward_nets: usize,
    forward_nets: usize,
    card: [usize; 4],
    reads: usize,
    inhibitors: usize,
    resets: usize,
    xor: usize,
    timeout: usize,
    and: usize,
    no_output: usize,
    source_transitions: usize,
    ref_complete: usize,
    ref_verdicts: [usize; 3],
    /// (net, property) pairs where the faithful and unit references disagree:
    /// the queries on which R1 can show.
    r1_sensitive: usize,
    /// DeadlockFree queries the undeclared token alone decides (the stray-token shape).
    stray_decisive: usize,
    /// [config][Proven, Violated, Unknown]
    verdicts: [[usize; 3]; 4],
    /// [config][Enumeration, Smt, Structural, NuScg, Unavailable]
    routes: [[usize; 5]; 4],
    replays: usize,
    /// Why routes answered `Unknown`, by reason prefix.
    unknown_reasons: HashMap<String, usize>,
}

impl Stats {
    fn merge(&mut self, o: &Stats) {
        self.nets += o.nets;
        self.queries += o.queries;
        self.undeclared_marked += o.undeclared_marked;
        self.declared_arcless += o.declared_arcless;
        self.untouched_arc_place += o.untouched_arc_place;
        self.multi_forward_nets += o.multi_forward_nets;
        self.forward_nets += o.forward_nets;
        for i in 0..4 {
            self.card[i] += o.card[i];
        }
        self.reads += o.reads;
        self.inhibitors += o.inhibitors;
        self.resets += o.resets;
        self.xor += o.xor;
        self.timeout += o.timeout;
        self.and += o.and;
        self.no_output += o.no_output;
        self.source_transitions += o.source_transitions;
        self.ref_complete += o.ref_complete;
        for i in 0..3 {
            self.ref_verdicts[i] += o.ref_verdicts[i];
        }
        self.r1_sensitive += o.r1_sensitive;
        self.stray_decisive += o.stray_decisive;
        for c in 0..4 {
            for k in 0..3 {
                self.verdicts[c][k] += o.verdicts[c][k];
            }
            for k in 0..5 {
                self.routes[c][k] += o.routes[c][k];
            }
        }
        self.replays += o.replays;
        for (k, v) in &o.unknown_reasons {
            *self.unknown_reasons.entry(k.clone()).or_default() += v;
        }
    }

    fn render(&self) -> String {
        let mut s = format!(
            "nets {} / queries {} | undeclared-marked {} declared-arcless {} untouched-arc-place {} | \
             forward nets {} (multi-token {}) | inputs one/exactly/all/atLeast {:?} | reads {} inhibitors {} resets {} | \
             outputs and {} xor {} timeout {} none {} | source transitions {}\n",
            self.nets,
            self.queries,
            self.undeclared_marked,
            self.declared_arcless,
            self.untouched_arc_place,
            self.forward_nets,
            self.multi_forward_nets,
            self.card,
            self.reads,
            self.inhibitors,
            self.resets,
            self.and,
            self.xor,
            self.timeout,
            self.no_output,
            self.source_transitions,
        );
        s.push_str(&format!(
            "reference: complete nets {} | verdicts violated/holds/undecided {:?} | R1-sensitive queries {} | stray-decisive deadlock queries {} | replays checked {}\n",
            self.ref_complete, self.ref_verdicts, self.r1_sensitive, self.stray_decisive, self.replays
        ));
        for (c, cfg) in CONFIGS.iter().enumerate() {
            s.push_str(&format!(
                "  {:7} proven/violated/unknown {:?}  routes enum/smt/structural/nu/unavail {:?}\n",
                cfg.name, self.verdicts[c], self.routes[c]
            ));
        }
        let mut reasons: Vec<_> = self.unknown_reasons.iter().collect();
        reasons.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        for (k, v) in reasons.iter().take(12) {
            s.push_str(&format!("  unknown x{v}: {k}\n"));
        }
        s
    }
}

fn route_slot(r: VerificationRoute) -> usize {
    match r {
        VerificationRoute::Enumeration => 0,
        VerificationRoute::Smt => 1,
        VerificationRoute::Structural => 2,
        VerificationRoute::NuScg => 3,
        VerificationRoute::Unavailable => 4,
    }
}

/// Runs every configuration on every property of `net` and returns the findings.
fn check_net(net: &NetSpec, props: &[Prop], stats: &mut Stats) -> Vec<Finding> {
    let built = net.build();
    let m0 = net.initial_marking();
    let idx = net.index();
    let rnet = RefNet::new(net);
    let faithful = explore(&rnet, &net.initial, ForwardSemantics::Faithful);
    let multi = net.has_multi_forward();
    let unit = if multi { Some(explore(&rnet, &net.initial, ForwardSemantics::Unit)) } else { None };
    let universe = net.names.len();

    stats.nets += 1;
    stats.ref_complete += faithful.complete as usize;
    stats.undeclared_marked += net.undeclared.is_some() as usize;
    stats.declared_arcless += net.declared_extra.is_some() as usize;
    stats.multi_forward_nets += multi as usize;
    let touched: HashSet<usize> = net
        .transitions
        .iter()
        .flat_map(|t| {
            let mut v: Vec<usize> = t.inputs.iter().map(|(p, _)| *p).collect();
            v.extend(&t.reads);
            v.extend(&t.inhibitors);
            v.extend(&t.resets);
            if let Some(o) = &t.out {
                let mut outs = Vec::new();
                out_places(o, &mut outs);
                v.extend(outs);
            }
            v
        })
        .collect();
    stats.untouched_arc_place += (0..net.arc_places).any(|p| !touched.contains(&p)) as usize;
    let mut has_fw = false;
    for t in &net.transitions {
        for (_, c) in &t.inputs {
            stats.card[match c {
                Card::One => 0,
                Card::Exactly(_) => 1,
                Card::All => 2,
                Card::AtLeast(_) => 3,
            }] += 1;
        }
        stats.reads += t.reads.len();
        stats.inhibitors += t.inhibitors.len();
        stats.resets += t.resets.len();
        stats.source_transitions += t.inputs.is_empty() as usize;
        match &t.out {
            None => stats.no_output += 1,
            Some(o) => {
                let s = format!("{o:?}");
                stats.and += s.contains("And(") as usize;
                stats.xor += s.contains("Xor(") as usize;
                stats.timeout += s.contains("Timeout(") as usize;
                has_fw |= s.contains("Forward");
            }
        }
    }
    stats.forward_nets += has_fw as usize;

    let mut findings = Vec::new();
    for prop in props {
        stats.queries += 1;
        let rv = ref_verdict(&faithful, prop, &idx, &rnet);
        stats.ref_verdicts[match rv {
            RefVerdict::Violated => 0,
            RefVerdict::Holds => 1,
            RefVerdict::Undecided => 2,
        }] += 1;
        let uv = unit.as_ref().map(|u| ref_verdict(u, prop, &idx, &rnet));
        if uv.is_some_and(|uv| uv != rv) {
            stats.r1_sensitive += 1;
        }
        if let (Some(s), Prop::Deadlock { sinks }) = (net.undeclared, prop) {
            let mut without = sinks.clone();
            without.push(net.names[s].clone());
            let p2 = Prop::Deadlock { sinks: without };
            if rv == RefVerdict::Violated && ref_verdict(&faithful, &p2, &idx, &rnet) != RefVerdict::Violated {
                stats.stray_decisive += 1;
            }
        }

        let mut results: Vec<(&'static str, Option<bool>)> = Vec::new(); // Some(true)=proven, Some(false)=violated
        for (ci, cfg) in CONFIGS.iter().enumerate() {
            let r = run_config(&built, &m0, prop, *cfg);
            stats.routes[ci][route_slot(r.route)] += 1;
            // Known iff the net carries a multi-token forward and the unit reference
            // would not raise the same finding.
            let classify = |unit_ok: bool| if multi && unit_ok { Class::KnownForward } else { Class::New };
            match &r.verdict {
                Verdict::Proven { method, .. } => {
                    stats.verdicts[ci][0] += 1;
                    results.push((cfg.name, Some(true)));
                    if rv == RefVerdict::Violated {
                        findings.push(Finding {
                            class: classify(uv != Some(RefVerdict::Violated)),
                            kind: "WRONG PROVEN",
                            config: cfg.name,
                            property: prop.describe(),
                            detail: format!("method {method}, route {:?}; the reference reaches a violation", r.route),
                        });
                    }
                }
                Verdict::Violated => {
                    stats.verdicts[ci][1] += 1;
                    results.push((cfg.name, Some(false)));
                    let has_trace = !r.counterexample_trace.is_empty() || !r.counterexample_transitions.is_empty();
                    if has_trace {
                        stats.replays += 1;
                        if let Err(why) = replay(&rnet, &idx, universe, &net.initial, prop, &r, ForwardSemantics::Faithful) {
                            let unit_ok = replay(&rnet, &idx, universe, &net.initial, prop, &r, ForwardSemantics::Unit).is_ok();
                            findings.push(Finding {
                                class: classify(unit_ok),
                                kind: if rv == RefVerdict::Holds { "WRONG VIOLATED" } else { "REPLAY FAILS" },
                                config: cfg.name,
                                property: prop.describe(),
                                detail: format!(
                                    "route {:?}, confirmed {:?}: {why}\n    trace names {:?}",
                                    r.route, r.counterexample_confirmed, r.counterexample_transitions
                                ),
                            });
                        }
                    } else if rv == RefVerdict::Holds {
                        findings.push(Finding {
                            class: classify(uv == Some(RefVerdict::Violated)),
                            kind: "WRONG VIOLATED",
                            config: cfg.name,
                            property: prop.describe(),
                            detail: format!("route {:?}, no trace; the reference's state space is closed and clean", r.route),
                        });
                    }
                }
                Verdict::Unknown { reason } => {
                    stats.verdicts[ci][2] += 1;
                    // Quoted names masked, so one cause is one line.
                    let mut key = String::new();
                    let mut quoted = false;
                    for ch in reason.chars().take(110) {
                        if ch == '\'' {
                            quoted = !quoted;
                            if quoted {
                                key.push_str("'_'");
                            }
                        } else if !quoted {
                            key.push(ch);
                        }
                    }
                    *stats.unknown_reasons.entry(format!("{}: {key}", cfg.name)).or_default() += 1;
                }
            }
        }
        let proven: Vec<&str> = results.iter().filter(|(_, v)| *v == Some(true)).map(|(n, _)| *n).collect();
        let violated: Vec<&str> = results.iter().filter(|(_, v)| *v == Some(false)).map(|(n, _)| *n).collect();
        // Only worth its own line when the reference could not settle it: otherwise
        // the per-route findings above already name the wrong side.
        if !proven.is_empty() && !violated.is_empty() && rv == RefVerdict::Undecided {
            findings.push(Finding {
                class: if multi { Class::KnownForward } else { Class::New },
                kind: "ROUTES DISAGREE",
                config: "-",
                property: prop.describe(),
                detail: format!("proven by {proven:?}, violated by {violated:?}; reference undecided"),
            });
        }
    }
    findings
}

fn out_places(o: &OSpec, acc: &mut Vec<usize>) {
    match o {
        OSpec::Place(p) => acc.push(*p),
        OSpec::And(c) | OSpec::Xor(c) => c.iter().for_each(|x| out_places(x, acc)),
        OSpec::Timeout(c) => out_places(c, acc),
        OSpec::Forward { to, .. } => acc.push(*to),
    }
}

fn z3_or_skip(test: &str) -> bool {
    if z3_available() {
        return true;
    }
    assert!(
        std::env::var("CI").is_err(),
        "{test} cannot run on this CI runner: no `z3` binary on PATH"
    );
    eprintln!("skipping {test}: z3 binary not on PATH");
    false
}

fn env_usize(name: &str) -> Option<usize> {
    std::env::var(name).ok().and_then(|v| v.parse().ok())
}

fn report_findings(label: &str, net: &NetSpec, findings: &[Finding]) -> String {
    let mut s = format!("--- {label}\n{}\n", net.describe());
    for f in findings {
        s.push_str(&format!(
            "  [{:?}] {} [{}] {}: {}\n",
            f.class, f.kind, f.config, f.property, f.detail
        ));
    }
    s
}

// ======================================================================
// Tests
// ======================================================================

/// The random differential run. Fails on every disagreement, those explained by the
/// ForwardInput deposit bug (R1) too, unless `ROUTE_AGREEMENT_STRICT=0`.
#[test]
fn routes_agree_with_each_other_and_the_reference() {
    if !z3_or_skip("routes_agree_with_each_other_and_the_reference") {
        return;
    }
    let nets = env_usize("ROUTE_AGREEMENT_NETS").unwrap_or(DEFAULT_NETS);
    let base_seed = std::env::var("ROUTE_AGREEMENT_SEED")
        .ok()
        .and_then(|v| u64::from_str_radix(v.trim_start_matches("0x"), 16).ok())
        .unwrap_or(0x5EED);
    let threads = env_usize("ROUTE_AGREEMENT_THREADS")
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get()))
        .max(1);
    let strict = std::env::var("ROUTE_AGREEMENT_STRICT").map_or(true, |v| v != "0");
    let verbose = std::env::var("ROUTE_AGREEMENT_VERBOSE").is_ok_and(|v| v == "1");

    let start = Instant::now();
    let next = AtomicUsize::new(0);
    let stats = Mutex::new(Stats::default());
    let reports: Mutex<Vec<(usize, Class, String)>> = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut local = Stats::default();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= nets {
                        break;
                    }
                    let seed = base_seed.wrapping_add(i as u64);
                    let net = gen_net(seed);
                    let props = gen_props(seed, &net);
                    // One named thread per net: a verifier panic fails the test
                    // with the seed in the panic line, and is never caught here.
                    let (findings, net_stats) = std::thread::Builder::new()
                        .name(format!("route-agreement seed {seed:#x}"))
                        .spawn({
                            let (net, props) = (net.clone(), props.clone());
                            move || {
                                let mut st = Stats::default();
                                let findings = check_net(&net, &props, &mut st);
                                (findings, st)
                            }
                        })
                        .expect("spawn net thread")
                        .join()
                        .unwrap_or_else(|_| panic!("net seed {seed:#x} panicked (message above)"));
                    local.merge(&net_stats);
                    if !findings.is_empty() {
                        let class = if findings.iter().any(|f| f.class == Class::New) {
                            Class::New
                        } else {
                            Class::KnownForward
                        };
                        let text = report_findings(&format!("seed {seed:#x}"), &net, &findings);
                        reports.lock().unwrap().push((i, class, text));
                    }
                }
                stats.lock().unwrap().merge(&local);
            });
        }
    });
    let stats = stats.into_inner().unwrap();
    let mut reports = reports.into_inner().unwrap();
    reports.sort_by_key(|(i, _, _)| *i);
    let new: Vec<&String> = reports.iter().filter(|(_, c, _)| *c == Class::New).map(|(_, _, t)| t).collect();
    let known: Vec<&String> =
        reports.iter().filter(|(_, c, _)| *c == Class::KnownForward).map(|(_, _, t)| t).collect();
    eprintln!(
        "[route-agreement] {nets} nets from seed {base_seed:#x} on {threads} threads in {:.1}s\n{}\
         nets with NEW disagreements: {} | nets with only known ForwardInput (R1) disagreements: {}",
        start.elapsed().as_secs_f64(),
        stats.render(),
        new.len(),
        known.len()
    );
    if verbose {
        for t in &known {
            eprintln!("{t}");
        }
    } else if let Some(t) = known.first() {
        eprintln!("first known-R1 net (ROUTE_AGREEMENT_VERBOSE=1 for all):\n{t}");
    }
    for t in &new {
        eprintln!("{t}");
    }
    assert!(new.is_empty(), "{} net(s) with new route disagreements (see stderr)", new.len());
    assert!(
        !strict || known.is_empty(),
        "{} net(s) with ForwardInput (R1) disagreements (the R1 fix regressed?)",
        known.len()
    );
}

/// The generator must be able to produce both historical wrong-Proven shapes,
/// or the differential run could not have caught them.
#[test]
fn generator_reaches_both_historical_shapes() {
    let mut stats = Stats::default();
    let mut r1_nets = 0;
    let mut stray_nets = 0;
    for i in 0..400u64 {
        let net = gen_net(0x5EED + i);
        let props = gen_props(0x5EED + i, &net);
        let idx = net.index();
        let rnet = RefNet::new(&net);
        let f = explore(&rnet, &net.initial, ForwardSemantics::Faithful);
        let u = explore(&rnet, &net.initial, ForwardSemantics::Unit);
        let mut r1 = false;
        let mut stray = false;
        for p in &props {
            let rv = ref_verdict(&f, p, &idx, &rnet);
            // The R1 shape: faithful says violated, unit semantics says it holds.
            r1 |= rv == RefVerdict::Violated && ref_verdict(&u, p, &idx, &rnet) == RefVerdict::Holds;
            if let (Some(s), Prop::Deadlock { sinks }) = (net.undeclared, p) {
                let mut without = sinks.clone();
                without.push(net.names[s].clone());
                stray |= rv == RefVerdict::Violated
                    && ref_verdict(&f, &Prop::Deadlock { sinks: without }, &idx, &rnet) == RefVerdict::Holds;
            }
        }
        r1_nets += r1 as usize;
        stray_nets += stray as usize;
        stats.nets += 1;
        stats.multi_forward_nets += net.has_multi_forward() as usize;
    }
    eprintln!("[route-agreement generator] of 400 nets: {r1_nets} expose R1, {stray_nets} expose the stray-token shape, {} carry a multi-token forward", stats.multi_forward_nets);
    assert!(r1_nets >= 5, "generator hit the ForwardInput shape only {r1_nets} times in 400 nets");
    assert!(stray_nets >= 5, "generator hit the stray-token shape only {stray_nets} times in 400 nets");
}

/// Sanity of the reference itself, straight from the spec's firing rules.
#[test]
fn reference_follows_the_spec_firing_rules() {
    // all(a) with 3 tokens, xor(c, timeout(forward_input(a, b))): the forward
    // carries all three ([IO-014]); reset(c) clears c before the output lands.
    let net = NetSpec {
        names: vec!["a".into(), "b".into(), "c".into()],
        arc_places: 3,
        declared_extra: None,
        undeclared: None,
        transitions: vec![TSpec {
            name: "t".into(),
            inputs: vec![(0, Card::All)],
            reads: vec![],
            inhibitors: vec![],
            resets: vec![2],
            out: Some(OSpec::Xor(vec![
                OSpec::Place(2),
                OSpec::Timeout(Box::new(OSpec::Forward { from: 0, to: 1 })),
            ])),
        }],
        initial: vec![3, 0, 4],
    };
    let r = RefNet::new(&net);
    let succ = fire(&r.transitions[0], &net.initial, ForwardSemantics::Faithful);
    // Completing action writes c, or writes b itself (the Timeout alternative's
    // claim, [IO-015]); the expired budget forwards all three into b.
    assert_eq!(succ, vec![vec![0, 0, 1], vec![0, 1, 0], vec![0, 3, 0]]);
    assert_eq!(fire(&r.transitions[0], &net.initial, ForwardSemantics::Unit)[2], vec![0, 1, 0]);
    // Read needs a token; inhibitor blocks on any; reset needs nothing.
    let t = RefT { name: "u".into(), inputs: vec![], reads: vec![0], inhibitors: vec![1], resets: vec![2], alts: vec![vec![]], timeout: None };
    assert!(enabled(&t, &vec![1, 0, 0]));
    assert!(!enabled(&t, &vec![0, 0, 0]));
    assert!(!enabled(&t, &vec![1, 1, 0]));
    assert_eq!(strip_branch("t3_b12"), "t3");
    assert_eq!(strip_branch("t3"), "t3");
}

/// Runs every configuration on one hand-built net and property and returns the
/// findings, for the regression cases.
fn check_fixed(net: &NetSpec, prop: Prop, expect: RefVerdict) -> Vec<Finding> {
    let rnet = RefNet::new(net);
    let ex = explore(&rnet, &net.initial, ForwardSemantics::Faithful);
    assert_eq!(ref_verdict(&ex, &prop, &net.index(), &rnet), expect, "reference verdict for {}", prop.describe());
    check_net(net, &[prop], &mut Stats::default())
}

/// Regression: a token on a place the net does not declare ([CORE-072], inert)
/// strands the quiescent initial marking. Every route used to drop it and say
/// `Proven` (fixed in e058472).
#[test]
fn regression_stray_token_on_undeclared_place() {
    if !z3_or_skip("regression_stray_token_on_undeclared_place") {
        return;
    }
    // t: one(c) -> d, sink d, M0 = {a: 1} with `a` undeclared.
    let net = NetSpec {
        names: vec!["c".into(), "d".into(), "a".into()],
        arc_places: 2,
        declared_extra: None,
        undeclared: Some(2),
        transitions: vec![TSpec {
            name: "t".into(),
            inputs: vec![(0, Card::One)],
            reads: vec![],
            inhibitors: vec![],
            resets: vec![],
            out: Some(OSpec::Place(1)),
        }],
        initial: vec![0, 0, 1],
    };
    let findings = check_fixed(&net, Prop::Deadlock { sinks: vec!["d".into()] }, RefVerdict::Violated);
    assert!(findings.is_empty(), "{}", report_findings("stray token", &net, &findings));
    let findings = check_fixed(&net, Prop::Bound { place: "a".into(), bound: 0 }, RefVerdict::Violated);
    assert!(findings.is_empty(), "{}", report_findings("stray token bound", &net, &findings));
}

/// Regression (R1, ForwardInput deposit): `exactly(2, a)` with a timeout branch
/// `forward_input(a, b)` deposits 2 tokens into `b` ([IO-014]); the flattener and
/// the state-class graph's branch expansion deposited 1, so `PlaceBound(b, 1)` came
/// back `Proven` from the structural route, the state-equation phase, IC3 and
/// enumeration alike.
#[test]
fn regression_forward_input_deposits_every_consumed_token() {
    if !z3_or_skip("regression_forward_input_deposits_every_consumed_token") {
        return;
    }
    // t: exactly(2, a) -> xor(c, timeout(50, forward_input(a, b)))   M0 = {a: 2}
    let net = NetSpec {
        names: vec!["a".into(), "b".into(), "c".into()],
        arc_places: 3,
        declared_extra: None,
        undeclared: None,
        transitions: vec![TSpec {
            name: "t".into(),
            inputs: vec![(0, Card::Exactly(2))],
            reads: vec![],
            inhibitors: vec![],
            resets: vec![],
            out: Some(OSpec::Xor(vec![
                OSpec::Place(2),
                OSpec::Timeout(Box::new(OSpec::Forward { from: 0, to: 1 })),
            ])),
        }],
        initial: vec![2, 0, 0],
    };
    let findings = check_fixed(&net, Prop::Bound { place: "b".into(), bound: 1 }, RefVerdict::Violated);
    assert!(findings.is_empty(), "{}", report_findings("R1 forward", &net, &findings));
}
