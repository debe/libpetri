//! Differential tests of the colour-slot linear program of [NU-053]
//! (`slot_bound_lp`): against the state space, against the semiflow bound it replaced,
//! against z3 as an independent optimiser, and through `build_plan` with deliberately
//! wrong answers, which the exact re-check must refuse.
//!
//! The corpus is the shared parity cases (`spec/verification-fixtures/slot-bound-lp.json`),
//! the PNID relay nets of [NU-054] at budgets 1 and 2, and seeded random small ν-nets.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/nets.rs"]
#[allow(dead_code)]
mod nets;
#[path = "common/old_slot_bound.rs"]
mod old_slot_bound;
#[path = "common/relay_nets.rs"]
mod relay_nets;
#[path = "common/slot_lp_cases.rs"]
mod slot_lp_cases;

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::io::Write;
use std::process::{Command, Stdio};

use libpetri_core::action::fork;
use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{and, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::exact::BigInt;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::name_coloured_encoder::{self, ColouredPlan};
use libpetri_verification::name_fragment::{self, FragmentMode};
use libpetri_verification::net_flattener::{self, FlatNet, FlatTransition};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::slot_bound_lp::{self, LpAnswer, ScaledCover, SlotBound};
use libpetri_verification::smt_verifier::z3_available;
use libpetri_verification::z3_process::Z3Solver;

/// One LP subject: a flat net, its initial marking and its coloured places.
struct Subject {
    id: String,
    flat: FlatNet,
    initial: MarkingState,
    coloured: Vec<usize>,
}

fn parity_subjects() -> Vec<Subject> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../spec/verification-fixtures/slot-bound-lp.json");
    let doc = json::parse_json(&std::fs::read_to_string(path).expect("read slot-bound-lp.json"));
    doc.arr("cases")
        .iter()
        .map(|c| {
            let built = slot_lp_cases::build(c);
            Subject { id: built.id, flat: built.flat, initial: built.initial, coloured: built.coloured }
        })
        .collect()
}

/// The coloured places `build_plan` hands the slot bound, captured through its `lp`
/// closure; `None` when a structural refusal comes first.
fn plan_coloured(
    net: &PetriNet,
    flat: &FlatNet,
    initial: &MarkingState,
    budgets: &[&str],
    carriers: &[&str],
    mode: FragmentMode,
) -> Option<Vec<usize>> {
    let budget: HashSet<String> = budgets.iter().map(|s| s.to_string()).collect();
    let carrier: HashSet<String> = carriers.iter().map(|s| s.to_string()).collect();
    let mints = name_fragment::declared_mints(net, &budget, &HashSet::new());
    let seen = RefCell::new(None);
    let _ = name_coloured_encoder::build_plan(
        net,
        flat,
        initial,
        &mints,
        mode,
        &carrier,
        |c| {
            *seen.borrow_mut() = Some(c.to_vec());
            slot_bound_lp::solve(flat, initial, c)
        },
        |_| {},
    );
    seen.into_inner()
}

/// The PNID relay nets at budgets 1 and 2, with the coloured set their plan computes.
fn relay_subjects() -> Vec<Subject> {
    use relay_nets::*;
    let nets: Vec<(&str, Vec<Row>, &str, &[&str])> = vec![
        ("fig12c", fig_12c(), "R", &FIG_12C_CARRIERS),
        ("n1", n1_corr(), "SUPPLY", &[]),
        ("s-union", s_union(), "SUPPLY", &["q"]),
        ("join-chain", join_chain(), "S", &[]),
        ("join-chain-split", join_chain_split(), "S", &[]),
        ("self-loop", self_loop(false), "S", &[]),
        ("self-loop-independent", self_loop(true), "S", &[]),
    ];
    let mut out = Vec::new();
    for (name, rows, budget, carriers) in nets {
        let net = pnid_net(name, &rows);
        let flat = net_flattener::flatten(&net);
        for scale in [1usize, 2] {
            let mut m = MarkingStateBuilder::new().tokens(budget, scale);
            if name == "join-chain-split" {
                m = m.tokens("S2", scale);
            }
            if name == "self-loop-independent" {
                m = m.tokens("T", scale);
            }
            let initial = m.build();
            let Some(coloured) = plan_coloured(&net, &flat, &initial, &[budget], carriers, FragmentMode::Extended)
            else {
                continue;
            };
            out.push(Subject { id: format!("{name}@{scale}"), flat: flat.clone(), initial, coloured });
        }
    }
    out
}

/// xorshift64*, so the corpus needs no dependency.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

/// A seeded small ν-like flat net: two keys (sometimes a third coloured carrier), a budget,
/// a few uncoloured places, mints into the keys, joins out of them, a coloured drain now
/// and then, and uncoloured rows, some with a reset or consume-all arc on an uncoloured
/// place. Coloured places start empty.
fn random_subject(seed: u64) -> Subject {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let carrier = rng.chance(30);
    let extra = 1 + rng.below(3) as usize;
    let mut names: Vec<String> = vec!["a".into(), "b".into(), "budget".into()];
    if carrier {
        names.push("c".into());
    }
    for i in 0..extra {
        names.push(format!("u{i}"));
    }
    names.sort();
    let n = names.len();
    let idx = |p: &str| names.iter().position(|q| q == p).unwrap();
    let keys: Vec<usize> = if carrier { vec![idx("a"), idx("b"), idx("c")] } else { vec![idx("a"), idx("b")] };
    let carrier_place = if carrier { Some(idx("c")) } else { None };
    let unc: Vec<usize> = (0..n).filter(|p| !keys.contains(p)).collect();
    let mut rows: Vec<FlatTransition> = Vec::new();
    let mut add = |name: String, pre: Vec<i64>, post: Vec<i64>, reset: Vec<usize>, all: Vec<usize>| {
        rows.push(FlatTransition::new(name, pre, post).with_reset_places(reset).with_consume_all(all));
    };
    for m in 0..1 + rng.below(2) {
        let mut pre = vec![0i64; n];
        let mut post = vec![0i64; n];
        pre[idx("budget")] = 1 + rng.below(3) as i64;
        if rng.chance(30) {
            pre[unc[rng.below(unc.len() as u64) as usize]] += 1;
        }
        for &k in &keys {
            if rng.chance(85) || k == idx("a") {
                post[k] = 1;
            }
        }
        if rng.chance(30) {
            post[unc[rng.below(unc.len() as u64) as usize]] += 1;
        }
        add(format!("mint{m}"), pre, post, vec![], vec![]);
    }
    for j in 0..1 + rng.below(2) {
        let mut pre = vec![0i64; n];
        let mut post = vec![0i64; n];
        for &k in &keys {
            if Some(k) != carrier_place || rng.chance(50) {
                pre[k] = 1;
            }
        }
        post[idx("budget")] = rng.below(3) as i64;
        if rng.chance(50) {
            post[unc[rng.below(unc.len() as u64) as usize]] += 1;
        }
        add(format!("join{j}"), pre, post, vec![], vec![]);
    }
    if rng.chance(30) {
        let mut pre = vec![0i64; n];
        let mut post = vec![0i64; n];
        pre[keys[rng.below(keys.len() as u64) as usize]] = 1;
        post[unc[rng.below(unc.len() as u64) as usize]] = 1;
        add("drain".into(), pre, post, vec![], vec![]);
    }
    for t in 0..rng.below(4) {
        let mut pre = vec![0i64; n];
        let mut post = vec![0i64; n];
        let from = unc[rng.below(unc.len() as u64) as usize];
        let to = unc[rng.below(unc.len() as u64) as usize];
        pre[from] = 1 + rng.below(2) as i64;
        post[to] += 1 + rng.below(2) as i64;
        let (mut reset, mut all) = (vec![], vec![]);
        let side = unc[rng.below(unc.len() as u64) as usize];
        match rng.below(6) {
            0 if side != from => reset.push(side),
            1 => {
                pre[from] = 1;
                all.push(from);
            }
            _ => {}
        }
        add(format!("side{t}"), pre, post, reset, all);
    }
    let mut initial = MarkingStateBuilder::new().tokens("budget", rng.below(4) as usize);
    for &u in &unc {
        if names[u] != "budget" && rng.chance(40) {
            initial = initial.tokens(names[u].clone(), 1 + rng.below(2) as usize);
        }
    }
    let place_index: HashMap<String, usize> = names.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
    Subject {
        id: format!("random-{seed}"),
        flat: FlatNet { places: names, place_index, place_count: n, transitions: rows },
        initial: initial.build(),
        coloured: keys,
    }
}

fn corpus() -> Vec<Subject> {
    let mut all = parity_subjects();
    all.extend(relay_subjects());
    all.extend((0..300).map(random_subject));
    all
}

/// The simplex's checked bound.
fn lp_bound(s: &Subject) -> SlotBound {
    slot_bound_lp::checked(&s.flat, &s.initial, &s.coloured, slot_bound_lp::solve(&s.flat, &s.initial, &s.coloured))
}

// ---- explicit state spaces ----

const STATE_CAP: usize = 20_000;

/// Fires a row as Lean `fireAD` does: a reset or consume-all place ends at the row's
/// deposit, every other place at `m − pre + post`. Inhibitor and read arcs are ignored,
/// which only adds markings.
fn fire_ad(t: &FlatTransition, m: &[i64]) -> Option<Vec<i64>> {
    if (0..m.len()).any(|p| t.pre[p] > m[p]) {
        return None;
    }
    Some(
        (0..m.len())
            .map(|p| {
                if t.reset_places.contains(&p) || t.consume_all.contains(&p) {
                    t.post[p]
                } else {
                    m[p] - t.pre[p] + t.post[p]
                }
            })
            .collect(),
    )
}

/// The largest coloured token count over the `fireAD` state space, and whether it closed.
fn max_coloured_tokens(s: &Subject) -> (i64, bool) {
    let m0: Vec<i64> = s.flat.places.iter().map(|p| s.initial.count(p) as i64).collect();
    let mut seen: HashSet<Vec<i64>> = HashSet::from([m0.clone()]);
    let mut queue = VecDeque::from([m0]);
    let mut best = 0;
    while let Some(m) = queue.pop_front() {
        best = best.max(s.coloured.iter().map(|&p| m[p]).sum());
        for t in &s.flat.transitions {
            if let Some(next) = fire_ad(t, &m) {
                if seen.len() >= STATE_CAP {
                    return (best, false);
                }
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }
    }
    (best, true)
}

/// The name semantics of the flat rows: a row consuming coloured places takes one name
/// from all of them and writes it into its coloured outputs; a row writing coloured places
/// without consuming one writes a fresh name. The largest number of names live at once
/// and the largest coloured token count, and whether the space closed.
fn max_live_names(s: &Subject) -> (usize, usize, bool) {
    let n = s.flat.place_count;
    let is_col = |p: usize| s.coloured.contains(&p);
    type State = (Vec<i64>, Vec<(usize, u32)>);
    // Names renamed by first appearance, so the space stays finite.
    let normal = |(unc, mut col): State| -> State {
        col.sort_unstable();
        let mut map: HashMap<u32, u32> = HashMap::new();
        for e in &mut col {
            let next = map.len() as u32;
            e.1 = *map.entry(e.1).or_insert(next);
        }
        col.sort_unstable();
        (unc, col)
    };
    let m0: Vec<i64> = s.flat.places.iter().map(|p| s.initial.count(p) as i64).collect();
    let start = normal((m0, Vec::new()));
    let mut seen: HashSet<State> = HashSet::from([start.clone()]);
    let mut queue = VecDeque::from([start]);
    let (mut live, mut tokens) = (0, 0);
    while let Some((unc, col)) = queue.pop_front() {
        let names: BTreeSet<u32> = col.iter().map(|e| e.1).collect();
        live = live.max(names.len());
        tokens = tokens.max(col.len());
        for t in &s.flat.transitions {
            let unc_ok = (0..n).all(|p| is_col(p) || t.pre[p] <= unc[p]);
            if !unc_ok {
                continue;
            }
            let fired_unc: Vec<i64> = (0..n)
                .map(|p| {
                    if is_col(p) {
                        0
                    } else if t.reset_places.contains(&p) || t.consume_all.contains(&p) {
                        t.post[p]
                    } else {
                        unc[p] - t.pre[p] + t.post[p]
                    }
                })
                .collect();
            let col_in: Vec<usize> = s.coloured.iter().copied().filter(|&p| t.pre[p] > 0).collect();
            let col_out: Vec<usize> = s.coloured.iter().copied().filter(|&p| t.post[p] > 0).collect();
            let candidates: Vec<u32> = if col_in.is_empty() {
                vec![(0..).find(|x| !names.contains(x)).unwrap()]
            } else {
                names
                    .iter()
                    .copied()
                    .filter(|&x| col_in.iter().all(|&p| col.iter().filter(|e| **e == (p, x)).count() as i64 >= t.pre[p]))
                    .collect()
            };
            if col_in.is_empty() && col_out.is_empty() {
                let next = normal((fired_unc, col.clone()));
                if seen.len() >= STATE_CAP {
                    return (live, tokens, false);
                }
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
                continue;
            }
            for x in candidates {
                let mut c = col.clone();
                for &p in &col_in {
                    for _ in 0..t.pre[p] {
                        let i = c.iter().position(|e| *e == (p, x)).unwrap();
                        c.remove(i);
                    }
                }
                for &p in &col_out {
                    for _ in 0..t.post[p] {
                        c.push((p, x));
                    }
                }
                let next = normal((fired_unc.clone(), c));
                if seen.len() >= STATE_CAP {
                    return (live, tokens, false);
                }
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }
    }
    (live, tokens, true)
}

/// LP `k` ≥ the largest coloured token count ≥ the largest number of live names, on every
/// subject with an optimum; the state space may be cut at [`STATE_CAP`], and every marking
/// it holds is reachable.
#[test]
fn lp_k_bounds_the_explicit_state_space() {
    let mut checked = 0;
    let mut tight = 0;
    for s in corpus() {
        let SlotBound::Bound { k, .. } = lp_bound(&s) else { continue };
        let (tokens, closed) = max_coloured_tokens(&s);
        let (live, name_tokens, names_closed) = max_live_names(&s);
        assert!(tokens <= k as i64, "[{}] {tokens} coloured tokens reachable above k={k}", s.id);
        assert!(live <= name_tokens, "[{}]", s.id);
        if closed && names_closed {
            assert!(name_tokens as i64 <= tokens, "[{}] name semantics beyond fireAD", s.id);
        }
        checked += 1;
        tight += usize::from(tokens == k as i64);
    }
    eprintln!("[slot-bound LP] k bounds the state space on {checked} subjects, tight on {tight}");
    assert!(checked >= 200 && tight >= 100, "checked {checked}, tight {tight}");
}

/// LP `k` ≤ the semiflow bound wherever the semiflow code returned one (truncated or
/// not), and an infeasible program means the semiflow code returned none: every covering
/// semiflow, and the summed fallback, is a feasible weighting.
#[test]
fn lp_k_never_exceeds_the_semiflow_bound() {
    let (mut compared, mut smaller, mut admitted) = (0, 0, 0);
    for s in corpus() {
        let old = old_slot_bound::colour_slot_bound(
            &s.coloured,
            &old_slot_bound::validated_semiflows(&s.flat, &s.initial),
        );
        match (lp_bound(&s), old) {
            (SlotBound::Bound { k, .. }, Some(old)) => {
                assert!(k <= old, "[{}] LP k={k} above the semiflow bound {old}", s.id);
                compared += 1;
                smaller += usize::from(k < old);
            }
            (SlotBound::Bound { .. }, None) => admitted += 1,
            (SlotBound::Infeasible { .. }, old) => {
                assert_eq!(old, None, "[{}] LP infeasible but a covering semiflow exists", s.id)
            }
            (other, _) => panic!("[{}] unexpected answer {other:?}", s.id),
        }
    }
    eprintln!(
        "[slot-bound LP] compared {compared} (LP smaller on {smaller}); {admitted} admitted that the semiflows refused"
    );
    assert!(compared >= 40 && smaller >= 10 && admitted >= 10, "{compared} {smaller} {admitted}");
}

/// A `QF_LRA` question about the program: `extra` conjoined to its constraints.
fn lra_script(s: &Subject, extra: &str) -> String {
    let n = s.flat.place_count;
    let mut out = String::from("(set-logic QF_LRA)\n");
    for p in 0..n {
        out.push_str(&format!("(declare-const y{p} Real)\n(assert (>= y{p} 0.0))\n"));
    }
    for &p in &s.coloured {
        out.push_str(&format!("(assert (>= y{p} 1.0))\n"));
    }
    let real = |v: i64| if v < 0 { format!("(- {}.0)", -v) } else { format!("{v}.0") };
    let sum = |terms: Vec<String>| if terms.is_empty() { "0.0".to_string() } else { format!("(+ 0.0 {})", terms.join(" ")) };
    for t in &s.flat.transitions {
        let terms = (0..n)
            .filter(|&p| t.post[p] != t.pre[p])
            .map(|p| format!("(* {} y{p})", real(t.post[p] - t.pre[p])))
            .collect();
        out.push_str(&format!("(assert (<= {} 0.0))\n", sum(terms)));
    }
    let objective = sum(
        (0..n)
            .filter(|&p| s.initial.count(&s.flat.places[p]) != 0)
            .map(|p| format!("(* {} y{p})", real(s.initial.count(&s.flat.places[p]) as i64)))
            .collect(),
    );
    out.push_str(&extra.replace("OBJ", &objective));
    out.push_str("\n(check-sat)\n");
    out
}

fn z3_answer(script: &str) -> String {
    let program = std::env::var("LIBPETRI_Z3").ok().filter(|v| !v.is_empty()).unwrap_or_else(|| "z3".into());
    let mut child = Command::new(program)
        .args(["-smt2", "-in", "-T:60"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn z3");
    child.stdin.take().unwrap().write_all(script.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8_lossy(&out.stdout).lines().next().unwrap_or("").trim().to_string()
}

/// The optimum agrees with z3 over the reals: at the LP's optimum the program is
/// satisfiable, strictly below it unsatisfiable, and an infeasible program is
/// unsatisfiable outright.
#[test]
fn the_lp_optimum_agrees_with_z3() {
    if !z3_available() {
        eprintln!("skipping the_lp_optimum_agrees_with_z3: z3 binary not on PATH");
        return;
    }
    let mut agreed = 0;
    for s in corpus() {
        match lp_bound(&s) {
            SlotBound::Bound { value, .. } => {
                let v = format!("(/ {}.0 {}.0)", value.numer(), value.denom());
                assert_eq!(z3_answer(&lra_script(&s, &format!("(assert (<= OBJ {v}))"))), "sat", "[{}]", s.id);
                assert_eq!(z3_answer(&lra_script(&s, &format!("(assert (< OBJ {v}))"))), "unsat", "[{}] {value}", s.id);
            }
            SlotBound::Infeasible { .. } => assert_eq!(z3_answer(&lra_script(&s, "")), "unsat", "[{}]", s.id),
            other => panic!("[{}] unexpected answer {other:?}", s.id),
        }
        agreed += 1;
    }
    eprintln!("[slot-bound LP] z3 agrees on {agreed} subjects");
}

/// The seeded composed workflow of 255 places and 341 rows: optimum 6 (two budget tokens
/// times three keys), within twice as many pivots as the presolved program has places and
/// rows. The time is measured by the `slot_bound_lp` Criterion benchmark.
#[test]
fn the_composed_workflow_solves_in_few_pivots() {
    let s = parity_subjects().into_iter().find(|s| s.id == "composed-workflow-7").expect("composed workflow");
    assert_eq!((s.flat.place_count, s.flat.transitions.len()), (255, 341));
    let (answer, pivots) = slot_bound_lp::solve_counted(&s.flat, &s.initial, &s.coloured);
    let LpAnswer::Optimal { places, rows, .. } = &answer else { panic!("{answer:?}") };
    assert!(pivots <= 2 * (places + rows), "{pivots} pivots over {places} places and {rows} rows");
    let bound = slot_bound_lp::checked(&s.flat, &s.initial, &s.coloured, answer);
    assert_eq!(bound.k(), Some(6), "{bound:?}");
}

// ---- the re-check cannot be bypassed ----

/// The scatter-gather ν-net plus `archive: merged → archived`, a row the presolve drops
/// (it produces into no place upstream of the keys).
fn scatter_gather_archive() -> PetriNet {
    let p = |n: &str| Place::<String>::new(n);
    let key = |s: &String| NameId::new(s.clone());
    let (source, budget, pending, a, b, merged, archived) =
        (p("source"), p("budget"), p("pending"), p("branchA"), p("branchB"), p("merged"), p("archived"));
    let fork_t = Transition::builder("fork")
        .input(one(&source))
        .input(one(&budget))
        .output(and(vec![out_place(&a), out_place(&b), out_place(&pending)]))
        .action(fork())
        .build();
    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .input(one(&pending))
        .match_spec(MatchSpec::builder().key(&a, key).key(&b, key).build())
        .output(and(vec![out_place(&merged), out_place(&budget)]))
        .action(fork())
        .build();
    let archive = Transition::builder("archive").input(one(&merged)).output(out_place(&archived)).action(fork()).build();
    PetriNet::builder("scatter_gather_archive").transitions([fork_t, join, archive]).build()
}

/// `build_plan` with the simplex replaced by `answer`, and the bound it reported.
fn plan_with(net: &PetriNet, initial: &MarkingState, answer: impl FnOnce(&FlatNet) -> LpAnswer) -> (Option<ColouredPlan>, SlotBound) {
    let flat = net_flattener::flatten(net);
    let budget: HashSet<String> = HashSet::from(["budget".to_string()]);
    let mints = name_fragment::declared_mints(net, &budget, &HashSet::new());
    let reported = RefCell::new(None);
    let plan = name_coloured_encoder::build_plan(
        net,
        &flat,
        initial,
        &mints,
        FragmentMode::Base,
        &HashSet::new(),
        |_| answer(&flat),
        |b| *reported.borrow_mut() = Some(b.clone()),
    );
    (plan, reported.into_inner().expect("the sink is called once the plan reaches the bound"))
}

/// Weights by place name, every other place 0.
fn weights(flat: &FlatNet, by_name: &[(&str, i64)], d: i64) -> LpAnswer {
    let mut w = vec![BigInt::zero(); flat.place_count];
    for (p, v) in by_name {
        w[flat.place_index[*p]] = BigInt::from(*v);
    }
    LpAnswer::Optimal { cover: ScaledCover { weights: w, denominator: BigInt::from(d) }, places: 5, rows: 2 }
}

#[test]
fn build_plan_takes_k_only_from_a_weighting_the_re_check_accepts() {
    let net = scatter_gather_archive();
    let m0 = MarkingStateBuilder::new().tokens("source", 3).tokens("budget", 2).build();
    let optimal = [("branchA", 1), ("branchB", 1), ("budget", 2)];

    let (plan, bound) = plan_with(&net, &m0, |flat| {
        let keys = vec![flat.place_index["branchA"], flat.place_index["branchB"]];
        slot_bound_lp::solve(flat, &m0, &keys)
    });
    assert_eq!(plan.map(|p| p.k), Some(4), "{bound:?}");

    let refused = [
        (vec![("branchA", 1), ("branchB", 1), ("budget", 2), ("pending", -1)], 1, "place 'pending' has negative weight -1"),
        (vec![("branchA", 2), ("branchB", 1), ("budget", 6)], 2, "coloured place 'branchB' has weight 1 below the denominator 2"),
        (
            optimal.iter().copied().chain([("archived", 1)]).collect(),
            1,
            "transition 'archive' increases the weighted sum by 1",
        ),
        (optimal.to_vec(), 0, "denominator 0 is not positive"),
        (optimal.to_vec(), -1, "denominator -1 is not positive"),
        (vec![("branchA", 1), ("branchB", 1), ("budget", 2), ("source", 1 << 31)], 1, "k=6442450948 exceeds 2147483647"),
    ];
    for (w, d, reason) in refused {
        let (plan, bound) = plan_with(&net, &m0, |flat| weights(flat, &w, d));
        assert!(plan.is_none(), "{reason}");
        assert_eq!(bound, SlotBound::CheckFailed { reason: reason.to_string() });
        assert_eq!(
            bound.report_line().unwrap(),
            format!("  Colour-slot bound: none (LP weighting failed the exact re-check: {reason})")
        );
    }

    // A feasible weighting that is not optimal is accepted, with its larger k.
    let (plan, bound) = plan_with(&net, &m0, |flat| weights(flat, &[("branchA", 1), ("branchB", 1), ("budget", 2), ("source", 1)], 1));
    assert_eq!(plan.map(|p| p.k), Some(7), "{bound:?}");
    // Every answer without a weighting refuses the plan.
    for answer in [LpAnswer::Infeasible { places: 5, rows: 2 }, LpAnswer::PivotLimit { limit: 350 }, LpAnswer::Stopped] {
        let (plan, _) = plan_with(&net, &m0, |_| answer.clone());
        assert!(plan.is_none(), "{answer:?}");
    }
}

// ---- verdict invariance ----

/// Runs a HORN script: `sat` proves the property (no bad marking is reachable), `unsat`
/// violates it.
fn spacer(script: &str) -> String {
    let solver = Z3Solver::resolve().expect("z3");
    let reply = solver.run(script, "slot-bound-lp-test", 20_000, &[]).expect("z3 run");
    reply.stdout.lines().next().unwrap_or("").trim().to_string()
}

/// On the scatter-gather fixture (the shared coloured net whose `k` changed, 10 to 4), the
/// coloured encoding answers every query the same with the LP's `k` as with the old
/// semiflow weighting's, fed to `build_plan` through its `lp` closure. Spacer may run out
/// of time on the larger encoding (`unknown`); it must never answer the other way.
#[test]
fn the_lp_k_and_the_semiflow_k_give_the_same_verdicts() {
    if !z3_available() {
        eprintln!("skipping the_lp_k_and_the_semiflow_k_give_the_same_verdicts: z3 binary not on PATH");
        return;
    }
    let built = nets::build("nuScatterGather");
    let flat = net_flattener::flatten(&built.net);
    let coloured: Vec<usize> = ["branchA", "branchB"].iter().map(|p| flat.place_index[*p]).collect();
    let old = old_slot_bound::colour_slot_weighting(
        flat.place_count,
        &coloured,
        &old_slot_bound::validated_semiflows(&flat, &built.initial),
    )
    .expect("the scatter-gather net has a covering semiflow");
    let old_answer = LpAnswer::Optimal {
        cover: ScaledCover { weights: old.iter().map(|&w| BigInt::from(w)).collect(), denominator: BigInt::one() },
        places: 0,
        rows: 0,
    };
    let (old_plan, _) = plan_with(&built.net, &built.initial, |_| old_answer);
    let (lp_plan, _) = plan_with(&built.net, &built.initial, |f| slot_bound_lp::solve(f, &built.initial, &coloured));
    let (old_plan, lp_plan) = (old_plan.expect("old plan"), lp_plan.expect("LP plan"));
    assert_eq!((old_plan.k, lp_plan.k), (10, 4));
    let queries: [(SmtProperty, Vec<String>, &str); 5] = [
        (SmtProperty::place_bound("budget", 2), vec![], "sat"),
        (SmtProperty::place_bound("branchA", 2), vec![], "sat"),
        (SmtProperty::place_bound("branchA", 1), vec![], "unsat"),
        (SmtProperty::place_bound("merged", 2), vec![], "unsat"),
        (SmtProperty::place_bound("pending", 2), vec![], "sat"),
    ];
    let mut decided = 0;
    for (property, sinks, expected) in queries {
        let mut answers = Vec::new();
        for plan in [&old_plan, &lp_plan] {
            let enc = name_coloured_encoder::encode_coloured(plan, &flat, &built.initial, &property, &[], &sinks, &[], &[])
                .expect("encodes");
            let start = std::time::Instant::now();
            answers.push(spacer(&enc.smt2));
            eprintln!("[slot-bound LP] k={} {property:?}: {} in {:?}", plan.k, answers.last().unwrap(), start.elapsed());
        }
        assert_eq!(answers[1], expected, "LP k: {property:?}");
        assert!(answers[0] == expected || answers[0] == "unknown", "old k: {property:?} {answers:?}");
        decided += usize::from(answers[0] == expected);
    }
    assert!(decided >= 3, "the old k decided only {decided} queries");
}
