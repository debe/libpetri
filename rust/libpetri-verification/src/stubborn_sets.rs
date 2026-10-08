//! Stubborn sets of [VER-024]: at each class the enumeration expands only the
//! enabled transitions of one stubborn set, which keeps every reachable dead
//! marking (`lean/Libpetri/Novel/Stubborn.lean`). Footprints and indexes are
//! computed once per net; places are compared by name.

use std::collections::{BTreeSet, HashMap};

use libpetri_core::input::{In, required_count};
use libpetri_core::petri_net::PetriNet;

use crate::branch_outcomes;
use crate::marking_state::MarkingState;

/// One enabling condition: a place that needs `need` tokens, or none for an inhibitor.
struct Condition {
    place: String,
    need: usize,
    inhibitor: bool,
}

/// The footprints of a net's transitions, and the closure that picks a stubborn set.
pub(crate) struct StubbornSets {
    names: Vec<String>,
    index: HashMap<String, usize>,
    /// Per transition, every other transition dependent with it.
    dependents: Vec<Vec<usize>>,
    /// Per transition, its enabling conditions: inputs and reads by place name, then inhibitors.
    conditions: Vec<Vec<Condition>>,
    /// Per place, the transitions with an outcome depositing into it.
    increasers: HashMap<String, Vec<usize>>,
    /// Per place, the transitions with it among their inputs or resets.
    decreasers: HashMap<String, Vec<usize>>,
}

fn add(index: &mut HashMap<String, Vec<usize>>, place: &str, i: usize) {
    let list = index.entry(place.to_string()).or_default();
    if list.last() != Some(&i) {
        list.push(i);
    }
}

impl StubbornSets {
    /// Computes the footprints of every transition of `net`.
    pub(crate) fn new(net: &PetriNet) -> Self {
        let n = net.transitions().len();
        let mut names = Vec::with_capacity(n);
        let mut index = HashMap::with_capacity(n);
        let mut tests: Vec<BTreeSet<String>> = Vec::with_capacity(n);
        let mut writes: Vec<BTreeSet<String>> = Vec::with_capacity(n);
        let mut overwrites: Vec<BTreeSet<String>> = Vec::with_capacity(n);
        let mut conditions = Vec::with_capacity(n);
        let mut testers = HashMap::new();
        let mut writers = HashMap::new();
        let mut overwriters = HashMap::new();
        let mut increasers = HashMap::new();
        let mut decreasers = HashMap::new();
        for (i, t) in net.transitions().iter().enumerate() {
            names.push(t.name().to_string());
            index.insert(t.name().to_string(), i);
            let mut tst = BTreeSet::new();
            let mut wr = BTreeSet::new();
            let mut ow = BTreeSet::new();
            let mut dec = BTreeSet::new();
            let mut inc = BTreeSet::new();
            let mut enabling = Vec::new();
            for spec in t.input_specs() {
                let p = spec.place_name().to_string();
                tst.insert(p.clone());
                wr.insert(p.clone());
                dec.insert(p.clone());
                if matches!(spec, In::All { .. } | In::AtLeast { .. }) {
                    ow.insert(p.clone());
                }
                enabling.push(Condition { place: p, need: required_count(spec), inhibitor: false });
            }
            for arc in t.reads() {
                tst.insert(arc.place.name().to_string());
                enabling.push(Condition { place: arc.place.name().to_string(), need: 1, inhibitor: false });
            }
            // Stable: an input and a read on one place keep the input first. String
            // order is code-point order.
            enabling.sort_by(|x, y| x.place.cmp(&y.place));
            let inhibitors: BTreeSet<String> =
                t.inhibitors().iter().map(|a| a.place.name().to_string()).collect();
            for p in inhibitors {
                tst.insert(p.clone());
                enabling.push(Condition { place: p, need: 0, inhibitor: true });
            }
            for arc in t.resets() {
                let p = arc.place.name().to_string();
                wr.insert(p.clone());
                ow.insert(p.clone());
                dec.insert(p);
            }
            for outcome in branch_outcomes::outcomes(t) {
                for (p, _) in &outcome.deposits {
                    wr.insert(p.clone());
                    inc.insert(p.clone());
                }
            }
            for p in &tst {
                add(&mut testers, p, i);
            }
            for p in &wr {
                add(&mut writers, p, i);
            }
            for p in &ow {
                add(&mut overwriters, p, i);
            }
            for p in &inc {
                add(&mut increasers, p, i);
            }
            for p in &dec {
                add(&mut decreasers, p, i);
            }
            tests.push(tst);
            writes.push(wr);
            overwrites.push(ow);
            conditions.push(enabling);
        }
        // t and u are dependent when one writes what the other tests, or one
        // overwrites what the other writes ([VER-024] "Footprints").
        let collect = |into: &mut BTreeSet<usize>, i: usize, places: &BTreeSet<String>, by: &HashMap<String, Vec<usize>>| {
            for p in places {
                for &j in by.get(p).map(Vec::as_slice).unwrap_or(&[]) {
                    if j != i {
                        into.insert(j);
                    }
                }
            }
        };
        let dependents = (0..n)
            .map(|i| {
                let mut dep = BTreeSet::new();
                collect(&mut dep, i, &writes[i], &testers);
                collect(&mut dep, i, &tests[i], &writers);
                collect(&mut dep, i, &overwrites[i], &writers);
                collect(&mut dep, i, &writes[i], &overwriters);
                dep.into_iter().collect()
            })
            .collect();
        StubbornSets { names, index, dependents, conditions, increasers, decreasers }
    }

    /// Which of `enabled` (a class's enabled transitions, by name) to expand at
    /// `marking`: the closure, over every enabled seed, with the fewest enabled
    /// members, the code-point-smallest seed name breaking ties. One flag per entry
    /// of `enabled`, so the caller keeps its own order.
    pub(crate) fn select(&self, marking: &MarkingState, enabled: &[String]) -> Vec<bool> {
        if enabled.len() <= 1 {
            return vec![true; enabled.len()];
        }
        let mut is_enabled = vec![false; self.names.len()];
        for name in enabled {
            is_enabled[self.index[name.as_str()]] = true;
        }
        let mut seeds: Vec<&String> = enabled.iter().collect();
        seeds.sort();
        let mut best: Option<Vec<bool>> = None;
        let mut best_count = usize::MAX;
        for seed in seeds {
            let mut set = vec![false; self.names.len()];
            let count = self.closure(self.index[seed.as_str()], marking, &is_enabled, best_count, &mut set);
            if count < best_count {
                best = Some(set);
                best_count = count;
                if count == 1 {
                    break;
                }
            }
        }
        let best = best.expect("an enabled seed always closes");
        enabled.iter().map(|name| best[self.index[name.as_str()]]).collect()
    }

    /// Fills `in_set` with the closure from `seed` under D1 / D2 and returns the
    /// number of enabled members, or `bound` once it reaches it, since it can no
    /// longer win.
    fn closure(
        &self,
        seed: usize,
        marking: &MarkingState,
        is_enabled: &[bool],
        bound: usize,
        in_set: &mut [bool],
    ) -> usize {
        let mut work = vec![seed];
        in_set[seed] = true;
        let mut enabled_count = 0;
        while let Some(i) = work.pop() {
            let next: &[usize] = if is_enabled[i] {
                enabled_count += 1;
                if enabled_count >= bound {
                    return bound;
                }
                &self.dependents[i]
            } else {
                self.scapegoat(i, marking)
            };
            for &j in next {
                if !in_set[j] {
                    in_set[j] = true;
                    work.push(j);
                }
            }
        }
        enabled_count
    }

    /// D2: the transitions that can satisfy the first unsatisfied condition of
    /// disabled `i`.
    fn scapegoat(&self, i: usize, marking: &MarkingState) -> &[usize] {
        for c in &self.conditions[i] {
            let have = marking.count(&c.place);
            let unsatisfied = if c.inhibitor { have > 0 } else { have < c.need };
            if unsatisfied {
                let by = if c.inhibitor { &self.decreasers } else { &self.increasers };
                return by.get(&c.place).map(Vec::as_slice).unwrap_or(&[]);
            }
        }
        panic!(
            "stubborn set: transition '{}' is disabled with every condition satisfied",
            self.names[i]
        );
    }
}
