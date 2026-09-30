//! Loader for the conformance corpus schema
//! (`spec/verification-fixtures/conformance/README.md`): one `nets/<id>.json`
//! becomes a real [`PetriNet`], its initial [`MarkingState`] and its properties.
//!
//! Exactly the schema's semantics, nothing inferred:
//! * `places` are the **declared** places, put on the net builder whether or not
//!   an arc names them; an arc may name a place `places` omits (a place by use);
//! * `marking` may name a place that no arc touches and `places` omits — an inert
//!   place ([CORE-072]); it goes into the marking only;
//! * inputs `one` / `exactly` / `all` / `atLeast` ([IO-001]–[IO-004]), at most one
//!   per place per transition ([CORE-030]); inhibitor / read / reset arcs;
//! * output trees `place` / `and` / `xor` / `timeout` / `forward` ([IO-011]–[IO-016]),
//!   `null` or absent meaning no output; a `forward`'s `from` must be an input place;
//! * `timing` (`{"kind", "earliestMs", "latestMs"}`, absent = immediate) onto the
//!   transition's [`Timing`] ([TIME-002]–[TIME-006]); `deadline` / `window` are
//!   reapable ([TIME-013]), which the verifier reads for reap-quiescence ([VER-002]).
//!
//! A malformed net panics with the net id and the offending field: the corpus is
//! generated, so a loader error is a generator or loader bug, never data to skip.

#![allow(dead_code)]

use std::collections::HashSet;

use libpetri_core::action::fork;
use libpetri_core::arc::{inhibitor, read, reset};
use libpetri_core::input;
use libpetri_core::output::{self, Out};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::{Place, PlaceRef};
use libpetri_core::timing::{self, Timing};
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;

use crate::json::Json;

/// One property of a corpus net.
#[derive(Debug, Clone)]
pub struct CorpusProperty {
    pub id: String,
    /// The schema's `type`, kept for reporting.
    pub kind: String,
    pub property: SmtProperty,
    /// `sinks` of `deadlock-free` / `terminates-at-sink`; empty otherwise.
    pub sinks: Vec<String>,
}

/// A loaded corpus net.
pub struct CorpusNet {
    pub id: String,
    pub net: PetriNet,
    pub marking: MarkingState,
    pub properties: Vec<CorpusProperty>,
    /// Transition names in file order, to map a verifier's branch-suffixed name
    /// (`t_b1`) back to the net's own.
    pub transition_names: Vec<String>,
}

impl CorpusNet {
    /// The net's own name for a verifier trace step: the name itself when the net
    /// has such a transition, else the name with the flattener's `_b<k>` branch
    /// suffix removed when that is one.
    pub fn transition_name(&self, step: &str) -> String {
        if self.transition_names.iter().any(|n| n == step) {
            return step.to_string();
        }
        if let Some(pos) = step.rfind("_b") {
            let digits = &step[pos + 2..];
            if !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()) {
                let base = &step[..pos];
                if self.transition_names.iter().any(|n| n == base) {
                    return base.to_string();
                }
            }
        }
        step.to_string()
    }
}

fn place(name: &str) -> Place<i32> {
    Place::<i32>::new(name)
}

fn strings(v: &Json, key: &str, id: &str) -> Vec<String> {
    match v.get(key) {
        None | Some(Json::Null) => Vec::new(),
        Some(Json::Arr(items)) => items
            .iter()
            .map(|x| match x {
                Json::Str(s) => s.clone(),
                other => panic!("{id}: `{key}` holds a non-string {other:?}"),
            })
            .collect(),
        Some(other) => panic!("{id}: `{key}` is not an array: {other:?}"),
    }
}

fn count(v: &Json, key: &str, id: &str) -> usize {
    match v.get(key) {
        Some(Json::Num(n)) if *n >= 0.0 && n.fract() == 0.0 => *n as usize,
        other => panic!("{id}: `{key}` is not a whole number: {other:?}"),
    }
}

fn output_of(o: &Json, inputs: &HashSet<String>, id: &str, t: &str) -> Out {
    match o.str("type") {
        "place" => output::out_place(&place(o.str("place"))),
        "and" => {
            let cs = o.arr("children");
            assert!(!cs.is_empty(), "{id}/{t}: `and` with no children");
            output::and(cs.iter().map(|c| output_of(c, inputs, id, t)).collect())
        }
        "xor" => {
            let cs = o.arr("children");
            assert!(cs.len() >= 2, "{id}/{t}: `xor` needs at least two children");
            output::xor(cs.iter().map(|c| output_of(c, inputs, id, t)).collect())
        }
        "timeout" => {
            let ms = count(o, "afterMs", id) as u64;
            assert!(ms > 0, "{id}/{t}: `timeout.afterMs` must be positive");
            let child = o.get("child").unwrap_or_else(|| panic!("{id}/{t}: `timeout` without `child`"));
            output::timeout(ms, output_of(child, inputs, id, t))
        }
        "forward" => {
            let from = o.str("from");
            assert!(inputs.contains(from), "{id}/{t}: `forward.from` '{from}' is not an input place");
            output::forward_input(&place(from), &place(o.str("to")))
        }
        other => panic!("{id}/{t}: unknown output type '{other}'"),
    }
}

fn property_of(p: &Json, id: &str) -> CorpusProperty {
    let pid = p.str("id").to_string();
    let kind = p.str("type").to_string();
    let mut sinks = Vec::new();
    let property = match kind.as_str() {
        "deadlock-free" => {
            sinks = strings(p, "sinks", id);
            SmtProperty::DeadlockFree
        }
        "terminates-at-sink" => {
            sinks = strings(p, "sinks", id);
            SmtProperty::TerminatesAtSink
        }
        "place-bound" => SmtProperty::place_bound(p.str("place"), count(p, "bound", id)),
        "mutual-exclusion" => SmtProperty::mutual_exclusion(strings(p, "places", id)),
        "unreachable" => SmtProperty::unreachable(strings(p, "places", id)),
        "quiescent-count" => {
            let min = count(p, "min", id);
            let max = match p.get("max") {
                None | Some(Json::Null) => None,
                Some(_) => Some(count(p, "max", id)),
            };
            assert!(max.is_none_or(|m| m >= min), "{id}/{pid}: quiescent-count max < min");
            SmtProperty::quiescent_count(strings(p, "places", id), min, max, Vec::new())
        }
        other => panic!("{id}/{pid}: unknown property type '{other}'"),
    };
    CorpusProperty { id: pid, kind, property, sinks }
}

/// A transition's `timing` object ([TIME-002]–[TIME-006]).
fn timing_of(tm: &Json, id: &str, name: &str) -> Timing {
    let ms = |k: &str| -> u64 {
        match tm.get(k) {
            Some(Json::Num(v)) if *v >= 0.0 && v.fract() == 0.0 => *v as u64,
            other => panic!("{id}/{name}: timing `{k}` is not a whole number: {other:?}"),
        }
    };
    match tm.str("kind") {
        "immediate" | "unconstrained" => timing::immediate(),
        "deadline" => timing::deadline(ms("latestMs")),
        "delayed" => timing::delayed(ms("earliestMs")),
        "window" => timing::window(ms("earliestMs"), ms("latestMs")),
        "exact" => timing::exact(ms("earliestMs")),
        other => panic!("{id}/{name}: unknown timing kind '{other}'"),
    }
}

/// Builds a corpus net from its parsed JSON document.
pub fn load_net(doc: &Json) -> CorpusNet {
    let id = doc.str("id").to_string();
    let mut nb = PetriNet::builder(id.as_str());
    let mut transition_names = Vec::new();
    for t in doc.arr("transitions") {
        let name = t.str("name");
        assert!(!transition_names.iter().any(|n: &String| n == name), "{id}: transition '{name}' twice");
        transition_names.push(name.to_string());
        let mut tb = Transition::builder(name);
        let mut inputs = HashSet::new();
        for a in t.arr("inputs") {
            let p = place(a.str("place"));
            assert!(inputs.insert(a.str("place").to_string()), "{id}/{name}: two input arcs on '{}' (CORE-030)", a.str("place"));
            tb = tb.input(match a.str("kind") {
                "one" => input::one(&p),
                "exactly" => {
                    let n = count(a, "n", &id);
                    assert!(n >= 1, "{id}/{name}: exactly needs n >= 1");
                    input::exactly(n, &p)
                }
                "all" => input::all(&p),
                "atLeast" => {
                    let n = count(a, "n", &id);
                    assert!(n >= 1, "{id}/{name}: atLeast needs n >= 1");
                    input::at_least(n, &p)
                }
                other => panic!("{id}/{name}: unknown input kind '{other}'"),
            });
        }
        for p in strings(t, "inhibitors", &id) {
            tb = tb.inhibitor(inhibitor(&place(&p)));
        }
        for p in strings(t, "reads", &id) {
            tb = tb.read(read(&place(&p)));
        }
        for p in strings(t, "resets", &id) {
            tb = tb.reset(reset(&place(&p)));
        }
        match t.get("output") {
            None | Some(Json::Null) => {}
            Some(o) => tb = tb.output(output_of(o, &inputs, &id, name)),
        }
        match t.get("priority") {
            None | Some(Json::Null) => {}
            Some(Json::Num(p)) => tb = tb.priority(*p as i32),
            Some(other) => panic!("{id}/{name}: `priority` is not a number: {other:?}"),
        }
        match t.get("timing") {
            None | Some(Json::Null) => {}
            Some(tm) => tb = tb.timing(timing_of(tm, &id, name)),
        }
        nb = nb.transition(tb.action(fork()).build());
    }
    for p in strings(doc, "places", &id) {
        nb = nb.place(PlaceRef::new(p.as_str()));
    }
    let mut mb = MarkingStateBuilder::new();
    match doc.get("marking") {
        None | Some(Json::Null) => {}
        Some(Json::Obj(entries)) => {
            for (p, n) in entries {
                match n {
                    Json::Num(k) if *k >= 0.0 && k.fract() == 0.0 => {
                        if *k > 0.0 {
                            mb = mb.tokens(p.clone(), *k as usize);
                        }
                    }
                    other => panic!("{id}: marking of '{p}' is not a whole number: {other:?}"),
                }
            }
        }
        Some(other) => panic!("{id}: `marking` is not an object: {other:?}"),
    }
    let properties = doc.arr("properties").iter().map(|p| property_of(p, &id)).collect();
    CorpusNet { id, net: nb.build(), marking: mb.build(), properties, transition_names }
}
