//! The shared colour-slot LP cases of [NU-053] (`spec/verification-fixtures/slot-bound-lp.json`).
//!
//! Each case is a flat net given as rows (pre and post counts per place, optionally the
//! places a reset or consume-all arc clears), the coloured places and an initial marking.
//! The inputs are written by hand; the `expected` object of every case (status, presolved
//! sizes, pivots, work, optimum, `k` and the scaled weighting) is written by the Rust
//! script-parity test under `scripts/smt-script-parity.py --update` and read by every
//! language. Test-only code, shared through `#[path]`.

#![allow(dead_code)]

use std::collections::HashMap;

use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::net_flattener::{FlatNet, FlatTransition};
use libpetri_verification::slot_bound_lp::{self, LpAnswer, SlotBound};

use super::json::Json;

/// One case, built.
pub struct LpCase {
    pub id: String,
    pub flat: FlatNet,
    pub initial: MarkingState,
    pub coloured: Vec<usize>,
}

fn counts(row: &Json, key: &str, index: &HashMap<String, usize>, n: usize) -> Vec<i64> {
    let mut v = vec![0i64; n];
    if let Some(Json::Obj(entries)) = row.get(key) {
        for (place, count) in entries {
            let Json::Num(c) = count else { panic!("count of '{place}' is not a number") };
            v[*index.get(place).unwrap_or_else(|| panic!("unknown place '{place}'"))] += *c as i64;
        }
    }
    v
}

fn indices(row: &Json, key: &str, index: &HashMap<String, usize>) -> Vec<usize> {
    row.str_arr_opt(key).iter().map(|p| index[p]).collect()
}

/// Builds a case from its JSON object.
pub fn build(case: &Json) -> LpCase {
    let places: Vec<String> = case.str_arr_opt("places");
    let n = places.len();
    let index: HashMap<String, usize> = places.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
    let transitions = case
        .arr("rows")
        .iter()
        .map(|row| {
            FlatTransition::new(row.str("name"), counts(row, "pre", &index, n), counts(row, "post", &index, n))
                .with_reset_places(indices(row, "reset", &index))
                .with_consume_all(indices(row, "consumeAll", &index))
        })
        .collect();
    let mut coloured: Vec<usize> = case.str_arr_opt("coloured").iter().map(|p| index[p]).collect();
    coloured.sort_unstable();
    let mut initial = MarkingStateBuilder::new();
    if let Some(Json::Obj(entries)) = case.get("marking") {
        for (place, count) in entries {
            let Json::Num(c) = count else { panic!("marking of '{place}' is not a number") };
            initial = initial.tokens(place.clone(), *c as usize);
        }
    }
    LpCase {
        id: case.str("id").to_string(),
        flat: FlatNet { places, place_index: index, place_count: n, transitions },
        initial: initial.build(),
        coloured,
    }
}

/// What the simplex and the checker give on a case, as the `expected` object.
pub fn expected(case: &LpCase) -> Json {
    let (answer, counts) = slot_bound_lp::solve_counted(&case.flat, &case.initial, &case.coloured);
    let mut fields: Vec<(String, Json)> = Vec::new();
    let num = |v: usize| Json::Num(v as f64);
    let status = match &answer {
        LpAnswer::Optimal { .. } => "optimal",
        LpAnswer::Infeasible { .. } => "infeasible",
        LpAnswer::TooLarge { .. } => "too-large",
        LpAnswer::WorkLimit { .. } => "work-limit",
        LpAnswer::CoefficientLimit { .. } => "coefficient-limit",
        LpAnswer::Stopped => "stopped",
        other => panic!("unknown answer {other:?}"),
    };
    fields.push(("status".into(), Json::Str(status.into())));
    match &answer {
        LpAnswer::Optimal { places, rows, .. }
        | LpAnswer::Infeasible { places, rows }
        | LpAnswer::TooLarge { places, rows } => {
            fields.push(("places".into(), num(*places)));
            fields.push(("rows".into(), num(*rows)));
        }
        _ => {}
    }
    fields.push(("pivots".into(), num(counts.pivots)));
    fields.push(("work".into(), num(counts.work as usize)));
    if let LpAnswer::Optimal { cover, .. } = &answer {
        let bound = slot_bound_lp::checked(&case.flat, &case.initial, &case.coloured, answer.clone());
        let SlotBound::Bound { k, value, .. } = bound else {
            panic!("[{}] the simplex's weighting failed the re-check: {bound:?}", case.id)
        };
        fields.push(("optimum".into(), Json::Str(value.to_string())));
        fields.push(("k".into(), num(k)));
        fields.push((
            "weights".into(),
            Json::Obj(
                case.flat
                    .places
                    .iter()
                    .zip(&cover.weights)
                    .filter(|(_, w)| !w.is_zero())
                    .map(|(p, w)| (p.clone(), Json::Str(w.to_string())))
                    .collect(),
            ),
        ));
        fields.push(("denominator".into(), Json::Str(cover.denominator.to_string())));
    }
    Json::Obj(fields)
}

fn compact(v: &Json) -> String {
    match v {
        Json::Null => "null".into(),
        Json::Bool(b) => b.to_string(),
        Json::Num(n) if n.fract() == 0.0 => format!("{}", *n as i64),
        Json::Num(n) => n.to_string(),
        Json::Str(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
        Json::Arr(items) => format!("[{}]", items.iter().map(compact).collect::<Vec<_>>().join(", ")),
        Json::Obj(entries) => format!(
            "{{{}}}",
            entries.iter().map(|(k, v)| format!("\"{k}\": {}", compact(v))).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// Pretty JSON: a value whose compact form fits in 100 columns stays on one line.
pub fn pretty(v: &Json, indent: usize) -> String {
    let flat = compact(v);
    if flat.len() + indent <= 100 {
        return flat;
    }
    let pad = " ".repeat(indent + 2);
    match v {
        Json::Arr(items) => format!(
            "[\n{}\n{}]",
            items.iter().map(|i| format!("{pad}{}", pretty(i, indent + 2))).collect::<Vec<_>>().join(",\n"),
            " ".repeat(indent)
        ),
        Json::Obj(entries) => format!(
            "{{\n{}\n{}}}",
            entries
                .iter()
                .map(|(k, v)| format!("{pad}\"{k}\": {}", pretty(v, indent + 2)))
                .collect::<Vec<_>>()
                .join(",\n"),
            " ".repeat(indent)
        ),
        _ => flat,
    }
}
