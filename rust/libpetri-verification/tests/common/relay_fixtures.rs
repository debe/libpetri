//! The \[NU-054\] relay fixtures of `spec/verification-fixtures/nu-relay-fixtures.json` (the
//! relay part of the SMT script-parity set), read with the crate's minimal JSON
//! reader and built through [`relay_nets`](super::relay_nets). Needs the `json`
//! and `relay_nets` modules beside it.

#![allow(dead_code)]

use super::relay_nets::{Row, pnid_net};
use libpetri_core::petri_net::PetriNet;

/// The relay fixtures of `spec/verification-fixtures/nu-relay-fixtures.json` (the NU-054 part
/// of the SMT script-parity set), read with the crate's minimal JSON reader.
pub fn relay_fixtures() -> Vec<super::json::Json> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../spec/verification-fixtures/nu-relay-fixtures.json");
    let raw = std::fs::read_to_string(path).expect("read nu-relay-fixtures.json");
    super::json::parse_json(&raw).arr("fixtures").to_vec()
}

/// A relay fixture's net, from its inline `rows`.
pub fn fixture_net(fixture: &super::json::Json) -> PetriNet {
    use super::json::Json;
    let list = |j: &Json| -> Vec<String> {
        match j {
            Json::Arr(items) => items
                .iter()
                .map(|it| match it {
                    Json::Str(s) => s.clone(),
                    other => panic!("expected a place name, got {other:?}"),
                })
                .collect(),
            other => panic!("expected an array, got {other:?}"),
        }
    };
    let rows: Vec<Row> = fixture
        .arr("rows")
        .iter()
        .map(|row| match row {
            Json::Arr(cells) if cells.len() == 5 => {
                let Json::Str(name) = &cells[0] else {
                    panic!("row without a transition name: {row:?}")
                };
                (name.clone(), list(&cells[1]), list(&cells[2]), list(&cells[3]), list(&cells[4]))
            }
            other => panic!("malformed relay fixture row {other:?}"),
        })
        .collect();
    pnid_net(fixture.str("net"), &rows)
}

/// A relay fixture's initial marking, from its `marking` object.
pub fn fixture_marking(fixture: &super::json::Json) -> Vec<(String, usize)> {
    use super::json::Json;
    match fixture.get("marking") {
        Some(Json::Obj(entries)) => entries
            .iter()
            .map(|(p, v)| match v {
                Json::Num(n) => (p.clone(), *n as usize),
                other => panic!("expected a token count for '{p}', got {other:?}"),
            })
            .collect(),
        other => panic!("expected a marking object, got {other:?}"),
    }
}
