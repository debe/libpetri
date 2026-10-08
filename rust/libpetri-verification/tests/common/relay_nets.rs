//! Row-built nets for the \[NU-054\] join-relay fixtures: the PNID
//! transcriptions of `research/net-metrics/validation/pnid/src/nets.ts` the
//! spec's test derivation names, plus the AC3 join chain and a correlated
//! self-loop. Row for row the nets of TypeScript's `tests/fixtures/pnid-nets.ts`
//! and Java's `JoinRelayTest`.
//!
//! Every place holds `String` tokens whose value is their own name; a row
//! consumes each input once and produces each output once.

#![allow(dead_code)]

use libpetri_core::action::fork;
use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{and, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;

/// One transition: name, inputs, outputs, match keys, relay targets.
pub type Row = (String, Vec<String>, Vec<String>, Vec<String>, Vec<String>);

fn strs(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|s| s.to_string()).collect()
}

/// A row without a match.
pub fn t(name: &str, ins: &[&str], outs: &[&str]) -> Row {
    (name.into(), strs(ins), strs(outs), Vec::new(), Vec::new())
}

/// A matched join on `keys`, relaying to `relays`.
pub fn j(name: &str, ins: &[&str], outs: &[&str], keys: &[&str], relays: &[&str]) -> Row {
    (name.into(), strs(ins), strs(outs), strs(keys), strs(relays))
}

fn key(s: &String) -> NameId {
    NameId::new(s.clone())
}

pub fn pnid_net(name: &str, rows: &[Row]) -> PetriNet {
    let p = |n: &str| Place::<String>::new(n);
    let mut transitions = Vec::with_capacity(rows.len());
    for (tname, ins, outs, keys, relays) in rows {
        let mut b = Transition::builder(tname.as_str());
        for i in ins {
            b = b.input(one(&p(i)));
        }
        if !outs.is_empty() {
            let out = if outs.len() == 1 {
                out_place(&p(&outs[0]))
            } else {
                and(outs.iter().map(|o| out_place(&p(o))).collect())
            };
            b = b.output(out).action(fork());
        }
        if !keys.is_empty() {
            let mut ms = MatchSpec::builder();
            for k in keys {
                ms = ms.key(&p(k), key);
            }
            for r in relays {
                ms = ms.relay_to(&p(r), key);
            }
            b = b.match_spec(ms.build());
        }
        transitions.push(b.build());
    }
    PetriNet::builder(name).transitions(transitions).build()
}

/// Drops every relay declaration: the same net as the analysers saw it before NU-054.
pub fn without_relays(rows: &[Row]) -> Vec<Row> {
    rows.iter()
        .map(|(n, i, o, k, _)| (n.clone(), i.clone(), o.clone(), k.clone(), Vec::new()))
        .collect()
}

/// P Fig. 12(c), resource closure 2: `e` rejoins the branches onto `P5`, a key
/// of the `f` / `g` joins. Carriers P1, B1, B2, C1, D1; budget R.
pub fn fig_12c() -> Vec<Row> {
    vec![
        t("a", &["R"], &["P1", "OR"]),
        t("b", &["P1"], &["B1", "B2"]),
        t("c", &["B1"], &["C1"]),
        t("d", &["B2"], &["D1"]),
        j("e", &["C1", "D1"], &["P5"], &["C1", "D1"], &["P5"]),
        j("f", &["P5", "OR"], &["R"], &["P5", "OR"], &[]),
        j("g", &["P5", "OR"], &["R"], &["P5", "OR"], &[]),
    ]
}

pub const FIG_12C_CARRIERS: [&str; 5] = ["P1", "B1", "B2", "C1", "D1"];

/// P Fig. 6(a) N1, correlated: `B` writes the case back onto its own key `Y1`
/// and onto `w`, `q`; `D` onto its key `Y2` and `r`. Budget SUPPLY.
pub fn n1_corr() -> Vec<Row> {
    vec![
        t("A", &["SUPPLY"], &["Y1", "p"]),
        j("B", &["p", "Y1"], &["Y1", "w", "q"], &["p", "Y1"], &["Y1", "w", "q"]),
        t("C", &["Y1"], &["Y2"]),
        j("D", &["q", "w", "Y2"], &["Y2", "r"], &["q", "w", "Y2"], &["Y2", "r"]),
        j("E", &["Y2", "r"], &["E_done"], &["Y2", "r"], &[]),
    ]
}

/// S union N ⊕ M: the join `b` on (`p`, `s`) relays to the carrier `q`; `c`
/// relays `q` into `s` and `r`; `d` drains `r`. Budget SUPPLY, carrier q.
pub fn s_union() -> Vec<Row> {
    vec![
        t("a", &["SUPPLY"], &["p"]),
        j("b", &["p", "s"], &["q"], &["p", "s"], &["q"]),
        t("c", &["q"], &["s", "r"]),
        t("d", &["r"], &["d_done"]),
    ]
}

/// AC3 join chain: `fork` co-mints onto `A`, `B`, `D`; `j1` relays to `C`; `j2`
/// joins `C`, `D` onto `done`.
pub fn join_chain() -> Vec<Row> {
    vec![
        t("fork", &["S"], &["A", "B", "D"]),
        j("j1", &["A", "B"], &["C"], &["A", "B"], &["C"]),
        j("j2", &["C", "D"], &["done"], &["C", "D"], &[]),
    ]
}

/// AC3 variant: `D` comes from a second, independent mint.
pub fn join_chain_split() -> Vec<Row> {
    vec![
        t("fork", &["S"], &["A", "B"]),
        t("mint2", &["S2"], &["D"]),
        j("j1", &["A", "B"], &["C"], &["A", "B"], &["C"]),
        j("j2", &["C", "D"], &["done"], &["C", "D"], &[]),
    ]
}

/// Correlated self-loop: `B` joins `p, Y` and writes the name back onto its own
/// key `Y` and onto `q`; `D` joins `q, Y`. With `independent_q` the `q` token
/// comes from a second mint, so `D` never finds one name on both.
pub fn self_loop(independent_q: bool) -> Vec<Row> {
    let mut rows = vec![t("A", &["S"], &["p", "Y"])];
    if independent_q {
        rows.push(t("A2", &["T"], &["q"]));
        rows.push(j("B", &["p", "Y"], &["Y", "x"], &["p", "Y"], &["Y"]));
    } else {
        rows.push(j("B", &["p", "Y"], &["Y", "q"], &["p", "Y"], &["Y", "q"]));
    }
    rows.push(j("D", &["q", "Y"], &["done"], &["q", "Y"], &[]));
    rows
}

/// \[NU-055\] The search-as-you-type net of the worked example, row for row the nets of
/// `spec/verification-fixtures/nu-aligned-fixtures.json`: `apply` joins `reply` and `box` by
/// name and relays to `box` and `staged`; the buggy variant's `apply_bug` takes any reply.
/// Mints `sendA`, `sendB`; carriers `inflightA`, `inflightB`, `list` (and, for the buggy
/// variant, `box`, `reply`, `staged`).
pub fn search_as_you_type(bug: bool) -> Vec<Row> {
    vec![
        t("first", &["idle", "typed"], &["armedA"]),
        t("retire", &["box", "typed"], &["armedB"]),
        t("sendA", &["armedA"], &["box", "inflightA"]),
        t("sendB", &["armedB"], &["box", "inflightB"]),
        t("fetchA", &["inflightA"], &["reply"]),
        t("fetchB", &["inflightB"], &["reply"]),
        if bug {
            t("apply_bug", &["reply", "slot"], &["staged", "clr"])
        } else {
            j("apply", &["reply", "box", "slot"], &["box", "staged", "clr"], &["reply", "box"], &["box", "staged"])
        },
        t("clearNone", &["listEmpty", "clr"], &["ready"]),
        t("clear", &["list", "clr"], &["ready"]),
        t("show", &["staged", "ready"], &["list", "slot"]),
    ]
}
