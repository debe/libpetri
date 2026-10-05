//! The colour-slot linear program of [NU-053] on the seeded composed workflow of the shared
//! parity cases (255 places, 341 flat rows, three keys, a budget of 2): the exact simplex
//! and the re-check `build_plan` runs on its answer. The target is below 50 ms in a release
//! build; the semiflow enumeration it replaced took about 10 s on a net of this size.

use std::hint::black_box;

use criterion::{Criterion, criterion_group, criterion_main};

use libpetri_verification::slot_bound_lp;

#[path = "../../libpetri-verification/tests/common/json.rs"]
mod json;
#[path = "../../libpetri-verification/tests/common/slot_lp_cases.rs"]
mod slot_lp_cases;

fn composed_workflow() -> slot_lp_cases::LpCase {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../spec/verification-fixtures/slot-bound-lp.json");
    let doc = json::parse_json(&std::fs::read_to_string(path).expect("read slot-bound-lp.json"));
    let case = doc
        .arr("cases")
        .iter()
        .find(|c| c.str("id") == "composed-workflow-7")
        .expect("the composed workflow case");
    slot_lp_cases::build(case)
}

fn slot_bound(c: &mut Criterion) {
    let case = composed_workflow();
    c.bench_function("slot_bound_lp/composed_workflow_255x341", |b| {
        b.iter(|| {
            let answer = slot_bound_lp::solve(&case.flat, &case.initial, &case.coloured);
            let bound = slot_bound_lp::checked(&case.flat, &case.initial, &case.coloured, answer);
            assert_eq!(bound.k(), Some(6));
            black_box(bound)
        })
    });
}

criterion_group!(benches, slot_bound);
criterion_main!(benches);
