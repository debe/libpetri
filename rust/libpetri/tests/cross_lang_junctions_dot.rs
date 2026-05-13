//! Cross-language DOT byte-parity fixture: builds a net that exercises both
//! XOR-junction and AND-junction synthesis (per EXP-012) in a single
//! transition's output tree. The transition fires from one input place to a
//! combined output spec `AND(XOR(a, b), c)` — yielding one AND junction and
//! one nested XOR junction.
//!
//! Mirrors `java/src/test/java/org/libpetri/export/CrossLangJunctionsDot.java`
//! and `typescript/scripts/cross-lang-junctions-dot.ts`. Consumed by
//! `scripts/cross-lang-dot-parity.sh`.

use std::env;
use std::fs;
use std::path::PathBuf;

use libpetri::core::input::one;
use libpetri::core::output::{and_places, out_place, xor_places};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::transition::Transition;
use libpetri_export::dot_exporter::dot_export;

fn workspace_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .map(PathBuf::from)
        .unwrap_or(manifest)
}

#[test]
fn emits_junctions_complex_dot() {
    // Net layout — every junction-target place is "pre-seeded" into the
    // mapper's place-analysis map by an earlier source transition so the
    // junction-emitting transition's unordered Out.allPlaces() traversal
    // does NOT determine the place declaration order in the final DOT.
    // This works around an arc-iteration-order divergence in Java's
    // Out.allPlaces() (HashSet-backed, JVM-randomised).
    let src_a = Place::<String>::new("srcA");
    let src_b = Place::<String>::new("srcB");
    let src_c = Place::<String>::new("srcC");
    let src_d = Place::<String>::new("srcD");
    let a = Place::<String>::new("a");
    let b = Place::<String>::new("b");
    let c = Place::<String>::new("c");
    let d = Place::<String>::new("d");
    let src_xor = Place::<String>::new("srcXor");
    let src_and = Place::<String>::new("srcAnd");

    // Seed transitions: register each leaf place into the analysis map in
    // pre-order before any junction-bearing transition is examined.
    let seed_a = Transition::builder("seedA")
        .input(one(&src_a))
        .output(out_place(&a))
        .build();
    let seed_b = Transition::builder("seedB")
        .input(one(&src_b))
        .output(out_place(&b))
        .build();
    let seed_c = Transition::builder("seedC")
        .input(one(&src_c))
        .output(out_place(&c))
        .build();
    let seed_d = Transition::builder("seedD")
        .input(one(&src_d))
        .output(out_place(&d))
        .build();

    // The junction transitions — these are what actually exercise EXP-012.
    let t_xor = Transition::builder("routeXor")
        .input(one(&src_xor))
        .output(xor_places(&[&a, &b]))
        .build();

    let t_and = Transition::builder("routeAnd")
        .input(one(&src_and))
        .output(and_places(&[&c.as_ref(), &d.as_ref()]))
        .build();

    let net = PetriNet::builder("junctions")
        .transition(seed_a)
        .transition(seed_b)
        .transition(seed_c)
        .transition(seed_d)
        .transition(t_xor)
        .transition(t_and)
        .build();

    let dot = dot_export(&net, None);

    let out_path = match env::var("LIBPETRI_CROSS_LANG_OUT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => workspace_root().join("target/cross-lang-junctions-dot/rust.dot"),
    };
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).expect("create parent dir for cross-lang DOT output");
    }
    fs::write(&out_path, &dot).expect("write cross-lang DOT output");
}
