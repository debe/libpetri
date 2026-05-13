//! Cross-language DOT byte-parity fixture: builds a plain non-composed
//! [`PetriNet`] (no subnet composition, no clusters in the rendered DOT)
//! and writes the resulting DOT to the path supplied via the
//! `LIBPETRI_CROSS_LANG_OUT` environment variable (or
//! `target/cross-lang-flat-dot/rust.dot` under the workspace root by default).
//!
//! Mirrors `java/src/test/java/org/libpetri/export/CrossLangFlatDot.java`
//! and `typescript/scripts/cross-lang-flat-dot.ts`. Consumed by
//! `scripts/cross-lang-dot-parity.sh`.

use std::env;
use std::fs;
use std::path::PathBuf;

use libpetri::core::input::one;
use libpetri::core::output::out_place;
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
fn emits_flat_non_composed_dot() {
    let p1 = Place::<String>::new("p1");
    let p2 = Place::<String>::new("p2");

    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .build();

    let net = PetriNet::builder("flat")
        .place(p1.as_ref())
        .place(p2.as_ref())
        .transition(t1)
        .build();

    let dot = dot_export(&net, None);

    let out_path = match env::var("LIBPETRI_CROSS_LANG_OUT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => workspace_root().join("target/cross-lang-flat-dot/rust.dot"),
    };
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).expect("create parent dir for cross-lang DOT output");
    }
    fs::write(&out_path, &dot).expect("write cross-lang DOT output");
}
