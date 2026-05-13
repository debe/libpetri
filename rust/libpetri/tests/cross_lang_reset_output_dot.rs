//! Cross-language DOT byte-parity fixture: builds a net where a transition
//! both outputs to a place and resets the same place — the renderer must
//! collapse the two arcs into a single combined edge per EXP-013.
//!
//! Mirrors `java/src/test/java/org/libpetri/export/CrossLangResetOutputDot.java`
//! and `typescript/scripts/cross-lang-reset-output-dot.ts`. Consumed by
//! `scripts/cross-lang-dot-parity.sh`.

use std::env;
use std::fs;
use std::path::PathBuf;

use libpetri::core::arc::reset;
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
fn emits_reset_output_collapse_dot() {
    let cache = Place::<String>::new("cache");

    // refresh: outputs to cache AND resets cache -> single combined edge.
    let refresh = Transition::builder("refresh")
        .output(out_place(&cache))
        .reset(reset(&cache))
        .build();

    let net = PetriNet::builder("reset_collapse")
        .place(cache.as_ref())
        .transition(refresh)
        .build();

    let dot = dot_export(&net, None);

    let out_path = match env::var("LIBPETRI_CROSS_LANG_OUT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => workspace_root().join("target/cross-lang-reset-output-dot/rust.dot"),
    };
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).expect("create parent dir for cross-lang DOT output");
    }
    fs::write(&out_path, &dot).expect("write cross-lang DOT output");
}
