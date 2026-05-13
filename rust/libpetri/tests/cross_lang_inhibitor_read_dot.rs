//! Cross-language DOT byte-parity fixture: builds a net with at least one
//! Read arc and one Inhibitor arc on the same transition to verify the
//! renderer styles each distinctly and produces byte-identical DOT across
//! languages.
//!
//! Mirrors `java/src/test/java/org/libpetri/export/CrossLangInhibitorReadDot.java`
//! and `typescript/scripts/cross-lang-inhibitor-read-dot.ts`. Consumed by
//! `scripts/cross-lang-dot-parity.sh`.

use std::env;
use std::fs;
use std::path::PathBuf;

use libpetri::core::arc::{inhibitor, read};
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
fn emits_inhibitor_read_styling_dot() {
    let req = Place::<String>::new("req");
    let done = Place::<String>::new("done");
    let lock = Place::<String>::new("lock");
    let paused = Place::<String>::new("paused");

    let process = Transition::builder("process")
        .input(one(&req))
        .read(read(&lock))
        .inhibitor(inhibitor(&paused))
        .output(out_place(&done))
        .build();

    // Place ordering matches the renderer's place-analysis traversal
    // (inputs -> outputs -> inhibitors -> reads), required for byte-parity
    // because some language backends ignore the builder's place list and
    // re-derive ordering from arc iteration.
    let net = PetriNet::builder("inh_read")
        .place(req.as_ref())
        .place(done.as_ref())
        .place(paused.as_ref())
        .place(lock.as_ref())
        .transition(process)
        .build();

    let dot = dot_export(&net, None);

    let out_path = match env::var("LIBPETRI_CROSS_LANG_OUT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => workspace_root().join("target/cross-lang-inhibitor-read-dot/rust.dot"),
    };
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).expect("create parent dir for cross-lang DOT output");
    }
    fs::write(&out_path, &dot).expect("write cross-lang DOT output");
}
