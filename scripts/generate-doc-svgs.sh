#!/usr/bin/env bash
# Generates committed SVG diagrams for libpetri-core and libpetri-export crate docs.
#
# These SVGs are committed to source control because libpetri-docgen depends on
# libpetri-core and libpetri-export, so they can't use build.rs without a cycle.
#
# Run from the repository root:
#   scripts/generate-doc-svgs.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$ROOT_DIR/rust"

CORE_DOC_DIR="$RUST_DIR/libpetri-core/doc"
EXPORT_DOC_DIR="$RUST_DIR/libpetri-export/doc"

mkdir -p "$CORE_DOC_DIR" "$EXPORT_DOC_DIR"

# Build and run a temporary binary that generates the SVGs
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

cat > "$TMPDIR/Cargo.toml" << TOML
[package]
name = "generate-doc-svgs"
version = "0.0.0"
edition = "2024"
publish = false

[dependencies]
libpetri-docgen = { path = "$RUST_DIR/libpetri-docgen" }
TOML

mkdir -p "$TMPDIR/src"
cat > "$TMPDIR/src/main.rs" << 'RUST'
use libpetri_docgen::*;
use libpetri_docgen::export::graph::RankDir;
use libpetri_docgen::export::mapper::DotConfig;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let core_doc_dir = &args[1];
    let export_doc_dir = &args[2];

    // --- libpetri-core: arc_types.svg ---
    generate_arc_types(core_doc_dir);

    // --- libpetri-core: timing_modes.svg ---
    generate_timing_modes(core_doc_dir);

    // --- libpetri-export: export_example.svg ---
    generate_export_example(export_doc_dir);

    eprintln!("Generated SVGs in {core_doc_dir} and {export_doc_dir}");
}

/// All 5 arc types on one transition.
fn generate_arc_types(out_dir: &str) {
    let source = Place::<i32>::new("source");
    let result = Place::<i32>::new("result");
    let blocked = Place::<i32>::new("blocked");
    let context = Place::<String>::new("context");
    let cleared = Place::<i32>::new("cleared");

    let process = Transition::builder("process")
        .input(one(&source))
        .output(out_place(&result))
        .inhibitor(inhibitor(&blocked))
        .read(read(&context))
        .reset(reset(&cleared))
        .action(fork())
        .build();

    let net = PetriNet::builder("ArcTypes")
        .transition(process)
        .build();

    SvgGenerator::new()
        .out_dir(out_dir)
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            show_types: true,
            ..DotConfig::default()
        })
        .generate("arc_types", &net);
}

/// Chain of 5 transitions showing each timing variant.
fn generate_timing_modes(out_dir: &str) {
    let p0 = Place::<i32>::new("p0");
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");
    let p4 = Place::<i32>::new("p4");
    let p5 = Place::<i32>::new("p5");

    let t_immediate = Transition::builder("immediate")
        .input(one(&p0))
        .output(out_place(&p1))
        .timing(immediate())
        .action(fork())
        .build();

    let t_deadline = Transition::builder("deadline")
        .input(one(&p1))
        .output(out_place(&p2))
        .timing(deadline(5000))
        .action(fork())
        .build();

    let t_delayed = Transition::builder("delayed")
        .input(one(&p2))
        .output(out_place(&p3))
        .timing(delayed(1000))
        .action(fork())
        .build();

    let t_window = Transition::builder("window")
        .input(one(&p3))
        .output(out_place(&p4))
        .timing(window(200, 5000))
        .action(fork())
        .build();

    let t_exact = Transition::builder("exact")
        .input(one(&p4))
        .output(out_place(&p5))
        .timing(exact(3000))
        .action(fork())
        .build();

    let net = PetriNet::builder("TimingModes")
        .transition(t_immediate)
        .transition(t_deadline)
        .transition(t_delayed)
        .transition(t_window)
        .transition(t_exact)
        .build();

    SvgGenerator::new()
        .out_dir(out_dir)
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            show_types: false,
            show_intervals: true,
            ..DotConfig::default()
        })
        .generate("timing_modes", &net);
}

/// Small net showing the export pipeline in action.
fn generate_export_example(out_dir: &str) {
    let input = Place::<String>::new("input");
    let processing = Place::<String>::new("processing");
    let done = Place::<String>::new("done");
    let errors = Place::<String>::new("errors");
    let config = Place::<String>::new("config");

    let validate = Transition::builder("validate")
        .input(one(&input))
        .read(read(&config))
        .output(out_place(&processing))
        .timing(immediate())
        .action(fork())
        .build();

    let complete = Transition::builder("complete")
        .input(one(&processing))
        .output(xor_places(&[&done, &errors]))
        .timing(delayed(500))
        .action(fork())
        .build();

    let net = PetriNet::builder("ExportExample")
        .transition(validate)
        .transition(complete)
        .build();

    SvgGenerator::new()
        .out_dir(out_dir)
        .config(DotConfig {
            direction: RankDir::LeftToRight,
            show_types: true,
            show_intervals: true,
            ..DotConfig::default()
        })
        .generate("export_example", &net);
}
RUST

cd "$ROOT_DIR"
cargo run --manifest-path "$TMPDIR/Cargo.toml" -- "$CORE_DOC_DIR" "$EXPORT_DOC_DIR"

echo "Done. Generated SVGs:"
ls -la "$CORE_DOC_DIR"/*.svg "$EXPORT_DOC_DIR"/*.svg
