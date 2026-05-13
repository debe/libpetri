//! Cross-language DOT byte-parity fixture: builds the canonical
//! producer / bounded-buffer / consumer pipeline composed via
//! [`PetriNetBuilder::compose_with`] and writes the resulting DOT to the
//! path supplied via the `LIBPETRI_CROSS_LANG_OUT` environment variable
//! (or `target/cross-lang-pipeline-dot/rust.dot` under the workspace root
//! by default).
//!
//! Mirrors `java/src/test/java/org/libpetri/export/CrossLangPipelineDot.java`
//! and `typescript/scripts/cross-lang-pipeline-dot.ts`. Consumed by
//! `scripts/cross-lang-dot-parity.sh`.
//!
//! Implemented as an integration test (rather than an example or bin) so
//! `cargo test --workspace` exercises the same export path used by the
//! parity script.

use std::env;
use std::fs;
use std::path::PathBuf;

use libpetri::core::input::one;
use libpetri::core::output::{and_places, out_place};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::transition::Transition;
use libpetri_export::dot_exporter::dot_export;

fn producer() -> SubnetDef<()> {
    let next_item = Place::<String>::new("nextItem");
    let output = Place::<String>::new("output");

    let produce = Transition::builder("produce")
        .input(one(&next_item))
        .output(out_place(&output))
        .build();

    SubnetDef::<()>::builder("Producer")
        .place(&next_item)
        .transition(produce)
        .output_port("output", &output)
        .build()
}

fn bounded_buffer(capacity: usize) -> SubnetDef<()> {
    assert!(capacity >= 1, "capacity must be >= 1, got: {capacity}");

    let put = Place::<String>::new("put");
    let get = Place::<String>::new("get");
    let items = Place::<String>::new("items");
    let slots = Place::<String>::new("slots");

    let enqueue = Transition::builder("enqueue")
        .input(one(&put))
        .input(one(&slots))
        .output(out_place(&items))
        .build();

    let dequeue = Transition::builder("dequeue")
        .input(one(&items))
        .output(and_places(&[&get.as_ref(), &slots.as_ref()]))
        .build();

    SubnetDef::<()>::builder(format!("BoundedBuffer-{capacity}"))
        .place(&items)
        .place(&slots)
        .transition(enqueue)
        .transition(dequeue)
        .input_port("put", &put)
        .output_port("get", &get)
        .build()
}

fn consumer() -> SubnetDef<()> {
    let input = Place::<String>::new("input");
    let consumed = Place::<String>::new("consumed");

    let consume = Transition::builder("consume")
        .input(one(&input))
        .output(out_place(&consumed))
        .build();

    SubnetDef::<()>::builder("Consumer")
        .place(&consumed)
        .transition(consume)
        .input_port("input", &input)
        .build()
}

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR points at the per-crate dir (rust/libpetri); the
    // workspace root is one level up.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .map(PathBuf::from)
        .unwrap_or(manifest)
}

#[test]
fn emits_canonical_pipeline_dot() {
    let prod_def = producer();
    let buf_def = bounded_buffer(2);
    let cons_def = consumer();

    let prod = prod_def.instantiate("prod", ());
    let buf = buf_def.instantiate("buf", ());
    let cons = cons_def.instantiate("cons", ());

    let producer_to_buffer = Place::<String>::new("producerToBuffer");
    let buffer_to_consumer = Place::<String>::new("bufferToConsumer");

    let net = PetriNet::builder("pipeline")
        .compose_with(&prod, |b| {
            b.bind_port::<String>("output", &producer_to_buffer);
        })
        .compose_with(&buf, |b| {
            b.bind_port::<String>("put", &producer_to_buffer)
                .bind_port::<String>("get", &buffer_to_consumer);
        })
        .compose_with(&cons, |b| {
            b.bind_port::<String>("input", &buffer_to_consumer);
        })
        .build();

    let dot = dot_export(&net, None);

    let out_path = match env::var("LIBPETRI_CROSS_LANG_OUT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => workspace_root().join("target/cross-lang-pipeline-dot/rust.dot"),
    };
    if let Some(parent) = out_path.parent() {
        fs::create_dir_all(parent).expect("create parent dir for cross-lang DOT output");
    }
    fs::write(&out_path, &dot).expect("write cross-lang DOT output");
}
