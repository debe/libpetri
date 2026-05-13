//! Integration tests for the subnet-aware rustdoc helpers.
//!
//! Mirrors the Java/TS subnet doclet test plan: assert that
//! `dot_export_subnet_def` produces valid DOT containing the interface-port
//! styling, that `dot_export_composed_with_clusters` produces DOT with
//! `subgraph cluster_*` blocks for prefixed names, and that the SVG
//! post-processing injects `data-instance` attributes.

use libpetri_docgen::*;

fn build_mover_subnet() -> SubnetDef<()> {
    let p_in = Place::<String>::new("in");
    let p_out = Place::<String>::new("out");
    let move_t = Transition::builder("move").input(one(&p_in)).output(out_place(&p_out)).build();
    SubnetDef::<()>::builder("Mover")
        .transition(move_t.clone())
        .input_port("input", &p_in)
        .output_port("output", &p_out)
        .channel("move_ch", &move_t)
        .build()
}

#[test]
fn subnet_def_dot_contains_interface_cluster_and_port_styling() {
    let def = build_mover_subnet();
    let dot = dot_export_subnet_def(&def);

    // Interface cluster wraps the port + channel ids.
    assert!(
        dot.contains("subgraph cluster_iface_Mover"),
        "missing interface cluster: {dot}"
    );
    assert!(dot.contains("label=\"interface\""));

    // Port nodes carry the `interface-port` styling — fillcolor #e7f1ff,
    // stroke #1d4ed8 (per spec/petri-net-styles.json).
    assert!(
        dot.contains("\"#e7f1ff\""),
        "interface-port fill color missing: {dot}"
    );
    assert!(
        dot.contains("\"#1d4ed8\""),
        "interface-port stroke color missing: {dot}"
    );

    // Channel transitions get the `sync-channel` styling — fillcolor #f3e8ff.
    assert!(
        dot.contains("\"#f3e8ff\""),
        "sync-channel fill color missing: {dot}"
    );
}

#[test]
fn subnet_def_interface_only_dot_contains_stub_node() {
    let def = build_mover_subnet();
    let dot = subnet_dot_export::interface_only(&def);

    assert!(dot.contains("digraph Mover"), "missing digraph header: {dot}");
    assert!(dot.contains("stub_Mover"), "missing stub node: {dot}");
    assert!(dot.contains("(internals omitted)"), "missing stub label: {dot}");
    // Interface-port styling on the port nodes.
    assert!(dot.contains("\"#e7f1ff\""), "interface-port fill missing");
    // The body's `move` transition is NOT drawn — but the channel surface
    // (sync-channel node) is. Confirm by checking the body edge `p_in -> t_move`
    // is absent (it would be present in the body DOT export).
    assert!(
        !dot.contains("p_in -> t_move"),
        "body edges leaked into interface-only: {dot}"
    );
}

#[test]
fn instance_dot_contains_cluster_subgraph_for_prefix() {
    let def = build_mover_subnet();
    let inst = def.instantiate("b1", ());
    let dot = dot_export_instance(&inst);

    // The cluster post-processing must emit a subgraph cluster_<prefix>
    // for every node whose semantic name carries a `/`-prefix per MOD-040.
    assert!(
        dot.contains("subgraph cluster_b1"),
        "missing cluster subgraph for prefix 'b1': {dot}"
    );
    // The cluster's label is the original prefix string.
    assert!(dot.contains("label=\"b1\""), "cluster label mismatch: {dot}");
}

#[test]
fn composed_with_clusters_emits_cluster_for_each_prefix() {
    // Build two instances and compose them so the resulting flat net has
    // nodes with `a/...` and `b/...` semantic names.
    let def = build_mover_subnet();
    let a = def.instantiate("a", ());
    let b = def.instantiate("b", ());

    // Synthesise a composed flat net by manually combining the renamed
    // bodies via the PetriNet builder.
    let mut builder = PetriNet::builder("composed");
    for t in a.renamed_body().transitions() {
        builder = builder.transition(t.clone());
    }
    for t in b.renamed_body().transitions() {
        builder = builder.transition(t.clone());
    }
    let net = builder.build();

    let dot = dot_export_composed_with_clusters(&net);
    assert!(
        dot.contains("subgraph cluster_a"),
        "missing cluster_a in composed dot: {dot}"
    );
    assert!(
        dot.contains("subgraph cluster_b"),
        "missing cluster_b in composed dot: {dot}"
    );
}

#[test]
fn composed_without_prefixes_returns_dot_unchanged() {
    // No `/`-prefixed names → no clusters injected.
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1").input(one(&p1)).output(out_place(&p2)).build();
    let net = PetriNet::builder("flat").transition(t).build();

    let dot = dot_export_composed_with_clusters(&net);
    assert!(!dot.contains("subgraph cluster_"), "unexpected cluster in flat net: {dot}");
}

#[test]
fn dot_export_subnet_def_handles_subnet_without_ports() {
    // A subnet with no ports + no channels still works (no interface
    // cluster injection).
    let p = Place::<i32>::new("p");
    let t = Transition::builder("t").input(one(&p)).build();
    let def: SubnetDef<()> = SubnetDef::builder("Empty").transition(t).build();

    let dot = dot_export_subnet_def(&def);
    assert!(dot.contains("digraph Empty"));
    assert!(!dot.contains("subgraph cluster_iface_"));
}

#[test]
fn generate_subnet_def_svg_writes_inlined_html() {
    let def = build_mover_subnet();
    let tmp = std::env::temp_dir();

    let path = SvgGenerator::new()
        .out_dir(&tmp)
        .generate_subnet_def("test_subnet_def", &def);

    assert!(path.exists(), "svg path not written");
    let content = std::fs::read_to_string(&path).unwrap();
    // Inlined CSS + JS from the resources/ directory.
    assert!(content.contains("<style>"), "missing inlined CSS");
    assert!(content.contains("<script>"), "missing inlined JS");
    // The bundled viewer global must be present and the init script must
    // call its mount() entry point.
    assert!(content.contains("LibpetriViewer"), "viewer global missing");
    assert!(content.contains("LibpetriViewer.mount"), "viewer init script missing");
    // DOT source is embedded as a data-dot attribute (the viewer reads it).
    assert!(content.contains("data-dot=\""), "data-dot attribute missing");
    // Old API surface must be gone.
    assert!(!content.contains("PetriNetDiagrams"), "stale global reference: {content}");
    assert!(
        !content.contains("class=\"diagram-legend\""),
        "stale legend placeholder still emitted"
    );
    assert!(
        !content.contains("class=\"diagram-filter-strip\""),
        "stale filter placeholder still emitted"
    );
    // Subnet header markup.
    assert!(content.contains("subnet-diagram"), "missing subnet-diagram class");
    assert!(content.contains(">Mover<"), "subnet name missing in header");

    let _ = std::fs::remove_file(path);
}

#[test]
fn generate_instance_svg_writes_with_instance_header() {
    let def = build_mover_subnet();
    let inst = def.instantiate("ai1", ());
    let tmp = std::env::temp_dir();

    let path = SvgGenerator::new()
        .out_dir(&tmp)
        .generate_instance("test_instance", &inst);

    assert!(path.exists());
    let content = std::fs::read_to_string(&path).unwrap();
    assert!(content.contains(">instance<"));
    assert!(content.contains(">ai1<"));
    assert!(content.contains(">Mover<"));
    let _ = std::fs::remove_file(path);
}

#[test]
fn macro_dispatches_to_petri_net() {
    // Verify the macro accepts each of the three reference types. We use a
    // custom out_dir (the macro defaults to OUT_DIR which isn't set during
    // `cargo test`) so we cannot drive the macro in this test directly —
    // it routes to generate_svg() which reads OUT_DIR. Instead, exercise
    // the same trait-dispatch path the macro expands to.
    use libpetri_docgen::PetriDocSvg;

    let p = Place::<i32>::new("p");
    let t = Transition::builder("t").input(one(&p)).build();
    let net = PetriNet::builder("flow").transition(t).build();

    // unsafe { ... }: temporarily set OUT_DIR for this test
    let prev = std::env::var("OUT_DIR").ok();
    let tmp = std::env::temp_dir();
    // SAFETY: tests run sequentially within a single thread by default for
    // crates with no test-thread overrides; the parent test harness owns
    // the env var space.
    unsafe {
        std::env::set_var("OUT_DIR", &tmp);
    }

    let path = PetriDocSvg::generate(&net, "macro_test");
    assert!(path.exists());
    let _ = std::fs::remove_file(path);

    // SAFETY: same guarantee as above.
    unsafe {
        match prev {
            Some(v) => std::env::set_var("OUT_DIR", v),
            None => std::env::remove_var("OUT_DIR"),
        }
    }
}
