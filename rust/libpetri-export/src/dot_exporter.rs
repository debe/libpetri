use libpetri_core::petri_net::PetriNet;

use crate::dot_renderer::render_dot;
use crate::mapper::{DotConfig, map_to_graph};

/// Convenience function: maps a PetriNet to DOT format string.
pub fn dot_export(net: &PetriNet, config: Option<&DotConfig>) -> String {
    let default_config = DotConfig::default();
    let config = config.unwrap_or(&default_config);
    let graph = map_to_graph(net, config);
    render_dot(&graph)
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn dot_export_simple() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let dot = dot_export(&net, None);
        assert!(dot.contains("digraph test"));
        assert!(dot.contains("p_p1"));
        assert!(dot.contains("p_p2"));
        assert!(dot.contains("t_t1"));
    }

    // ============================================================
    //  MOD-026 / MOD-040 / EXP-016: direct-composition cluster export
    // ============================================================

    use libpetri_core::subnet_def::SubnetDef;

    /// A producer subnet whose output place is named `pipe` (wires by name).
    fn pipe_producer() -> SubnetDef<()> {
        let seed = Place::<String>::new("seed");
        let pipe = Place::<String>::new("pipe");
        SubnetDef::<()>::builder("PipeProducer")
            .place(&seed)
            .place(&pipe)
            .transition(
                Transition::builder("emit")
                    .input(one(&seed))
                    .output(out_place(&pipe))
                    .build(),
            )
            .build()
    }

    /// A consumer subnet whose input place is named `pipe` (wires by name).
    fn pipe_consumer() -> SubnetDef<()> {
        let pipe = Place::<String>::new("pipe");
        let sink = Place::<String>::new("sink");
        SubnetDef::<()>::builder("PipeConsumer")
            .place(&pipe)
            .place(&sink)
            .transition(
                Transition::builder("eat")
                    .input(one(&pipe))
                    .output(out_place(&sink))
                    .build(),
            )
            .build()
    }

    /// A standalone subnet with names distinct from the pipe fixtures, used
    /// to instance-compose a `prefix/`-named component alongside a directly-
    /// composed one.
    fn widget() -> SubnetDef<()> {
        let raw = Place::<String>::new("raw");
        let done = Place::<String>::new("done");
        SubnetDef::<()>::builder("Widget")
            .place(&raw)
            .place(&done)
            .transition(
                Transition::builder("build")
                    .input(one(&raw))
                    .output(out_place(&done))
                    .build(),
            )
            .build()
    }

    /// Returns the body substring of the first `subgraph cluster_<id> {`
    /// block, up to its first closing `}` (mirrors the Java test's `find`).
    fn cluster_body<'a>(dot: &'a str, cluster_decl: &str) -> &'a str {
        let start = dot
            .find(cluster_decl)
            .unwrap_or_else(|| panic!("expected '{cluster_decl}' in:\n{dot}"));
        let end = dot[start..]
            .find('}')
            .map(|i| start + i)
            .unwrap_or_else(|| panic!("expected closing brace after '{cluster_decl}'"));
        &dot[start..end]
    }

    /// EXP-016 AC#7 / MOD-040 AC#6: a directly-composed net emits one
    /// `subgraph cluster_<subnetName>` block per subnet; private nodes go
    /// inside, the shared place stays top-level.
    #[test]
    fn dot_export_direct_composed_clusters_by_subnet_name() {
        let net = PetriNet::builder("Pipeline")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        let dot = dot_export(&net, None);

        assert!(
            dot.contains("subgraph cluster_PipeProducer {"),
            "direct composition must cluster by subnet name. DOT:\n{dot}"
        );
        assert!(
            dot.contains("subgraph cluster_PipeConsumer {"),
            "direct composition must cluster by subnet name. DOT:\n{dot}"
        );

        let prod = cluster_body(&dot, "subgraph cluster_PipeProducer {");
        assert!(prod.contains("p_seed"), "seed must be in producer cluster");
        assert!(prod.contains("t_emit"), "emit must be in producer cluster");

        let cons = cluster_body(&dot, "subgraph cluster_PipeConsumer {");
        assert!(cons.contains("p_sink"), "sink must be in consumer cluster");
        assert!(cons.contains("t_eat"), "eat must be in consumer cluster");

        // The shared 'pipe' place has no single owner — top-level only.
        assert!(
            !prod.contains("p_pipe"),
            "shared place 'pipe' must not be inside the producer cluster"
        );
        assert!(
            !cons.contains("p_pipe"),
            "shared place 'pipe' must not be inside the consumer cluster"
        );
    }

    /// EXP-016 AC#4: a flat net carrying no membership emits no clusters,
    /// and the DOT is byte-identical to the same net before MOD-026.
    #[test]
    fn dot_export_flat_net_no_clusters() {
        let pending = Place::<String>::new("Pending");
        let processed = Place::<String>::new("Processed");
        let t = Transition::builder("Process")
            .input(one(&pending))
            .output(out_place(&processed))
            .build();
        let net = PetriNet::builder("FlatNet").transition(t).build();

        let dot = dot_export(&net, None);

        assert!(
            !dot.contains("subgraph cluster_"),
            "flat net must not emit any cluster subgraph. DOT:\n{dot}"
        );
        assert!(net.subnet_membership().is_empty());
    }

    /// ClusterSource::Prefix clusters only by '/' name segments — a
    /// direct-composed net has none, so no clusters are emitted.
    #[test]
    fn dot_export_cluster_source_prefix_ignores_metadata() {
        let net = PetriNet::builder("Pipeline")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        let config = DotConfig {
            cluster_source: crate::graph::ClusterSource::Prefix,
            ..DotConfig::default()
        };
        let dot = dot_export(&net, Some(&config));

        assert!(
            !dot.contains("subgraph cluster_"),
            "ClusterSource::Prefix must ignore subnet metadata. DOT:\n{dot}"
        );
    }

    /// ClusterSource::None suppresses clustering even for a metadata-bearing
    /// directly-composed net that would otherwise cluster.
    #[test]
    fn dot_export_cluster_source_none_suppresses_all_clusters() {
        let net = PetriNet::builder("Pipeline")
            .compose_direct(&pipe_producer())
            .compose_direct(&pipe_consumer())
            .build();

        let config = DotConfig {
            cluster_source: crate::graph::ClusterSource::None,
            ..DotConfig::default()
        };
        let dot = dot_export(&net, Some(&config));

        assert!(
            !dot.contains("subgraph cluster_"),
            "ClusterSource::None must emit no clusters. DOT:\n{dot}"
        );
    }

    /// MOD-026 AC#5: fusing away a non-canonical place removes its entry; the
    /// remaining canonical place still clusters under its subnet.
    #[test]
    fn dot_export_direct_composed_then_fuse_clusters_canonical() {
        use libpetri_core::fusion::FusionSet;

        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let subnet = SubnetDef::<()>::builder("AB")
            .transition(
                Transition::builder("move")
                    .input(one(&a))
                    .output(out_place(&b))
                    .build(),
            )
            .build();
        let net = PetriNet::builder("Host")
            .compose_direct(&subnet)
            .fuse([FusionSet::of("ab", &a, &[&b])])
            .build();

        let dot = dot_export(&net, None);
        let body = cluster_body(&dot, "subgraph cluster_AB {");
        assert!(body.contains("p_a"), "canonical place 'a' clusters under AB");
        assert!(body.contains("t_move"), "transition 'move' clusters under AB");
        // 'b' was fused away — it must not appear as a place node at all.
        // Match the node-declaration syntax (`<id> [`) rather than a bare
        // substring so a future place named e.g. `b_x` cannot mask a leak.
        assert!(
            !dot.contains("p_b ["),
            "non-canonical fused place 'b' must be gone. DOT:\n{dot}"
        );
    }

    /// MOD-040 AC#7: a net that both directly composes a subnet and instance-
    /// composes another carries metadata for the direct nodes and '/'
    /// prefixes for the instance nodes. Under the default Auto source the
    /// exporter clusters direct nodes by subnet name and instance nodes by
    /// prefix — both cluster kinds coexist.
    #[test]
    fn dot_export_mixed_direct_and_instance_both_cluster_kinds() {
        let net = PetriNet::builder("Mixed")
            .compose_direct(&pipe_producer())
            .compose_auto(&widget().instantiate_unit("inst1"))
            .build();

        let dot = dot_export(&net, None);

        assert!(
            dot.contains("subgraph cluster_PipeProducer {"),
            "direct-composed subnet must cluster by subnet name. DOT:\n{dot}"
        );
        assert!(
            dot.contains("subgraph cluster_inst1 {"),
            "instance-composed subnet must cluster by prefix. DOT:\n{dot}"
        );

        let meta = cluster_body(&dot, "subgraph cluster_PipeProducer {");
        assert!(
            meta.contains("p_seed") && meta.contains("t_emit"),
            "metadata cluster must hold the direct subnet's nodes. Cluster:\n{meta}"
        );
        assert!(
            !meta.contains("inst1"),
            "metadata cluster must not absorb prefix-named instance nodes. Cluster:\n{meta}"
        );

        let inst = cluster_body(&dot, "subgraph cluster_inst1 {");
        assert!(
            inst.contains("p_inst1_raw") && inst.contains("t_inst1_build"),
            "prefix cluster must hold the instance's renamed nodes. Cluster:\n{inst}"
        );
    }

    /// ClusterSource::Metadata is strict — it clusters only from membership
    /// metadata. An instance-composed net carries none, only '/' prefixes, so
    /// Metadata emits no clusters at all. This is what distinguishes Metadata
    /// from Auto, which would cluster by prefix.
    #[test]
    fn dot_export_cluster_source_metadata_ignores_prefix_only_net() {
        let net = PetriNet::builder("Host")
            .compose_auto(&widget().instantiate_unit("inst1"))
            .build();

        let config = DotConfig {
            cluster_source: crate::graph::ClusterSource::Metadata,
            ..DotConfig::default()
        };
        let dot = dot_export(&net, Some(&config));

        assert!(
            !dot.contains("subgraph cluster_"),
            "ClusterSource::Metadata must not fall back to prefix detection. DOT:\n{dot}"
        );
    }
}
