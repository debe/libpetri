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
}
