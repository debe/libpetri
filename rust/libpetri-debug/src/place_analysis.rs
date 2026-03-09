//! Analyze places for start/end/environment classification.

use std::collections::HashMap;

use libpetri_core::output;
use libpetri_core::petri_net::PetriNet;

/// Analysis info for a single place.
#[derive(Debug, Clone)]
pub struct PlaceAnalysisInfo {
    pub token_type: String,
    pub has_incoming: bool,
    pub has_outgoing: bool,
}

/// Analyzes all places in a Petri net for structural classification.
#[derive(Debug, Clone)]
pub struct PlaceAnalysis {
    data: HashMap<String, PlaceAnalysisInfo>,
}

impl PlaceAnalysis {
    /// Build place analysis from a PetriNet.
    pub fn from_net(net: &PetriNet) -> Self {
        let mut data: HashMap<String, PlaceAnalysisInfo> = HashMap::new();

        fn ensure<'a>(
            data: &'a mut HashMap<String, PlaceAnalysisInfo>,
            name: &str,
        ) -> &'a mut PlaceAnalysisInfo {
            data.entry(name.to_string())
                .or_insert_with(|| PlaceAnalysisInfo {
                    token_type: "unknown".into(),
                    has_incoming: false,
                    has_outgoing: false,
                })
        }

        for t in net.transitions() {
            // Input arcs: place → transition (place has outgoing)
            for input in t.input_specs() {
                ensure(&mut data, input.place_name()).has_outgoing = true;
            }

            // Output arcs: transition → place (place has incoming)
            if let Some(out) = t.output_spec() {
                for p in output::all_places(out) {
                    ensure(&mut data, p.name()).has_incoming = true;
                }
            }

            // Inhibitor arcs: just ensure place exists
            for inh in t.inhibitors() {
                ensure(&mut data, inh.place.name());
            }

            // Read arcs: place has outgoing
            for r in t.reads() {
                ensure(&mut data, r.place.name()).has_outgoing = true;
            }

            // Reset arcs: just ensure place exists
            for r in t.resets() {
                ensure(&mut data, r.place.name());
            }
        }

        Self { data }
    }

    /// Returns the analysis data.
    pub fn data(&self) -> &HashMap<String, PlaceAnalysisInfo> {
        &self.data
    }

    /// Returns `true` if the place is a start place (no incoming arcs).
    pub fn is_start(&self, place_name: &str) -> bool {
        self.data
            .get(place_name)
            .is_some_and(|info| !info.has_incoming)
    }

    /// Returns `true` if the place is an end place (no outgoing arcs).
    pub fn is_end(&self, place_name: &str) -> bool {
        self.data
            .get(place_name)
            .is_some_and(|info| !info.has_outgoing)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn start_and_end_classification() {
        let p1 = Place::<i32>::new("start");
        let p2 = Place::<i32>::new("mid");
        let p3 = Place::<i32>::new("end");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .build();

        let net = PetriNet::builder("test").transitions([t1, t2]).build();
        let analysis = PlaceAnalysis::from_net(&net);

        assert!(analysis.is_start("start"));
        assert!(!analysis.is_end("start"));
        assert!(!analysis.is_start("mid"));
        assert!(!analysis.is_end("mid"));
        assert!(!analysis.is_start("end"));
        assert!(analysis.is_end("end"));
    }
}
