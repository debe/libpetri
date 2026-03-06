use crate::net_flattener::FlatNet;

/// Incidence matrix C[t][p] = post[t][p] - pre[t][p].
#[derive(Debug, Clone)]
pub struct IncidenceMatrix {
    pub pre: Vec<Vec<i64>>,
    pub post: Vec<Vec<i64>>,
    pub incidence: Vec<Vec<i64>>,
    pub place_count: usize,
    pub transition_count: usize,
}

impl IncidenceMatrix {
    /// Computes the incidence matrix from a flattened net.
    pub fn from_flat_net(flat: &FlatNet) -> Self {
        let place_count = flat.place_count;
        let transition_count = flat.transitions.len();

        let mut pre = vec![vec![0i64; place_count]; transition_count];
        let mut post = vec![vec![0i64; place_count]; transition_count];

        for (tid, ft) in flat.transitions.iter().enumerate() {
            for (pid, &count) in ft.pre.iter().enumerate() {
                pre[tid][pid] = count;
            }
            for (pid, &count) in ft.post.iter().enumerate() {
                post[tid][pid] = count;
            }
        }

        let incidence: Vec<Vec<i64>> = (0..transition_count)
            .map(|tid| {
                (0..place_count)
                    .map(|pid| post[tid][pid] - pre[tid][pid])
                    .collect()
            })
            .collect();

        Self {
            pre,
            post,
            incidence,
            place_count,
            transition_count,
        }
    }

    /// Returns the transposed incidence matrix (place x transition).
    pub fn transposed(&self) -> Vec<Vec<i64>> {
        let mut result = vec![vec![0i64; self.transition_count]; self.place_count];
        for (tid, row) in self.incidence.iter().enumerate() {
            for (pid, &val) in row.iter().enumerate() {
                result[pid][tid] = val;
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net_flattener::flatten;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn simple_chain_matrix() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);

        assert_eq!(matrix.place_count, 2);
        assert_eq!(matrix.transition_count, 1);

        let p1_idx = flat.place_index["p1"];
        let p2_idx = flat.place_index["p2"];

        assert_eq!(matrix.pre[0][p1_idx], 1);
        assert_eq!(matrix.post[0][p2_idx], 1);
        assert_eq!(matrix.incidence[0][p1_idx], -1);
        assert_eq!(matrix.incidence[0][p2_idx], 1);
    }

    #[test]
    fn transposed_dimensions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .build();
        let net = PetriNet::builder("test").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);
        let ct = matrix.transposed();

        assert_eq!(ct.len(), 3);
        assert_eq!(ct[0].len(), 2);
    }
}
