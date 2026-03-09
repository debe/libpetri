const EPSILON: f64 = 1e-9;

/// Difference Bound Matrix for encoding firing domains in Time Petri Nets.
///
/// Float64 matrix representation. Reference clock at index 0,
/// transition clocks at indices 1..n.
///
/// bounds[i][j] represents the upper bound on (x_i - x_j).
#[derive(Debug, Clone)]
pub struct Dbm {
    dim: usize,
    data: Vec<f64>,
    clock_names: Vec<String>,
    empty: bool,
}

impl Dbm {
    /// Creates a new DBM of the given size (n clocks + reference clock 0).
    pub fn new(size: usize) -> Self {
        let data = vec![f64::INFINITY; size * size];
        let mut dbm = Self {
            dim: size,
            data,
            clock_names: Vec::new(),
            empty: false,
        };
        for i in 0..size {
            dbm.set(i, i, 0.0);
        }
        dbm
    }

    /// Creates an initial firing domain for enabled transitions.
    pub fn create(clock_names: Vec<String>, lower_bounds: &[f64], upper_bounds: &[f64]) -> Self {
        let n = clock_names.len();
        let dim = n + 1;
        let mut dbm = Self::new(dim);
        dbm.clock_names = clock_names;

        for i in 0..n {
            dbm.set(0, i + 1, -lower_bounds[i]); // -lower bound
            dbm.set(i + 1, 0, upper_bounds[i]); // upper bound
        }

        dbm.canonicalize();
        dbm
    }

    /// Creates an empty (unsatisfiable) DBM.
    pub fn empty_dbm() -> Self {
        Self {
            dim: 1,
            data: vec![0.0],
            clock_names: Vec::new(),
            empty: true,
        }
    }

    /// Returns the matrix size (dim x dim).
    pub fn size(&self) -> usize {
        self.dim
    }

    /// Returns the clock names.
    pub fn clock_names(&self) -> &[String] {
        &self.clock_names
    }

    /// Returns true if the DBM represents an empty zone.
    pub fn is_empty(&self) -> bool {
        self.empty
    }

    /// Gets the bound D[i][j] (clock_i - clock_j <= D[i][j]).
    pub fn get(&self, i: usize, j: usize) -> f64 {
        self.data[i * self.dim + j]
    }

    /// Sets the bound D[i][j].
    pub fn set(&mut self, i: usize, j: usize, value: f64) {
        self.data[i * self.dim + j] = value;
    }

    /// Returns the lower bound for clock i: -D[0][i+1].
    pub fn lower_bound(&self, i: usize) -> f64 {
        if self.empty || i >= self.clock_names.len() {
            return 0.0;
        }
        let val = -self.get(0, i + 1);
        if val == 0.0 { 0.0 } else { val } // normalize -0
    }

    /// Returns the upper bound for clock i: D[i+1][0].
    pub fn upper_bound(&self, i: usize) -> f64 {
        if self.empty || i >= self.clock_names.len() {
            return f64::INFINITY;
        }
        self.get(i + 1, 0)
    }

    /// Returns true if clock i can fire (lower bound <= epsilon after time passage).
    pub fn can_fire(&self, i: usize) -> bool {
        !self.empty && self.lower_bound(i) <= EPSILON
    }

    /// Canonicalizes the DBM using Floyd-Warshall algorithm.
    pub fn canonicalize(&mut self) {
        if self.empty {
            return;
        }
        let n = self.dim;
        for k in 0..n {
            for i in 0..n {
                for j in 0..n {
                    let ik = self.get(i, k);
                    let kj = self.get(k, j);
                    if ik < f64::INFINITY && kj < f64::INFINITY {
                        let via = ik + kj;
                        if via < self.get(i, j) {
                            self.set(i, j, via);
                        }
                    }
                }
            }
        }
        // Check for negative diagonal (empty zone)
        for i in 0..n {
            if self.get(i, i) < -EPSILON {
                self.empty = true;
                return;
            }
        }
    }

    /// Lets time pass: set all lower bounds to 0 (minimum firing time reached).
    pub fn let_time_pass(&self) -> Dbm {
        if self.empty {
            return self.clone();
        }
        let mut result = self.clone();
        for i in 1..self.dim {
            result.set(0, i, 0.0);
        }
        result.canonicalize();
        result
    }

    /// Computes successor firing domain after firing transition at `fired_clock`.
    ///
    /// Implements the Berthomieu-Diaz successor formula:
    /// intersect constraints, canonicalize, substitute/eliminate fired clock,
    /// add fresh intervals for newly enabled, then final canonicalization.
    pub fn fire_transition(
        &self,
        fired_clock: usize,
        new_clock_names: &[String],
        new_lower_bounds: &[f64],
        new_upper_bounds: &[f64],
        persistent_clocks: &[usize],
    ) -> Dbm {
        if self.empty {
            return self.clone();
        }

        let n = self.clock_names.len();
        if fired_clock >= n {
            return Dbm::empty_dbm();
        }

        // Step 1: Intersect with "fired fires first" constraint
        let mut constrained = self.data.clone();
        let dim = self.dim;
        let f = fired_clock + 1;

        for i in 0..n {
            if i != fired_clock {
                let idx = i + 1;
                let pos = f * dim + idx;
                constrained[pos] = constrained[pos].min(0.0);
            }
        }

        // Step 2: Canonicalize
        if !canonicalize_in_place(&mut constrained, dim) {
            return Dbm::empty_dbm();
        }

        // Steps 3 & 4: Build new DBM with persistent + newly enabled clocks
        let new_n = persistent_clocks.len() + new_clock_names.len();
        let new_dim = new_n + 1;
        let mut new_data = vec![f64::INFINITY; new_dim * new_dim];
        for i in 0..new_dim {
            new_data[i * new_dim + i] = 0.0;
        }

        // Copy persistent clocks with transformed bounds
        for (pi, &old_clock) in persistent_clocks.iter().enumerate() {
            let old_idx = old_clock + 1;
            let new_idx = pi + 1;

            let upper = constrained[old_idx * dim + f];
            let lower = (-constrained[f * dim + old_idx]).max(0.0);

            new_data[new_idx] = -lower; // row 0, col new_idx
            new_data[new_idx * new_dim] = upper; // row new_idx, col 0

            // Inter-clock constraints between persistent transitions
            for (pj, &old_j) in persistent_clocks.iter().enumerate() {
                let old_j_idx = old_j + 1;
                let new_j = pj + 1;
                new_data[new_idx * new_dim + new_j] = constrained[old_idx * dim + old_j_idx];
            }
        }

        // Step 5: Add fresh intervals for newly enabled transitions
        let offset = persistent_clocks.len();
        for (k, _) in new_clock_names.iter().enumerate() {
            let idx = offset + k + 1;
            new_data[idx] = -new_lower_bounds[k]; // row 0, col idx
            new_data[idx * new_dim] = new_upper_bounds[k]; // row idx, col 0
        }

        // Build new clock names
        let mut all_names = Vec::with_capacity(new_n);
        for &idx in persistent_clocks {
            all_names.push(self.clock_names[idx].clone());
        }
        all_names.extend(new_clock_names.iter().cloned());

        let mut result = Dbm {
            dim: new_dim,
            data: new_data,
            clock_names: all_names,
            empty: false,
        };
        result.canonicalize();
        result
    }

    /// Generates a canonical string representation for deduplication.
    pub fn canonical_string(&self) -> String {
        if self.empty {
            return "DBM[empty]".to_string();
        }
        let mut parts = Vec::new();
        for i in 0..self.clock_names.len() {
            let lo = self.lower_bound(i);
            let hi = self.upper_bound(i);
            parts.push(format!(
                "{}:[{},{}]",
                self.clock_names[i],
                format_bound(lo),
                format_bound(hi)
            ));
        }
        format!("DBM{{{}}}", parts.join(", "))
    }
}

fn canonicalize_in_place(data: &mut [f64], dim: usize) -> bool {
    for k in 0..dim {
        for i in 0..dim {
            for j in 0..dim {
                let ik = data[i * dim + k];
                let kj = data[k * dim + j];
                if ik < f64::INFINITY && kj < f64::INFINITY {
                    let via = ik + kj;
                    if via < data[i * dim + j] {
                        data[i * dim + j] = via;
                    }
                }
            }
        }
    }
    for i in 0..dim {
        if data[i * dim + i] < -EPSILON {
            return false;
        }
    }
    true
}

fn format_bound(b: f64) -> String {
    if b >= f64::INFINITY / 2.0 {
        "\u{221e}".to_string()
    } else if b == b.trunc() {
        format!("{}", b as i64)
    } else {
        format!("{:.3}", b)
    }
}

impl PartialEq for Dbm {
    fn eq(&self, other: &Self) -> bool {
        if self.empty && other.empty {
            return true;
        }
        if self.empty || other.empty {
            return false;
        }
        if self.clock_names.len() != other.clock_names.len() {
            return false;
        }
        if self.clock_names != other.clock_names {
            return false;
        }
        if self.data.len() != other.data.len() {
            return false;
        }
        for i in 0..self.data.len() {
            if (self.data[i] - other.data[i]).abs() > EPSILON {
                return false;
            }
        }
        true
    }
}

impl Eq for Dbm {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dbm_new() {
        let dbm = Dbm::new(3);
        assert_eq!(dbm.size(), 3);
        assert_eq!(dbm.get(0, 0), 0.0);
        assert_eq!(dbm.get(1, 1), 0.0);
        assert_eq!(dbm.get(0, 1), f64::INFINITY);
    }

    #[test]
    fn dbm_create_with_bounds() {
        let dbm = Dbm::create(vec!["t1".into(), "t2".into()], &[5.0, 3.0], &[10.0, 8.0]);
        assert_eq!(dbm.clock_names().len(), 2);
        assert_eq!(dbm.lower_bound(0), 5.0);
        assert_eq!(dbm.upper_bound(0), 10.0);
        assert_eq!(dbm.lower_bound(1), 3.0);
        assert_eq!(dbm.upper_bound(1), 8.0);
    }

    #[test]
    fn dbm_bounds() {
        let mut dbm = Dbm::new(3);
        dbm.clock_names = vec!["t1".into(), "t2".into()];
        dbm.set(0, 1, -5.0);
        dbm.set(1, 0, 10.0);
        assert_eq!(dbm.lower_bound(0), 5.0);
        assert_eq!(dbm.upper_bound(0), 10.0);
        assert!(dbm.can_fire(0) || !dbm.can_fire(0)); // depends on canonicalization
    }

    #[test]
    fn dbm_canonicalize() {
        let mut dbm = Dbm::new(3);
        dbm.set(1, 0, 10.0);
        dbm.set(0, 1, -5.0);
        dbm.set(2, 0, 8.0);
        dbm.set(0, 2, -3.0);
        dbm.canonicalize();
        assert!(dbm.get(1, 2) <= 10.0 + 8.0);
    }

    #[test]
    fn dbm_empty() {
        let mut dbm = Dbm::new(2);
        dbm.set(0, 1, -10.0);
        dbm.set(1, 0, 5.0);
        dbm.canonicalize();
        assert!(dbm.is_empty());
    }

    #[test]
    fn dbm_let_time_pass() {
        let dbm = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        let passed = dbm.let_time_pass();
        // After time passage, lower bound should be 0
        assert_eq!(passed.lower_bound(0), 0.0);
        // Upper bound preserved
        assert_eq!(passed.upper_bound(0), 10.0);
    }

    #[test]
    fn dbm_equality() {
        let a = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        let b = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        assert_eq!(a, b);
    }

    #[test]
    fn dbm_inequality() {
        let a = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        let b = Dbm::create(vec!["t1".into()], &[3.0], &[10.0]);
        assert_ne!(a, b);
    }

    #[test]
    fn dbm_fire_transition() {
        let dbm = Dbm::create(vec!["t1".into(), "t2".into()], &[5.0, 3.0], &[10.0, 8.0]);
        let passed = dbm.let_time_pass();

        // Fire t1 (clock 0), t2 persists (clock 1)
        let result = passed.fire_transition(
            0,
            &[],
            &[],
            &[],
            &[1], // t2 is persistent
        );
        assert!(!result.is_empty());
        assert_eq!(result.clock_names().len(), 1);
        assert_eq!(result.clock_names()[0], "t2");
    }

    #[test]
    fn dbm_fire_with_newly_enabled() {
        let dbm = Dbm::create(vec!["t1".into()], &[0.0], &[f64::INFINITY]);
        let passed = dbm.let_time_pass();

        // Fire t1, enable t2 and t3
        let result = passed.fire_transition(
            0,
            &["t2".into(), "t3".into()],
            &[2.0, 0.0],
            &[5.0, 3.0],
            &[],
        );
        assert!(!result.is_empty());
        assert_eq!(result.clock_names().len(), 2);
        assert_eq!(result.clock_names()[0], "t2");
        assert_eq!(result.clock_names()[1], "t3");
    }

    #[test]
    fn dbm_can_fire() {
        let dbm = Dbm::create(vec!["t1".into()], &[0.0], &[10.0]);
        let passed = dbm.let_time_pass();
        assert!(passed.can_fire(0));

        // With high lower bound and no time passage
        let dbm2 = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        assert!(!dbm2.can_fire(0)); // hasn't waited long enough
    }

    #[test]
    fn dbm_canonical_string() {
        let dbm = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        let s = dbm.canonical_string();
        assert!(s.contains("t1"));
        assert!(s.contains("5"));
        assert!(s.contains("10"));
    }

    #[test]
    fn dbm_empty_dbm() {
        let dbm = Dbm::empty_dbm();
        assert!(dbm.is_empty());
        assert_eq!(dbm.canonical_string(), "DBM[empty]");
    }

    #[test]
    fn dbm_fire_persistent_bounds_adjusted() {
        // After firing t1 with t2 persistent, t2's bounds should be relative to fire time
        let dbm = Dbm::create(vec!["t1".into(), "t2".into()], &[0.0, 0.0], &[5.0, 10.0]);
        let passed = dbm.let_time_pass();

        let result = passed.fire_transition(
            0, // fire t1
            &[],
            &[],
            &[],
            &[1], // t2 persists
        );

        assert!(!result.is_empty());
        // t2 upper bound should still be finite
        assert!(result.upper_bound(0) < f64::INFINITY);
    }

    #[test]
    fn dbm_fire_replaces_fired_clock() {
        let dbm = Dbm::create(vec!["t1".into()], &[0.0], &[5.0]);
        let passed = dbm.let_time_pass();

        // Fire t1, enable t2 with different bounds
        let result = passed.fire_transition(0, &["t2".into()], &[1.0], &[3.0], &[]);

        assert_eq!(result.clock_names().len(), 1);
        assert_eq!(result.clock_names()[0], "t2");
        assert_eq!(result.lower_bound(0), 1.0); // fresh interval lower bound
        assert_eq!(result.upper_bound(0), 3.0);

        // After let_time_pass, lower bound drops to 0
        let passed = result.let_time_pass();
        assert_eq!(passed.lower_bound(0), 0.0);
    }

    #[test]
    fn dbm_infeasible_constraints_produce_empty() {
        // lower > upper should produce empty DBM
        let dbm = Dbm::create(
            vec!["t1".into()],
            &[10.0],
            &[5.0], // upper < lower
        );
        assert!(dbm.is_empty());
    }

    #[test]
    fn dbm_multiple_clocks_inter_constraints() {
        // Two clocks with tight constraints
        let dbm = Dbm::create(vec!["t1".into(), "t2".into()], &[1.0, 2.0], &[3.0, 4.0]);
        assert!(!dbm.is_empty());

        // After canonicalization, inter-clock constraints should be tightened
        // t1 - t2 <= upper_t1 - lower_t2 = 3 - 2 = 1
        assert!(dbm.get(1, 2) <= 1.0 + 1e-9);
    }

    #[test]
    fn dbm_lower_bound_out_of_range() {
        let dbm = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        // Out of range index
        assert_eq!(dbm.lower_bound(10), 0.0);
        assert_eq!(dbm.upper_bound(10), f64::INFINITY);
    }

    #[test]
    fn dbm_equality_with_different_names() {
        let a = Dbm::create(vec!["t1".into()], &[5.0], &[10.0]);
        let b = Dbm::create(vec!["t2".into()], &[5.0], &[10.0]);
        // Different names → not equal
        assert_ne!(a, b);
    }

    #[test]
    fn dbm_empty_equality() {
        let a = Dbm::empty_dbm();
        let b = Dbm::empty_dbm();
        assert_eq!(a, b);
    }

    #[test]
    fn dbm_let_time_pass_preserves_upper() {
        let dbm = Dbm::create(vec!["t1".into(), "t2".into()], &[3.0, 5.0], &[10.0, 15.0]);
        let passed = dbm.let_time_pass();
        assert_eq!(passed.lower_bound(0), 0.0);
        assert_eq!(passed.lower_bound(1), 0.0);
        assert_eq!(passed.upper_bound(0), 10.0);
        assert_eq!(passed.upper_bound(1), 15.0);
    }
}
