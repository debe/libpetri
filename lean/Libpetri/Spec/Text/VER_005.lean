import Libpetri.Spec.Text

requirement_text VER_005
  id "VER-005"
  title "P-Invariant Computation"
  priority SHOULD
  kind F
  body r#"The verifier computes place invariants (P-invariants) from the net's incidence matrix. A P-invariant is a nonzero weight vector `w` such that `w · M = constant` for all markings M reachable in the untimed abstraction of the verified net ([VER-004]).

P-invariants provide structural proofs that do not require state enumeration.

⟦s1|*When* the SMT pipeline ([VER-003]) builds its CHC encoding, the verifier *shall* compute the P-invariants of the verified net from the net's incidence matrix, with one injector column for each environment place into which it models injection ([VER-006]).⟧

⟦s2|The verifier *shall* report a nonzero weight vector `w` with a constant `c` as a P-invariant only when the product of `w` with every column of that incidence matrix is zero and `w · M = c` holds on every marking `M` reachable in the untimed abstraction of the verified net ([VER-004]), injections included.⟧

⟦s3|*When* the verifier computes the P-invariants of a net that has a transition and in which no transition has a reset arc, an `All` input or an `AtLeast` input, it *shall* report P-invariants such that every weight vector of zeros and ones over the net's places whose product with every column of that incidence matrix is zero is a rational linear combination of their weight vectors.⟧

*When* the verifier computes P-invariants, it *shall* list each one it reports in the verification result, with its weights and its constant.

**Acceptance Criteria:**
1. P-invariants are computed from the incidence matrix.
2. Each invariant satisfies `sum(weights[i] * marking[i]) = constant` for all markings reachable in the untimed abstraction of the verified net ([VER-004]).
3. Invariants are reported in the verification result.

**Test derivation:** Net with known invariant (e.g., token conservation); verify invariant is discovered."#
