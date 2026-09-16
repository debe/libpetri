; State-equation phase (VER-018): every reachable marking satisfies the marking
; equation for the firing counts of its run (an upper bound on a place a
; consume-all or reset arc clears); unsat = no such marking violates the property.
(set-logic QF_LIA)
(declare-const m0 Int)
(declare-const m1 Int)
(declare-const n0 Int)
(assert (>= m0 0))
(assert (>= m1 0))
(assert (>= n0 0))
(assert (= m1 (+ 0 n0)))
(assert (> m1 0))
(check-sat)
(get-model)