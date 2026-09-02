; IC3/PDR certificate check (plain SMT-LIB2, not HORN):
; each VC below must be unsat for the certificate to stand.
(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool
    true)

(declare-const m0 Int)
(declare-const m1 Int)
(declare-const m0p Int)
(declare-const m1p Int)

; VC1 initiation (VC1)
(push)
(assert (not (Reachable 3 0)))
(check-sat)
(pop)

; VC2 consecution (VC2)
(push)
(assert (>= m0 0))
(assert (>= m1 0))
(assert (Reachable m0 m1))
(assert (and (>= m0 2) (= m0p 0) (= m1p (+ m1 1)) (>= m0p 0) (>= m1p 0)))
(assert (not (Reachable m0p m1p)))
(check-sat)
(pop)

; VC3 safety (VC3)
(push)
(assert (>= m0 0))
(assert (>= m1 0))
(assert (Reachable m0 m1))
(assert (> m1 1))
(check-sat)
(pop)