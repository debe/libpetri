; IC3/PDR certificate check (plain SMT-LIB2, not HORN):
; each VC below must be unsat for the certificate to stand.
(define-fun Reachable ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)

(declare-const m0 Int)
(declare-const m1 Int)
(declare-const m0p Int)
(declare-const m1p Int)
(declare-const n0 Int)
(declare-const n0p Int)

; VC1 initiation (VC1)
(push)
(assert (not (and (Reachable 3 0 0) (= (+ (* 1 3) (* 1 0)) 3) (>= 0 0) (= 3 (+ 3 (- 0))) (= 0 (+ 0 0)))))
(check-sat)
(pop)

; VC2 consecution (VC2)
(push)
(assert (>= m0 0))
(assert (>= m1 0))
(assert (>= n0 0))
(assert (and (Reachable m0 m1 n0) (= (+ (* 1 m0) (* 1 m1)) 3) (>= n0 0) (= m0 (+ 3 (- n0))) (= m1 (+ 0 n0))))
(assert (and (>= m0 1) (= m0p (- m0 1)) (= m1p (+ m1 1)) (>= m0p 0) (>= m1p 0) (= n0p (+ n0 1)) (>= n0p 0)))
(assert (not (and (Reachable m0p m1p n0p) (= (+ (* 1 m0p) (* 1 m1p)) 3) (>= n0p 0) (= m0p (+ 3 (- n0p))) (= m1p (+ 0 n0p)))))
(check-sat)
(pop)

; VC3 safety (VC3)
(push)
(assert (>= m0 0))
(assert (>= m1 0))
(assert (>= n0 0))
(assert (and (Reachable m0 m1 n0) (= (+ (* 1 m0) (* 1 m1)) 3) (>= n0 0) (= m0 (+ 3 (- n0))) (= m1 (+ 0 n0))))
(assert (> m1 3))
(check-sat)
(pop)