(set-option :produce-proofs true)
(set-logic HORN)

(declare-fun Reachable (Int Int) Bool)
(declare-fun Error () Bool)

(assert (Reachable 3 0))

(assert (forall ((m0 Int) (m1 Int) (m0p Int) (m1p Int))
  (=> (and (Reachable m0 m1)
            (>= m0 2)
            (= m0p 0)
            (= m1p (+ m1 1))
            (>= m0p 0)
            (>= m1p 0))
      (Reachable m0p m1p))))

(assert (forall ((m0 Int) (m1 Int))
  (=> (and (Reachable m0 m1) (> m1 1))
      Error)))

(assert (not Error))
(check-sat)
(get-proof)
(get-model)