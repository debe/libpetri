; Linear state-equation bound (VER-015): y >= 0 with y.C <= 0 on every
; transition gives y.M <= y.M0 for every reachable M; sat = the violating
; markings' demand exceeds that bound, so none is reachable.
(set-logic QF_LIA)
(declare-const y0 Int)
(declare-const y1 Int)
(assert (>= y0 0))
(assert (>= y1 0))
(assert (= y0 0))
(assert (<= (+ (- y0) y1) 0))
(assert (>= y1 1))
(check-sat)
(get-model)