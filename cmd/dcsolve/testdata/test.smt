;; x > 1
;; y ≤ 2
;; y > x, defined as y - x > 0

(declare-const x Real)
(declare-const y Real)
(assert (> x 1))
(assert (<= y 2))
(assert (> (- y x) 0))
