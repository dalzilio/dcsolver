;; x > 1
;; x - y ≤ 0
;; y - x ≤ 1

(declare-const x Real)
(declare-const y Real)
(assert (> x 1))
(assert (<= y 2))
;; (assert (>= y x))
(assert (> (- y x) 0))
