(declare-const z0 Int)
(declare-const z1 Int)
(declare-const z2 Int)

(assert (<= (- z0 start) 2))
(assert (< (- z1 z0) 3))
(assert (<= (- z2 z1) 4))
(assert (= z2 9))
