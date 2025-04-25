;; panda -s docs/scn/mutex.scn docs/nets/mutex.net -M -P -v (last solution)
;;
;;   t1@1 t2 t4@5 t5 t6@6 t3 $8 	 SAT
;;   feas. sol.: [Δ(0,t1): 1, Δ(1,t2): 3, Δ(2,t4): 1, Δ(4,t5): 1, Δ(7,t6): 0, Δ(10,t3): 2, 𝜏: 0]
;;   constraints:
;; 1 ≤ z0 ≤ 1
;; 1 ≤ z1 - z0 ≤ 3
;; 5 ≤ z2 ≤ 5
;; 0 ≤ z2 - z1 ≤ 3
;;     z3 - z1 ≤ 4
;; 1 ≤ z3 - z2 < ∞
;; 6 ≤ z4 ≤ 6
;;     z4 - z1 ≤ 4
;; 0 ≤ z4 - z3 ≤ 3
;; 0 ≤ z5 - z1 ≤ 4
;; 0 ≤ z5 - z4 ≤ 3
;; 8 ≤ zc ≤ 8
;;     zc - z4 ≤ 3
;; 0 ≤ zc - z5 < ∞

(declare-const start Int)
(assert (= start 0))
(declare-const z0 Int)
(assert (>= z0 0))
(declare-const z1 Int)
(assert (>= z1 0))
(declare-const z2 Int)
(assert (>= z2 0))
(declare-const z3 Int)
(assert (>= z3 0))
(declare-const z4 Int)
(assert (>= z4 0))
(declare-const z5 Int)
(assert (>= z5 0))
(declare-const zc Int)
(assert (>= zc 0))

(assert (<= (- z0 start) 1))
(assert (<= (- z2 start) 5))
(assert (<= (- z4 start) 6))
(assert (<= (- zc start) 8))
(assert (<= (- start z0) (- 1)))
(assert (<= (- z1 z0) 3))
(assert (<= (- z0 z1) (- 1)))
(assert (<= (- z2 z1) 3))
(assert (<= (- z3 z1) 4))
(assert (<= (- z4 z1) 4))
(assert (<= (- z5 z1) 4))
(assert (<= (- z1 z2) 0))
(assert (<= (- start z2) (- 5)))
(assert (<= (- z2 z3) (- 1)))
(assert (<= (- z4 z3) 3))
(assert (<= (- z3 z4) 0))
(assert (<= (- start z4) (- 6)))
(assert (<= (- z5 z4) 3))
(assert (<= (- zc z4) 3))
(assert (<= (- z4 z5) 0))
(assert (<= (- z1 z5) 0))
(assert (<= (- start zc) (- 8)))
(assert (<= (- z5 zc) 0))
