;; panda -s docs/scn/mutex_t.scn docs/nets/mutex.net -MPv
;;
;; traces:
;;   t1 t2 t4 t5 t6 	 SAT
;;   feas. sol.: [Δ(0,t1): 0, Δ(1,t2): 1, Δ(2,t4): 0, Δ(3,t5): 1, Δ(4,t6): 0]
;;   constraints:
;; 
;; 0 ≤ z0 ≤ 3
;; 1 ≤ z1 - z0 ≤ 3
;; 0 ≤ z2 - z1 ≤ 3
;;     z3 - z1 ≤ 4
;; 1 ≤ z3 - z2 < ∞
;;     z4 - z1 ≤ 4
;; 0 ≤ z4 - z3 ≤ 3

(declare-const start Real)
(declare-const z0 Real)
(declare-const z1 Real)
(declare-const z2 Real)
(declare-const z3 Real)
(declare-const z4 Real)

(assert (<= (- z0 start) 3))
(assert (<= (- start z0) 0))
(assert (<= (- z1 z0) 3))
(assert (<= (- z0 z1) (- 1)))
(assert (<= (- z2 z1) 3))
(assert (<= (- z3 z1) 4))
(assert (<= (- z4 z1) 4))
(assert (<= (- z1 z2) 0))
(assert (<= (- z2 z3) (- 1)))
(assert (<= (- z4 z3) 3))
(assert (<= (- z3 z4) 0))