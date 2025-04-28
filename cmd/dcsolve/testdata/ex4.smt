;; panda -s docs/scn/mutex_t_timed.scn docs/nets/mutex.net -M -P -v
;; reached state(s): 5
;; traces:
;;   t1@1 t2 t4@5 t5 t6@6 $8 	 SAT
;;   feas. sol.: [Δ(0,t1): 1, Δ(1,t2): 3, Δ(2,t4): 1, Δ(3,t5): 1, Δ(4,t6): 0, 𝜏: 2]
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
;; 8 ≤ zc ≤ 8
;;     zc - z1 ≤ 4
;; 0 ≤ zc - z4 ≤ 3

(declare-const start Real)
(declare-const z0 Real)
(declare-const z1 Real)
(declare-const z2 Real)
(declare-const z3 Real)
(declare-const z4 Real)
(declare-const zc Real)

(assert (<= (- z0 start) 1))
(assert (<= (- z2 start) 5))
(assert (<= (- z4 start) 6))
(assert (<= (- start z0) (- 1)))
(assert (<= (- z1 z0) 3))
(assert (<= (- z0 z1) (- 1)))
(assert (<= (- z2 z1) 3))
(assert (<= (- z3 z1) 4))
(assert (<= (- z4 z1) 4))
(assert (<= (- zc z1) 4))
(assert (<= (- z1 z2) 0))
(assert (<= (- start z2) (- 5)))
(assert (<= (- z2 z3) (- 1)))
(assert (<= (- z4 z3) 3))
(assert (<= (- z3 z4) 0))
(assert (<= (- start z4) (- 6)))
(assert (<= (- zc z4) 3))
(assert (<= (- z4 zc) 0))

;;
;; The trace is not feasible if we choose zc > 8, whereas
;; there is a solution with zc = 8.
;;
(assert (< (- start zc) (- 8)))
;; (assert (<= (- zc start) 8))
