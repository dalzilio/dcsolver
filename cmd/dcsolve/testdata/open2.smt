;; panda docs/nets/open2.net  -s docs/scn/open2.scn -M -P -v
;; 
;; reached state(s): 3
;; traces:
;;   t1 t1 t2 	 SAT
;;   feas. sol.: [Δ(0,t1): 2⁻, Δ(1,t1): 1⁻, Δ(2,t2): 0]
;;   constraints:
;; 0 ≤ z0 < 2
;;     z1 < 4
;; 0 ≤ z1 - z0 < 2
;; 3 ≤ z2 < 4
;; 0 ≤ z2 - z1 < ∞

(declare-const start Int)
(assert (= start 0))
(declare-const z0 Int)
(assert (>= z0 0))
(declare-const z1 Int)
(assert (>= z1 0))
(declare-const z2 Int)
(assert (>= z2 0))

(assert (< (- z0 start) 2))
(assert (< (- z1 start) 4))
(assert (< (- z2 start) 4))
(assert (<= (- start z0) 0))
(assert (< (- z1 z0) 2))
(assert (<= (- z0 z1) 0))
(assert (<= (- z1 z2) 0))
(assert (<= (- start z2) (- 3)))