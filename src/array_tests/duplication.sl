
(set-logic ALL)
(synth-fun inv-fn ((x (Array Int Int))) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))


(define-fun init-fn ((x (Array Int Int)) ) Bool 
	(forall ((index Int))
	(and
	(= (select x (bvsub (* 2 1) (+ index 1))) (select x (bvsub 1 (+ index 1))))
	(= (select x (bvsub (* 2 1) (+ index 2))) (select x (bvsub 1 (+ index 1)))))))


(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) (= (select x (* 2 index)) (select x (+ (* 2 index) 1)))))

(constraint (=> (init-fn x) (inv-fn x)))
;(constraint (=> (and (inv-fn x) (trans-fn x x! )) (inv-fn x!)))
(constraint (=> (inv-fn x ) (post-fn x )))
(check-synth)
