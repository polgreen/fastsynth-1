(set-logic ALL)
(synth-fun inv-fn ((x (Array Int Int))) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))


(define-fun init-fn ((x (Array Int Int))) Bool 
	(forall ((index Int)) (=> (< index 10)
	(= (select x (+ index 15)) index))))


(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) 
	(=> (and (< index 10) (>= index 0))
	(= (select x (+ index 15)) index))))

(constraint (=> (init-fn x) (inv-fn x)))
;(constraint (=> (and (inv-fn x) (trans-fn x x!)) (inv-fn x!)))
(constraint (=> (inv-fn x) (post-fn x)))
(check-synth)
