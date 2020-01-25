(set-logic ALL)
(synth-fun inv-fn ((i Int) (x (Array Int Int))) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var i Int)
(declare-var i! Int)


(define-fun init-fn ((i Int) (x (Array Int Int))) Bool 
	(and (= i 0) 
	(= (select x 2) 1)))

(define-fun trans-fn ((i Int) (x (Array Int Int))
	(i! Int)) Bool 
		(ite (not (= (select x i) 1))
		(and (= (select x! i) 1)(= i! (+ i 1))) (= i! i)))

(define-fun post-fn ((i Int) (x (Array Int Int)) ) Bool
(or (not (= (select x i) 1)) 
	(exists ((index Int)) (and (= (select x index) 1)
	(forall ((index2 Int)) (=> (and (< index2 index) (>= index2 0)) (= (select x index2) 1)))))))

(constraint (=> (init-fn i x) (and (post-fn i x)(inv-fn i x))))
(constraint (=> (and (inv-fn i x) (post-fn i x) (trans-fn i x i!)) (and (post-fn i! x!)(inv-fn i! x!))))
;(constraint (=> (and (post-fn i x) (inv-fn i x)) (post-fn i x)))
(check-synth)


