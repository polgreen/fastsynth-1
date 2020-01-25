(set-logic ALL)
(synth-fun inv-fn ((x (Array Int Int))) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))

(define-fun init-fn ((x (Array Int Int))) Bool 
	(exists ((index Int)) (and (= (select x index) 1)
		(forall ((index2 Int)) (=> (> index2 index)
		(= (select x index )0 ))))))



(define-fun trans-fn ((x (Array Int Int)) 
	(x! (Array Int Int))) Bool 
	(forall ((index Int))  
		(=> (and (not (= (select x index) 0))(not (= (select x index) 1)))
			(= (select x! index) 2))))


(define-fun post-fn ((x (Array Int Int))) Bool 
		(exists ((index Int)) (and (= (select x index) 1)
		(forall ((index2 Int)) (=> (> index2 index)
		(= (select x index )0 ))))))

(constraint (=> (init-fn x) (inv-fn x)))
(constraint (=> (and (inv-fn x) (trans-fn x x!)) (inv-fn x!)))
(constraint (=> (inv-fn x) (post-fn x)))
(check-synth)
