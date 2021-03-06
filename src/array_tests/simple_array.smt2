(set-logic ALL)
(declare-fun inv-fn ((Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))

(define-fun init-fn ((x (Array Int Int))) Bool 
	(forall ((index Int)) (= (select x index) 10)))


(define-fun trans-fn ((x (Array Int Int)) 
	(x! (Array Int Int))) Bool 
	(forall ((index Int))  
		(ite (<= (select x index) 100)
			(= (select x! index) (+ (select x index) 1))
			(= (select x! index ) (select x index))
			)))

(define-fun post-fn ((x (Array Int Int))) Bool 
	(forall ((index Int)) (>= (select x index) 10)))


(assert (forall ((x (Array Int Int))
(x! (Array Int Int)))
(and 
(=> (init-fn x) (inv-fn x))
(=> (and (inv-fn x) (trans-fn x x! )) (inv-fn x! ))
(=> (inv-fn x ) (post-fn x )))))
(check-sat)
(get-model)

