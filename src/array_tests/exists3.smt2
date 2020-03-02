(set-logic ALL)
(declare-fun inv-fn (Int (Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var i Int)
(declare-var i! Int)

(define-fun init-fn ((x (Array Int Int))) Bool 
	(forall ((index Int)) (= (select x index) index)))


(define-fun trans-fn ((x (Array Int Int)) 
	(x! (Array Int Int))) Bool 
		(= x! (store x 0 0)))

(define-fun post-fn ((x (Array Int Int))) Bool 
	(exists ((index Int)) (= (select x index) 1)))

(assert (forall ((x (Array Int Int))
(x! (Array Int Int)) (i Int))
(and 
(=> (init-fn i x) (inv-fn i x))
(=> (and (inv-fn i x) (trans-fn i x i! x! )) (inv-fn i! x! ))
(=> (inv-fn i x ) (post-fn i x )))))
(check-sat)
(get-model)
