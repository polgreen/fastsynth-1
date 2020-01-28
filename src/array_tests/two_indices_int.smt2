(set-logic ALL)
(declare-fun inv-fn ((Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))


(define-fun init-fn ((x (Array Int Int)) ) Bool 
	(forall ((index Int))(= (select x index) index)))



(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) (<= (select x index) (select x (+ index 1)))))

(assert (forall ((x (Array Int Int))
(x! (Array Int Int)))
(and 
(=> (init-fn x) (inv-fn x))
(=> (inv-fn x ) (post-fn x )))))
(check-sat)
(get-model)
