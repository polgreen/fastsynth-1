
(set-logic ALL)
(declare-fun inv-fn ((Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))


(define-fun init-fn ((x (Array Int Int)) ) Bool 
	(forall ((index Int))
	(and
	(= (select x (bvsub (* 2 1) (+ index 1))) (select x (bvsub 1 (+ index 1))))
	(= (select x (bvsub (* 2 1) (+ index 2))) (select x (bvsub 1 (+ index 1)))))))


(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) (= (select x (* 2 index)) (select x (+ (* 2 index) 1)))))


 
(assert (forall ((x (Array Int Int))(x! (Array Int Int))) 
(and (=> (init-fn x) (inv-fn x))
(=> (and (inv-fn x ) (trans-fn x x!)) (inv-fn x!))
(=> (inv-fn x y) (post-fn x y)))))
(check-sat)
(get-model)


