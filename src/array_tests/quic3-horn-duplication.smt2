(set-logic HORN)
(set-option :fp.spacer.ground_pobs false)
(set-option :fp.spacer.q3.use_qgen true)
(declare-fun inv-fn ((Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))


(define-fun init-fn ((x (Array Int Int)) ) Bool 
	(forall ((index Int))
	(and
	(= (select x (- (* 2 1) (+ index 1))) (select x (- 1 (+ index 1))))
	(= (select x (- (* 2 1) (+ index 2))) (select x (- 1 (+ index 1)))))))


(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) (= (select x (* 2 index)) (select x (+ (* 2 index) 1)))))


 
(assert (forall ((x (Array Int Int))(x! (Array Int Int))) 
(=> (init-fn x) (inv-fn x))))
(assert (forall ((x (Array Int Int))(x! (Array Int Int))) 
(=> (inv-fn x) (post-fn x))))
(check-sat)
(get-model)


