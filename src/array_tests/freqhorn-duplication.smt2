(set-logic HORN)
(declare-rel inv-fn ((Array Int Int)))

(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-rel fail ())


(define-fun init-fn ((x (Array Int Int)) ) Bool 
	(forall ((index Int))
	(and
	(= (select x (- (* 2 1) (+ index 1))) (select x (- 1 (+ index 1))))
	(= (select x (- (* 2 1) (+ index 2))) (select x (- 1 (+ index 1)))))))


(define-fun post-fn ((x (Array Int Int))) Bool 
(forall ((index Int)) (= (select x (* 2 index)) (select x (+ (* 2 index) 1)))))


 
(rule
(=> (init-fn x) (inv-fn x)))
(rule
(=> (and (inv-fn x) (post-fn x)) fail))
(query fail)



