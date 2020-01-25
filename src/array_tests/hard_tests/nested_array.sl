(set-logic ALL)
(synth-fun inv-fn ((x (Array Int (Array Int Int)))) Bool)
(declare-var x (Array Int (Array Int Int)))
(declare-var x! (Array Int (Array Int Int)))

(define-fun init-fn ((x (Array Int (Array Int Int)))) Bool
	(forall ((index1 Int) (index2 Int)) (= (select (select x index1) index2) 1)))

(define-fun trans-fn ((x (Array Int (Array Int Int))) (x! (Array Int (Array Int Int)))) Bool
(exists ((index Int)) (= (select (select x! index) index ) 0)))


(define-fun post-fn ((x (Array Int (Array Int Int)))) Bool
	(forall ((index1 Int)) (exists ((index2 Int)) (= (select (select x index1) index2) 1))))

(constraint (=> (init-fn x) (inv-fn x)))
;(constraint (=> (and (inv-fn x) (trans-fn x x!)) (inv-fn x!)))
(constraint (=> (inv-fn x) (post-fn x)))
(check-synth)

