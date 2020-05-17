(set-logic HORN)
(declare-fun inv-fn ((Array Int Int) Int Int) Bool)
(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var i! Int)
(declare-var swapped Int)
(declare-var swapped! Int)

(define-fun init-fn ((a (Array Int Int))(swapped Int)(i Int)) Bool 
  (and (= i 1) (= swapped 1)))


(define-fun trans-fn ((a (Array Int Int))(swapped Int)(i Int) (a! (Array Int Int))(swapped! Int)(i! Int)) Bool 
	(ite (> (select a i) (select a (- i 1))) (and (= (select a! i)(select a (- i 1)))
	(= (select a! (- i 1))(select a i))(= i! (+ i 1)) (= swapped! 1))
	(and (= swapped! 0)(= a! a) (= i! i))))


(define-fun trans-fn ((a (Array Int Int))(swapped Int)(i Int) (a! (Array Int Int))(swapped! Int)(i! Int)) Bool 
	(ite (> (select a i) (select a (- i 1))) (and (= (select a! i)(select a (- i 1)))
	(= (select a! (- i 1))(select a i))(= i! (+ i 1)) (= swapped! 1))
	(and (= swapped! 0)(= a! a) (= i! i))))

(assert (forall ((a (Array Int Int))(a! (Array Int Int))(swapped Int)(i Int)(swapped! Int)(i! Int)) 
 (=> (init-fn a swapped i) (inv-fn a swapped i))))

(assert (forall ((a (Array Int Int))(a! (Array Int Int))(swapped Int)(i Int)(swapped! Int)(i! Int)) (=> (and (inv-fn a swapped i) (trans-fn a  swapped i a! swapped! i!)) (inv-fn a! swapped! i!))))

(assert (forall ((a (Array Int Int))(a! (Array Int Int))(swapped Int)(i Int)(swapped! Int)(i! Int))
(=> (inv-fn a swapped i) (post-fn a swapped i))))
(check-sat)
(get-model)