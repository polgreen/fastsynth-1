(set-logic HORN)

(declare-fun inv-fn ((Array Int Int) Int ) Bool)
(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var i! Int)

(define-fun init-fn ((a (Array Int Int))(i Int)) Bool 
 (and (= i 0) (= (select a i) 0)))


(define-fun trans-fn ((a (Array Int Int))(i Int) (a! (Array Int Int))(i! Int)) Bool 
  (and (ite (>= (select a i) 0) (= i! (+ i 1)) (= i! i)) (= a! a)))

(define-fun post-fn ((a (Array Int Int))(i Int)) Bool 
  (forall ((index Int)) (=> (and (< index i) (>= index 0)) (>= (select a index)0))))


(assert (forall ((a (Array Int Int))(a! (Array Int Int))
 (i! Int) (i Int)) 
 (=> (init-fn a i) (inv-fn a i))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))
 (i! Int) (i Int)) (=> (and (inv-fn a i) (trans-fn a  i a! i! )) (inv-fn a! i!))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))
 (i! Int) (i Int)) (=> (and (inv-fn a i )(< (select a i) 0)) (post-fn a i ))))
(check-sat)
(get-model)

; this encoding is wrong


