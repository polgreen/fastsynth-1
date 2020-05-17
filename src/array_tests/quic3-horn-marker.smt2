(set-logic HORN)

(declare-fun inv-fn ((Array Int Int) Int Int) Bool)
(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var i! Int)
(declare-var pos Int)
(declare-var pos! Int)



(define-fun init-fn ((a (Array Int Int))(i Int)(pos Int)) Bool 
  (and (= (select a pos) 7) (= i 0) (>= 0 pos)))


(define-fun trans-fn ((a (Array Int Int))(i Int)(pos Int) (a! (Array Int Int))(i! Int)(pos! Int)) Bool  
   (and (ite (= (select a i ) 7) (= i! i)(= i! (+ i 1))) (= pos! pos) (= a! a)))


(define-fun post-fn ((a (Array Int Int))(i Int)(pos Int)) Bool 
  (<= i pos))


(assert (forall ((a (Array Int Int))(a! (Array Int Int))(pos Int)(i Int)(pos! Int)(i! Int))  
(=> (init-fn a i pos) (inv-fn a i pos))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))(pos Int)(i Int)(pos! Int)(i! Int))  (=> (and (inv-fn a i pos) (trans-fn a  i pos a! i! pos!)) (inv-fn a! i! pos!))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))(pos Int)(i Int)(pos! Int)(i! Int)) (=> (inv-fn a i i) (post-fn a i i))))
(check-sat)
(get-model)

; based on standard-sentinal-2c