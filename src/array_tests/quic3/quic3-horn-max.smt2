(set-logic HORN)
(declare-fun inv-fn ((Array Int Int) Int Int) Bool)
(declare-var a (Array Int Int))
(declare-var max Int)
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var max! Int)
(declare-var i! Int)



(define-fun init-fn ((a (Array Int Int))(max Int)(i Int)) Bool 
  (and (= max (select a 0))(= i 0)))


(define-fun trans-fn ((a (Array Int Int))(max Int)(i Int) (a! (Array Int Int))(max! Int)(i! Int)) Bool  
   (and (= i! (+ i 1))
   (=> (> (select a i) max) (= max! (select a i)))))


(define-fun post-fn ((a (Array Int Int))(max Int)(i Int)) Bool 
  (forall ((index Int)) (=> (and (>= index 0)(< index i)) (<= (select a index) max))))


(assert (forall ((a (Array Int Int))(a! (Array Int Int))(max Int)(i Int)(max! Int)(i! Int)) 
(=> (init-fn a max i) (inv-fn a max i))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))(max Int)(i Int)(max! Int)(i! Int))  (=> (and (inv-fn a max i) (trans-fn a  max i a! max! i!)) (inv-fn a! max! i!))))
(assert (forall ((a (Array Int Int))(a! (Array Int Int))(max Int)(i Int)(max! Int)(i! Int))  (=> (inv-fn a max i) (post-fn a max i))))
(check-sat)
(get-model)

; based on sanfoundry 27