(set-logic HORN)
(declare-fun inv-fn ((Array Int Int) Int Int) Bool)
(declare-var a (Array Int Int))
(declare-var min Int)
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var min! Int)
(declare-var i! Int)

(define-fun init-fn ((a (Array Int Int))(min Int)(i Int)) Bool 
  (and (= min 0)(= i 0)))


(define-fun trans-fn ((a (Array Int Int))(min Int)(i Int) (a! (Array Int Int))(min! Int)(i! Int)) Bool 
   (or (> i 100) 
   (and (= i! (+ i 1))
   (=> (< (select a i) min) (= min! (select a i))))))



(define-fun post-fn ((a (Array Int Int))(min Int)(i Int)) Bool 
  (forall ((index Int)) (=> (< index 100) (> (select a index) min))))


(assert (forall ((a (Array Int Int))(a! (Array Int Int))(min Int)(i Int)(min! Int)(i! Int)) 
 (=> (init-fn a min i) (inv-fn a min i))))

(assert (forall ((a (Array Int Int))(a! (Array Int Int))(min Int)(i Int)(min! Int)(i! Int))  (=> (and (inv-fn a min i) (trans-fn a  min i a! min! i!)) (inv-fn a! min! i!))))

(assert (forall ((a (Array Int Int))(a! (Array Int Int))(min Int)(i Int)(min! Int)(i! Int))  (=> (and (inv-fn a min i )(>= i 100)) (post-fn a min i))))
(check-sat)
(get-model)
