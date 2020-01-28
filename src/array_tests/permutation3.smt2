(set-logic ALL)
(declare-fun inv-fn ((Array Int Int) (Array Int Int)) Bool)
(declare-var a (Array Int Int))
(declare-var a! (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b! (Array Int Int))




(define-fun init-fn ((a (Array Int Int)) (b (Array Int Int))) Bool
(= a b))


(define-fun trans-fn ((a (Array Int Int)) (b (Array Int Int)) (a! (Array Int Int)) (b! (Array Int Int))) Bool
(and
(= a! (store (store a 1 (select a 0)) 0 (select a 1)))
(= b! b)))

(define-fun trans2-fn ((a (Array Int Int)) (b (Array Int Int)) (a! (Array Int Int)) (b! (Array Int Int))) Bool
(forall ((index1 Int )) (and (= (select a! index1) (+ (select a! index1)1))
(= (select b! index1) (+ (select b! index1)1)))))


(define-fun post-fn ((a (Array Int Int)) (b (Array Int Int))) Bool
(forall ((index1 Int))(exists ((index2 Int)) (= (select a index1) (select b index2)))))


(assert (forall ((x (Array Int Int))(y (Array Int Int))
(x! (Array Int Int))(y! (Array Int Int)))
(and 
(=> (init-fn x y) (inv-fn x y))
(=> (and (inv-fn x y) (trans-fn x y x! y!)) (inv-fn x! y!))
(=> (inv-fn x y) (post-fn x y)))))
(check-sat)
(get-model)
