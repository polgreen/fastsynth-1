(set-logic ALL)
(synth-fun inv-fn ((a (Array Int Int))(b (Array Int Int)) (idx2 Int)) Bool)
(declare-var a (Array Int Int))
(declare-var a! (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b! (Array Int Int))
(declare-var idx1 Int)
(declare-var idx1! Int)


(define-fun init-fn ((a (Array Int Int)) (b (Array Int Int))) Bool
(= a b))


(define-fun trans-fn ((a (Array Int Int)) (b (Array Int Int)) (a! (Array Int Int)) (b! (Array Int Int))
(idx1 Int) (idx1! Int)) Bool
(and
(= a! (store a idx1 (select a 7)))
(= a! (store a 7 (select a idx1)))
(= b! b)))

(define-fun post-fn ((a (Array Int Int)) (b (Array Int Int))(idx2 Int)) Bool
(exists ((index2 Int)) (= (select a idx2) (select b index2))))


(constraint (=> (init-fn a b) (inv-fn a b idx1)))
(constraint (=> (and (inv-fn a b idx1) (trans-fn a b a! b! idx1 idx1!)) (inv-fn a! b! idx1!)))
(constraint (=> (inv-fn a b idx1) (post-fn a b idx1)))
(check-synth)
