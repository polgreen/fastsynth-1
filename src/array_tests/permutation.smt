(set-logic ALL)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var a! (Array Int Int))
(declare-var b! (Array Int Int))
(declare-var idx1 Int)
(declare-var idx2 Int)

(define-fun inv-fn((a (Array Int Int))(b (Array Int Int)))Bool
(and (or (= (select a 0) (select b 0)) (= (select a 0) (select b 1)) ) (or (= (select b 0) (select a 1)) (= (select b 1) (select a 1)) ) ))


(assert(not (and (=> (= a b)(inv-fn a b ))
(=> (and (and (< idx1 2) (>= idx1 0) ) (and (< idx2 2) (>= idx2 0) ) )(=> (and (inv-fn a b ) (and (= a! (store (store a idx1 (select a idx2)) idx2 (select a idx1))) (= b! b) ) )(inv-fn a! b! )))
(=> (inv-fn a b )(and (or (= (select a 0) (select b 0)) (= (select a 0) (select b 1)) ) (or (= (select a 1) (select b 0)) (= (select a 1) (select b 1)) ) )))))

(check-sat)
(get-model)