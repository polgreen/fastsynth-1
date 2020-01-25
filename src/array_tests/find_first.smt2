(set-logic ALL)
(declare-fun x () (Array Int Int))
(declare-fun x! () (Array Int Int))
(declare-fun i () Int)
(declare-fun i! () Int)
(declare-fun c () Int)

(define-fun init ((x (Array Int Int)) (c Int)) Bool 
	(= (select x c) 10))

(define-fun post-fn ((x (Array Int Int))(c Int)) Bool 
	(exists ((index Int)) (=> (>= index 0) (and (= (select x index) 10)
	(forall ((index2 Int)) (=> (and (>= index2 0)(< index2 index)) (not (= (select x index2) 10))))))))

(assert (not (=> (init x c) (post-fn x c))))

(check-sat)
(get-model)

;(constraint (=> (init-fn i x c) (inv-fn i x c)))
;(constraint (=> (and (inv-fn i x c) (trans-fn i x c i!)) (inv-fn i! x c)))
;(constraint (=> (inv-fn i x c) (post-fn i x c)))
;(check-synth)


