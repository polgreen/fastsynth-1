; sygus solver says unknown
(set-logic ALL)
(synth-fun inv-fn ((x (Array Int Int)) (c Int)) Bool)
(declare-var x (Array Int Int))
(declare-var c Int)

(define-fun init-fn ((x (Array Int Int)) (c Int)) Bool 
	(and (>= c 0)(= (select x c) 10)))

(define-fun post-fn ((x (Array Int Int))(c Int)) Bool 
	(exists ((index Int)) (=> (>= index 0) (and (= (select x index) 10)
	(forall ((index2 Int)) (=> (and (>= index2 0)(< index2 index)) (not (= (select x index2) 10))))))))

(constraint (=> (init-fn x c ) (inv-fn x c )))

(constraint (=> (inv-fn x c ) (post-fn x c )))
(check-synth)


