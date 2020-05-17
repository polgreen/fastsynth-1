(set-logic ALL)
(synth-fun inv-fn ((a (Array Int Int)) (b (Array Int Int))(c (Array Int Int))(i Int)) Bool)
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var b! (Array Int Int))
(declare-var c! (Array Int Int))
(declare-var i! Int)


(define-fun init-fn ((a (Array Int Int)) (b (Array Int Int))(c (Array Int Int))(i Int)) Bool 
	(= i 0))

(define-fun trans-fn ((a (Array Int Int)) (b (Array Int Int))(c (Array Int Int))(i Int)(a! (Array Int Int)) (b! (Array Int Int))(c! (Array Int Int))(i! Int)) Bool	  
		(and (= i! (+ i 1))
		(= (select c! i)(bvsub (select a i) (select b i)))))


(define-fun post-fn ((a (Array Int Int)) (b (Array Int Int))(c (Array Int Int))(i Int)) Bool 
(forall ((index Int)) (=> (< index 4) (= (select c index) (bvsub (select a index) (select b index))))))

(constraint (=> (init-fn a b c i) (inv-fn a b c i)))
(constraint (=> (and (inv-fn a b c i) (trans-fn a b c i a! b! c! i! )) (inv-fn a! b! c! i!)))
(constraint (=> (and (inv-fn a b c i )(> i 4)) (post-fn a b c i )))
(check-synth)
