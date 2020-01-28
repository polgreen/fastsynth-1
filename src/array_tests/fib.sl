(set-logic ALL)
(synth-fun inv-fn ((i Int) (x (Array Int Int))) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var i Int)
(declare-var i! Int)

(define-fun init-fn ((i Int) (x (Array Int Int))) Bool 
(and
	(forall ((index Int)) (= (select x i) 1))
	(= i 0)))


(define-fun trans-fn ((i Int)  (x (Array Int Int)) 
	(i! Int) (x! (Array Int Int))) Bool 
	(and
	(= (select x! (+ i 2)) (+ (select x (+ i 1)) (select x i)))
	(= i! (+ i 1))))

(define-fun post-fn ((i Int) (x (Array Int Int))) Bool 
	(forall ((index Int))  (< (select x index) (select x (+ index 1)))))

(constraint (=> (init-fn i x) (inv-fn i x)))
(constraint (=> (and (inv-fn i x) (trans-fn i x i! x!)) (inv-fn i! x!)))
(constraint (=> (inv-fn i x) (post-fn i x)))
(check-synth)


