; (declare-var a (Array Int Int))
(declare-var i Int)
(declare-var i! Int)
(declare-var alength Int)
(declare-var j Int)
(declare-var j! Int)

(define-fun init-fn ((i Int) (j Int))Bool
	(and (= i 0) (= j 0) ))

(define-fun trans-fn ((i Int) (j Int)(alength Int)(i! Int)(j! Int)) Bool
	(ite (< i alength) (and (= i! (+ i 1))(= j! 1) )
		(and (= i! i)(= j! j))))
	
(define-fun post-fn ((i Int)(j Int)(alength Int)) Bool
	(=> (>= i alength) (=> (= 0 alength)(= j 0) )))

(synth-fun inv-fn ((i Int) (j Int) (alength Int)) Bool )

(constraint (=> (init-fn i j)(inv-fn i j alength)))
(constraint (=> (and (inv-fn i j alength)(trans-fn i j alength i! j!))(inv-fn i! j! alength) ))
(constraint (=> (inv-fn i j alength)(post-fn i j alength)))
(check-synth)
