(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var alength Int)
(declare-var b (Array Int Int))
(declare-var b! (Array Int Int))
(declare-var blength Int)
(declare-var blength! Int)
(declare-var i Int)
(declare-var i! Int)

(define-fun init-fn ((i Int)(blength Int))Bool
(and (= i 0)(= blength 0)))
	

(define-fun trans-fn ((a1 (Array Int Int))(a2 (Array Int Int))(alength Int)(b (Array Int Int))
(blength Int)(i Int)(b! (Array Int Int))(blength! Int)(i! Int)) Bool
	(ite (< i alength)
		(and (ite (= (select a1 i)(select a2 i))
			(and (= b! (store b blength i)) (= blength! (+ blength 1)))
			(and (= b! b)(= blength! blength))) (= i! (+ i 1)))
		(and (= i! i)(= blength! blength)(= b! b))))

(define-fun post-fn ((a1 (Array Int Int))(a2 (Array Int Int))(alength Int)(b (Array Int Int))
(blength Int)(i Int)) Bool
(forall ((index Int))
	(=> (and (<= 0 index)(< index blength)) 
		(and (<= 0 (select b index))(< (select b index) alength)  )  ) ))

(synth-fun inv-fn ((a1 (Array Int Int))(a2 (Array Int Int))(alength Int)(b (Array Int Int))
(blength Int)(i Int)) Bool
; ((B Bool) (I Int))
; ((B Bool ((and B B)(or B B)(>= I I)
;  (>= alength 3)
;  (>= blength 3)
;  (>= i 3)
;  (forall ((local_var0 Int)) 
;  	(or (and (>= (+ (* (- 1) (select b local_var0)) alength ) 1) 
;  		(>= (select b local_var0) 0) ) (< blength (+ local_var0 1)))) 
;  (forall ((local_var0 Int)) (=> (and(<= 0 local_var0) (< local_var0 I ))
;  	(and (>= (+ (* (- 1) (select b local_var0)) alength ) 1) 
;  		(>= (select b local_var0) 0) )) )
;  (>= alength 0)
;  (>= blength 0)
;  (>= i 0)))
;  (I Int (1 0 alength blength i (+ I I)(- I)))
; )
)



(constraint (=> (init-fn i blength) (inv-fn a1 a2 alength b blength i)))
(constraint (=> (and (inv-fn a1 a2 alength b blength i) (trans-fn a1 a2 alength b blength i b! blength! i!))
				(inv-fn a1 a2 alength b! blength! i!)))

(constraint (=> (inv-fn a1 a2 alength b blength i) (post-fn a1 a2 alength b blength i)))
(check-synth)						