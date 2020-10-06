(set-logic ALL)
(declare-var a (Array Int Int))
(declare-var a! (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b! (Array Int Int))
(declare-var alength Int)
(declare-var i Int)

(define-fun init-fn ((i Int))Bool
	(= i 0))

(declare-fun trans-fn ((i Int)(alength Int)(a (Array Int Int))
	(b (Array Int Int))(i! Int) (b! (Array Int Int))) Bool 
	(ite (< i alength)
		(and (i! (+ i 1))
		(ite (= (select a i) 1)
			( = b! (store b i 1))
			(= b! (select b i 0))))))

(declare-fun post-fn ((i Int)(alength Int)


