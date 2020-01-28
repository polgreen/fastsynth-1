(set-logic HORN)
(declare-rel inv-fn ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var y (Array Int Int))
(declare-var y! (Array Int Int))
(declare-var c1 Int)
(declare-var c2 Int)
(declare-var c1! Int)
(declare-var c2! Int)


(define-fun init-fn ((x (Array Int Int)) (y (Array Int Int)) (c1 Int) (c2 Int)) Bool 
	(and (forall ((index Int)) (= (select y index) 10))
	(forall ((index Int)) (= (select x index) 10))
	(> c1 0) (> c2 0)))


(define-fun trans-fn ((x (Array Int Int)) (y (Array Int Int))(c1 Int) (c2 Int)
	(x! (Array Int Int)) (y! (Array Int Int))(c1! Int) (c2! Int)) Bool 
	(forall ((index Int))
		(and
			(= (select x! index) (+ (select y index) c1))
			(= (select y! index ) (+ (select x index) c2))
			(= c1! c2!)
			)))

(define-fun post-fn ((x (Array Int Int)) (y (Array Int Int))(c1 Int) (c2 Int)) Bool 
	(forall ((index Int))(=(- (select x index) (select y index)) 0)))
 
(rule
(=> (init-fn x y c1 c2) (inv-fn x y c1 c2)))

(rule
(=> (and (inv-fn x y c1 c2) (trans-fn x y  c1 c2 x! y! c1! c2!)) (inv-fn x! y! c1 c2)))

(rule
(=> (and (inv-fn x y c1 c2) (not (post-fn x y c1 c2))) fail ))
(query fail :print-certificate true)
