(set-logic ALL)

(declare-fun inv-fn (Int Int (Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var c Int)
(declare-var k Int)


(define-fun init-fn ((c Int) (k Int) (x (Array Int Int))) Bool 
	(and(= k 1000)(forall((index Int))(=> (< index k)(= (select x index) c)))))

(define-fun post-fn ((c Int) (x (Array Int Int)) ) Bool 
	(exists ((index Int)) (and (= (select x index) c)
	(forall ((index2 Int)) (=> (and (>= index2 0)(< index2 index)) (= (select x index2) c))))))

(assert (forall ((x (Array Int Int))
 (c Int) (k Int))
(and 
(=> (init-fn c k x) (inv-fn c k x))
(=> (inv-fn c k x) (post-fn c k x)))))
(check-sat)
(get-model)


