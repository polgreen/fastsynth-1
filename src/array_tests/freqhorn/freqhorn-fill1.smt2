(set-logic HORN)
(declare-fun inv-fn (Int (Array Int Int)) Bool)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var c Int)
(declare-var c! Int)



(define-fun init-fn ((c Int) (x (Array Int Int))) Bool 
(and (= c 0) (= (select x 0) 0)))

(define-fun trans-fn ((c Int) (x (Array Int Int)) (c! Int) (x! (Array Int Int))) Bool 
	(and (= c! (+ c 1))
	(and (= (select x! c) 0) 
	(forall ((index Int)) (=> (not(= index c)) (= (select x! index)(select x index)))))))


(define-fun post-fn ((c Int) (x (Array Int Int)) ) Bool 
	(forall ((index Int)) (=> (and (>= index 0) (< index c)) (= (select x index) 0))))

(assert (forall ((x (Array Int Int))(x! (Array Int Int))
 (c Int) (k Int)  (c! Int) (k! Int))
(=> (init-fn c k x) (inv-fn c k x))))
(assert (forall ((x (Array Int Int))(x! (Array Int Int))
 (c Int) (k Int)  (c! Int) (k! Int))
(=> (and (inv-fn c k x) (trans-fn c k x c! k! x!)) (inv-fn c! k! x!))))
(assert (forall ((x (Array Int Int))(x! (Array Int Int))
 (c Int) (k Int)  (c! Int) (k! Int))
(=> (inv-fn c k x) (post-fn c x))))
(check-sat)





