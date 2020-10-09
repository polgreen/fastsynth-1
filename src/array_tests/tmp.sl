(set-logic ALL)
(declare-var c Int)
(declare-var x (Array Int Int))
(declare-var x! (Array Int Int))
(declare-var c! Int)
(synth-fun inv-fn((parameter0 Int)(parameter1 (Array Int Int)))Bool) 
(constraint (=> (and (< c 2) (>= c 0) )(=> (and (= c 0) (= (select x 0) 0) )(inv-fn c x ))))
(constraint (=> (and (< c 2) (>= c 0) )(=> (and (inv-fn c x ) (and (= c! (+ c 1 )) (= x! (store x c 0)) (and (=> (not (= 0 c))(= (select x! 0) (select x 0))) (=> (not (= 1 c))(= (select x! 1) (select x 1))) ) ) )(inv-fn c! x! ))))
(constraint (=> (and (< c 2) (>= c 0) )(=> (and (>= c 3) (inv-fn c x ) )(and (=> (and (>= 0 0) (< 0 3) )(= (select x 0) 0)) (=> (and (>= 1 0) (< 1 3) )(= (select x 1) 0)) ))))
(check-synth)