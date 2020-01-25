(set-logic ALL)
(declare-var x (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var x! (Array (_ BitVec 2) (_ BitVec 32)))

(synth-fun inv-fn((parameter0 (Array (_ BitVec 2) (_ BitVec 32))))Bool) 


(constraint (=> 
(and 

(= (select x (_ bv0 2)) (_ bv0 32)) 
(= (select x (_ bv1 2)) (_ bv1 32)) 
(= (select x (_ bv2 2)) (_ bv2 32)) 
(= (select x (_ bv3 2)) (_ bv3 32)) 
)

(inv-fn x )))


(constraint (=> (and (inv-fn x ) (= x x!))(inv-fn x!))) 


(constraint (=> (inv-fn x )
 (and
 (bvsle(select x (_ bv0 2)) (select x (bvadd (_ bv0 2) (_ bv1 2))))
 (bvsle(select x (_ bv1 2)) (select x (bvadd (_ bv1 2) (_ bv1 2))))
 (bvsle(select x (_ bv2 2)) (select x (bvadd (_ bv2 2) (_ bv1 2))))
 )
 ))
(check-synth)