(set-logic ALL)
(synth-fun inv-fn ((x (Array (_ BitVec 32) (_ BitVec 32)))) Bool)
(declare-var x (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x! (Array (_ BitVec 32) (_ BitVec 32)))


(define-fun init-fn ((x (Array (_ BitVec 32) (_ BitVec 32))) ) Bool 
	(forall ((index (BitVec 32))) (=> (bvult index (_ bv100 32))(= (select x index) index))))


(define-fun trans-fn ((x (Array (_ BitVec 32) (_ BitVec 32)))
	(x! (Array (_ BitVec 32) (_ BitVec 32)))) Bool 
	(= x! x))

(define-fun post-fn ((x (Array (_ BitVec 32) (_ BitVec 32)))) Bool 
(forall ((index (BitVec 32))) 
	(=> (bvult index (_ bv10 32)) (bvule (select x index) (select x (bvadd index (_ bv1 32)))))))

(constraint (=> (init-fn x) (inv-fn x)))
(constraint (=> (and (inv-fn x) (trans-fn x x! )) (inv-fn x!)))
(constraint (=> (inv-fn x ) (post-fn x )))
(check-synth)
