
(declare-var a (Array (_ BitVec 32) (_ BitVec 3)))
(declare-var b (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var c (_ BitVec 32))

(constraint(distinct 
(select a 
(select b c)) 
(_ bv3 3)))

(check-synth)
