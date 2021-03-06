(set-logic BV)

(synth-fun inv ((x (BitVec 32))) Bool )

; base case
(constraint (inv #x00000000))

(declare-var x (BitVec 32) )

; property
(constraint (=> (and (inv x) (not (= (bvadd x #x00000001) #x0000000a)))
                (not (= (bvadd x #x00000001) #x0000000f))))

; step case
(constraint (=> (and (inv x) (not (= (bvadd x #x00000001) #x0000000a)))
                (inv (bvadd x #x00000001))))

(check-synth)
