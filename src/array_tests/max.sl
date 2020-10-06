; sygus solver times out. test solution?
(set-logic ALL)
(synth-fun inv-fn ((a (Array Int Int))(max Int)(i Int)) Bool)
(declare-var a (Array Int Int))
(declare-var max Int)
(declare-var i Int)
(declare-var a! (Array Int Int))
(declare-var max! Int)
(declare-var i! Int)

(define-fun init-fn ((a (Array Int Int))(max Int)(i Int)) Bool 
  (and (= max (select a 0))(= i 0)))


(define-fun trans-fn ((a (Array Int Int))(max Int)(i Int)(max! Int)(i! Int)) Bool  
   (ite (< i 100)
   (and (= i! (+ i 1))
   (=> (> (select a i) max) (= max! (select a i))))
   (and (= max! max) (= i! i))))


(define-fun post-fn ((a (Array Int Int))(max Int)(i Int)) Bool 
  (forall ((index Int)) (=> (and (>= index 0)(< index i)) (<= (select a index) max))))


(constraint (=> (init-fn a max i) (inv-fn a max i)))
(constraint (=> (and (inv-fn a max i) (trans-fn a  max i max! i!)) (inv-fn a max! i!)))
(constraint (=> (inv-fn a max i) (post-fn a max i)))
(check-synth)

; based on sanfoundry 27