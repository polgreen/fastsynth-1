(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(define-fun init-fn ((x (Array Int Int))) Bool 
  (exists ((index Int)) (= (select x index) 0)))

(define-fun post-fn ((x (Array Int Int))) Bool 
  (not(forall ((index Int)) (= (select x index) 1))))

(rule (=> (and (inv a b i n) (< i n) (= (store b i (select a (- n i1))) b1) (= i1 (+ i 1))) (inv a b1 i1 n)))

(rule (=> (and (inv a b i n) (>= i n) (<= 0 i1) (< i1 n) (not (= (select a i1) (select b (- n i1 1))))) fail))

(query fail)