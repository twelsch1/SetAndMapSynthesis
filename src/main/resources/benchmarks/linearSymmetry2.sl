(set-logic LIA)
(synth-fun f ((a1 Int) (a2 Int) (x1 Int) (x2 Int) (x3 Int) ) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int)
(declare-var a2 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (and (= (f a1 a2 x1 x2 x3) (f a1 a2 x2 x1 x3))
(iteB (and true (>= a1 a2)) 
(or (= (f a1 a2 x1 x2 x3) (+ (* 10 x1) (+ (* 24 x2) (* x3 8)))) (= (f a1 a2 x1 x2 x3) (+ (* 10 x2) (+ (* 24 x1) (* x3 8)))))  
(or (= (f a1 a2 x1 x2 x3) (+ (* 11 x1) (+ (* 25 x2) (* x3 9)))) (= (f a1 a2 x1 x2 x3) (+ (* 11 x2) (+ (* 25 x1) (* x3 9)))))

)
))
(check-synth)