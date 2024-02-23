(set-logic LIA)
(synth-fun f ((a1 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool)) Bool (or (and b1 b2) (and (not b1) b3)))

(declare-var a1 Int)  
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int) (declare-var x4 Int)

(constraint

(and (<= (f a1 x1 x2 x3 x4) (f a1 x2 x1 x3 x4)) 
(<= (f a1 x1 x2 x3 x4) (f a1 x1 x2 x4 x3)) 
(or 
(= (+ (- (* 2 x4) (* 3 x3)) (+ (* 2 x2) (+ x1 1))) (f a1 x1 x2 x3 x4)) 
(= (+ (- (* 2 x4) (* 3 x3)) (+ (* 2 x1) (+ x1 1))) (f a1 x1 x2 x3 x4))
(= (+ (- (* 2 x3) (* 3 x4)) (+ (* 2 x2) (+ x1 1))) (f a1 x1 x2 x3 x4)) 
(= (+ (- (* 2 x3) (* 3 x4)) (+ (* 2 x1) (+ x1 1))) (f a1 x1 x2 x3 x4))     
))

)



(check-synth)