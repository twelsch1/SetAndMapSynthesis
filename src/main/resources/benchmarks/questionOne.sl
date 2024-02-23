(set-logic LIA)
(synth-fun f ((a1 Int) (x1 Int) (x2 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool)) Bool (or (and b1 b2) (and (not b1) b3)))

(declare-var a1 Int)  
(declare-var x1 Int) (declare-var x2 Int)

(constraint
(iteB (= a1 1)
(and (<= (f a1 x1 x2) (f a1 x2 x1)) 
(or 
(= (+ (* 2 x2) (+ x1 1)) (f a1 x1 x2)) 
(= (+ (* 2 x1) (+ x2 1)) (f a1 x1 x2))
(= (+ (* 2 x2) (+ x1 3)) (f a1 x1 x2)) 
(= (+ (* 2 x1) (+ x2 3)) (f a1 x1 x2))

))

(iteB (= a1 2)
(= (+ (* 2 x2) (+ x1 1)) (f a1 x1 x2)) 
(iteB (= a1 3)
(= (+ (* 2 x1) (+ x2 1)) (f a1 x1 x2))
(iteB (= a1 4)
(= (+ (* 2 x2) (+ x1 3)) (f a1 x1 x2)) 
(= (+ (* 2 x1) (+ x2 3)) (f a1 x1 x2))
))))
)





(check-synth)