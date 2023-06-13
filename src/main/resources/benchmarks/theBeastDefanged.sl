(set-logic LIA)

(synth-fun f ((a1 Int) (a2 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int) (declare-var a2 Int)
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int) (declare-var x4 Int) (declare-var x5 Int)

(constraint 
(iteB (>= a1 a2)
(and
(= (f a1 a2 x1 x2 x3 x4 x5) (f a1 a2  x1 x3 x2 x4 x5))
(= (f a1 a2 x1 x2 x3 x4 x5) (f a1 a2  x2 x1 x3 x4 x5))
(= (f a1 a2 x1 x2 x3 x4 x5) (f a1 a2  x2 x3 x1 x4 x5)) 
(= (f a1 a2 x1 x2 x3 x4 x5 ) (f a1 a2  x3 x1 x2 x4 x5))
(= (f a1 a2 x1 x2 x3 x4 x5) (f a1 a2  x3 x2 x1 x4 x5))
(or 

(= ( + 1 (- x1 (- x2 x3))) (f a1 a2  x1 x2 x3 x4 x5))
(= ( + 1 (- x1 (- x3 x2))) (f a1 a2  x1 x2 x3 x4 x5))
(= ( + 1 (- x2 (- x1 x3))) (f a1 a2  x1 x2 x3 x4 x5))
(= ( + 1 (- x2 (- x3 x1))) (f a1 a2  x1 x2 x3 x4 x5))   
(= ( + 1 (- x3 (- x1 x2))) (f a1 a2  x1 x2 x3 x4 x5))
(= ( + 1 (- x3 (- x2 x1))) (f a1 a2  x1 x2 x3 x4 x5))         
)

)

true

))

(check-synth)