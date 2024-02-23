(set-logic LIA)
(synth-fun f ((x1 Int) (x2 Int) (x3 Int)) Int)
(define-fun iteB ((b1 Bool) (b2 Bool) (b3 Bool))
 Bool (or (and b1 b2 ) (and (not b1 ) b3)))
 
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int)

(constraint 
(and (= (f x1 x2 x3) (f x3 x1 x2))
(or
(= (f x1 x2 x3) (- (+ x1 x3) x2))
(= (f x1 x2 x3) (- (+ x2 x3) x1))
(= (f x1 x2 x3) (- (+ x1 x2) x3))

)

)

)

(check-synth)