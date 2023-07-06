(set-logic LIA)
(synth-fun f ((a1 Int) (x1 Int) (x2 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool)) Bool (or (and b1 b2) (and (not b1) b3)))

(declare-var a1 Int)  
(declare-var x1 Int) (declare-var x2 Int)

(constraint
(iteB (>= a1 5)
(and
(=> (distinct x1 x2) (distinct (f a1 x1 x2) (f a1 x2 x1)))
(or (= (f a1 x1 x2) a1) (= (f a1 x1 x2) (+ a1 8))
(= (f a1 x1 x2) 1) (= (f a1 x1 x2) 3)))

(and (= (f a1 x1 x2) (f a1 x2 x1)) 
(or (= (- x1 x2) (f a1 x2 x1)) (= (- x2 x1) (f a1 x2 x1))))

))

(check-synth)