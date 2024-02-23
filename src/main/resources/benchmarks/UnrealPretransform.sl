(set-logic LIA)
(synth-fun f ((a Int) (x1 Int) (x2 Int) (x3 Int)) Int)
(define-fun iteB ((b1 Bool) (b2 Bool) (b3 Bool))
 Bool (or (and b1 b2 ) (and (not b1 ) b3)))
(declare-var a Int) (declare-var x1 Int) 
(declare-var x2 Int) (declare-var x3 Int) 

(constraint
(or

(and (= a 1) (or
(and (= (f a x1 x2 x3) (f a x2 x1 x3))
(or (= (f a x1 x2 x3) (+ x2 7)) (= (f a x1 x2 x3) (+ x1 7))))
(and (= (f a x1 x2 x3) (f a x1 x3 x2))
(or (= (f a x1 x2 x3) (+ x2 3)) (= (f a x1 x2 x3) (+ x3 3))))))


(and (= a 2) (= (f a x1 x2 x3) (f a x3 x2 x1))
(or (= (f a x1 x2 x3) (+ x2 7)) (= (f a x1 x2 x3) (+ x2 3))))

(and (distinct a 1) (distinct a 2) (= (f a x1 x2 x3) (+ x2 7)))
)


)


(check-synth)