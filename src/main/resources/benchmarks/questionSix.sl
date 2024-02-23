(set-logic LIA)
(synth-fun f ((a Int) (b Int) (c Int) (d Int) (e Int)) Int)
(define-fun iteB ((b1 Bool) (b2 Bool) (b3 Bool))
 Bool (or (and b1 b2 ) (and (not b1 ) b3)))
(declare-var a1 Int) (declare-var a2 Int)
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int)

(constraint (iteB (= a1 1)
(and (>= (f a1 a2  x1 x2 x3) (f a1 a2  x1 x3 x2))
(>= (f a1 a2  x1 x2 x3) (f a1 a2  x2 x1 x3))
(= (f a1 a2  x1 x2 x3) (f a1 a2  x2 x3 x1)) 
(= (f a1 a2  x1 x2 x3) (f a1 a2  x3 x1 x2))
(= (f a1 a2  x1 x2 x3) (f a1 a2  x3 x2 x1))
(or (= (+ x1 (+ (* 2 x2) (* 3 x3))) (f a1 a2  x1 x2 x3))
(= (+ x1 (+ (* 2 x3) (* 3 x2))) (f a1 a2  x1 x2 x3))
(= (+ x2 (+ (* 2 x1) (* 3 x3))) (f a1 a2  x1 x2 x3))
(= (+ x2 (+ (* 2 x3) (* 3 x1))) (f a1 a2  x1 x2 x3))
(= (+ x3 (+ (* 2 x1) (* 3 x2))) (f a1 a2  x1 x2 x3)) 
(= (+ x3 (+ (* 2 x2) (* 3 x1))) (f a1 a2  x1 x2 x3))))

(and (= (f a1 a2 x1 x2 x3) (f a1 a2 x2 x1 x3))
(= (f a1 a2 x1 x2 x3) (f a1 x3 x2 x1 a2))
(or (= (f a1 a2 x1 x2 x3) (+ x1 a2))
(= (f a1 a2 x1 x2 x3) (+ x2 a2))
(= (f a1 a2 x1 x2 x3) (+ x2 x3))
(= (f a1 a2 x1 x2 x3) (+ x1 x3))


)
)


))


(check-synth)