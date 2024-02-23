(set-logic LIA)

(synth-fun f ((a1 Int) (x1 Int) (x2 Int) (x3 Int)) Int)

(declare-var a1 Int)
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int)

(constraint 

(and
(or
(= (f a1 x1 x2 x3) (- (- (* 2 x1) (* 3 x2)) x3))
(= (f a1 x1 x2 x3) (- (- (* 2 x1) (* 3 x3)) x2))
(= (f a1 x1 x2 x3) (- (- (* 2 x3) (* 3 x1)) x2))
(= (f a1 x1 x2 x3) (- (- (* 2 x3) (* 3 x2)) x1))
(= (f a1 x1 x2 x3) (- (- (* 2 x2) (* 3 x1)) x3))
(= (f a1 x1 x2 x3) (- (- (* 2 x2) (* 3 x3)) x1))
)

(= (f a1 x1 x2 x3) (f a1 x3 x2 x1))
)

)

(check-synth)