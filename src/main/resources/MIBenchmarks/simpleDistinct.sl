(set-logic LIA)

(synth-fun f ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int)

(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int) (declare-var x4 Int)

(constraint
(and
(=> (distinct x1 x2) (distinct (f x1 x2 x3 x4) (f x2 x1 x3 x4)))
(or
(= (f x1 x2 x3 x4) x3)
(= (f x1 x2 x3 x4) (+ x3 8))
(= (f x1 x2 x3 x4) 4)
(= (f x1 x2 x3 x4) 9)
)
)

)

(check-synth)