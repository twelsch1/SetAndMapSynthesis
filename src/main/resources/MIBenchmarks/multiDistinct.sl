(set-logic LIA)

(synth-fun f ((a1 Int) (a2 Int) (a3 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int) (declare-var a2 Int) (declare-var a3 Int)
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int) (declare-var x4 Int)


(constraint
(iteB (>= a1 a2)

(iteB (>= a1 a3)
(and
(=> 

(distinct x1 x2)

(distinct (f a1 a2 a3 x1 x2 x3 x4) (f a1 a2 a3 x2 x1 x3 x4))





)
(or
(= (f a1 a2 a3 x1 x2 x3 x4) 1)
(= (f a1 a2 a3 x1 x2 x3 x4) 2)

)
)


(and
(=> 

(distinct x1 x3)

(distinct (f a1 a2 a3 x1 x2 x3 x4) (f a1 a2 a3 x3 x2 x1 x4))





)
(or
(= (f a1 a2 a3 x1 x2 x3 x4) 1)
(= (f a1 a2 a3 x1 x2 x3 x4) 2)

)
)






)


(and
(=> 

(distinct x1 x4)

(distinct (f a1 a2 a3 x1 x2 x3 x4) (f a1 a2 a3 x4 x2 x3 x1))





)
(or
(= (f a1 a2 a3 x1 x2 x3 x4) 1)
(= (f a1 a2 a3 x1 x2 x3 x4) 2)

)
)

)
)

(check-synth)