(set-logic LIA)

(synth-fun f ((a1 Int) (a2 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int) (declare-var a2 Int)
(declare-var x1 Int) (declare-var x2 Int) (declare-var x3 Int) (declare-var x4 Int)


(constraint
(iteB (>= a1 a2)



(and
(=> 

(and (distinct x2 x3) (distinct x1 x3) (distinct x1 x2))



(and

(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x1 x3 x2 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x2 x3 x1 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x2 x1 x3 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x3 x2 x1 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x3 x1 x2 x4))


)

)
(or
(= (f a1 a2 x1 x2 x3 x4) 1)
(= (f a1 a2 x1 x2 x3 x4) 2)
(= (f a1 a2 x1 x2 x3 x4) 3)
(= (f a1 a2 x1 x2 x3 x4) 4)
(= (f a1 a2 x1 x2 x3 x4) 5)
(= (f a1 a2 x1 x2 x3 x4) 6)
)
)


(and
(=> 

(and (distinct x2 x3) (distinct x1 x3) (distinct x1 x2))



(and

(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x1 x3 x2 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x2 x3 x1 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x2 x1 x3 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x3 x2 x1 x4))
(distinct (f a1 a2 x1 x2 x3 x4) (f a1 a2 x3 x1 x2 x4))


)

)
(or
(= (f a1 a2 x1 x2 x3 x4) 1)
(= (f a1 a2 x1 x2 x3 x4) 7)
(= (f a1 a2 x1 x2 x3 x4) 8)
(= (f a1 a2 x1 x2 x3 x4) 9)
(= (f a1 a2 x1 x2 x3 x4) 10)
(= (f a1 a2 x1 x2 x3 x4) 11)
)
)






)
)

(check-synth)
