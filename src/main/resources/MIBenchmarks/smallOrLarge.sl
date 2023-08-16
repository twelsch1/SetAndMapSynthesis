(set-logic LIA)

(synth-fun f ((a1 Int) (a2 Int) (x1 Int) (x2 Int)) Int)

(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int) (declare-var a2 Int)
(declare-var x1 Int) (declare-var x2 Int)

(constraint 

(and
(= (f a1 a2 x1 x2) (f a1 a2 x2 x1))
(iteB (>= a1 a2)
(and (>= x1 (f a1 a2 x1 x2)) (>= x2 (f a1 a2 x1 x2)))
(and (<= x1 (f a1 a2 x1 x2)) (<= x2 (f a1 a2 x1 x2)))

)


)

)


(check-synth)



