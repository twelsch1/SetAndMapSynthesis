(set-logic LIA)

(synth-fun symm3 ((x Int) (y Int) (z Int)) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var x Int) (declare-var y Int) (declare-var z Int)

(constraint (= (symm3 x y z) (symm3 x z y)))
(constraint (= (symm3 x y z) (symm3 y x z)))
(constraint (= (symm3 x y z) (symm3 y z x))) 
(constraint (= (symm3 x y z) (symm3 z x y)))
(constraint (= (symm3 x y z) (symm3 z y x)))

(constraint (or 

(= (- x (- y z)) (symm3 x y z))
(= (- x (- z y)) (symm3 x y z))
(= (- y (- x z)) (symm3 x y z))
(= (- y (- z x)) (symm3 x y z))   
(= (- z (- x y)) (symm3 x y z))
(= (- z (- y x)) (symm3 x y z))         

))

(check-synth)
