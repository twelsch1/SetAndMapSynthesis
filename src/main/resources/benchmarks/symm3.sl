(set-logic LIA)

(synth-fun symm3 ((x Int) (y Int) (z Int)) Int)

(declare-var x Int) (declare-var y Int) (declare-var z Int)

(constraint (= (symm3 x y z) (symm3 x z y)))
(constraint (= (symm3 x y z) (symm3 y x z)))
(constraint (= (symm3 x y z) (symm3 y z x))) 
(constraint (= (symm3 x y z) (symm3 z x y)))
(constraint (= (symm3 x y z) (symm3 z y x)))

(constraint (or 

(= (- x (+ y z)) (symm3 x y z))

(= (- y (+ z x)) (symm3 x y z))   

(= (- z (+ y x)) (symm3 x y z))         

))

(check-synth)
