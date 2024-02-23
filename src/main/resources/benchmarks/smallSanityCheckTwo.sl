(set-logic LIA)

(synth-fun f ((x Int) (y Int) (z Int)) Int)

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(constraint (= (f x y z) (f y z x)))
(constraint 

(and (<= x (f x y z)) (<= y (f x y z)) (= z (f x y z))  )

)

(check-synth)