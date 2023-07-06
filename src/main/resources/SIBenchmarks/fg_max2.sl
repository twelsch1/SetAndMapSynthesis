;;Grammar set to LIA
;;See figure 2.
(set-logic LIA)
;;Constraints on the input
;;Defines the structure of
;;the function to be synthesized
;;i.e. two integer inputs
(synth-fun max2 ((x Int) (y Int)) Int
)
;;inputs are declared
(declare-var x Int)
(declare-var y Int)
;;constraints on the output,
;;ensure that output is greater
;;than or equal to x
(constraint (>= (max2 x y) x))
;;ensure that output is greater than
;;or equal to y 
(constraint (>= (max2 x y) y))
;;ensure that the output is x or
;;y 
(constraint (or (= x (max2 x y))
				(= y (max2 x y))))
(check-synth)

