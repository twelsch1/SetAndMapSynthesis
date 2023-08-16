; max4.sl
; Synthesize the maximum of 4 integers, from a purely declarative spec

;;Preconditions
;;logic set to Linear Integer Arithmetic
(set-logic LIA)
;;specifies the structure of the function to be synthesized
(synth-fun max4 ((x Int) (y Int) (z Int) (w Int)) Int
)

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)

;;Constraints
(constraint (>= (max4 x y z w) x))
(constraint (>= (max4 x y z w) y))
(constraint (>= (max4 x y z w) z))
(constraint (>= (max4 x y z w) w))
(constraint (or (= x (max4 x y z w))
            (or (= y (max4 x y z w))
            (or (= z (max4 x y z w))
	        (= w (max4 x y z w))))))

(check-synth)

