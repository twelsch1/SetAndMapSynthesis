(set-logic LIA)

(synth-fun f ((x Int) (y Int)) Int)

(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (f y x)))
(constraint 

(and (< (+ (* 3 y) (+ ( * 2 x) 7))   (f x y)) (< (+ (* 3 x) (+ ( * 2 y) 3))   (f x y))))

(check-synth)