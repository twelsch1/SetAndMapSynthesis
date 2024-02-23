(set-logic LIA)
(synth-fun f ((x Int) (y Int) (z Int) (w Int)) Int)

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)
(constraint 
 
 
 (and (= (f x y z w) (f y x z w)) (= (f x y z w) (f x y w z))
 (or
 
 (= (f x y z w) (+ (+ (+ x (* 2 y)) (* 3 z)) (* 4 w)))
 (= (f x y z w) (+ (+ (+ y (* 2 x)) (* 3 z)) (* 4 w)))
 (= (f x y z w) (+ (+ (+ x (* 2 y)) (* 4 z)) (* 3 w)))
 (= (f x y z w) (+ (+ (+ y (* 2 x)) (* 4 z)) (* 3 w)))
 
 )
 
 )
    
)
(check-synth)