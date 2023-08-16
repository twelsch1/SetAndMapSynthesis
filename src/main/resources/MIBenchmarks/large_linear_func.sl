(set-logic LIA)

(synth-fun f ((x Int) (y Int)) Int)

(define-fun dfunc ((x Int)) Int
    (+ (* x 100) 1000))
    
    
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (f y x)))
(constraint (and (>= (dfunc x) (f x y)) (>= (dfunc y) (f x y))))

(check-synth)