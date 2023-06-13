(set-logic LIA)
(synth-fun max6_hybrid ((x Int) (y Int) (z Int) (a Int) (b Int) (c Int) (d Int) (e Int) (f Int) ) Int) 


(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)
(declare-var c Int)
(declare-var d Int)
(declare-var e Int)
(declare-var f Int)

(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(constraint (and (= (max6_hybrid x y z a b c d e f) (max6_hybrid y x z a b c d e f))
(iteB  (and (>= a b) (>= a c) (>= a d) (>= a e) (>= a f))  
(or (= (+ z (- x y)) (max6_hybrid x y z a b c d e f)) (= (+ z (- y x)) (max6_hybrid x y z a b c d e f)))
(or (= (+ (- x y) (* 2 z)) (max6_hybrid x y z a b c d e f)) (= (+ (- y x) (* 2 z)) (max6_hybrid x y z a b c d e f)))
)
))

(check-synth)