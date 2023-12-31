(set-logic LIA)
(synth-fun f ((a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int) (a6 Int) (a7 Int) (x1 Int) (x2 Int) (x3 Int) ) Int)
(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )

(declare-var a1 Int)
(declare-var a2 Int)
(declare-var a3 Int)
(declare-var a4 Int)
(declare-var a5 Int)
(declare-var a6 Int)
(declare-var a7 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(constraint (and (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (f a1 a2 a3 a4 a5 a6 a7 x2 x1 x3))
(iteB (and true  (>= a1 a2)  (>= a1 a3)  (>= a1 a4)  (>= a1 a5)  (>= a1 a6)  (>= a1 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 10 x1) (+ (* 24 x2) (* 8 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 10 x2) (+ (* 24 x1) (* 8 x3))))) (iteB (and true  (>= a2 a1)  (>= a2 a3)  (>= a2 a4)  (>= a2 a5)  (>= a2 a6)  (>= a2 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 11 x1) (+ (* 25 x2) (* 9 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 11 x2) (+ (* 25 x1) (* 9 x3))))) (iteB (and true  (>= a3 a1)  (>= a3 a2)  (>= a3 a4)  (>= a3 a5)  (>= a3 a6)  (>= a3 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 12 x1) (+ (* 26 x2) (* 10 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 12 x2) (+ (* 26 x1) (* 10 x3))))) (iteB (and true  (>= a4 a1)  (>= a4 a2)  (>= a4 a3)  (>= a4 a5)  (>= a4 a6)  (>= a4 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 13 x1) (+ (* 27 x2) (* 11 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 13 x2) (+ (* 27 x1) (* 11 x3))))) (iteB (and true  (>= a5 a1)  (>= a5 a2)  (>= a5 a3)  (>= a5 a4)  (>= a5 a6)  (>= a5 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 14 x1) (+ (* 28 x2) (* 12 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 14 x2) (+ (* 28 x1) (* 12 x3))))) (iteB (and true  (>= a6 a1)  (>= a6 a2)  (>= a6 a3)  (>= a6 a4)  (>= a6 a5)  (>= a6 a7) ) (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 15 x1) (+ (* 29 x2) (* 13 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 15 x2) (+ (* 29 x1) (* 13 x3)))))  (or (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 16 x1) (+ (* 30 x2) (* 14 x3)))) (= (f a1 a2 a3 a4 a5 a6 a7 x1 x2 x3) (+ (* 16 x2) (+ (* 30 x1) (* 14 x3)))))))))))))
(check-synth)