(set-logic LIA)
(synth-fun f ((a1 Int) (a2 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int)

(declare-var a1 Int)
(declare-var a2 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(constraint 
    (and

    (= (f a1 a2 x1 x2 x3 x4) (f a1 a2 x1 x3 x2 x4))
     (= (f a1 a2 x1 x2 x3 x4) (f a1 a2 x2 x1 x3 x4))
     (or 
     
     (= (f a1 a2 x1 x2 x3 x4) x1)
     (= (f a1 a2 x1 x2 x3 x4) x2)
     (= (f a1 a2 x1 x2 x3 x4) x3)     
     )

    
    
    )
    
)
(check-synth)