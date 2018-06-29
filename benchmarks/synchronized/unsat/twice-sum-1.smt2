(declare-rel f1 (Int Int))
(declare-rel fail ())
(declare-var y Int)
(declare-var n Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var m1 Int)
(declare-var m2 Int)

(rule (=> (<= n 0) (f1 n 0)))
(rule (=> (and (> n 0) (f1 (- n 1) y)) (f1 n (+ n n y))))

(rule (=> (and (>= x2 x1) (f1 x1 m1) (f1 x2 m2) (> m1 m2)) fail))
(query fail :print-certificate true)
