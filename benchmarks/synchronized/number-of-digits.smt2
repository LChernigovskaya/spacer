(declare-rel f1 (Int Int))
(declare-rel _div (Int Int Int))
(declare-rel fail ())
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var n Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)

(rule (=> (< x y) (_div x y 0)))
(rule (=> (and (>= x y) (_div (- x y) y z)) (_div x y (+ z 1))))

(rule (=> (< n 10) (f1 n 1)))
(rule (=> (and (>= n 10) (_div n 10 x) (f1 x y)) (f1 n (+ y 1))))
(rule (=> (and (> x1 x2) (f1 x1 z1) (f1 x2 z2) (< z1 z2)) fail))

(query fail :print-certificate true)
