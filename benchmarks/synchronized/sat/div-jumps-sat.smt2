(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var r Int)
(declare-var r1 Int)

(declare-rel d (Int Int Int))
(declare-rel fail ())

(rule (=> (< x y) (d x y 0)))
(rule (=> (and (>= x y) (d (- x y) y r)) (d x y (+ r 1))))
(rule (=> (and (> y 0) (> a 0) (d a y r) (d (+ a y) y r1) (= r1 (+ 1 r))) fail))

(query fail :print-certificate true)
