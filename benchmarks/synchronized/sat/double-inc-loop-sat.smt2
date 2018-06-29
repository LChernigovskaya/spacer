(declare-var x1 Int)
(declare-var y1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var i Int)
(declare-var n Int)
(declare-var r Int)
(declare-var m1 Int)
(declare-var m2 Int)

(declare-rel f1 (Int Int Int))
(declare-rel fail ())

(rule (=> (>= i n) (f1 i n 0)))
(rule (=> (and (< i n) (f1 (+ i 1) n r)) (f1 i n (+ r 2))))
(rule (=> (and (>= x2 x1) (f1 1 x1 m1) (f1 1 x2 m2) (< m1 (+ m2 1))) fail))

(query fail :print-certificate true)
