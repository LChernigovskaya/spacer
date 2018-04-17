(declare-rel inc1 (Int Int Int))
(declare-rel fail ())

(declare-var r Int)
(declare-var n Int)
(declare-var m Int)
(declare-var n1 Int)
(declare-var m1 Int)
(declare-var n2 Int)
(declare-var m2 Int)
(declare-var n3 Int)
(declare-var m3 Int)
(declare-var i Int)

(rule (=> (>= i n) (inc1 i n 0)))
(rule (=> (and (< i n) (inc1 (+ 1 i) n r)) (inc1 i n (+ r 1))))
(rule (=> (and (> n1 0) (> n2 0) (> n3 0) (inc1 0 n1 m1) (inc1 0 n2 m2) (inc1 0 n3 m3) (> (+ m1 m2 m3) 0)) fail))

(query fail :print-certificate true)
