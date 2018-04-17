(declare-rel inc1 (Int Int Int))
(declare-rel fail ())

(declare-var r Int)
(declare-var r1 Int)
(declare-var n Int)
(declare-var m Int)
(declare-var i Int)

(rule (=> (>= i n) (inc1 i n 0)))
(rule (=> (and (< i n) (inc1 (+ 1 i) n r)) (inc1 i n (+ r 1) )))
(rule (=> (and (> n 0) (> m 0) (inc1 0 n r) (inc1 0 n r1) (> (+ r r1) 0)) fail))

(query fail :print-certificate true)
