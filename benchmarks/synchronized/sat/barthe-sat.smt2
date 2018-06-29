(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)
(declare-var i Int)
(declare-var n Int)
(declare-var c Int)
(declare-var r Int)
(declare-var r1 Int)

(declare-rel f1 (Int Int Int Int))
(declare-rel fail ())

(rule (=> (>= i n) (f1 i n c 0)))
(rule (=> (and (< i n) (= r (+ c i r1)) (f1 (+ i 1) c n r1)) (f1 i n c r)))
(rule (=> (and (>= y1 0) (>= x2 x1) (>= y2 y1) (f1 0 x1 y1 z1) (f1 0 x2 y2 z2) (<= z1 z2)) fail))

(query fail :print-certificate true)
