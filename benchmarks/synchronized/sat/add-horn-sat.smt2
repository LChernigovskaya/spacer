(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)
(declare-var x2 Int)
(declare-var y2 Int)
(declare-var z2 Int)
(declare-var i Int)
(declare-var j Int)
(declare-var r Int)

(declare-rel f1 (Int Int Int))
(declare-rel fail ())

(rule (=> (= i j) (f1 i j j)))
(rule (=> (and (not (= i j)) (f1 (- i 1) (+ j 1) r)) (f1 i j r)))
(rule (=> (and (>= x1 0) (>= x2 x1) (>= y2 y1) (f1 x1 y1 z1) (f1 x2 y2 z2) (< z1 (+ z2 1))) fail))

(query fail :print-certificate true)
