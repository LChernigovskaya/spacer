(declare-rel _mod (Int Int Int))
(declare-rel fail ())
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)

(rule (=> (< x y) (_mod x y x)))
(rule (=> (and (>= x y) (_mod (- x y) y z)) (_mod x y z)))

(rule (=> (and (> y 0) (> x 0) (> a 0) (_mod a y z) (_mod (+ a y) y b) (= z b)) fail))

(query fail :print-certificate true)
