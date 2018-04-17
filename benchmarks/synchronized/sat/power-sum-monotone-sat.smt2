(declare-rel mult (Int Int Int))
(declare-rel pwr (Int Int Int))
(declare-rel fail ())
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)
(declare-var c Int)
(declare-var d Int)

(rule (=> (= x 0) (mult x y 0)))
(rule (=> (and (not (= x 0)) (mult (- x 1) y z)) (mult x y (+ z y))))
(rule (=> (= a 0) (pwr a x 1)))
(rule (=> (and (not (= a 0)) (pwr (- a 1) x z) (mult z x y)) (pwr a x y)))

(rule (=> (and (< 0 x) (< 0 y) (= z (+ x y)) (> a 0) (pwr a x b) (pwr a y c) (pwr a z d) (<= (+ b c) d)) fail))

(query fail :print-certificate true)
