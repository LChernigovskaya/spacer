(declare-rel mult (Int Int Int))
(declare-rel pwr (Int Int Int))
(declare-rel fail ())
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)

(rule (=> (= x 0) (mult x y 0)))
(rule (=> (and (not (= x 0)) (mult (- x 1) y z)) (mult x y (+ z y))))
(rule (=> (= a 0) (pwr a x 1)))
(rule (=> (and (not (= a 0)) (pwr (- a 1) x z) (mult z x y)) (pwr a x y)))

(rule (=> (and (> y x) (> x 0) (> a 0) (pwr a y z) (pwr a x b) (> z b)) fail))

(query fail :print-certificate true)
