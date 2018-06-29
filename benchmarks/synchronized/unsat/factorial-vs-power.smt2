(declare-rel fact (Int Int))
(declare-rel mult (Int Int Int))
(declare-rel pwr (Int Int Int))
(declare-rel fail ())

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)
(declare-var c Int)

(rule (mult 0 y 0) MULT-FACT)
(rule (=> (and (mult (- x 1) y z) (> x 0)) (mult x y (+ y z))) MULT_REC)

(rule (fact 0 1) FACT-FACT)
(rule (=> (and (> a 0) (fact (- a 1) c) (mult c a b)) (fact a b)) FACT-REC)

(rule (fact 0 1) POW-FACT)
(rule (=> (and (> a 0) (pwr (- a 1) x c) (mult c x b)) (pwr a x b)) POW-REC)

(rule (=> (and (> x 1) (pwr x x a) (fact x b) (<= a b)) fail) QUERY)
(query fail :print-certificate true)
