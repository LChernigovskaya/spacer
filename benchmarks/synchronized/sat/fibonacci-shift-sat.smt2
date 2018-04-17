(declare-rel fact (Int Int))
(declare-rel mult (Int Int Int))
(declare-rel fail ())

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var a Int)
(declare-var b Int)
(declare-var c Int)

(rule (mult 0 y 0) MULT-FACT)
(rule (=> (and (mult (- x 1) y (- z y)) (> x 0)) (mult x y z)) MULT_REC)

;(rule (fact 0 1) FACT-FACT)
;(rule (=> (and (> a 0) (fact (- a 1) c) (mult a c b)) (fact a b))FACT-REC)

;(rule (=> (and (> x 0) (fact a b) (fact x y) (> a x) (< b y)) fail)QUERY)
(rule (=> (and (> x 0) (> a x) (> y 0) (mult x y z) (mult a y b) (> b z)) fail)QUERY)
(query fail :print-certificate true)
