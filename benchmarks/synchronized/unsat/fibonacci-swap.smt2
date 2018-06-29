(declare-rel fib (Int Int))
(declare-rel fib-swap (Int Int))
(declare-rel fail ())

(declare-var a Int)
(declare-var b Int)
(declare-var n Int)
(declare-var m Int)

(rule (=> (< n 2) (fib n 1)))
(rule (=> (and (>= n 2) (fib (- n 1) a) (fib (- n 2) b)) (fib n (+ a b))))
(rule (=> (< n 2) (fib-swap n 1)))
(rule (=> (and (>= n 2) (fib-swap (- n 2) a) (fib-swap (- n 1) b)) (fib-swap n (+ a b))))
(rule (=> (and (> n 1) (fib n a) (fib-swap n b) (not (= a b))) fail))

(query fail :print-certificate true)
