(declare-rel fib (Int Int))
(declare-rel fail ())

(declare-var a Int)
(declare-var b Int)
(declare-var n Int)
(declare-var m Int)

(rule (=> (< n 2) (fib n 1)))
(rule (=> (and (>= n 2) (fib (- n 1) a) (fib (- n 2) b)) (fib n (+ a b))))
(rule (=> (and (< m n) (fib m a) (fib n b) (> a b)) fail))

(query fail :print-certificate true)
