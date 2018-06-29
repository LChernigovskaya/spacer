(declare-rel lucas (Int Int))
(declare-rel fail ())

(declare-var a Int)
(declare-var b Int)
(declare-var n Int)
(declare-var m Int)

(rule (=> (= n 1) (lucas n 2)))
(rule (=> (= n 2) (lucas n 1)))
(rule (=> (and (> n 2) (lucas (- n 1) a) (lucas (- n 2) b)) (lucas n (+ a b))))

(rule (=> (and (< 1 m) (< m n) (lucas m a) (lucas n b) (>= a b)) fail))

(query fail :print-certificate true)
