(declare-rel gcd (Int Int Int))
(declare-rel fail ())

(declare-var r Int)
(declare-var r1 Int)
(declare-var n Int)
(declare-var m Int)

(rule (=> (= n 0) (gcd n m m)))
(rule (=> (= m 0) (gcd n m n)))
(rule (=> (and (< n m) (> n 0) (> m 0) (gcd m n r)) (gcd n m r)))
(rule (=> (and (>= n m) (> n 0) (> m 0) (gcd m (- n m) r)) (gcd n m r)))
(rule (=> (and (> n 0) (> m 0) (gcd n m r) (gcd m n r1) (= r r1)) fail))

(query fail :print-certificate true)
