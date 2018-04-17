(declare-rel m91 (Int Int))
(declare-rel fail ())
(declare-var n Int)
(declare-var m Int)
(declare-var p Int)
(declare-var v Int)

(rule (=> (> m 100) (m91 m (- m 10))))
(rule (=> (and (<= m 100) (m91 (+ m 11) p) (m91 p n)) (m91 m n)))

(rule (=> (and (<= m n) (m91 m p) (m91 n v) (<= p v)) fail))

(query fail :print-certificate true)
