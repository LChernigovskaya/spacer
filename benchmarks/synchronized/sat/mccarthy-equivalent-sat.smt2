(declare-rel m91 (Int Int))
(declare-rel m91-2 (Int Int))
(declare-rel fail ())
(declare-var n Int)
(declare-var m Int)
(declare-var p Int)

(rule (=> (> m 100) (m91 m (- m 10))))
(rule (=> (and (<= m 100) (m91 (+ m 11) p) (m91 p n)) (m91 m n)))
(rule (=> (>= m 101) (m91-2 m (- m 10))))
(rule (=> (and (< m 101) (m91-2 (+ m 11) p) (m91-2 p n)) (m91-2 m n)))

(rule (=> (and (m91 m n) (m91-2 m p) (= n p)) fail))

(query fail :print-certificate true)
