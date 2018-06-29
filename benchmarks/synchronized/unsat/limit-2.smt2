(declare-rel f (Int Int))
(declare-rel g (Int Int))
(declare-rel fail ())

(declare-var r Int)
(declare-var n Int)
(declare-var m Int)
(declare-var n1 Int)
(declare-var m1 Int)
(declare-var n2 Int)
(declare-var m2 Int)
(declare-var i Int)

(rule (=> (<= n 1) (f n n)))
(rule (=> (and (> n 1) (f (- n 1) r)) (f n (+ r n))))
(rule (=> (<= n 1) (g n n)))
(rule (=> (and (> n 1) (g (- n 1) r)) (g n (+ r n))))

(rule (=> (and (= n1 n2) (f n1 m1) (g n2 m2) (not (= m1 m2))) fail))

(query fail :print-certificate true)
