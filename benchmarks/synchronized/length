
(set-option :fixedpoint.datalog.synchronization true)
;(set-option :fixedpoint.generate_proof_trace true)

(declare-datatypes (T) ((Lst nil (cons (hd T) (tl Lst)))))
(declare-var xs (Lst Int))
(declare-var ys (Lst Int))
(declare-var x Int)
(declare-var l Int)
(declare-rel length ((Lst Int) Int))
(declare-rel fail ())

(rule (=> (= xs nil) (length xs 0)) LEN-FACT)
(rule (=> (and (= xs (cons x ys)) (length ys l)) (length xs (+ l 1))) LEN-REC)

(rule (=> (and (length xs l) (length xs x) (not (= x l))) fail) QUERY-CLAUSE)

(query fail :print-certificate true)

