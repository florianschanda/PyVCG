(set-logic QF_LIA)
(set-option :produce-models true)

(declare-const x Int)
(assert (> x 1))
(assert (not (= x 0)))
(assert (not (not (= x 3))))
(check-sat)
(get-value (x))
(exit)

;; result = sat
;;
;; x = 3
