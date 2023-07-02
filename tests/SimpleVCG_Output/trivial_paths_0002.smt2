(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-const x Int)
(assert (> x 5))
(assert (not (= x 0)))
(assert (not (not (= x 3))))
(check-sat)
(get-value (x))
(exit)

;; result = unsat
