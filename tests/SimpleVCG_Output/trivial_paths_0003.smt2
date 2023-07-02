(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-const x Int)
(assert (> x 1))
(assert (not (not (= x 0))))
(check-sat)
(get-value (x))
(exit)

;; result = unsat
