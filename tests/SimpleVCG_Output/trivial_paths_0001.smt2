(set-logic QF_LIA)
(set-option :produce-models true)

(declare-const x Int)
(assert (> x 5))
(assert (not (not (= x 0))))
(check-sat)
(get-value (x))
(exit)

;; result = unsat
