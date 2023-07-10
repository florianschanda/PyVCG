(set-logic QF_SAT)
(set-option :produce-models true)

(declare-const potato Bool)
(assert potato)
;; second attempt
(assert (not potato))
(check-sat)
(get-value (potato))
(exit)

;; result = unsat
