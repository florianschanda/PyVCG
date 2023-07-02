(set-logic QF_UF)
(set-option :produce-models true)

(declare-const potato Bool)
(assert potato)
(assert (not potato))
(check-sat)
(get-value (potato))
(exit)

;; result = unsat
