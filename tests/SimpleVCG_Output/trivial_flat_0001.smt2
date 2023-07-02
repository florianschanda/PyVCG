(set-logic QF_UF)
(set-option :produce-models true)

(declare-const potato Bool)
(assert (not potato))
(check-sat)
(get-value (potato))
(exit)

;; result = sat
;;
;; potato = False
