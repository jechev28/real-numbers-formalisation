; Tested with Z3 version 4.5.0 - 64 bit.

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

(define-fun assoc () Bool
	(= (xor (xor p q) r) (xor p (xor q r))))

(assert (not assoc))
(check-sat)

; $ z3 xor
; $ unsat
