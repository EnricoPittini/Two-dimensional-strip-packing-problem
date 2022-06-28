; EXAMPLE OF SMT-LIB FILE, ACCORDING TO THE ENCODING 3E
; Example on a very simple instance (it is not an existing instance, but it's a simpler instance)

; EXAMPLE OF USAGE
; From the CDMO-Project directory
; $ z3 sm/encoding_3E_example.smt2
; OUTPUT
; sat
; ((coordX_0 0)
;  (coordY_0 0)
;  (coordX_1 0)
;  (coordY_1 2))


; w=4
; n=2
; 2 2
; 3 3
; l_max=5

(set-option :produce-models true)
(set-logic QF_IDL)

(declare-const coordX_0 Int)
(declare-const coordX_1 Int)
(declare-const coordY_0 Int)
(declare-const coordY_1 Int)


(assert (and (>= coordX_0 0) (<= coordX_0 (- 4 2))))
(assert (and (>= coordX_1 0) (<= coordX_1 (- 4 3))))

(assert (and (>= coordY_0 0) (<= coordY_0 (- 5 2))))
(assert (and (>= coordY_1 0) (<= coordY_1 (- 5 3))))

(assert (or (<= (+ coordX_0 2) coordX_1) (<= (+ coordX_1 3) coordX_0) (<= (+ coordY_0 2) coordY_1) (<= (+ coordY_1 3) coordY_0)))

(check-sat)
(get-value (coordX_0 coordY_0 coordX_1 coordY_1))

