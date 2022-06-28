; EXAMPLE OF SMT-LIB FILE, ACCORDING TO THE ENCODING 0
; Example on a very simple instance (it is not an existing instance, but it's a simpler instance)

; EXAMPLE OF USAGE
; From the CDMO-Project directory
; $ z3 sm/encoding_0_example.smt2
; OUTPUT
; sat
; (((coordX 0) 0)
;  ((coordX 1) 0)
;  ((coordY 0) 0)
;  ((coordY 1) 2))


; w=4
; n=2
; 2 2
; 3 3
; l_max=5

(set-option :produce-models true)

(declare-fun coordX (Int) Int)
(declare-fun coordY (Int) Int)

(assert (and (>= (coordX 0) 0) (<= (coordX 0) (- 4 2))))
(assert (and (>= (coordX 1) 0) (<= (coordX 1) (- 4 3))))

(assert (and (>= (coordY 0) 0) (<= (coordY 0) (- 5 2))))
(assert (and (>= (coordY 1) 0) (<= (coordY 1) (- 5 3))))

(assert (or (<= (+ (coordX 0) 2) (coordX 1)) (<= (+ (coordX 1) 3) (coordX 0)) (<= (+ (coordY 0) 2) (coordY 1)) (<= (+ (coordY 1) 3) (coordY 0))))

(check-sat)
(get-value ((coordX 0) (coordX 1) (coordY 0) (coordY 1)))



