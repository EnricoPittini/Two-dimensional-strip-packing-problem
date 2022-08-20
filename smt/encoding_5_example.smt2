; EXAMPLE OF SMT-LIB FILE, ACCORDING TO THE ENCODING 5
; Example on a very simple instance (it is not an existing instance, but it's a simpler instance)

; EXAMPLE OF USAGE
; From the CDMO-Project directory
; $ z3 smt/encoding_5_example.smt2
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
(declare-fun r (Int) Bool)
(declare-fun actual_dimsX (Int) Int)
(declare-fun actual_dimsY (Int) Int)

; DOMAINS
(assert (>= (coordX 0) 0))
(assert (or (r 0) (<= (coordX 0) (- 4 2))))
(assert (or (not (r 0)) (<= (coordX 0) (- 4 2))))

(assert (>= (coordX 1) 0))
(assert (or (r 1) (<= (coordX 1) (- 4 3))))
(assert (or (not (r 1)) (<= (coordX 1) (- 4 3))))

(assert (>= (coordY 0) 0))
(assert (or (r 0) (<= (coordY 0) (- 5 2))))
(assert (or (not (r 0)) (<= (coordY 0) (- 5 2))))

(assert (>= (coordY 1) 0))
(assert (or (r 1) (<= (coordY 1) (- 5 3))))
(assert (or (not (r 1)) (<= (coordY 1) (- 5 3))))

; ACTUAL DIMENSIONS
(assert (or (r 0) (and (= (actual_dimsX 0) 2) (= (actual_dimsY 0) 2))))
(assert (or (not (r 0)) (and (= (actual_dimsX 0) 2) (= (actual_dimsY 0) 2))))

(assert (or (r 1) (and (= (actual_dimsX 1) 3) (= (actual_dimsY 1) 3))))
(assert (or (not (r 1)) (and (= (actual_dimsX 1) 3) (= (actual_dimsY 1) 3))))

; NON-OVERLAPPING
(assert (or (<= (+ (coordX 0) (actual_dimsX 0)) (coordX 1)) (<= (+ (coordX 1) (actual_dimsX 1)) (coordX 0)) (<= (+ (coordY 0) (actual_dimsY 0)) (coordY 1)) (<= (+ (coordY 1) (actual_dimsY 1)) (coordY 0))))

(check-sat)
(get-value ((coordX 0) (coordX 1) (coordY 0) (coordY 1)))
(get-value ((actual_dimsX 0) (actual_dimsX 1) (actual_dimsY 0) (actual_dimsY 1)))



