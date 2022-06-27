; w=4
; n=2
; 2 2
; 3 3
; l_max=5

(declare-fun coordX (Int) Int)
(declare-fun coordY (Int) Int)

(assert (and (>= (select coordX 0) 0) (<= (select coordX 0) (- 4 2))))
(assert (and (>= (select coordX 1) 0) (<= (select coordX 1) (- 4 3))))

(assert (and (>= (select coordY 0) 0) (<= (select coordY 0) (- 5 2))))
(assert (and (>= (select coordY 1) 0) (<= (select coordY 1) (- 5 3))))

(assert (or (<= (+ (select coordX 0) 2) (select coordX 1)) (<= (+ (select coordX 1) 3) (select coordX 0)) (<= (+ (select coordY 0) 2) (select coordY 1)) (<= (+ (select coordY 1) 3) (select coordY 0))))

(check-sat)
(get-value ((select coordX 0) (select coordX 1) (select coordY 0) (select coordY 1)))

