(define l (cons 1 (cons 1 (cons 1 1))))
(eq? (car l) (car (cdr l)))