(define x (cons 1 1))
(define l (cons x x))
(eq? (car l) (cdr l))