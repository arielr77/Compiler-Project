(define a 'alpha)
(define b 'beta)

(define l ((lambda (x y)
               (list 
                 (lambda () (set! x y))
                 (lambda () (cons x y)))) a b))
((car (cdr l)))
((car l))
((car (cdr l)))

