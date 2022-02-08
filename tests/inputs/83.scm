(define foo ((lambda (x) (list (lambda () (set! x (+ x 1))) (lambda () x))) 10))

(+ ((car (cdr foo))) ((car (cdr foo))))
