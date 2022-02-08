(define foo (lambda (x)
				(cons
					(begin (lambda () (set! x 1) 'void))
					(lambda () x))))
(define p (foo 2))

(let* ((a ((cdr p)))
      (b ((car p)))
      (c ((cdr p))))
    (cons a (cons b (cons c '()))))
