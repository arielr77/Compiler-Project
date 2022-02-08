(define Y 
	(lambda (foo)
	((lambda (f) (foo (lambda (x) ((f f) x))))
		(lambda (f) (foo (lambda (x) ((f f) x)))))))

(define max
	(Y (lambda (f)
		(lambda (l)
			(if (null? l) 0
				(let ((cdr-max (f (cdr l))))
					(if (> (car l) cdr-max) (car l) cdr-max)))))))
(define depth
	(lambda (f)
		(lambda (t)
			(if (pair? t)
				(+ 1 (max (map f t)))
				0))))

((Y depth) '((1 2 3) (4 (5 (6))) (((((7 (8) 9 10 11 12) 13) 14)))))
