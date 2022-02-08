(define length
	(lambda (l)
		(if (null? l) 0
			(+ 1 (length (cdr l))))))

(= (length ''''''''a) (length ``````````a))
