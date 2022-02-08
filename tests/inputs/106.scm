(define x (+ 2))
((lambda (x) 
	(set! x (+ 2 3))
	x) x)
	
