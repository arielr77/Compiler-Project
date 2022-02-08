(((lambda (x) 
	(lambda (y . z) 
		(if `notbool (+ x  (* y (car z)) (car (cdr z)))))) 9) 10 11 12)
