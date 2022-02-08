((lambda(x y)
	(set! x 3)
	((lambda (x)
		x
		(set! y 4)
		) 0)
		y) 1 2)
