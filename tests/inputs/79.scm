(eq? ((lambda (x . y)
	(cons x y)) 'a 'b 'c 'd)
	'(a b c d))
