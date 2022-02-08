(letrec ((foo (((lambda (n)
	(lambda (n)
		(cons
			(lambda ()
				(set! n (+ n 1)) n)
			(lambda ()
				(set! n 0))))) 10) 200)))
    (begin ((cdr foo)) ((car foo))))
