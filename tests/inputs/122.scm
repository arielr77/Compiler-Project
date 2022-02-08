(define ascii 
	(lambda ()
		(letrec ((loop (lambda (i)
						(if (< i 127)
							(cons `(,i ,(integer->char i)) (loop (+ 1 i)))
							'()))))
			(loop (char->integer #\space)))))

(ascii)
