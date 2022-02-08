;;; Programmer: Mayer Goldberg, 2014

(define fact
  (let ((x (lambda (x)
	     ((x (lambda (x) (lambda (y) (lambda (z) ((x z) (y z))))))
	      (lambda (x) (lambda (y) x)))))
	(->
	 ((lambda (x) (x x))
	  (lambda (->)
	    (lambda (n)
	      (if (zero? n)
		  (lambda (x) (lambda (y) y))
		  (let ((z ((-> ->) (- n 1))))
		    (lambda (x)
		      (lambda (y)
			(x ((z x) y)))))))))))
    (lambda (n)
      ((((((((x (x (x (x x)))) (((x (x (x (x x)))) ((x (x (x x))) (x
      (x (x (x x)))))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x x
      ))))) (x (x (x (x x))))))) ((x (x (x x))) (x (x (x x))))) ((((
      (x (x (x (x x)))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x
      (x x)))))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x x)))))
      (x (x (x (x x))))))) ((x (x (x x))) (x (x (x x))))) (((((x (x
      (x (x x)))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x (x x))
      )))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x x))))) (x (x
      (x (x x))))))) ((x (x (x x))) (x (x (x x))))) (((x (x (x (x x)
      ))) (x (x (x x)))) (x (x (x x))))) (((x (x (x(x x)))) (((((x (
      x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (x (x (x x)))
      ) (((x (x (x (x x)))) ((x (x (x x))) (((x(x (x (x x)))) (((x (
      x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (((x (x (x (x
      x)))) ((x (x (x x))) (x (x (x x))))) (x(x (x (x x))))))) ((x (
      x (x x))) (x (x (x x))))))) ((((x (x(x (x x)))) (((x (x (x (x
      x)))) ((x (x (x x))) (x (x (x (x x)))))) (((x (x (x (x x)))) (
      (x (x (x x))) (x (x (x x))))) (x(x (x (x x))))))) ((x (x (x x)
      )) (x (x (x x))))) (((x (x (x (x x)))) (x (x (x x)))) (x (x (x
      x))))))) (((((x (x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))
      ))) (x (x (x x)))) ((x (x(x (x x)))) (((x (x (x (x x)))) ((x (
      x (x x))) (x (x (x (x x)))))) (x (x (x x)))))) (((((x (x (x (x
      x)))) (((x (x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (
      ((x (x (x (x x)))) ((x (x (x x))) (x (x (x x))))) (x (x (x (x
      x))))))) ((x (x (x x))) (x (x (x x))))) (((x (x (x (x x)))) (x
      (x (x x)))) (x (x (x x))))) (x (x (x x))))))) (((x (x (x (x x)
      ))) (((((x (x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (
      x(x (x x)))) (((x(x (x (x x)))) ((x (x (x x))) (x (x (x (x x))
      )))) (x (x (x x))))) (((((x (x (x (x x)))) (((x (x (x (x x))))
      ((x (x (x x)))(x (x (x (x x)))))) (((x (x (x (x x)))) ((x (x (
      x x))) (x (x(x x))))) (x (x (x (x x))))))) ((x (x (x x))) (x (
      x (x x)))))(((x (x (x (x x)))) (x (x (x x)))) (x (x (x x)))))
      (x (x (x x)))))) (((((x (x (x (x x)))) (((x (x (x (x x)))) ((x
      (x (x x)))(x (x (x (x x)))))) (((x (x (x (x x)))) ((x (x (x x)
      )) (x (x(x x))))) (x (x (x (x x))))))) ((x (x (x x))) (x (x (x
      x)))))(((x (x (x (x x)))) (x (x (x x)))) (x (x (x x))))) ((x (
      x (x x))) (((x (x (x (x x)))) (x (x (x x)))) (x (x (x x)))))))
      )))(((((x (x (x (x x)))) ((x (x (x x))) (((x (x (x (x x)))) ((
      (x(x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (((x (x (x
      (x x)))) ((x (x (x x))) (x (x (x x))))) (x (x (x (x x)))))))((
      x (x (x x))) (x (x (x x))))))) ((((x (x (x (x x)))) (((x (x(x
      (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (((x (x (x (x x)))
      )((x (x (x x))) (x (x (x x))))) (x (x (x (x x))))))) ((x(x (x
      x))) (x (x (x x))))) (((x (x (x (x x)))) (x (x (x x))))(x (x (
      x x)))))) (((x (x (x (x x)))) (((x (x (x (x x)))) ((x (x (x x)
      ))(x (x (x (x x)))))) (x (x (x x))))) ((x (x (x x)))(((x (x (x
      (x x)))) (x (x (x x)))) (x (x (x x))))))) (((x (x(x (x x)))) (
      ((x (x (x (x x)))) ((x (x (x x))) (x (x (x (x x)))))) (x (x (x
      x))))) ((x (x (x x))) (((x (x (x (x x)))) (x(x (x x)))) (x (x
      (x x))))))))) ((x (x (x x))) (((x (x (x (x x)))) (x (x (x x)))
      )(x (x (x x))))))
	 (-> n))
	(lambda (x) (+ x 1))) 0))))

(fact 5)
