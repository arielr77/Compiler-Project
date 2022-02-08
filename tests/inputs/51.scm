((lambda (x) (x x 50000))
 (lambda (x n)
   (if (zero? n) #t
       (x x (- n 1)))))
