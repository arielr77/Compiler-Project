(define even?
          (lambda (x)
            (or (= x 0)
                (odd? (- x 1)))))
(define odd?
 (lambda (x)
   (and (not (= x 0))
        (even? (- x 1)))))
(even? 5)
(even? 4)
(odd? 2)
(odd? 15)