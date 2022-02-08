(letrec ((loop (lambda (x n)
                   (if (zero? n)
                       #t
                       (begin
                         (set! x 5)
                         (lambda () x)
                         (loop x (- n 1)))))))
    (loop #f 4000000))
