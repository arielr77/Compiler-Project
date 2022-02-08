(define foo (((lambda (n)
                (lambda (n)
                    ((lambda (a b) (cons a b))
                        (lambda ()
                            (set! n (+ n 1)) n)
                        (lambda ()
                            (set! n 0))))) 10) 10))
                            
                            
                            
((car foo))
((cdr foo))
((car foo))
((car foo))
((car foo))
