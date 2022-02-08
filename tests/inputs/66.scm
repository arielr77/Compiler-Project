((lambda (x y) ((lambda (a b c) (a b c)) x
                                           ((lambda () ((lambda (z) z) #t))) y)) (lambda (q r) r) #f)