(map map (list 
             (lambda (x) (+ x x)) 
             (lambda (x) (- x))
             (lambda (x) (* x x)) 
             (lambda (x)  (/ x)))
       '((1 2.0) (3 4e0) (5 6e-1) (7 8e1)))
