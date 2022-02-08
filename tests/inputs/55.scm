(define list-ref
    (lambda (ls n)
      (if (= n 0)
          (car ls)
          (list-ref (cdr ls) (- n 1))))) 

(list-ref '(a b c) 0)
(list-ref '(a b c) 1) 
(list-ref '(a b c) 2)