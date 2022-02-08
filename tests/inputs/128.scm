(define list? (lambda (x)
	(or (null? x) (and (pair? x) (list? (cdr x))))))

(define describe
  (lambda (e)
    (cond
     ((list? e) `(list ,@(map describe e)))
     ((pair? e) `(cons ,(describe (car e))
        ,(describe (cdr e))))
     ((or (null? e) (symbol? e)) `',e)
     (else e))))
     
(describe '(sym "str" #\c 1))
