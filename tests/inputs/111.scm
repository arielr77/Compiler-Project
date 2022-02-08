(define a "alpha")
(define b "alpha")

(string-set! a 0 #\b)
(and (eq? a b) (equal? (string-ref a 0) (string-ref b 0)))
