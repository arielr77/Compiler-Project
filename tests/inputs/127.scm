(define str (make-string 5 #\space))

(string-set! str 0 #\t)
(string-set! str 1 #\Tab)
(string-set! str 3 #\n) 
(string-set! str 4 #\newline)

str
