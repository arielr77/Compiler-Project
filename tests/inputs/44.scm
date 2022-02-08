((lambda (a b . c)
   ((lambda (a b . c) (list a b c))
    c b a))
 1 2 3)