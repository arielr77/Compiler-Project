((lambda x
   ((lambda (_) '())
    (set-car! x 'd))
   x) 'a 'b 'c)
