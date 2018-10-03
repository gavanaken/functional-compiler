
(letrec ([odd? (lambda (n) (if (= n '1) '#t (even? (- n '1))))]
         [even? (lambda (n) (odd? (- n '1)))])
  (odd? '5))

