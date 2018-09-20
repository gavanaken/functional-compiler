#lang racket

; by Greg Van Aken

(provide my-reverse
         my-append
         interp
         free)

; ### First, a direct, recursive appraoch ###
;(define (my-reverse lst)
;  (if (null? lst) '()
;      (my-append (my-reverse (cdr lst)) (list (car lst)))))

; ### Now a clever use of foldl ###
(define (my-reverse lst)
  (foldl cons '() lst))

; ### Again, recursive and direct ###
;(define (my-append lst0 lst1)
;  (if (null? lst0) lst1
;      (cons (car lst0) (my-append (cdr lst0) lst1))))

; ### This time we'll use foldr ###
(define (my-append lst0 lst1)
  (foldr cons lst1 lst0))


;; A possible solution for interp, partially stubbed out
(define (interp exp)
  (define (interp-env exp env)
    (match exp
           [`(lambda (,x) ,e)
            ;(display "Make a lambda\n")
            (lambda (y) (interp-env e (hash-set env x y))) ;ideally env would now be extended to contain a variable reference
            ]

           [`(,fun ,arg)
            (define funv (interp-env fun env))
            (define argv (interp-env arg env))
            ;(display "Apply funv on the argument value\n")
            (funv argv)
            ]

          [`,x
            ;(display "match a symbol\n")
            (hash-ref env x)
            ]))
  (interp-env exp (hash)))

(define (free exp)
  (define newl '())
  (define (free-list exp lst)
    (match exp
           [`(lambda (,x) ,e)
            (free-list e (my-append lst (list x)))
            ]

           [`(,fun ,arg)
            (free-list fun lst)
            (free-list arg lst)
            ]

          [`,x
           (if (member x lst) (set! newl newl) (set! newl (my-append newl (list x))))
            ]))
  (free-list exp (list))
  newl)
