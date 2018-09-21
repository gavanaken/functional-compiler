#lang racket


(require "solution.rkt")
(provide run-test)


; Some functions for dealing with church-encoded values in Racket
(define (church->nat cv) ((cv add1) 0))
(define (church->list cv) ((cv (lambda (car) (lambda (cdr) (cons car (church->list cdr)))))
                           (lambda (na) '())))
(define (church->bool cv) ((cv (lambda (_) #t)) (lambda (_) #f)))
(define (church->pair cv)
  ((cv (lambda (car) (lambda (cdr) (cons car cdr)))) 'unused))

(define (mk-church-converter val)
  ;; mk-church-converter :: Value -> (ChurchValue -> Value)
  (cond
   [(number? val) church->nat]
   [(boolean? val) church->bool]
   [(list? val)
    (compose1
     (curry
      map
      (lambda (x y)
        ((mk-church-converter x) y))
      val)
     church->list)]
   [(pair? val)
    (lambda (pair)
      (match (church->pair pair)
        [(cons x y)
          (cons
           ((mk-church-converter (car val)) x)
           ((mk-church-converter (cdr val)) y))]))]
   [else (error 'invalid-value-template)]))

;; Returns true if the term is not in the output grammar
(define (invalid-term? e)
  (match e
    [`(lambda ,(? (listof symbol?) xs) ,e0) (invalid-term? e0)]
    [(? symbol?) #f]
    [`(,es ...) (ormap invalid-term? es)]
    [else #t]))

(define (with-church-encoded inp church-val/k)
  (define church (church-encode inp))
  (when (invalid-term? church) (error 'invalid-term))
  (define val (eval church (make-base-namespace)))
  (church-val/k val))

;; test implementation of "church-encode" by:
;; - giving it as input an expression `inp`
;; - decoding results using `expected` as template
;; - compare decoded value with `expected`
(define (mk-simple-test inp [expected (eval inp (make-base-namespace))])
  (let ([convert (mk-church-converter expected)])
    (lambda ()
      (with-church-encoded
       inp
       (compose
        (curry equal? expected)
        convert)))))

;; Some tests for assignment 1
;; NOTE: -, sub1, zero? are extra credits.
(define tests
  (list
   ;; In each pair (test-name, cat, thunk), thunk runs a test and returns #t or #f
   ;; test-name is the name of the test
   ;; cat: one of 'public 'release 'secret
   (list
    "null?"
    'public
    (mk-simple-test '(null? '())))

   (list
    "null-thunk"
    'public
    (mk-simple-test '((lambda () '()))))

   (list
    "true"
    'public
    (mk-simple-test '#t))

   (list
    "zero"
    'public
    (mk-simple-test '0))

   (list
    "one"
    'public
    (mk-simple-test '1))

   (list
    "two"
    'public
    (mk-simple-test '2))

   (list
    "add1-0"
    'public
    (mk-simple-test '(add1 0)))

   (list
    "add1-1"
    'public
    (mk-simple-test '(add1 2)))

   (list
    "sub1-0"
    'public
    (mk-simple-test '(sub1 1)))

   (list
    "sub1-1"
    'public
    (mk-simple-test '(sub1 6)))

   (list
    "add-0"
    'public
    (mk-simple-test '(+ 1 1)))

   (list
    "add-1"
    'public
    (mk-simple-test '(+ 6 0)))

   (list
    "mul-0"
    'public
    (mk-simple-test '(* 3 4)))

   (list
    "and-or-0"
    'public
    (mk-simple-test
     '(or (or (and #f #t) (and #t #f)) (and #f #f))))

   (list
    "and-or-1"
    'public
    (mk-simple-test
     '(and (and (or #f #t) (or #t #f)) (or #t #t))))

   (list
    "and-or-2"
    'public
    (mk-simple-test
     '(or #f (and #t #t))))

   (list
    "if-0"
    'public
    (mk-simple-test '(if #t 0 1) 0))

   (list
    "if-1"
    'public
    (mk-simple-test '(if #f 2 3) 3))

   (list
    "if-not-0"
    'public
    (mk-simple-test '(if (not #t) 0 1)))

   (list
    "if-not-1"
    'public
    (mk-simple-test '(if (not (not (not #f))) 5 4)))

   (list
    "let-0"
    'public
    (mk-simple-test '(let ([a 5] [b 6]) b)))

   (list
    "list-0"
    'public
    (mk-simple-test
     '(cons 0 '())))

   (list
    "list-1"
    'public
    (mk-simple-test
     '(cons 2 (cons 3 (cons 5 (cons 7 (cons 11 '())))))))

   (list
    "map-0"
    'public
    (mk-simple-test
     '(letrec ([map (lambda (f lst)
                      (if (null? lst)
                          '()
                          (cons (f (car lst)) (map f (cdr lst)))))])
        (map (lambda (x) (+ 1 x))
             (cons 0 (cons 5 (cons 3 '())))))))

   ;; cons
   (list
    "cons-0"
    'public
    (mk-simple-test '(cons 3 1)))

   (list
    "app-0"
    'public
    (mk-simple-test
     '((lambda () 5))))
   
   (list
    "app-1"
    'public
    (mk-simple-test
     '((lambda (a b c) c) 1 2 3)))
   ))

(define (run-test/internal is-repl . args)
  ;; Run all tests, a specific test, or print the available tests
  (match args
    [(list "all")
     (define correct-count
       (foldl (lambda (testcase count)
                (match testcase
                  [(list test-name _ exec)
                   (define exec-result
                     (with-handlers ([exn:fail? identity])
                       (exec)))
                   (if (eq? exec-result #t)
                       (begin
                         ;; (display "Test ")
                         ;; (display test-name)
                         ;; (display " passed.")
                         ;; (newline)
                         (+ count 1))
                       (begin
                         (display "Test ")
                         (display test-name)
                         (display " failed!")
                         (newline)
                         count))]))
              0
              tests))
     (display "Score on available tests (may not include release tests or private tests): ")
     (display (/ (round (/ (* 10000 correct-count) (length tests))) 100.0))
     (display "%")
     (newline)]

    [(list "mk-test-props")
     (define groupped-tests
       ;; key: group (symbol)
       ;; value: reversed list of testcases
       (foldl
        (lambda (testcase h)
          (match testcase
            [(list _ grp _)
             (define cur-group
               (hash-ref h grp '()))
             (hash-set h grp (cons testcase cur-group))]))
        (hash)
        tests))
     (for-each
      displayln
      '("build.language=c"
        "build.make.file=Makefile"
        "test.exec=/usr/local/bin/racket ./tests.rkt &"))
     (for-each
      (lambda (kv)
        (match kv
          [(cons grp ts)
           (define testnames
             (reverse (map car ts)))
           (printf
            "test.cases.~a=~a~n"
            grp
            (string-join
             testnames
             ","))]))
      (hash->list
       groupped-tests))]

    [(list test-name)
     #:when (assoc test-name tests)
     (match (assoc test-name tests)
       [(list _ _ exec)
        (define exec-result
          (with-handlers ([exn:fail? identity])
            (exec)))
        (define passed (eq? exec-result #t))
        (displayln (if passed "Test passed!" "Test failed!"))
        (unless is-repl
          (exit (if (eq? exec-result #t) 0 1)))])]
    [else
     (display "Available tests: ")
     (newline)
     (display
      (string-join
       (map car tests)
       ", "))
     (newline)]))

(define run-test
  (curry run-test/internal #t))

(apply
 run-test/internal
 (cons
  #f
  (vector->list (current-command-line-arguments))))
