#lang racket


(require "solution.rkt")


;; Some tests that exercise the 4 functions required for assignment 0
(define tests
  (list
   ;; In each pair (test-name, thunk), thunk runs a test and returns #t or #f
   ;; test-name is the name of the test
   (list
    "reverse-0"
    'public
    (lambda ()
      (equal? (my-reverse '(9 5 7 3 1))
              '(1 3 7 5 9))))

   (list
    "append-0"
    'public
    (lambda ()
      (equal?
       (my-append (my-append '() '(1 2)) (my-append '(3 4 5) '()))
       '(1 2 3 4 5))))

   (list
    "append-1"
    'public
    (lambda ()
      (equal?
       (my-append '(1 2 3) (my-append '(4) '(5)))
       '(1 2 3 4 5))))

   (list
    "interp-lambda-I"
    'public
    (lambda ()
      (define exp '(lambda (x) x))
      (define val (interp exp))
      (define k (val 49))
      (equal? k 49)))

   (list
    "interp-app-0"
    'public
    (lambda ()
      (define exp '((lambda (x) x) (lambda (f) (lambda (x) (f (f x))))))
      (define val (interp exp))
      (define k ((val (lambda (x) (* x x))) 4))
      (equal? k 256)))

   (list
    "free-0"
    'public
    (lambda ()
      (define exp
        '(lambda (x)
           (lambda (x)
             (lambda (y)
               ((lambda (z) (w ((x y) z))) z)))))
      (equal? (list->set (free exp)) (set 'w 'z))))
))


;; Run all tests, a specific test, or print the available tests
(match (current-command-line-arguments)
       [(vector "all")
        (define correct-count
          (foldl (lambda (testcase count)
                   (match testcase
                          [(list test-name _ exec)
                           (define exec-result
                             (with-handlers ([exn:fail? identity])
                                            (exec)))
                           (if (eq? exec-result #t)
                               (+ count 1)
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

       [(vector test-name)
        #:when (assoc test-name tests)
        (match (assoc test-name tests)
               [(list _ _ exec)
                (define exec-result
                  (with-handlers ([exn:fail? identity])
                                 (exec)))
                (exit (if (eq? exec-result #t)
                          (begin (display "Test passed!\n") 0)
                          (begin (display "Test failed!\n") 1)))])]

       [else
        (display "Avaliable tests: ")
        (newline)
        (display
         (string-join
          (map car tests)
          ", "))
        (newline)])

