#lang racket

;; Testing apparatus for assignment 4

(require "desugar.rkt")
(require "cps.rkt")
(require "utils.rkt")
(require "closure-convert.rkt")


(define ((make-test kind path) exp ext)
  (match (cons kind ext)
         [(cons 'clo "scm")
          (lambda ()
            ;(display (format "Running closure conversion (scm) test ~s\n" path))
            (define cps (cps-convert (anf-convert (alphatize (assignment-convert (simplify-ir (desugar exp)))))))
            (define t0 (test-closure-convert closure-convert cps))
            t0)]
         [(cons 'clo "cps")
          (lambda ()
            ;(display (format "Running closure conversion (cps) test ~s\n" path))
            (define t0 (test-closure-convert closure-convert exp))
            t0)]
         [(cons 'to-llvm "scm")
          (lambda ()
            ;(display (format "Running llvm (scm) test ~s\n" path))
            (define cps (cps-convert (anf-convert (alphatize (assignment-convert (simplify-ir (desugar exp)))))))
            (define t0 (test-closure-convert closure-convert cps))
            (define pr (closure-convert cps))
            (if (and (proc-exp? pr) t0)
                (test-proc->llvm proc->llvm pr)
                #f))]
         [(cons 'to-llvm "cps")
          (lambda ()
            ;(display (format "Running llvm (cps) test ~s\n" path))
            (define t0 (test-closure-convert closure-convert exp))
            (define pr (closure-convert exp))
            (if (and (proc-exp? pr) t0)
                (test-proc->llvm proc->llvm pr)
                #f))]))

(define (tests-list dir)
  (map
   (lambda (path)
     (string->path
      (string-append "tests/" dir "/"
                     (path->string path))))
   (filter (lambda (path)
             (define p (path->string path))
             (member (last (string-split p ".")) '("cps" "scm")))
           (directory-list (string-append "tests/" dir "/")))))

(define ((path->test type kind) p)
  (define filename (last (string-split (path->string p) "/")))
  `(,(string-append (symbol->string kind) "-" (last (string-split (string-join (drop-right (string-split (path->string p) ".") 1) ".") "/")))
    ,type
    ,((make-test kind p)
      (with-input-from-file p read #:mode 'text)
      (last (string-split (path->string p) ".")))))

(define (count-make-vectors e)
  ; For extra-credit test to check efficiency
  (length (filter (lambda (x) (eq? x 'make-vector)) (flatten e))))

(define tests
  `(,@(map (path->test 'public 'clo) (tests-list "public"))
    ,@(map (path->test 'public 'to-llvm) (tests-list "public"))
    ,@(map (path->test 'release 'clo) (tests-list "release"))
    ,@(map (path->test 'release 'to-llvm) (tests-list "release"))  
    ,@(map (path->test 'secret 'clo) (tests-list "secret"))
    ,@(map (path->test 'secret 'to-llvm) (tests-list "secret"))))

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
             "test.exec=timeout -s KILL 13s /usr/local/bin/racket ./tests.rkt &"))
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



