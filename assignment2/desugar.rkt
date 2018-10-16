#lang racket

; by First Last

(provide desugar)
(require "utils.rkt")



(define (desugar-aux e)
  (match e
         [`(lambda ,(? symbol? x) ,e0)
          `(lambda ,x ,(desugar-aux e0))] ; stay the same, just desugar the e0
         [`(lambda (,(? symbol? x) ...) ,e0)
          `(lambda ,x ,(desugar-aux e0))]
    
         [`(if ,es ,if-true ,if-false)
          `(if (desugar-aux es) (desugar-aux if-true) (desugar-aux if-false))] ; just desugar exps
    
         [`(let* () ,e0)
          (desugar-aux e0)]
         [`(let* ([,x ,e0]) ,e1)
          (desugar-aux `(let ([,x ,e0]) ,e1))]
         [`(let* ([,x ,e0] . ,rest) ,e1)
          (desugar-aux `(let ([,x ,e0]) (let* ,rest ,e1)))]
         [`(let ,lp ([,xs ,es] ...) ,e0)
          (desugar-aux `(letrec ([,lp (lambda ,xs ,e0)]) (,lp . ,es)))]
         [`(let ([,xs ,es] ...) ,e0)
          `(let `(,x ,(map (lambda (e) (desugar-aux e)) es)) ,(desugar-aux e0))]   ; I think this is right?

         [`(,(? prim? op) ,es ...) ; this is a list of es? so we need to map over them
          `(prim ,op . ,(map desugar-aux es))]

         [`(quote ,(? datum? dat))
          `(quote ,dat)]

         [`(and) ; because of the recursion if we get here, its true
          `#t]
         [`(and ,e0)
          (desugar-aux e0)]
         [`(and ,e0 ,es ...)
          (desugar-aux
           `(if ,e0 (and . ,es) `#f))]

         [`(or) ; because of the recursion if we get here, its false
          `#f]
         [`(or ,e0)
          (desugar-aux e0)]
         [`(or ,e0 ,es ...)
          (desugar-aux
           `(if ,e0 `#t (or . ,es)))]

         [`(set! ,x ,e0)
          `(set! ,x ,(desugar-aux e0))]

         [`(apply ,e0 ,e1)
          `(apply ,(desugar-aux e0) ,(desugar-aux e1))] ; in both langs, desugar args

         [`(when ,e0 ,e1)
          (desugar-aux `(if ,e0 ,e1 (void)))]   ; void if false, otherwise do it
         [`(unless ,e0 ,e1)
          (desugar-aux `(if (not ,e0) ,e1 (void)))]   ; the opposite now

         [`(cond) `(prim void)]
         [`(cond [else ,e0])
          (desugar-aux e0)]
         [`(cond [,e0] . ,rest)
           (define f (gensym 'cond)) ; we need a new symbol every time
           (desugar-aux
           `(let ([,f ,e0])             ; point the symbol variable to the test expr.
              (if ,f ,f (cond . ,rest))))]     ; then go ahead and rcurse if needed
         [`(cond [,e0 ,e1] . ,rest)
          (desugar-aux `(if ,e0 ,e1 (cond . ,rest)))] ; recursive here, just branch if true (relies on the above being right)

         [`(let/cc ,x ,e0)
          (desugar-aux `(call/cc (lambda (,x) ,e)))]  ; taken from the documentation for this - depends on call/cc

         [`(case ,x) `(prim void)]
         [`(case ,x [else ,e0])
          (desugar-aux e0)]     ; Only one action - do it (base case)
         [`(case ,x [(,a ...) ,e0] . ,rest)
          (desugar-aux `(if (memv ,x `,a)
                            ,e0                     ; x is contained in a0
                            (case ,x . ,rest)))]    ; x is not contained in a0, "check" the rest


         [`(begin ,e0) (desugar-aux e0)]
         [`(begin ,e0 . ,rest)
          (desugar-aux
           `(let ([exp ,e0])    ; have desugar run the evalution
              (begin . ,rest)))]   ; then recurse on everything else
    
         [`(call/cc ,e0)
          "not sure"]

         [`(dynamic-wind ,e0 ,e1 ,e2)
          "not sure"]

         [`(guard (,x ,clause ...) ,e0)
          "not sure"]

         [`(raise ,e0)
          `(string-append "uncaught exception: " (desugar-aux ,e0))] ; this probably isn't right
    
         [`(delay ,e0)
          (desugar-aux
           `(list (lambda () ,e0) (mcons '#f '#f)))]

         [`(force ,e0)
          (define p (gensym 'promise))
          (desugar-aux
           `(let* ([,p ,e0]
                   [pair (last ,p)])
              (if (mcar pair)
                  (mcons pair)
                  (let ([exp (first ,p)])
                    (begin (set-mcar! (last ,p) '#t)
                           (set-mcdr! (last ,p) exp)
                           exp)))))]

         [`(letrec* ([,xs ,es] ...) ,e0)
          "not sure"]

         [`(letrec ([,xs ,es] ...) ,e0)
          (define fs (map gensym xs)) ; need discrete identifiers
          `(let ,(map (lambda (x e) `(,x '())) xs es)
             ,(desugar-aux
               `(begin
                 ,@(map (lambda (x f) `(set! ,x ,f)) xs fs)
                 ,e0)))]
    
           ; above with help from http://matt.might.net/articles/desugaring-scheme/
    
    
         [else '()]))


(define (desugar e)
  ; wrap e in any special functions or definitions you need
  ; and then pass it into a helper function that performs the
  ; case-by-case translation recursively
  (desugar-aux e))



; I, First Last, pledge on my honor that I have not given or 
; received any unauthorized assistance on this project.
