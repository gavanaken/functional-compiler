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
         [`(let ,(? symbol? lp) ([,xs ,es] ...) ,e0)
          (desugar-aux `(letrec ([,lp (lambda ,xs ,e0)]) (,lp . ,es)))]

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
    
         [else '()]))


(define (desugar e)
  ; wrap e in any special functions or definitions you need
  ; and then pass it into a helper function that performs the
  ; case-by-case translation recursively
  (desugar-aux e))



; I, First Last, pledge on my honor that I have not given or 
; received any unauthorized assistance on this project.
