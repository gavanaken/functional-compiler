#lang racket


;; A church-compiler
(provide churchify
         church-encode)

;; for an input language:
;
; e ::= (letrec ([x (lambda (x ...) e)]) e)    
;     | (let ([x e] ...) e)  
;     | (lambda (x ...) e)
;     | (e e ...)    
;     | x  
;     | (and e e) | (or e e)
;     | (if e e e)
;     | (uprim e) | (bprim e e)
;     | datum
; datum ::= nat | (quote ()) | #t | #f 
; nat ::= 0 | 1 | 2 | ... 
; x is a symbol
; uprim/bprim is a primitive operation in:
(define prims '(+ * cons add1 car cdr null? not))

;; To an output language:
;
; e ::= (lambda (x) e)
;     | (e e)
;     | x
;


(define (prim? prim)
  (if (member prim prims) #t #f))


(define (churchify-prim prim)
  (string->symbol (string-append "church:" (symbol->string prim))))


(define (churchify e)
  (match e
         ; Tagged expressions
         [`(letrec ([,f (lambda (,args ...) ,e0)]) ,e1)
          (churchify `(let ([,f (Y-comb (lambda (,f) (lambda ,args ,e0)))]) ,e1))] ; with help from http://matt.might.net/articles/compiling-up-to-lambda-calculus/
                                                                                   ; each subpiece can be handled by churchify

         [`(let ([,xs ,e0s] ...) ,e1)
          (churchify `((lambda ,xs ,e1) . ,e0s))] ; Is this right??

         [`(lambda () ,e0)
          `(lambda (_) ,(churchify e0))]
         [`(lambda (,x) ,e0)
          `(lambda (,x) ,(churchify e0))]
         [`(lambda (,x . ,rest) ,e0)
          `(lambda (,x) ,(churchify `(lambda ,rest ,e0)))] ;if you have more than one variable, then CURRY
         
         [(? symbol? x) ;symbols just map to their own reps probably
          x]

         [`(and ,e0 ,e1)
          (churchify `(if ,e0 (if ,e1 #t #f) #f))] ;just like nested conditionals

         [`(or ,e0 ,e1)
          (churchify `(if ,e0 #t (if ,e1 #t #f)))]

         [`(if ,e0 ,e1 ,e2)
          (churchify `(,e0 (lambda () ,e1) (lambda () ,e2)))]

         [`(,(? prim? prim) . ,args)
          (churchify `(,(churchify-prim prim) . ,args))]

         ; Datums
         [(? natural? nat)
          (define (apply-n nat)
            (cond
              [(= nat 0) 'x]
              [else `(f ,(apply-n (- nat 1)))]
              ))
          (churchify `(lambda (f) (lambda (x) ,(apply-n nat))))]
         [''()
          (churchify `(lambda (when-cons when-null) (when-null)))] ;null this time
         [#t
          (churchify `(lambda (tt ft) (tt)))] ; given 2 options, pick the first, match tt and ft from example
         [#f
          (churchify `(lambda (tt ft) (ft)))] ; ... pick the second

         ; Untagged application
         [`(,fun)
          (churchify `(,fun (lambda (_) _)))] ; fun applied to a blank lambda
         [`(,fun ,arg)
          `(,(churchify fun) ,(churchify arg))]
         [`(,fun ,arg . ,rest)
          (churchify `((,fun ,arg) . ,rest))]))


(define (church-encode e)
  (define Y-comb `((lambda (u) (u u)) (lambda (y) (lambda (mk) (mk (lambda (x) (((y y) mk) x)))))))
  ; define church-null? etc. here
  (define church-null? `(lambda (p) ((p (lambda (_) (lambda (_) #f))) (lambda (_) #t)))) ; with help from http://matt.might.net/articles/compiling-up-to-lambda-calculus/
  (define church-cons `(lambda (a b) (lambda (when-cons) (lambda (when-null) (when-cons a b))))) ; from asgnt
  (define church-car `(lambda (p) (p (lambda (a b) a) (lambda () (lambda (x) x))))) ; from asgnt
  (define church-cdr `(lambda (p) (p (lambda (a b) b) (lambda () (lambda (x) x))))) ; from asgnt
  (define church-add1 `(lambda (n0) (lambda (f x) (f ((n0 f) x))))) ; from asgnt
  (define church-+ `(lambda (n0 n1) (lambda (f x) ((n1 f) ((n0 f) x))))) ; Assuming natural numbers work right: n0 times of f, then n1 times of f
  (define church-* `(lambda (n0 n1) (lambda (f x) ((n0 (n1 f)) x)))) ; from asgnt: (n1 times of f) n0 times
  (define church-not `(lambda (b) (if b #f #t))) ; given a bool, if true go false, else true
  
  (churchify
   `(let ([Y-comb ,Y-comb]
         [church:null? ,church-null?]
         [church:cons ,church-cons]
         [church:car ,church-car]
         [church:cdr ,church-cdr]
         [church:add1 ,church-add1]
         [church:+ ,church-+]
         [church:* ,church-*]
         [church:not ,church-not]
         )
      ,e)))


