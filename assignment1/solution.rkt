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
          'blank]

         [`(let ([,xs ,e0s] ...) ,e1)
          'blank] ; Is this right??

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
          'blank] ;apply f(x) <nat> times!??
         ['(quote ())
          'blank]
         [#t
          (churchify `(lambda (a b) (a)))] ; given 2 options, pick the first
         [#f
          (churchify `(lambda (a b) (b)))] ; ... pick the second

         ; Untagged application
         [`(,fun)
          'blank]
         [`(,fun ,arg)
          'blank]
         [`(,fun ,arg . ,rest)
          'blank]))


(define (church-encode e)
  (define Y-comb `((lambda (u) (u u)) (lambda (y) (lambda (mk) (mk (lambda (x) (((y y) mk) x)))))))
  ; define church-null? etc. here
  (define church-null? `(lambda (when-cons when-null) (when-null))) ; from asgnt
  (define church-cons `(lambda (a b) (lambda (when-cons when-null) (when-cons a b)))) ; from asgnt
  (define church-car `(lambda (p) (p (lambda (a b) a) (lambda () omega)))) ; from asgnt
  (define church-cdr `(lambda (p) (p (lambda (a b) b) (lambda () omega)))) ; from asgnt
  (define church-add1 `(lambda (n0) (lambda (f) (lambda (x) (f ((n0 f) x)))))) ; from asgnt
  (define church-+ `(lambda (n0 n1) (lambda (f x) ((n1 f) ((n0 f) x))))) ; Assuming natural numbers work right: n0 times of f, then n1 times of f
  (define church-* `(lambda (n0 n1) (lambda (f x) ((n0 (n1 f)) x)))) ; from asgnt: (n1 times of f) n0 times
  (define church-not `((lambda (b) (if b #f #t)))) ; given a bool, if true go false, else true
  
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


