#lang racket

(provide assignment-convert
         alphatize
         anf-convert
         cps-convert)


(require "utils.rkt")


; The output of assignment 2:
; e ::= (let ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (lambda x e)
;     | (apply e e)
;     | (e e ...)
;     | (prim op e ...)
;     | (apply-prim op e)
;     | (if e e e)
;     | (set! x e)
;     | (call/cc e)
;     | x
;     | (quote dat)


(define (assignment-convert e)
  ; Suggestion: compute a set of mutated variables and save here.
  ; I.e., a set of all x where there exists a (set! x ...).
  (define mutated-vars (set->list (set)))
  ; A strategy like this can help you to avoid boxing variables that don't need to be boxed
  ; and slowing down compiled programs as a result.
  (define (boxify e)
    (match e
           ; box mutated vars at initialization,
           ; e.g., (let ([x '()]) ...) -> (let ([x (prim make-vector '1 '())]) ...)
           ; What happens to (lambda (x) ...) if x is mutated?
           
           ; .. all all other forms in the language ...

           [`(let ([,xs ,es] ...) ,e0)
            `(let ,(map (lambda (x e)
                          (if (memv x mutated-vars)
                              `(,x (prim make-vector '1 ,(boxify e)))
                              `(,x ,(boxify e))))xs es) ; map making a vector over anything that needs it - recurse on e's
               ,(boxify e0))] ; finally, recurse on the let body
           [`(lambda ,x ,e0)
            `(lambda ,x
               ,(if (memv x mutated-vars)
                    `(let ([,x (prim make-vector '1 ,x)]) ,(boxify e0)) ; make a vector out of the vars - recurse on e's
                    (boxify e0)))] ; finally, recurse on the lambda body
           [`(lambda (,x ...) ,e)
            "not sure"]
           [`(apply ,e0 ,e1)
            `(apply ,(boxify e0)
                    ,(boxify e1))] ; just box the e's
           [`(,es ...)
            (map boxify es)] ; just boxify over all e's
           [`(prim ,op ,es ...)
            `(prim ,op ,@(map boxify es))] ; I think we need to splice the map results (from desugar.rkt)
           [`(apply-prim ,op ,e0)
            `(apply-prim ,op ,(boxify e0))] ; just box e0
           [`(if ,e0 ,e1 ,e2)
            `(if ,(box e0) ,(box e1) ,(box e2))] ; just box the e's
           [`(set! ,x ,e0)
            `(prim vector-set! ,x '0 ,(boxify e0))]
           [`(set! ,x ,e0)
            `(prim vector-set! ,x '0 ,(boxify e0))] ; from SSA slides - being sure to box the e
           [`(call/cc ,e0)
            `(call/cc ,(boxify e0))] ; just box e0
           [(? symbol? x)
            (if (set-member? mutated-vars x)
                `(prim vector-ref ,x '0)
                x)]
           [`',dat `',dat] ; dat is dat
           ))
  (boxify e))


; assignment-convert => 

;;; set! is removed and replaced with vector-set!
; e ::= (let ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (lambda x e)
;     | (apply e e)
;     | (e e ...)
;     | (prim op e ...)
;     | (apply-prim op e)
;     | (if e e e)
;     | (call/cc e)
;     | x
;     | (quote dat)

; alphatize both takes and produces this language as well

(define (alphatize e)
  ; Defining curried rename function is convenient for mapping over lists of es
  (define ((rename env) e)
    (match e
           ; Rename all variables 
           [`(lambda (,xs ...) ,e0)
            (define xs+ (map gensym xs))
            (define env+ (foldl (lambda (x x+ env) (hash-set env x x+)) env xs xs+))
            `(lambda ,xs+ ,((rename env+) e0))]
           ; etc ...
           [`(let ([,xs ,es] ...) ,e0)
            (define xs+ (map gensym xs))
            (define env+ (foldl (lambda (x x+ env) (hash-set env x x+)) env xs xs+))
            "what is rest"]
           [`(lambda ,x ,e0)
            (define x+ (gensym x))
            (define env+ (hash-set env x x+))
            `(lambda ,x+ ,((rename env+) e0))]
           [`(prim ,op ,es ...)
            `(prim ,op ,@(map (rename env) es))] ; splice together mapping rename over the e's
           ))
  ((rename (hash)) e))


; Converts to ANF; adapted from Flanagan et al.
(define (anf-convert e)
  (define (normalize e k)
    '())
  ; We will write a simplified version in class
  (normalize e (lambda (x) x)))


; anf-convert =>

; e ::= (let ([x e]) e)
;     | (apply ae ae)
;     | (ae ae ...)
;     | (prim op ae ...)
;     | (apply-prim op ae)
;     | (if ae e e)
;     | (call/cc ae)
;     | ae
; ae ::= (lambda (x ...) e)
;      | (lambda x e)
;      | x
;      | (quote dat)


(define (cps-convert e)
  (define (T e cae)
    '())
  ; We will define a simpler version of this in class.
  ; You can add T and T-ae functions here.

  ; Kick it off with an initial continuation (lambda (k x) ..)
  ; Its continuation k is never used because first the prim halt is applied on x.
  (T e '(lambda (k x) (let ([_1 (prim halt x)]) (k x)))))


; cps-convert => 

; e ::= (let ([x (apply-prim op ae)]) e)
;     | (let ([x (prim op ae ...)]) e)
;     | (let ([x (lambda x e)]) e)
;     | (let ([x (lambda (x ...) e)]) e)
;     | (let ([x (quote dat)]) e)
;     | (apply ae ae)
;     | (ae ae ...)
;     | (if ae e e)
; ae ::= (lambda (x ...) e)
;      | (lambda x e)
;      | x
;      | (quote dat)


