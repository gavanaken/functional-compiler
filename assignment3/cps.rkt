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
                          `(,x (prim make-vector '1 ,(boxify e)))
                          `(,x ,(boxify e)))xs es) ; map making a vector over anything that needs it - recurse on e's
               ,(boxify e0))] ; finally, recurse on the let body
           [`(lambda ,x ,e0)
            `(lambda ,x
            `(let ([,x (prim make-vector '1 ,x)]) ,(boxify e0)) ; make a vector out of the vars - recurse on e's
               (boxify e0))] ; finally, recurse on the lambda body
           [`(lambda (,x ...) ,e)
            `(let ,(map (lambda (x) `(,x (prim make-vector '1 ,x))) x)
               ,(boxify e))]
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
            `(prim vector-ref ,x '0)
                x]
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
            `(let ,(map list xs+ (map (rename env) es)) ; I think this is right? pointing all the renamed xs to all the renamed es
               ,((rename env+) e0))] ; then recurse with the extended environment and whatever e0 is
           [`(lambda ,x ,e0)
            (define x+ (gensym x))
            (define env+ (hash-set env x x+))
            `(lambda ,x+ ,((rename env+) e0))]
           [`(prim ,op ,es ...)
            `(prim ,op ,@(map (rename env) es))] ; splice together mapping rename over the e's
           [`(apply ,e0 ,e1)
            `(apply ,((rename env) e0)
                    ,((rename env) e1))]
           [`(apply-prim ,op ,e0)
            `(apply-prim ,op ,((rename env) e0))]
           [`(if ,e0, e1, e2)
            `(if ,((rename env) e0)
                 ,((rename env) e1)
                 ,((rename env) e2))]
           [`(call/cc ,e0)
            `(call/cc ,((rename env) e0))]
           [(? symbol? x)
            (hash-ref env x)] ; just pull it out
           [`',dat `',dat] ; dat is dat
           ))
  ((rename (hash)) e))


; Converts to ANF; adapted from Flanagan et al.
(define (anf-convert e)
  (define (normalize-ae e k)
    (normalize e (lambda (anf)
                   (match anf
                     [(? symbol? x)
                      (k x)]
                     [`(lambda ,xs ,e0)
                      (k `(lambda ,xs ,e0))]
                     [else
                      (define ax (gensym 'a))
                      `(let ([,ax ,anf])
                         ,(k ax))]))))
  (define (normalize-aes es k)
    (if (null? es)
        (k '())
        (normalize-ae (car es) (lambda (ae)
                                 (normalize-aes (cdr es)
                                                (lambda (aes)
                                                  (k `(,ae ,@aes))))))))
  (define (normalize e k)
    (match e
      [(? symbol? x)
       (k x)]
      [(`',dat (k `',dat))]
      [`(lambda (,x) ,e0)
       (k `(lambda (,x) ,(anf-convert e0)))]
      [`(if ,e0 ,e1 ,e2)
       (normalize-ae e0 (lambda (ae)
                          (k `(if ,ae ,(anf-convert e1) ,(anf-convert e2)))))]
      [`(,es ...)
       (normalize-aes es k)]
      [`(let () ,e0)
       (normalize e0 k)]
      [`(let ([,x0 ,x1] . ,rest) ,e0)
       (k `(let ([,x0 ,(anf-convert x1)]) ; call k to bind but anf-convert x1 first
             ,(anf-convert
               `(let ,rest ,e0))))] ; recurse
      [`(apply ,aes ...)
       (normalize-aes aes (lambda (x) (k `(apply . ,x))))] ; is this right? need to deal with arbitrary argument #
      [`(prim ,op ,ae ...)
       (normalize-aes ae (lambda (x) (k `(prim ,op . ,x))))] ; same
      [`(apply-prim ,op ,e0)
       (normalize-ae e0 (lambda (x) (k `(apply-prim ,op ,x))))]
      (normalize e (lambda (x) x))))


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
  (define (T-ae ae)
    (match ae
      [(? symbol? x) x]
      [`(lambda (,x) ,e0)
       (define k (gensym 'k))
       `(lambda (,k ,x) ,(T-e e0 k))]
      
      [else ae]))
  (define (T-e e cae)
    (match e
      [(? symbol? x)
       `(,cae ,x ,x)]
      [`(lambda . ,rest)
       `(,cae 0 ,(T-ae e))]
      [`(let ([,x ,e0]) ,e1)
       (define _x (gensym '_))
       (T-e e0 `(lambda (,_x ,x) ,(T-e e1 cae)))]
      [`(if ,ae ,e0 ,e1)
       `(if ,ae ,(T-e e0 cae) ,(T-e e1 cae))]
      [`(,aef ,aes ...)
       `(,(T-ae aef) ,cae ,@(map T-ae aes))]))
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


