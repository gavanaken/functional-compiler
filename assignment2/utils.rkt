#lang racket


(provide prim? reserved? prims->list
         datum?
         test-desugar
         eval-scheme
         eval-ir
         scheme-exp?
         ir-exp?
         alphatized-exp?
         test-alphatize
         anf-exp?
         test-anf-convert
         cps-exp?
         test-cps-convert)


(define prims-list '(= > < <= >= + - * / 
                     cons? null? cons car cdr list first second third fourth fifth list
                     length list-tail drop take member memv map append foldl foldr
                     vector? vector make-vector vector-ref vector-set! vector-length
                     set set->list list->set set-add set-union set-first set-rest set-remove
                     hash hash-ref hash-set hash-count hash-has-key? hash?
                     list? void? promise? procedure? number? integer?
                     error void print display write exit halt
                     eq? eqv? equal? not))
(define (prims->list) prims-list)
(define (prim? op)
  (if (member op prims-list)
      #t
      #f))

(define reserved-list '(letrec letrec* let let* if and or set! quote begin
                               cond case when unless delay force dynamic-wind
                               raise guard call/cc prim apply-prim))
(define (reserved? id)
  (if (member id reserved-list)
      #t
      #f))

(define (datum? d)
  (match d
         [`#(,(? datum?) ...) #t]
         [`(,(? datum?) ...) #t]
         [(cons datum? datum?) #t]
         [(? string?) #t]
         [(? integer?) #t]
         [(? symbol?) #t]
         [(? boolean?) #t]
         [else (pretty-print `(bad-datum ,d)) #f]))


(define (scheme-exp? e [env (set)])
  (define (var? x) (symbol? x))
  (define ((rec/with env) e)
    (scheme-exp? e env))
  (define (no-duplicates? lst)
    (= (set-count (list->set lst)) (length lst)))
  (define (ext env lst)
    (set-union env (list->set lst)))
  (define (improper-args? args)
    (if (var? args)
        #t
        (and (cons? args)
             (var? (car args))
             (improper-args? (cdr args)))))
  (define (cond-clause? cls) 
    (match cls
           [`(,(? (rec/with env))) #t]
           [`(,(? (rec/with env)) ,(? (rec/with env))) #t]
           [else #f]))
  (define (case-clause? cls) 
    (match cls
           [`((,(? datum?) ...) ,(? (rec/with env))) #t]
           [else #f]))
  (match e
         [`(letrec* ([,(? var? xs) ,es] ...) ,e0)
          (and (no-duplicates? xs)
               (andmap (rec/with (ext env xs))
                       (cons e0 es)))]
         [`(letrec ([,(? var? xs) ,es] ...) ,e0)
          (and (no-duplicates? xs)
               (andmap (rec/with (ext env xs))
                       (cons e0 es)))]
         
         [`(let* () ,e0)
          ((rec/with env) e0)]
         [`(let* ([,x ,e0]) ,e1)
          ((rec/with env) `(let ([,x ,e0]) ,e1))]
         [`(let* ([,x ,e0] . ,rest) ,e1)
          ((rec/with env) `(let ([,x ,e0]) (let* ,rest ,e1)))]
         
         [`(let ([,(? symbol? xs) ,(? (rec/with env) es)] ...) ,e0)
          (and (no-duplicates? xs)
               ((rec/with (ext env xs)) e0))]
         [`(let ,(? var? lp)  ([,xs ,es] ...) ,e0)
          ((rec/with env) `(letrec ([,lp (lambda ,xs ,e0)]) (,lp . ,es)))]
         
         [`(lambda (,(? var? xs) ...) ,e0)
          (and (no-duplicates? xs)
               ((rec/with (ext env xs)) e0))]
         [`(lambda ,(? var? x) ,e0)
          ((rec/with (ext env (list x))) e0)]
         [`(lambda ,(? improper-args? args) ,e0)
          (and (no-duplicates? (flatten args))
               ((rec/with (ext env (flatten args))) e0))]
         
         [`(delay ,(? (rec/with env))) #t]
         [`(force ,(? (rec/with env))) #t]
         [`(guard (,(? symbol? x) ,clauses ...) ,(? (rec/with env)))
          (scheme-exp? `(cond . ,clauses) (ext env (list x)))]
         [`(raise ,(? (rec/with env))) #t]
         [`(dynamic-wind ,(? (rec/with env)) ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(cond ,(? cond-clause?) ...) #t]
         [`(cond ,(? cond-clause?) ... (else ,(? (rec/with env)))) #t]
         [`(case ,(? (rec/with env)) ,(? case-clause?) ...) #t]
         [`(case ,(? (rec/with env)) ,(? case-clause?) ... (else ,(? (rec/with env)))) #t]
         [`(and ,(? (rec/with env)) ...) #t]
         [`(or ,(? (rec/with env)) ...) #t]
         [`(when ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(unless ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(if ,(? (rec/with env)) ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(set! ,(? symbol?) ,(? (rec/with env))) #t]
         [`(begin ,(? (rec/with env)) ,(? (rec/with env)) ...) #t]
         [`(call/cc ,(? (rec/with env))) #t]
         [`(let/cc ,(? symbol? x) ,eb) ((rec/with (ext env (list x))) eb)]

         [(? var? x) (if (set-member? env x) #t (prim? x))]
         [`(quote ,(? datum?)) #t]

         [`(,(? prim?) ,(? (rec/with env)) ...) #t]
         [`(apply ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(,(? (rec/with env)) ,(? (rec/with env)) ...) #t]

         [else (pretty-print `(bad-scheme ,e ,env)) #f]))



(define (eval-scheme e)
  (if (scheme-exp? e)
      (racket-compile-eval e)
      (error 'malformed-scheme)))



(define (test-desugar desugar scheme-prog)  
  (define val1 (eval-scheme scheme-prog))   
  (define ir-e (desugar scheme-prog))       
  (define val2 (eval-ir ir-e))              
  (if (equal? val1 val2)
      #t
      (begin
        (display (format "Test-desugar: two different values (~a and ~a) before and after desugaring\n"
                         val1 val2))
        #f)))


(define (ir-exp? e [env (set)]) 
  (define (var? x) (symbol? x))
  (define ((rec/with env) e)
    (ir-exp? e env))
  (define (no-duplicates? lst)
    (= (set-count (list->set lst)) (length lst)))
  (define (ext env lst)
    (set-union env (list->set lst)))
  (match e
         [`(let ([,(? var? xs) ,(? (rec/with env) es)] ...) ,e0)
          (and (no-duplicates? xs)
               ((rec/with (ext env xs)) e0))]
         [`(lambda (,(? var? xs) ...) ,e0)
          (and (no-duplicates? xs)
               ((rec/with (ext env xs)) e0))]
         [`(lambda ,(? var? x) ,e0)
          ((rec/with (ext env (list x))) e0)]
         [`(apply ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(if ,(? (rec/with env)) ,(? (rec/with env)) ,(? (rec/with env))) #t]
         [`(set! ,(? symbol?) ,(? (rec/with env))) #t]
         [`(call/cc ,(? (rec/with env))) #t]
         [(? var? x) (if (set-member? env x) #t #f)]
         [`(quote ,(? datum?)) #t]
         [`(prim ,(? prim?) ,(? (rec/with env)) ...) #t]
         [`(apply-prim ,(? prim?) ,(? (rec/with env))) #t]
         [`(,(? (rec/with env)) ,(? (rec/with env)) ...) #t]
         [else (pretty-print `(bad-ir ,e ,env)) #f]))


(define (eval-ir e)
  (if (ir-exp? e)
      (racket-compile-eval e)
      (error 'malformed-ir)))


(define (test-alphatize box rename prog) 
  (define val (eval-ir prog))
  (define boxed-e (box prog))
  (define alphatized-e (rename boxed-e))
  (define correct (alphatized-exp? alphatized-e))
  (if correct
      (if (equal? val (eval-ir alphatized-e))
          #t
          (begin
            (if correct
                (display (format "Test-alphatized: two different values (~a and ~a) before and after boxing and alphatizing.\n"
                                 val (eval-ir alphatized-e)))
                (display "Output from boxing and alphatizing does not fit the output grammar.\n"))
            #f))
      (begin
        (display "Output not in alphatized language.")
        #f)))


(define (alphatized-exp? e)
  (define seen (set))
  (define (not-seen-var? x) 
    (define valid (and (var? x)  (not (set-member? seen x))))
    (set! seen (set-add seen x))
    valid)
  (define (var? x) (symbol? x))
  (define (no-duplicates? lst)
    (= (set-count (list->set lst)) (length lst)))
  (define (ext env lst)
    (set-union env (list->set lst)))
  (define (alpha? e)
    (match e
         [`(let ([,(? not-seen-var? xs) ,(? alpha? es)] ...) ,e0)
          (and (no-duplicates? xs)
               (alpha? e0))]
         [`(lambda (,(? not-seen-var? xs) ...) ,e0)
          (and (no-duplicates? xs)
               (alpha? e0))]
         [`(lambda ,(? not-seen-var? x) ,e0)
          (alpha? e0)]
         [`(apply ,(? alpha?) ,(? alpha?)) #t]
         [`(if ,(? alpha?) ,(? alpha?) ,(? alpha?)) #t]
         [`(call/cc ,(? alpha?)) #t]
         [(? var? x) #t]
         [`(quote ,(? datum?)) #t]
         [`(prim ,(? prim?) ,(? alpha?) ...) #t]
         [`(apply-prim ,(? prim?) ,(? alpha?)) #t]
         [`(,(? (and/c (not/c (lambda (x) (member x '(let lambda apply if call/cc quote prim quote-prim))))
                       alpha?))
            ,(? alpha?) ...) #t]
         [else (pretty-print `(bad-alphatized ,e)) #f]))
  (and (ir-exp? e) (alpha? e)))



(define (test-anf-convert anf-convert prog) 
  (define val (eval-ir prog))
  (define anf-e (anf-convert prog))
  (define correct (anf-exp? anf-e))
  (if (and correct (equal? val (eval-ir anf-e)))
      #t
      (begin
        (if correct
            (display (format "Test-anf-convert: two different values (~a and ~a) before and after anf conversion.\n"
                             val (eval-ir anf-e)))
            (display "Output from anf conversion does not fit ANF grammar.\n"))
        #f)))


(define (anf-exp? e)
  (define (a-exp? e)
    (match e
           [`(lambda ,xs ,(? c-exp? e0)) #t]
           [`',dat #t]
           [(? symbol? x) #t]
           [else #f]))
  (define (c-exp? e)
    (match e
           [`(let ([,(? symbol? x) ,(? c-exp? rhs)]) ,(? c-exp? e0)) #t]
           [`(if ,(? a-exp? ae) ,(? c-exp? e0) ,(? c-exp? e1)) #t]
           [`(prim ,op ,(? a-exp? aes) ...) #t]
           [`(apply-prim ,op ,(? a-exp? ae)) #t]
           [`(call/cc ,(? a-exp? ae)) #t]
           [`(apply ,(? a-exp? aes) ,(? a-exp? aes)) #t]
           [`(,(? a-exp? aes) ...) #t]
           [(? a-exp? e) #t]
           [else (pretty-print `(bad-anf ,e)) #f]))
  (and (ir-exp? e) (c-exp? e)))



(define (test-cps-convert cps-convert prog) 
  (define val (eval-ir prog))
  (define cps-e (cps-convert prog))
  (define correct (cps-exp? cps-e))
  (if (and correct (equal? val (eval-ir cps-e)))
      #t
      (begin
        (if correct
            (display (format "Test-cps-convert: two different values (~a and ~a) before and after cps conversion.\n"
                             val (eval-ir cps-e)))
            (display "Output from cps conversion does not fit the CPS grammar.\n"))
        #f)))




(define (cps-exp? e)
  (define (a-exp? e)
    (match e
           [`(lambda ,xs ,(? c-exp? e0)) #t]
           [`',dat #t]
           [(? symbol? x) #t]
           [else (pretty-print `(bad-cps-ae ,e)) #f]))
  (define (c-exp? e)
    (match e
           [`(let ([,(? symbol? x) (prim ,op ,(? a-exp? aes) ...)]) ,(? c-exp? e0)) #t]
           [`(let ([,(? symbol? x) (apply-prim ,op ,(? a-exp? ae))]) ,(? c-exp? e0)) #t]
           [`(if ,(? a-exp? ae) ,(? c-exp? e0) ,(? c-exp? e1)) #t]
           [`(apply ,(? a-exp? aes) ,(? a-exp? aes)) #t]
           [`(,(? a-exp? aes) ...) #t]
           [else (pretty-print `(bad-cps-e ,e)) #f]))
  (and (anf-exp? e) (c-exp? e)))



(define (racket-compile-eval e)
  (with-handlers ([exn:fail? (lambda (x) (pretty-print "Evaluation failed:") (pretty-print e) (error 'eval-fail))])
                 (parameterize ([current-namespace (make-base-namespace)])
                               (namespace-require 'rnrs)
                               (namespace-require 'racket)
                               (namespace-require 'srfi/34)
                               (eval (compile
                                      `(call/cc (lambda (exit+)
                                                  (define (halt x) (exit+ x))
                                                  (define (prim op . args) (apply op args))
                                                  (define (apply-prim op args) (apply op args))
                                                  ,e)))))))


                       


