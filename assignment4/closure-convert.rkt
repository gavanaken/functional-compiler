#lang racket

(require "utils.rkt")

(provide closure-convert
         proc->llvm)



; Pass that removes lambdas and datums as atomic and forces them to be let-bound
;   ...also performs a few small optimizations
(define (simplify-ae e)
  (define (wrap-aes aes wrap)
    (match-define (cons xs wrap+)
                  (foldr (lambda (ae xs+wrap)
                           (define gx (gensym 'arg))
                           (if (symbol? ae)
                               (cons (cons ae (car xs+wrap))
                                     (cdr xs+wrap))
                               (cons (cons gx (car xs+wrap))
                                     (lambda (e)
                                       (match ae
                                              [`(lambda ,xs ,body) 
                                               `(let ([,gx (lambda ,xs ,(simplify-ae body))])
                                                  ,((cdr xs+wrap) e))]
                                              [`',dat
                                               `(let ([,gx ',dat])
                                                  ,((cdr xs+wrap) e))])))))
                         (cons '() wrap)
                         aes))
    (wrap+ xs))
  (match e
         [`(let ([,x (lambda ,xs ,elam)]) ,e0)
          `(let ([,x (lambda ,xs ,(simplify-ae elam))]) ,(simplify-ae e0))]

         [`(let ([,x ',dat]) ,e0)
          `(let ([,x ',dat]) ,(simplify-ae e0))]

         [`(let ([,x (prim ,op ,aes ...)]) ,e0)
          (wrap-aes aes (lambda (xs) `(let ([,x (prim ,op ,@xs)]) ,(simplify-ae e0))))]
         [`(let ([,x (apply-prim ,op ,aes ...)]) ,e0)
          (wrap-aes aes (lambda (xs) `(let ([,x (apply-prim ,op ,@xs)]) ,(simplify-ae e0))))]

         [`(if (lambda . ,_) ,et ,ef)
          (simplify-ae et)]
         [`(if '#f ,et ,ef)
          (simplify-ae ef)]
         [`(if ',dat ,et ,ef)
          (simplify-ae et)]
         [`(if ,(? symbol? x) ,et ,ef)
          `(if ,x ,(simplify-ae et) ,(simplify-ae ef))]

         [`(apply ,ae0 ,ae1)
          'case-not-implemented]
         
         [`(,aes ...)
          (wrap-aes aes (lambda (xs) xs))]))


; Helper to remove vararg lambdas/callsites
(define (remove-varargs e) 
  (match e
         [`(let ([,x ',dat]) ,e0)
          `(let ([,x ',dat]) ,(remove-varargs e0))]
         [`(let ([,x (prim ,op ,xs ...)]) ,e0)
          `(let ([,x (prim ,op ,@xs)]) ,(remove-varargs e0))]
         [`(let ([,x (apply-prim ,op ,y)]) ,e0)
          `(let ([,x (apply-prim ,op ,y)]) ,(remove-varargs e0))]
         [`(let ([,x (lambda (,xs ...) ,body)]) ,e0)
          ; turns (xs ...) into x and immediately into (x)
          ; by adding the needed car/cdr calls and let bindings
          (define gx (gensym 'rvp))
          (define gx+e
            (foldr (lambda (x gx+e)
                     (define gx (gensym 'rvp))
                     (cons gx
                           `(let ([,x (prim car ,gx)])
                              (let ([,(car gx+e) (prim cdr ,gx)])
                                ,(cdr gx+e)))))
                   (cons (gensym 'na) (remove-varargs body))
                   xs))
          `(let ([,x (lambda (,(car gx+e)) ,(cdr gx+e))])
             ,(remove-varargs e0))]
         [`(let ([,x (lambda ,y ,body)]) ,e0)
          `(let ([,x (lambda (,y) ,(remove-varargs body))])
             ,(remove-varargs e0))]
         [`(if ,x ,e0 ,e1)
          `(if ,x ,(remove-varargs e0) ,(remove-varargs e1))]
         [`(apply ,f ,args)
          `(,f ,args)] 
         [`(,f ,xs ...)
          ; case not written
          'remove-varargs-call-sites]))

; call simplify-ae on input to closure convert, then remove vararg callsites/lambdas
(define (closure-convert cps)
  (define scps (simplify-ae cps))
  (define no-varargs-cps (remove-varargs scps))
  (define (bottom-up e procs)
    (match e
      [`(let ([,x ',dat]) ,e0)
       (match-define `(,e0+ ,free+ ,procs+)
                     (bottom-up e0 procs))
       `((let ([,x ',dat]) ,e0+)
         ,(set-remove free+ x)
         ,procs+)]
      [`(let ([,x (prim ,op ,xs ...)]) ,e0)
       (match-define `(,e0+ ,free+ ,procs+)
                     (bottom-up e0 procs))
       `((let ([,x (prim ,op ,@xs)]) ,e0+)
         ,(set-remove (set-union free+ (list->set xs)) x)
         ,procs+)]
      [`(let ([,x (lambda (,xs ...) ,body)]) ,e0)
       (match-define `(,e0+ ,free0+ ,procs0+)
                     (bottom-up e0 procs))
       (match-define `(,body+ ,freelam+ ,procs1+)
                     (bottom-up body procs0+))
       (define env-vars (foldl (lambda (x fr) (set-remove fr x))
                               freelam+
                               xs))
       (define ordered-env-vars (set->list env-vars))
       (define lamx (gensym 'lam))
       (define envx (gensym 'env))
       (define body++ (cdr (foldl (lambda (x count+body)
                                    (match-define (cons cnt bdy) count+body)
                                     (cons (+ 1 cnt)
                                           `(let ([,x (env-ref ,envx ,cnt)])
                                              ,bdy)))
                                  (cons 1 body+)
                                  ordered-env-vars)))
       `((let ([,x (make-closure ,lamx ,@ordered-env-vars)]) ,e0+)
         ,(set-remove (set-union free0+ env-vars) x)
         ((proc (,lamx ,envx ,@xs) ,body++) . ,procs1+))]
      [`(if ,(? symbol? x) ,e0 ,e1)
       (match-define `(,e0+ ,free0+ ,procs0+)
                     (bottom-up e0 procs))
       (match-define `(,e1+ ,free1+ ,procs1+)
                     (bottom-up e1 procs0+))
       `((if ,x ,e0+ ,e1+)
         ,(set-union free1+ free0+ (set x))
         ,procs1+)]
      [`(,(? symbol? xs) ...)
       `((clo-app ,@xs)
         ,(list->set xs)
         ,procs)]))
  ; case not written; see our livecoding from class
  (match-define `(,main-body ,free ,procs) (bottom-up no-varargs-cps '()))
  `((proc (main) ,main-body) . ,procs))


; Walk procedures and emit llvm code as a string
; (string-append "  %r0 = opcode i64 %a, %b \n"
;                "  %r1 = ... \n")
(define (proc->llvm proc)
  (match proc
    [`(let ([,x (prim ,op ,xs ...)]) ,e0)
     (string-append "  %" (c-name x) " = call i64 @" (prim-name op) "( i64 %" (c-name (car xs))
                    (foldl (lambda (x res) (string-append res ", i64 %" (c-name x))) "" (cdr xs))
     ")" (string-append "call " (prim-name op) "\n") ; actually call it
     (proc->llvm e0))]
    [`(let ([,x (apply-prim ,op ,x0)]) ,e0)
     (string-append "  %" (c-name x) " call i64 @" (prim-applyname op) "(i64 %" (c-name x0) ")"
                    (string-append "call " (prim-applyname op) "\n")
                    (proc->llvm e0))]
    ; dats ...
    [`(let ([,x ',(? integer? dat)]) ,e0)
     (string-append "  %" (c-name x) " = call i64 @const_init_int(i64 " (number->string dat) ")\n")
     (proc->llvm e0)]
    ; store i8* getelementptr inbounds ([6 x i8], [6 x i8]* @"??_C@_05CJBACGMB@hello?$AA@", i32 0, i32 0)
    [`(let ([,x ',(? string? dat)]) ,e0)
     (define brackets (string-append "[" (number->string (+ 1 (string-length dat))) " x i8]"))
     (string-append "  %" (c-name x) " = call 164 @const_init_string(i8* getelementptr inbounds (" brackets ", " brackets "* @" (c-name (gensym '??_)) ", i32 0, i32 0))\n")
     (proc->llvm e0)]
    [`(let ([,x '#t]) ,e0)
     (string-append "  %" (c-name x) " = call i64 @const_init_true()\n")
     (proc->llvm e0)]
    [`(let ([,x '#f]) ,e0)
      (string-append "  %" (c-name x) " = call i64 @const_init_false()\n")
      (proc->llvm e0)]

    [`(if ,x ,e0 ,e1)
     (define tobool (c-name (gensym 'tobool)))
     (define if.then (c-name (gensym 'if.then)))
     (define if.else (c-name (gensym 'if.else)))
     (string-append "  %" tobool " = trunc i8 %" (c-name x) "to i1\n"
      "  br i1 %" tobool ", label %" if.then  ", label %" if.else "\n"
                    "\n" if.then ":\n" (proc->llvm e0)
                    "\n" if.else ":\n" (proc->llvm e1))]
    
   ))





