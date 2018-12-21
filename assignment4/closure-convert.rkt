#lang racket

(require "utils.rkt")

(provide closure-convert
         procs->llvm)



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
(define (procs->llvm procs)
  (define globals "")
(define (proc->llvm proc)
  (match proc
    [`(let ([,x (prim ,op ,xs ...)]) ,e0)
     (string-append "  %" (c-name x) " = call i64 @" (prim-name op) "( i64 %" (c-name (car xs))
                    (foldl (lambda (x res) (string-append res ", i64 %" (c-name x))) "" (cdr xs))
     ")\n"
     (proc->llvm e0))]
    [`(let ([,x (apply-prim ,op ,x0)]) ,e0)
     (string-append "  %" (c-name x) " call i64 @" (prim-applyname op) "(i64 %" (c-name x0) ")\n"
                    (proc->llvm e0))]
    ; dats ...
    [`(let ([,x ',(? integer? dat)]) ,e0)
     (string-append "  %" (c-name x) " = call i64 @const_init_int(i64 " (number->string dat) ")\n")
     (proc->llvm e0)]
    ; store i8* getelementptr inbounds ([6 x i8], [6 x i8]* @"??_C@_05CJBACGMB@hello?$AA@", i32 0, i32 0)
    [`(let ([,x ',(? string? dat)]) ,e0)
     (define brackets (string-append "[" (number->string (+ 1 (string-length dat))) " x i8]"))
     (define xstring (c-name (gensym 'string)))
     (set! globals
                  (string-append globals
                      "@" xstring " = private unnamed_addr constant "
                      brackets " c\"" dat "\\00\", align 8\n"))
     (string-append "  %" (c-name x) " = call 164 @const_init_string(i8* getelementptr inbounds (" brackets ", " brackets "* @" xstring ", i32 0, i32 0))\n")
     (proc->llvm e0)]
    [`(let ([,x ',(? symbol? dat)]) ,e0)
     (define xsym (c-name (gensym 'sym)))
     (define brackets (string-append "[" (number->string (+1 (string-length (symbol->string dat)))) " x i8]"))
     (set! globals
                  (string-append globals
                      "@" xsym " = private unnamed_addr constant "
                      brackets " c\"" (symbol->string dat) "\\00\", align 8\n"))
     (string-append "  %" (c-name x) " = call 164 @const_init_string(i8* getelementptr inbounds (" brackets ", " brackets "* @" xsym ", i32 0, i32 0))\n")]
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

    [`(let ([,x (make-closure ,lamx ,xs ...)]) ,e0)
     (define ptrclo (c-name (gensym 'ptrclo)))
     (define envptrs (map (lambda (x) (c-name (gensym 'envptr))) xs))
     (define funcptr (c-name (gensym 'fptr)))
     (define n (match (car (filter (match-lambda [`(proc (,f . ,_) . ,_) (eq? f lamx)]) procs))
                             [`(proc (,lamx ,ys ...) . ,_) (length ys)]))
     (define f (c-name (gensym 'f)))
     (string-append
      "  %" ptrclo " = call i64* @alloc(i64 " (number->string (* (+ (length xs) 1) 8)) ")\n"
      (foldr string-append "" (map (lambda (eptr n)
             "  %" eptr " = getelementptr inbounds i64, i64* %" ptrclo ", i64 " (number->string n) "\n")
               envptrs (cdr (range (+ 1 (length xs))))))
      (foldr string-append "" (map (lambda (x eptr)
               "  store i64 %" (c-name x) ", i64* %" eptr "\n" )
             xs envptrs))
      "  %" funcptr " = getelementptr inbounds i64, i64* %" ptrclo ", i64 0\n"
      "  %" f " = ptrtoint void(i64" (foldr string-append "" (map (lambda (_) ",i64") (range (- n 1))))
      ")* @" (c-name lamx) " to i64\n"
      "  store i64 %" f ", i64* %" funcptr "\n"
      "  %" (c-name x) " = ptrtoint i64* %" ptrclo " to i64\n"
     (proc->llvm e0))]
    [`(let ([,x (env-ref ,envx ,cnt)]) ,e0)
     (define envxptr (c-name (gensym 'envptr)))
     (define eptr (c-name (gensym 'envptr)))
     (string-append
      "  %" envxptr " = inttoptr i64 %" (c-name envx) " to i64*\n"
      "  %" eptr " = getelementptr inbounds i64, i64* %" envxptr ", i64 " (number->string cnt) "\n"
      "  %" (c-name x) " = load i64, i64* %" (eptr) ", align 8\n"
      (proc->llvm e0))]
    [`(clo-app ,x ,xs ...)
     (define ptrclo (c-name (gensym 'ptrclo)))
     (define iptr (c-name (gensym 'iptr)))
     (define funcptr (c-name (gensym 'funcptr)))
     (define f (c-name (gensym 'f)))
     (string-append
      "  %" ptrclo " = inttpotr i64 %" (c-name x) " to i64*\n"
      "  %" iptr " = getelementptr inbounds i64, i64* %" ptrclo ", i64 0\n"
      "  %" f " = load i64, i64* %" iptr ", align 8\n"
      "  %" funcptr " = inttoptr i64 %" f " to void (i64" (foldl string-append "" (map (lambda (_) ",i64") (range (length xs))))
      ")*\n"
      "  musttail call fastcc void %" funcptr "(i64 %" (c-name x) (foldl (lambda (x acc) (string-append acc ", i64 %" (c-name x))) "" xs) ")\n"
      "  ret void\n")]
    
   ))

  (define (convert-to-llvm proc)
    (match proc
           [`(proc (main) ,e)
            (string-append
             "define void @proc_main() {\n"
             (proc->llvm e)
             "}\n"
             "\n\n"
             "define i32 @main() {\n"
             "  call fastcc void @proc_main()\n"
             "  ret i32 0\n"
             "}\n\n")]
           [`(proc (,lamx ,x0 ,xs ...) ,e0)
            (string-append
             "define void @" (symbol->string lamx)
             "("
             (foldl (lambda (x args) (string-append args ", i64 %" (c-name x)))
                    (string-append "i64 %" (c-name x0))
                    xs)
             ") {\n"
             (proc->llvm e0)
             "}\n")]))
  
  (define llvm-procs
    (apply string-append
           (map (lambda (s) (string-append s "\n\n"))
                (map convert-to-llvm procs))))
  (string-append llvm-procs
                 "\n\n\n"
                 globals))





