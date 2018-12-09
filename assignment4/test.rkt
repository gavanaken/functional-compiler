#lang racket

; Run this file or use the following at the REPL
(require "cps.rkt")
(require "utils.rkt")
(require "desugar.rkt")
(require "closure-convert.rkt")

; Load the test we're testing, perhaps amb.scm
(define scm (read (open-input-file "./tests/public/amb.scm" #:mode 'text)))

; Convert to cps, note that simplify-ir is added after the call to desugar
(define cps (cps-convert (anf-convert (alphatize (assignment-convert (simplify-ir (desugar scm)))))))
;(cps-exp? cps)

; Phases 1 and 2
(define p (closure-convert cps))
;(eval-proc p)
(define llvm (proc->llvm p))
(eval-llvm llvm)


