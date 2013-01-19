#lang racket

(require redex)
(require "simple-v1.ss")

(define sample-expr-1 (term ((+ 2 2))))
(redex-match L-simple-v1 e sample-expr-1)

(define sample-expr-2 (term ((if (== 3 4) (+ 2 2) (* 3 4)))))
(redex-match L-simple-v1 e sample-expr-2)

(define sample-expr-3 (term ((+ "The answer is " 42))))
(redex-match L-simple-v1 e sample-expr-3)

(define sample-stat-1 (term ((println (+ "The answer is " 42)))))

; a statement is not an expression:
; (redex-match L-simple-v1 e sample-stat-1)

(redex-match L-simple-v1 prog sample-stat-1)

(redex-match L-simple-v1 stat_1 sample-stat-1)

