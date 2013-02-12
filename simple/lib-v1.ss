#lang racket

(require redex)
(provide lib)

(require "simple-v1.ss")

; (define lib (term "I'm a teapot"))

(define lib (term (
  (val log (var Str) (cell ""))
  (val println (→ Str Void) (↦ (s Str) ({
    ; log.set(log.get() + s + "\n")
    ((sel log set) (+ (+ ((sel log get) ()) s) "\n"))
  })))
)))
