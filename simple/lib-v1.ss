#lang racket

(require redex)
(provide lib)

(require "simple-v1.ss")

; (define lib (term "I'm a teapot"))

; note that function application of function taking void is (f void), not (f ())

(define lib (term (
  (val log #|(var Str)|# (cell ""))
  (val println #|(→ Str Void)|# (↦ (s Str) ({
    ; log.set(log.get() + s + "\n")
    ((sel log set) (+ (+ ((sel log get) void) s) "\n"))
  })))
)))

(test-equal (redex-match? L e lib) #t)

(test-equal (judgment-holds (types-as ,lib [(val log (var Str))
                                            (val println (→ Str Void))])) #t)




