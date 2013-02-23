#lang racket

(require redex)
(require "simple-v1.ss")

(test-->> red
   (term ((if true 2 3) () ()))
   (term (2 () ())))

(test-->> red
   (term ((+ 4 3) () ()))
   (term (7 () ())))

(test-->> red
   (term ({(val f (↦ (n Int) n)) (f 4)} () ()))
   (term (4 () ())))

(define primelist-e (term {
  (val i (cell 2))
  (val N 12)
  (val nthPrime (↦ (n Int) (if (== n 1) 2 3)))
  (nthPrime 1)
}))

(test-equal (judgment-holds (types {} ,primelist-e Int)) #t)

(test-->> red
   (term (,primelist-e () ()))
   (term (2 () ())))

; This example must not work, but it does!
(traces red (term ({(val f (↦ (n Int) n)) (+ (f 4) n)} () ())))

(test-results)
