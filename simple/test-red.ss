#lang racket

(require redex)
(require "simple-v1.ss")

(test-->> red
   (term ((if true 2 3) () ()))
   (term (2 () ())))

(test-->> red
   (term ((+ 4 3) () ()))
   (term (7 () ())))

(define primelist-e (term {
  (val i (cell 2))
  (val n 12)
  (val nthPrime (↦ (n Int) (if (== n 1) 2 3)))
  (nthPrime 1)
}))

(test-->> red
   primelist-e
   (term 2))

(test-results)
