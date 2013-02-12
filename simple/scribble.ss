#lang racket

(require redex)

(require "simple-v1.ss")
(require "lib-v1.ss")

(define test0 (term ({
   (val f (→ Int (→ (→ Int Void) Void))
        (↦ (n Int) (↦ (g (→ Int Void)) {void})))
   (f 5)
})))

(define test1 (term ({
   (val f (↦ (g (→ Int Int)) (↦ (n Int) (if (== n 0) 1 (* n (g (- n 1)))))))
   (val i (↦ (n Int) n))
   ((f (f (f (f (f (f i)))))) 3)
})))

(define test2 (term ({
   (val a Int 5)
   (type foo [])
   (val b Int 6)
   (+ a b)
})))

(define test3 (term ({
   (type W [
             (val i Int)
             (val cond (→ Int Bool))
             (val body (→ Int Int))])
   (val f (→ Int (→ (→ Int Void) Void))
        (↦ (n Int) (↦ (g (→ Int Void)) {void})))
   (f 5)
})))

(define test4 (term ({
  (val lib ,lib)
  lib
})))

(define test5 (term (
  (val a 5)
  (val b 6)
)))

(define test test5)

(redex-match L e test)

(judgment-holds (types () ,test t) t)

(traces red (term (,test () ())))