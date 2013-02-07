#lang racket

(require redex)

(require "simple-v1.ss")

(define test0 (term ({
   (val f (→ Int (→ (→ Int Void) Void))
        (↦ (n Int) (↦ (g (→ Int Void)) {void})))
   (f 5)
})))

(define test1 (term ({
   (val f (↦ (g (→ Int Int)) (↦ (n Int) (if (== n 0) 1 (* n (g (- n 1)))))))
   (val i (↦ (n Int) n))
   ((f (f (f (f (f i))))) 5)
})))

(define test2 (term ({
   (val a Int 5)
   (type foo [])
   (val b Int 6)
   (+ a b)
})))

(define test (term ({
   (type W [
             (val i Int)
             (val cond (→ Int Bool))
             (val body (→ Int Int))])
   (val f (→ Int (→ (→ Int Void) Void))
        (↦ (n Int) (↦ (g (→ Int Void)) {void})))
   (f 5)
})))

(redex-match L-simple-v1 e test)

(judgment-holds (types () ,test t) t)

(term (calc-e-type () ,test))

(traces red (term (,test () ())))