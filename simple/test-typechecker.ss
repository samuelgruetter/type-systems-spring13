#lang racket

(require redex)
(require "simple-v1.ss")

(test-equal 
  (term (intersect-ts 
    String
    String))
  (term String))

(test-equal 
  (term (intersect-ts 
    [(val a []) (val b [])]
    [(val b []) (val a [])]))
  (term [(val a []) (val b [])]))

(test-equal 
  (term (intersect-ts 
    (-> [(val a String)] [(val foo [])])
    (-> [(val a String)] [(val bar [])])))
  (term (-> [(val a String)] [(val bar []) (val foo [])])))

(test-equal 
  (term (intersect-ts 
    (-> [(val a String)] [(val bar [])])
    (-> [(val a String)] [(val foo [])])))
  (term (-> [(val a String)] [(val bar []) (val foo [])])))


(test-results)
