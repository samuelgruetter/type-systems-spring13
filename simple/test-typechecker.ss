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


(test-results)
