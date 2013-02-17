#lang racket

(require redex)
(require "simple-v1.ss")

(define (test-types-equal t1 t2 b)
  (test-equal (term (types-equal ,t1 ,t2)) b))

(test-types-equal (term Str) (term Str) #t)
(test-types-equal (term Int) (term Str) #f)
(test-types-equal (term Str) (term Int) #f)

(test-types-equal (term [(val a []) (val b [])])
                  (term [(val b []) (val a [])]) #t)

(test-types-equal (term [(val a []) (val b []) (val c [])])
                  (term [(val a []) (val b [])           ]) #f)

(test-equal 
  (term (intersect-ts 
    Str
    Str))
  (term Str))

(test-types-equal 
  (term (intersect-ts 
    [(val a []) (val b [])]
    [(val b []) (val a [])]))
  (term [(val b []) (val a [])]) #t)

(test-equal (judgment-holds (types {(val a Str)} a Str)) #t)
(test-equal (judgment-holds (types {(val a Int)} a Str)) #f)

(test-equal (judgment-holds (sub Str Str)) #t)

(test-equal (judgment-holds (sub [(val a Str)] []           )) #t)
(test-equal (judgment-holds (sub [(val a Str)] [(val a Str)])) #t)
(test-equal (judgment-holds (sub [(val a Str)] [(val a Int)])) #f)



(test-types-equal 
  (term (intersect-ts 
    (→ [(val a Str)] [(val foo [])])
    (→ [(val a Str)] [(val bar [])])))
  (term (→ [(val a Str)] [(val bar []) (val foo [])]))  #t)

(test-types-equal 
  (term (intersect-ts 
    (→ [(val a Str)] [(val bar [])])
    (→ [(val a Str)] [(val foo [])])))
  (term (→ [(val a Str)] [(val foo []) (val bar [])]))  #t)

(test-types-equal 
  (term (intersect-ts 
    (→ [(val a Str)] [(val bar [])])
    (→ [(val a Str)] [(val foo [])])))
  (term (→ [(val a Str)] [(val foo [])]))  #f)

(test-types-equal 
  (term (intersect-ts 
    (→ [(val a Str)] [(val bar [])])
    (→ [(val a Str)] [(val foo [])])))
  (term (→ [(val a Str)] [(val foo []) (val bar []) (val bar2 [])])) #f)

(test-equal (judgment-holds (sub Int Int)) #t)

(test-equal (judgment-holds (sub Str Int)) #f)

(test-equal (judgment-holds (sub [(val label1 Int) (val label2 Int)] 
                                 [(val label2 Int)                 ])) #t)

(test-equal (judgment-holds (sub [(val label1 Int) (val label2 Int)] 
                                 [(val label2 Str)              ])) #f)

(test-results)
