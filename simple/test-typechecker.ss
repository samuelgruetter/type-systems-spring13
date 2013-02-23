#lang racket

(require redex)
(require "simple-v1.ss")

(define (test-types-equal t1 t2 b)
  (test-equal (term (types-equal ,t1 ,t2)) b))

(test-equal (judgment-holds 
  (types {(val f (→ Int Str)) (val x Int)} (f x) Str)) #t)
(test-equal (judgment-holds 
  (types {(val f (→ Int Str)) (val x Int)} (f x) Int)) #f)
(test-equal (judgment-holds 
  (types {} (↦ (v Int) v) (→ Int Int))) #t)
(test-equal (judgment-holds 
  (types {} (↦ (v Int) (+ v "foo")) (→ Int Str))) #t)
(test-equal (judgment-holds 
  (types {} (↦ (v Int) v) (→ Int Str))) #f)
(test-equal (judgment-holds 
  (types {} ((↦ (v Int) v) 7) Int)) #t)
(test-equal (judgment-holds 
  (types {} (↦ (v Int) v) Bool)) #f)
(test-equal (judgment-holds
  (types-as (if true ((val a 3)) ((val a 3) (val b 4))) [(val a Int)])) #t)
(test-equal (judgment-holds
  (types {} {(val a 5) (+ a 4)} Int)) #t)
(test-equal (judgment-holds
  (types {} {(val a 5) (val b 5)} Int)) #f)
(test-equal (judgment-holds
  (types {(val f (→ Int Void))} {(ign (f 4)) (val a 5) (+ a 4)} Int)) #t)
(test-equal (judgment-holds
  (types {(val f (→ Int Void))} {(ign (f 4)) (val a 5) (f 8)} Void)) #t)
(test-equal (judgment-holds
  (types {(val f (→ Int Void))} {(ign (f 4)) (val a 5) (f void)} Void)) #f)
(test-equal (judgment-holds
  (types {} {(val f (↦ (v Int) v)) (f 4)} Int)) #t)
(test-equal (judgment-holds
  (types {(type T1 Int)} {(val f (↦ (v T1) v)) (f 4)} Int)) #t)
(test-equal (judgment-holds
  (types {} {(type T1 Int) (val f (↦ (v T1) v)) (f 4)} Int)) #t)
(test-equal (judgment-holds
  (types {} {(type T1 Int) (val f (↦ (v T1) (+ v 1))) (f 4)} Int)) #t)
(test-equal (judgment-holds
  (types {} {(type T1 Str) (val f (↦ (v T1) (+ v 1))) (f 4)} Int)) #f)
(test-equal (judgment-holds
  (types-as ((val a 4) (val c "hi")) [(val c Str) (val a Int)])) #t)
(test-equal (judgment-holds
  (types-as ((val a 4) (val c "hi")) [(val a Int) (val c Str)])) #t)
(test-equal (judgment-holds
  (types-as ((val a 4) (val c "hi")) [(val a Int)])) #t)
(test-equal (judgment-holds
  (types-as ((val a 4) (val c "hi")) [(val a Int) (val c Int)])) #f)
(test-equal (judgment-holds
  (types {(type MyStr Str)} (↦ (v MyStr) v) (→ Str Str))) #t)
(test-equal (judgment-holds
  (types-as ((type MyStr Str) (val f (↦ (v MyStr) v)) (val s (f "")))
            [(val f (→ Str Str)) (val s Str)])) #t)
(test-equal (judgment-holds
  (types-as ((type MyStr Str) (val f (↦ (v MyStr) v)) (val s (f 1)))
            [(val f (→ Str Str)) (val s Str)])) #f)
(test-equal (judgment-holds
  (types-as (cell 0) (var Int))) #t)
(test-equal (judgment-holds
  (types-as (sel (cell 3) get) (→ Void Int))) #t)
(test-equal (judgment-holds
  (types-as (sel (cell 3) set) (→ Int Void))) #t)
(test-equal (judgment-holds
  (types-as ((val fSize (cell 0))
             (val size (↦ (v Void) ((sel fSize get) void))))
            [(val fSize (var Int))
             (val size (→ Void Int))])) #t)
(test-equal (judgment-holds
  (types-as {(type T1 Str) (type T2 T1) (↦ (a T2) a)} (→ Str Str))) #t)
(test-equal (judgment-holds
  (types-as {(type T1 Str) (type T2 T1) (↦ (a T2) a)} (→ Int Str))) #f)
(test-equal (judgment-holds
  (types {} {(val f (↦ (n Int) n)) n} Int)) #f)

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
