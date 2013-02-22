#lang racket
(require redex)
(require "simple-v1.ss")
(require "lib-v1.ss")

(provide example-vector)

(define example-vector (term (
{
   ;;; Imports ;;;
   (val lib ,lib)
   (val println (sel lib println))
   
   ;;; The "Library" ;;;
   (val std (
      (type IntVector [
         (val size (→ Void Int))
         (val maxSize Int)
         (val empty (→ Void Bool))
         (val at (→ Int (var Int)))
         (val pushBack (→ Int Void))
      ])
      (val newVector (↦ (v Void) (
         (val fSize (cell 0))
         (val e0 (cell 0))
         (val e1 (cell 0))
         (val e2 (cell 0))
         (val e3 (cell 0))
         
         (val size (↦ (v Void) ((sel fSize get) void)))
         (val maxSize 4)
         (val empty (↦ (v Void) (== 0 ((sel fSize get) void))))
         (val at #|(→ Int (var Int))|# (↦ (i Int) {
            (if (== i 0) 
               e0 
               ((if (== i 1) 
                  e1 
                  ((if (== i 2) 
                     e2 
                     ((if (== i 3) 
                        e3 
                        (cell 44444444)))))))) ; error
         }))
         (val pushBack #|(→ Int Void)|# (↦ (el Int) {
            (ign ((sel (at ((sel fSize get) void)) set) el))
            ; in C, this would be fSize++ :D
            ((sel fSize set) (+ ((sel fSize get) void) 1))
         }))
      )))
   ))
   
   ;;; The "Application" ;;;
   (ign (println "Hello World"))

   (val increase  (↦ (a (var Int)) ((sel a set) (+ ((sel a get) void) 1))))
   
   (val v ((sel std newVector) void))
   (ign (println (+ "v.size() = " ((sel v size) void))))
   (ign ((sel v pushBack) 1))
   (ign ((sel v pushBack) 2))
   (ign (println (+ "v.size() = " ((sel v size) void))))
   (ign (increase ((sel v at) 1)))
   
   (ign (println (+ "v.at(1).get() = " ((sel ((sel v at) 1) get) void))))
   
   0 ; return value of program
}
)))

(test-equal (redex-match? L e example-vector) #t)

(judgment-holds (types {} ,example-vector t) t)

(test-equal (judgment-holds (types-as ,example-vector Int)) #t)
(test-equal (judgment-holds (types-as ,example-vector Str)) #f)

; TODO make this work
(traces red (term (,example-vector () ())))
