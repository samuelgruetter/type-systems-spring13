#lang racket
(require redex)
(require "simple-v1.ss")
(provide example1)

(define example1 (term (
{
   ;;; The "Library" ;;;
   (val std (
      (val IntVector [
         (val size (-> Void Int))
         (val maxSize Int)
         (val empty (-> Void Bool))
         (val at (-> Int (var Int)))
         (val push_back (-> Int Void))
      ])
      (val newVector (-> Void IntVector) (=> (v Void) (
         (val fSize (var Int) (cell 0))
         (val e0 (var Int) (cell 0))
         (val e1 (var Int) (cell 0))
         (val e2 (var Int) (cell 0))
         (val e3 (var Int) (cell 0))
         
         (val size (=> (v Void) ((sel fSize get)())))
         (val maxSize 4)
         (val empty (=> (v Void) (== 0 ((sel fSize get)()))))
         (val at (-> Int (var Int)) (=> (i Int) {
            (if (== i 0) 
               e0 
               ((if (== i 1) 
                  e1 
                  ((if (== i 2) 
                     e2 
                     ((if (== i 3) 
                        e3 
                        null )))))))
         }))
         (val push_back (-> Int Void) (=> (el Int) {
            (ign ((sel (at ((sel fSize get) ())) set) el))
            ; in C, this would be fSize++ :D
            ((sel fSize set) (+ ((sel fSize get) ()) 1))
         }))
      )))
   ))

   ;;; The "Application" ;;;
   (println "Hello World")

   (val increase  (=> (a (var Int)) ((sel a set) (+ ((sel a get) ()) 1))))
   
   (val v (newVector ()))
   (ign ((sel v push_back) 1))
   (ign ((sel v push_back) 2))
   (ign (increase ((sel v at) 1)))
   
   (println ((sel ((sel v at) 1) get) ()))
   
   0 ; return value of program
}
)))

(redex-match L-simple-v1 prog example1)
