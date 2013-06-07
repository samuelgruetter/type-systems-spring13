#lang racket

(caching-enabled? #t) 

(require redex)
;(require "my_dotf.ss")
;(require "dotf.ss")
(require "../../dot/src/redex/dot.rkt")
;(require "dot_magic.rkt")




; The same as inf-paths-dotf.ss (see that file for more comments), 
; but adapted for dot.rkt.
; Still runs into an infinite loop.

; typecheck is defined in dotf.ss, but not in dot.rkt
; so we will use judgment (typeok env s T)
; note that T is an I argument, not O

(define T1 (term {rfn Top a 
        (:: (cc L) Bot {rfn Top z 
              ; if you comment out the following two lines, everything will work
              (:: (ca M) (sel (sel z (cv f)) (ca M))
                        (sel (sel z (cv f)) (ca M)))
              (:: (cv f) (sel a (cc L)))
              ;(:: (cv v) (sel z (ca M)))
        })
        (:: (cm m1) Top (sel a (cc L)))
        (:: (cm go) Top Top)
   }
))

(define s1 (term (val a = (new (
   ,T1
   ((cm m1) unusedX (val r = (new {(sel a (cc L)) ((cv f) r)
                                                 ;((cv v) r)
                                 }) in r))
   ;((cm go) x (sel a (cm m1) x))
   ((cm go) x (val res = (snd a (cm m1) x) in res))
)) ;in (snd a (cm go) a))))
in a)))
                      
(test-equal (redex-match? dot s s1) #t)

(judgment-holds (expansion ((                          ) ()) z Top            ((D_1 ...) (D_2 ...) (D_3 ...))))
(judgment-holds (expansion (((a ,T1) (r (sel a (cc L)))) ()) z (sel r (ca M)) ((D_1 ...) (D_2 ...) (D_3 ...))))

(printf "Start inf loop critical part...") (judgment-holds (typeok (() ()) ,s1 ,T1)) (printf " done\n")


(test-results)
