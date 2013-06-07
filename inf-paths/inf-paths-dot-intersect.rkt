#lang racket

(require redex)
;(require "my_dotf.ss")
;(require "dotf.ss")
(require "../../dot/src/redex/dot.rkt")
;(require "dot_magic.rkt")

; in a nutshell: in dot.rkt,
; new Tp1() typechecks, new Tp2() typechecks, but new (Tp1 ∧ Tp2)() inf loop
; that's how it was before

; now we need to explicitly say what we want to expand to get inf loop (see below)

(define Tp1 (term {rfn Top y
        (:: (cc A) Bot {rfn Top z 
              (:: (ca M) (sel (sel z (cv b)) (ca M))
                        (sel (sel z (cv b)) (ca M)))
              (:: (cv b) (sel y (cc B)))
        })
        (:: (cc B) Bot {rfn Top z 
              (:: (ca M) Top Top)
              (:: (cv a) (sel y (cc A)))
        })
   }
))
(test-equal (redex-match? dot T Tp1) #t)


(define Tp2 (term {rfn Top y
        (:: (cc A) Bot {rfn Top z 
              (:: (ca M) Top Top)
              (:: (cv b) (sel y (cc B)))
        })
        (:: (cc B) Bot {rfn Top z 
              (:: (ca M) (sel (sel z (cv a)) (ca M))
                        (sel (sel z (cv a)) (ca M)))
              (:: (cv a) (sel y (cc A)))
        })
   }
))
(test-equal (redex-match? dot T Tp2) #t)

(judgment-holds (expansion (() ()) y ,Tp1 Ds) Ds)
(judgment-holds (expansion (() ()) y ,Tp2 Ds) Ds)
(judgment-holds (expansion (() ()) y (,Tp1 ∧ ,Tp2) Ds) Ds)

(define se1 (term (val t1 = (new (,Tp1)) in t1)))
(test-equal (redex-match? dot s se1) #t)
(judgment-holds (typeok (() ()) ,se1 ,Tp1))

(define se3 (term (val t3 = (new ((,Tp1 ∧ ,Tp2))) in t3)))
(test-equal (redex-match? dot s se3) #t)

(printf "marker 1\n")

; before, this one inf looped:
(judgment-holds (typeok (() ()) ,se3 ,Tp1))
(judgment-holds (typeok (() ()) ,se3 (,Tp1 ∧ ,Tp2)))
(judgment-holds (typeok (() ()) ,se3 (,Tp2 ∧ ,Tp1)))

(printf "marker 2\n")

; this one inf loops:
(judgment-holds (expansion ({(e (,Tp1 ∧ ,Tp2)) (f (sel e (cc A)))} {}) z (sel f (ca M)) ((D_1 ...) (D_2 ...) (D_3 ...))))


; if we recursively evaluate intersections in (,Tp1 ∧ ,Tp2), we get Tp3 (not tested):
(define Tp3 (term {rfn Top y
        (:: (cc A) Bot {rfn Top z 
              (:: (ca M) (sel (sel z (cv b)) (ca M))
                        (sel (sel z (cv b)) (ca M)))
              (:: (cv b) (sel y (cc B)))
        })
        (:: (cc B) Bot {rfn Top z 
              (:: (ca M) (sel (sel z (cv a)) (ca M))
                        (sel (sel z (cv a)) (ca M)))
              (:: (cv a) (sel y (cc A)))
        })
   }
))



