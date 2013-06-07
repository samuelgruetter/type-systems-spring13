#lang racket

(require redex)
;(require "my_dotf.ss")
(require "dotf.ss")

(define e1 (term (val a = new {
   {rfn Top a 
        (: (cc L) Bot {rfn Top z 
              (: (ca M) (sel (sel z (cv f)) (ca M))
                        (sel (sel z (cv f)) (ca M)))
              (: (cv f) (sel a (cc L)))
              ;(: (cv v) (sel z (ca M)))
        })
        (: (cm m1) Top (sel a (cc L)))
        (: (cm go) Top Top)
   }
   ((cm m1) unusedX (val r = new {(sel a (cc L)) ((cv f) r)
                                                 ;((cv v) r)
                                 } in r))
   ((cm go) x (sel a (cm m1) x))
} in (sel a (cm go) a))))

; In body of m1, a new instance of a.L is created, which requires that the
; type labels in a.L all have LowerBound <: UpperBound. 
; For r.M, this means that we need r.f.M <: r.f.M
; To check this, dotf checks if r.f.M is wf, which requires that its bounds
; are wf, i.e. that r.f.f.M is wf, which requires that r.f.f.f.M ... and so on.
; But even if it could check wf-ness without running into inf. loop, it had to
; check that r.f.M is wfe, so it would expand r.f.M to r.f.f.M, again inf. loop.
; If it could also solve this problem, we can uncomment the two lines with 
; (cv v), so it needs to check whether a.L <: r.M (which is not the case)
; so it would apply (<:-TSEL) and check if a.L <: r.f.M, then if a.L <: r.f.f.M,
; and again inf. loop.

; Definition: ad hoc loop avoidance strategy = add to an inf loop prone function
; as first argument a list of all arguments it has previously been called with, 
; immediately return if function is called again with same arguments.
; E.g. used in is_wf-type or is_subtype of dotf.ss.

; Conclusion: Since paths can become arbitrarily long, the ad hoc loop avoidance
; strategy is not sufficient to prevent all infinite loops.

(test-equal (redex-match? dot e e1) #t)

(printf "Typechecking starts...")
(typecheck (term (() ())) e1)

(test-results)
