#lang racket
(require redex)
(require "ddot.ss")

(define typeX (term (rfn Top z
                         (: (ct A) Top Top)
                         (: (ct B) Top Top)
                         (: (ct C) Bot (sel z (ct B))))))

(term (xT->rel (a ,typeX)))

; 4.1 from DOT paper
(define typeX41 (term (rfn Top z
                        (: (ct La) Top Top)
                        (: (cv l) (sel z (ct La))))))
                        ;(: (cv l) Top))))
(define typeY41 (term (rfn Top z
                        (: (cv l) Top))))

(term (xT->rel (b ,typeX41)))
(term (xT->rel (c ,typeY41)))

; some nested type:
(define typeN1 (term 
  (rfn Top x (: (ct L) Bot ,typeX)
             (: (ct M) Bot (rfn ,typeX y 
                   (: (ct N) Bot (sel x (ct L)))
                   (: (cv vn) (sel y (ct N)))))
             (: (cv vm) (sel x (ct M))))))
; note that here, there will be no tuple like
; (Bot dd.vm.N), because we do not expand dd.M (inf loop risk)
(term (xT->rel (dd ,typeN1)))

; the same nested type, but M is inlined:
(define typeN11 (term 
  (rfn Top x (: (ct L) Bot ,typeX)
             (: (cv vm) (rfn ,typeX y 
                   (: (ct N) Bot (sel x (ct L)))
                   (: (cv vn) (sel y (ct N))))))))
; now (Bot ee.vm.N) will be present
(term (xT->rel (ee ,typeN11)))

