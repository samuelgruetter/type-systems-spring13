#lang racket

(require redex)
(require "edot.ss")
(require "dotf.ss")

;;;;;;;; tests ;;;;;;;;;;;;;;

; transitive closure
(term (sub-trcl {((cx A) (cx B)) ((cx B) (cx C)) ((cx B) Bot)}))

; simple translation test
(define typeX (term (rfn Top z
                         (: (ca A) Top Top)
                         (: (ca B) Top Top)
                         (: (ca C) Bot (sel z (ca B))))))
(term (T->T% () ,typeX))

; does this type make any sense?
(define typeW (term {rfn Top z
                         (: (ca L) Bot {rfn Top y 
                            (: (ca L) (sel z (ca L)) (sel y (ca L)))
                         })}))
(term (T->T% () ,typeW))

;;;;;;;;;; subtyping tests ;;;;;;;;;

(define typePair (term {rfn Top z (: (cv fst) Top) (: (cv snd) Top)}))
(define typePair% (term (T->T% () ,typePair)))
(printf "typePair:\n")
typePair
typePair%

; recursive lists
(define typeTopListCont (term {rfn Top z
                                             (: (ca L) Bot { rfn Top y
                                                (: (ca T) Bot Top)
                                                (: (cv head) (sel y (ca T)))
                                                (: (cv tail) (sel z (ca L)))
                                             })
                                             (: (cv myList) (sel z (ca L)))
}))
(define typePairListCont (term {rfn Top z
                                             (: (ca L) Bot { rfn Top y
                                                (: (ca T) Bot ,typePair)
                                                (: (cv head) (sel y (ca T)))
                                                (: (cv tail) (sel z (ca L)))
                                             })
                                             (: (cv myList) (sel z (ca L)))
}))
(define typeTopListCont% (term (T->T% () ,typeTopListCont)))
(printf "typeTopListCont:\n")
typeTopListCont
typeTopListCont%
(define typePairListCont% (term (T->T% () ,typePairListCont)))
(printf "typePairListCont:\n")
typePairListCont
typePairListCont%

(test-equal (term (sub () ,typePairListCont% ,typeTopListCont% )) #t)
(test-equal (term (sub () ,typeTopListCont%  ,typePairListCont%)) #f)
(test-equal (term (sub () ,typePairListCont% ,typePairListCont%)) #t)
(test-equal (term (sub () ,typeTopListCont%  ,typeTopListCont% )) #t)

; transitivity problems ?
(define typeA1 (term (rfn Top z
                         (: (cv l) ,typePair))))
(define typeA2 (term (rfn Top z
                         (: (ca La) Bot ,typePair)
                         (: (cv l) (sel z (ca La))))))
(define typeA3 (term (rfn Top z
                         (: (ca La) Bot ,typePair)
                         (: (ca Lb) Bot (sel z (ca La)))
                         (: (cv l) (sel z (ca Lb))))))
(define typeA1% (term (T->T% () ,typeA1)))
(define typeA2% (term (T->T% () ,typeA2)))
(define typeA3% (term (T->T% () ,typeA3)))

; sub is from edot, subtype is from dot
(test-equal (term           (sub     ()      ,typeA1% ,typeA1%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeA1  ,typeA1 )) #t)
(test-equal (term           (sub     ()      ,typeA1% ,typeA2%)) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeA1  ,typeA2 )) #f)
(test-equal (term           (sub     ()      ,typeA1% ,typeA3%)) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeA1  ,typeA3 )) #f)

(test-equal (term           (sub     ()      ,typeA2% ,typeA1%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeA2  ,typeA1 )) #t)
(test-equal (term           (sub     ()      ,typeA2% ,typeA2%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeA2  ,typeA2 )) #t)
(test-equal (term           (sub     ()      ,typeA2% ,typeA3%)) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeA2  ,typeA3 )) #f)

(test-equal (term           (sub     ()      ,typeA3% ,typeA1%)) #t) ; SUCCESS thanks to transitive closure calculation
(test-equal (judgment-holds (subtype (() ()) ,typeA3  ,typeA1 )) #t)
(test-equal (term           (sub     ()      ,typeA3% ,typeA2%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeA3  ,typeA2 )) #t)
(test-equal (term           (sub     ()      ,typeA3% ,typeA3%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeA3  ,typeA3 )) #t)

; "If B lower bound of A, then A upper bound of B"
; Q: Can the type system perform this reasoning?
; A: Yes, dot does so by (<:-TSEL) and edot does so by [(sub (bd_i ... (X% S% U%) bd_j ...) S% X%) #t]
(define typeX1 (term (rfn Top z 
                          (: (ca A) (sel z (ca B)) Top)
                          (: (ca B) Bot Top)
                          (: (cv l) (sel z (ca B))))))
(define typeY1 (term (rfn Top z 
                          (: (ca B) Bot Top)
                          (: (ca A) (sel z (ca B)) Top)
                          (: (cv l) (sel z (ca A))))))
(define typeX1% (term (T->T% () ,typeX1)))
(define typeY1% (term (T->T% () ,typeY1)))
(printf "typeX1:\n")
typeX1
typeX1%
(printf "typeY1:\n")
typeY1
typeY1%
(test-equal (term           (sub     ()      ,typeX1% ,typeY1%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeX1  ,typeY1 )) #t)
(test-equal (term           (sub     ()      ,typeY1% ,typeX1%)) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeY1  ,typeX1 )) #f)
(test-equal (term           (sub     ()      ,typeX1% ,typeX1%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeX1  ,typeX1 )) #t)
(test-equal (term           (sub     ()      ,typeY1% ,typeY1%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeY1  ,typeY1 )) #t)

; 4.1 from DOT paper
(define typeX41 (term (rfn Top z
                        (: (ca La) Top Top)
                        (: (cv l) (sel z (ca La))))))
(define typeY41 (term (rfn Top z
                        (: (cv l) Top))))
(define typeX41% (term (T->T% () ,typeX41)))
(printf "typeX41:\n")
typeX41
typeX41%
(define typeY41% (term (T->T% () ,typeY41)))
(printf "typeY41:\n")
typeY41
typeY41%
(test-equal (term (sub () ,typeX41% ,typeY41%)) #t)
(test-equal (term (sub () ,typeY41% ,typeX41%)) #f)
; probably it's possible to define a rule similar to (TERM-∋) which also works if
; the label l has a type defined by a type label which is member of the term,
; but actually we needed a reduction relation and objects to check it...


; sample usage of preservation:
; (preservation (term (val x = new ({rfn Top z (: (cv l) Top)} ((cv l) x)) in (sel x (cv l)))))


; 4.2a) from DOT paper:

; type with no expansion in DOT
(define typeNE (term {rfn Top z
                          (: (ca L) Bot (sel z (ca L)))
                          (: (cv myVar) (sel z (ca L)))
                     }))
(define typeNE% (term (T->T% () ,typeNE)))
(printf "typeNE:\n")
typeNE
typeNE%

; type which is the same as typeNE (?) but has an expansion in DOT
(define typeE (term {rfn Top z
                          (: (ca L) Bot Top)
                          (: (cv myVar) (sel z (ca L)))
                     }))
(define typeE% (term (T->T% () ,typeE)))
(printf "typeE:\n")
typeE
typeE%

; a third type to double-check
(define type3 (term {rfn Top z
                          (: (ca L) Bot ,typePair)
                          (: (cv myVar) (sel z (ca L)))
                     }))
(define type3% (term (T->T% () ,type3)))
(printf "type3:\n")
type3
type3%

(test-equal (term           (sub     ()      ,typeE%  ,typeE% )) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeE   ,typeE  )) #t)
(test-equal (term           (sub     ()      ,typeNE% ,typeE% )) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeNE  ,typeE  )) #t)
(test-equal (term           (sub     ()      ,type3%  ,typeE% )) #t)
(test-equal (judgment-holds (subtype (() ()) ,type3   ,typeE  )) #t)

(test-equal (term           (sub     ()      ,typeE%  ,typeNE%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeE   ,typeNE )) #t)
(test-equal (term           (sub     ()      ,typeNE% ,typeNE%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,typeNE  ,typeNE )) #t)
(test-equal (term           (sub     ()      ,type3%  ,typeNE%)) #t)
(test-equal (judgment-holds (subtype (() ()) ,type3   ,typeNE )) #t)

(test-equal (term           (sub     ()      ,typeE%  ,type3% )) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeE   ,type3  )) #f)
(test-equal (term           (sub     ()      ,typeNE% ,type3% )) #f)
(test-equal (judgment-holds (subtype (() ()) ,typeNE  ,type3  )) #f)
(test-equal (term           (sub     ()      ,type3%  ,type3% )) #t)
(test-equal (judgment-holds (subtype (() ()) ,type3   ,type3  )) #t)

; * I would like these to be true, because I believe that for all expressions e,
; we have e:typeE <=> e:typeNE.

;;;;;;; expression translation ;;;;;;;;;;;

(define-metafunction dot
  valnew : (x c) e -> e
  [(valnew (x c) e) (val x = new c in e)])

(define e1 
  (let ((typeX (term (rfn Top z
                        (: (ca A) Top Top)
                        (: (cm l) Top (sel z (ca A))))))
       (typeY (term (rfn Top z
                        (: (cm l) Top Top)))))
   (term
    (valnew
     (u (,typeX ((cm l) dummy (as (sel u (ca A)) u))))
     (sel (app (fun y (arrow Top ,typeY) ,typeY (app y (as Top u))) 
               (as (arrow Top ,typeY) (fun d Top ,typeX (cast ,typeX u)))) (cm l) (as Top u))))))
(define e1% (term (e->e% () ,e1)))
(printf "e1\n")
e1
e1%

(test-results)
