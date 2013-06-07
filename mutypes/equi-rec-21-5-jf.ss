#lang racket
(require redex)

; Implementation of subtype^ac algorithm on page 310, Figure 21-5 of
; Types and Programming Languages.
; Note that subtype^ac is expressed as a set of inference rules rather
; than as a recursive algorithm.

(define-language L
  ((S T)            ; type expressions
    X               ;   type variable
    Top             ;   Top
    (→ S T)         ;   function type
    (⨯ S T)         ;   product type
    (μ X T)         ;   recursive type
    Pos             ;   positive number
    Int)            ;   integer number
  (X                ; type variable
    variable-not-otherwise-mentioned)
  (Σ                ; set of subtyping assumptions
    {(S T) ...})    ;   S subtype of T
)

; Note that there are no terms, but only types

(define-judgment-form L
  #:mode (sub I I I)
  #:contract (sub Σ S T)
 
  [---------------------------------------------- ; extract assumption from Σ
   (sub {(S_i T_i) ... (S T) (S_j T_j) ...} S T)]

  [-------------- ; Top
   (sub Σ T Top)]
  
  [---------------- ; Pos <: Int
   (sub Σ Pos Int)]
  
  [------------ ; T <: T
   (sub Σ T T)]
  
  [(where Σ_0 (extend Σ ((⨯ S_1 S_2) (⨯ T_1 T_2))))
   (sub Σ_0 S_1 T_1)
   (sub Σ_0 S_2 T_2)
   ------------------------------------------------------ ; product subtyping
   (sub Σ (⨯ S_1 S_2) (⨯ T_1 T_2))]
  
  [(where Σ_0 (extend Σ ((→ S_1 S_2) (→ T_1 T_2))))
   (sub Σ_0 T_1 S_1)
   (sub Σ_0 S_2 T_2)
   ------------------------------------------------------ ; arrow subtyping
   (sub Σ (→ S_1 S_2) (→ T_1 T_2))]
  
  [(where Σ_0 (extend Σ ((μ X S) T)))
   (sub Σ_0 (subst X (μ X S) S) T)
   ------------------------------------------------------ ; μ left
   (sub Σ (μ X S) T)]
  
  [(where Σ_0 (extend Σ (S (μ X T))))
   (sub Σ_0 S (subst X (μ X T) T))
   ------------------------------------------------------ ; μ right
   (sub Σ S (μ X T))]
)

(define-judgment-form L
  #:mode (subtype I I)
  #:contract (subtype S T)
  [(sub () S T)
   ------------
   (subtype S T)]
)

(define-metafunction L
  extend : Σ (S T) -> Σ
  [(extend ((S_i T_i) ... (S_new T_new) (S_j T_j) ...) (S_new T_new))
           ((S_i T_i) ... (S_new T_new) (S_j T_j) ...)]
  [(extend ((S_i T_i) ...) (S_new T_new))
           ((S_i T_i) ...  (S_new T_new))]
)

(define-metafunction L
  [(different (S T) (S T)) #f]
  [(different (S_1 T_1) (S_2 T_2)) #t]
)

; (subst X S T) replaces all free occurrences of X in T by S
(define-metafunction L
  subst : X T T -> T
  [(subst X S X) S]
  [(subst X_1 S X_2) X_2]
  [(subst X S Top) Top]
  [(subst X S (→ T_1 T_2))
   (→ (subst X S T_1) (subst X S T_2))]
  [(subst X S (⨯ T_1 T_2))
   (⨯ (subst X S T_1) (subst X S T_2))]
  [(subst X S (μ X T)) ; stop recursion because X is not free inside T
   (μ X T)]
  [(subst X_1 S (μ X_2 T)) ; avoid variable capturing
   (μ X_2 (subst X_1 (subst X_2 X_2fresh S) T))
   (where X_2fresh ,(variable-not-in (term (S T)) (term myfreshvar)))]  
  [(subst X S Pos) Pos]
  [(subst X S Int) Int]
)

(test-equal (term (subtype Pos Int)) #t)
(test-equal (term (subtype Pos Pos)) #t)
(test-equal (term (subtype Int Pos)) #f)

(test-equal (term (subtype (→ Int Pos) (→ Pos Int))) #t)
(test-equal (term (subtype (→ Pos Pos) (→ Int Pos))) #f)
(test-equal (term (subtype (→ Int Int) (→ Int Pos))) #f)

(test-equal (term (subtype (⨯ (⨯ Int Int) (⨯ Pos Int))
                           (⨯ (⨯ Top Int) (⨯ Pos Top)))) #t)

(test-equal (term (subtype (⨯ (⨯ Int Top) (⨯ Pos Int))
                           (⨯ (⨯ Int Int) (⨯ Pos Int)))) #f)

(test-equal (term (different ((μ A (⨯ Pos A)) (μ A (⨯ Int A))) 
                             ((μ A (⨯ Pos A)) (μ A (⨯ Int A))))) #f)
(test-equal (term (different ((μ A (⨯ Pos A)) (μ A (⨯ Int A))) 
                             ((μ A (⨯ Pos A)) (μ A (⨯ Top A))))) #t)

(test-equal (term (subst A B (⨯ A A)))
            (term (⨯ B B)))

(test-equal (term (subst A B (⨯ A (μ A (→ A A)))))
            (term            (⨯ B (μ A (→ A A)))))

(test-equal (term (subst A (⨯ F F) (μ F (⨯ F (→ A A)))))
  (term (μ F (⨯ F (→ (⨯ myfreshvar myfreshvar) (⨯ myfreshvar myfreshvar))))))

(test-equal (term (subst A (⨯ F G) (μ F (μ G (→ A A)))))
  (term (μ F (μ G (→ (⨯ myfreshvar myfreshvar1) (⨯ myfreshvar myfreshvar1))))))

(test-equal (term (subst A (μ F (→ F F)) (μ F (μ G (→ A A)))))
  (term (μ F (μ G (→ (μ F (→ F F)) (μ F (→ F F)))))))

(test-equal (term (subst A (⨯ F (μ F (→ F F))) (μ F (μ G (→ A A))))) (term 
  (μ F (μ G (→ (⨯ myfreshvar (μ F (→ F F))) (⨯ myfreshvar (μ F (→ F F))))))))

(test-equal (term (subst A (μ A (→ Pos A)) (→ Pos A)))
  (term (→ Pos (μ A (→ Pos A)))))

; TODO first test the substitution function...

; PosStream and IntStream

#|
(test-equal (term (subtype (μ A (⨯ Pos A)) 
                           (μ A (⨯ Int A)))) #t)
|#

#|
(test-equal (term (subtype (μ A (⨯ Int A)) 
                           (μ A (⨯ Pos A)))) #f)
(test-equal (term (subtype (μ A (⨯ Int A)) 
                           (μ A (⨯ Int A)))) #t)
|#


(test-results)
