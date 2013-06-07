#lang racket
(require redex)

; Implementation of subtype^ac algorithm on page 310, Figure 21-5 of
; Types and Programming Languages.

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

(define-metafunction L
  sub : Σ S T -> boolean
 
  [(sub {(S_i T_i) ... (S T) (S_j T_j) ...} S T) #t]

  [(sub Σ T Top) #t]
  
  [(sub Σ Pos Int) #t]
  
  [(sub Σ T T) #t]
  
  [(sub Σ (⨯ S_1 S_2) (⨯ T_1 T_2))
   (and (sub Σ_0 S_1 T_1)
        (sub Σ_0 S_2 T_2))
   (where Σ_0 (extend Σ ((⨯ S_1 S_2) (⨯ T_1 T_2))))]
  
  [(sub Σ (→ S_1 S_2) (→ T_1 T_2))
   (and (sub Σ_0 T_1 S_1)
        (sub Σ_0 S_2 T_2))
   (where Σ_0 (extend Σ ((→ S_1 S_2) (→ T_1 T_2))))]
  
  [(sub Σ (μ X S) T)
   (sub Σ_0 (subst X (μ X S) S) T)
   (where Σ_0 (extend Σ ((μ X S) T)))]
  
  [(sub Σ S (μ X T))  
   (sub Σ_0 S (subst X (μ X T) T))
   (where Σ_0 (extend Σ (S (μ X T))))]
  
  [(sub Σ S T) #f]
)

(define-metafunction L
  subtype : S T -> boolean
  [(subtype S T) (sub () S T)]
)

(define-metafunction L
  and : boolean boolean -> boolean
  [(and #t #t) #t]
  [(and #f #t) #f]
  [(and #t #f) #f]
  [(and #f #f) #f]
)

(define-metafunction L
  extend : Σ (S T) -> Σ
  [(extend ((S_i T_i) ... (S_new T_new) (S_j T_j) ...) (S_new T_new))
           ((S_i T_i) ... (S_new T_new) (S_j T_j) ...)]
  [(extend ((S_i T_i) ...) (S_new T_new))
           ((S_i T_i) ...  (S_new T_new))]
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

(test-equal (term (subtype (μ A (⨯ Pos A)) (μ A (⨯ Int A)))) #t)

(test-equal (term (subtype (μ A (⨯ Top A)) (μ A (⨯ Int A)))) #f)

; PosStream and IntStream
(test-equal (term (subtype (μ A (⨯ Pos A)) 
                           (μ A (⨯ Int A)))) #t)
(test-equal (term (subtype (μ A (⨯ Int A)) 
                           (μ A (⨯ Pos A)))) #f)
(test-equal (term (subtype (μ A (⨯ Int A)) 
                           (μ A (⨯ Int A)))) #t)

; Window and Menu
; Window = (Id ⨯ Menu), Menu = (Id ⨯ Window)

; Window1 and Window2 are two different ways of defining a window,
; same for Menu1 and Menu2
(define Window1 (term (μ W (⨯ Int (⨯ Int W)))))
(define Menu1 (term (⨯ Int ,Window1)))
(define Menu2 (term (μ M (⨯ Int (⨯ Int M)))))
(define Window2 (term (⨯ Int ,Menu2)))

(test-equal (term (subtype ,Window1 ,Window2)) #t)
(test-equal (term (subtype ,Window2 ,Window1)) #t)
(test-equal (term (subtype ,Menu1 ,Menu2)) #t)
(test-equal (term (subtype ,Menu2 ,Menu1)) #t)

; Window and Menu with positive Id
(define PWindow (term (μ W (⨯ Pos (⨯ Pos W)))))
(define PMenu (term (⨯ Pos ,PWindow)))

(test-equal (term (subtype ,PWindow ,Window1)) #t)
(test-equal (term (subtype ,PMenu ,Menu1)) #t)
(test-equal (term (subtype ,Window1 ,PWindow)) #f)
(test-equal (term (subtype ,Menu1 ,PMenu)) #f)

; position of μ "quantifier"

(define T1 (term (μ A (⨯ A (μ B (→ A B))))))
(define T2 (term (μ A (μ B (⨯ A (→ A B))))))

(test-equal (term (subtype ,T1 ,T1)) #t)
(test-equal (term (subtype ,T2 ,T2)) #t)
(test-equal (term (subtype ,T1 ,T2)) #f)
(test-equal (term (subtype ,T2 ,T1)) #f)

(test-results)
