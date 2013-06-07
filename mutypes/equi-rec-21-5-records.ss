#lang racket
(require redex)

; subtype^ac algorithm on page 310, Figure 21-5 of TAPL,
; but with records instead of product types

(define-language L
  ((S T)            ; type expressions
    X               ;   type variable
    Top             ;   Top
    (→ S T)         ;   function type
    (Dl ...)        ;   record type
    (μ X T)         ;   recursive type
    Pos             ;   positive number
    Int)            ;   integer number
  (X                ; type variable
    variable-not-otherwise-mentioned)
  (Σ                ; set of subtyping assumptions
    {(S T) ...})    ;   S subtype of T
  (l                ; label in record
    variable-not-otherwise-mentioned)
  (Dl               ; declaration in record
    (val l T))
  (bool boolean)    ; workaround, boolean_1 is not accepted, but bool_1 is
)

; Note that there are no terms, but only types

(define-metafunction L
  sub : Σ S T -> bool
 
  [(sub {(S_i T_i) ... (S T) (S_j T_j) ...} S T) #t]

  [(sub Σ T Top) #t]
  
  [(sub Σ Pos Int) #t]
  
  [(sub Σ T T) #t]
  
  [(sub Σ (Dl_i ...) (Dl_j ...))
   (and (sub Σ_0 S T) ...)
   (where Σ_0 (extend Σ ((Dl_i ...) (Dl_j ...))))
   (where ((S T) ...) (subtype-conditions (Dl_i ...) (Dl_j ...)))]
  
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
  subtype : S T -> bool
  [(subtype S T) (sub () S T)]
)

; Given two record types (Dl_i ...) and (Dl_j ...), collect all subtyping
; relations ((S T) ...) that must hold in order to have (Dl_i ...) <: (Dl_j ...)
; Or if a label present in (Dl_j ...) is not in (Dl_i ...), return #f
(define-metafunction L
  subtype-conditions : (Dl ...) (Dl ...) -> ((S T) ...) or #f
  [(subtype-conditions (Dl ...) ()) ()]
  [(subtype-conditions (Dl_i ... (val l S) Dl_j ...) ((val l T) Dl_k ...))
   (extend (subtype-conditions (Dl_i ... Dl_j ...) (Dl_k ...)) (S T))]
  [(subtype-conditions (Dl_i ...) (Dl_j ...)) #f]
)

(define-metafunction L
  and : bool ... -> bool
  [(and #f bool ...) #f]
  [(and #t) #t]
  [(and #t bool_1 bool ...) (and bool_1 bool ...)]
)

(define-metafunction L
  extend : ((S T) ...) (S T) -> ((S T) ...)
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
  [(subst X S ((val l_i T_i) ...))
   ((val l_i (subst X S T_i)) ...)]
  [(subst X S (μ X T)) ; stop recursion because X is not free inside T
   (μ X T)]
  [(subst X_1 S (μ X_2 T)) ; avoid variable capturing
   (μ X_2 (subst X_1 (subst X_2 X_2fresh S) T))
   (where X_2fresh ,(variable-not-in (term (S T)) (term myfreshvar)))]  
  [(subst X S Pos) Pos]
  [(subst X S Int) Int]
)

#| TAPL p. 300
treeof (Top)(•)         = Top
treeof (T1 → T2 )(•)    = →
treeof (T1 → T2 )(i,π)  = treeof(T_i)(π)
treeof (T1 × T2 )(•)    = ×
treeof (T1 × T2 )(i,π)  = treeof (T_i)(π)
treeof (μX.T)(π)        = treeof([X ↦ μX.T]T)(π)
|#

; (tree T natural string boolean) returns a string representation of type T
; T can be infinite
; natural is the max depth, rest is printed as ...
; string is the prefix to be printed before each line except first
; string_1 is the prefix to be printed before the first line
(define-metafunction L
  tree : T natural string string -> string
  [(tree X natural string string_1) 
   ,(format "~aError: Unbound variable ~a" (term string) (term X))]
  [(tree Top natural string string_1) 
   ,(format "~aTop" (term  string_1))]
  [(tree Int natural string string_1) 
   ,(format "~aInt" (term  string_1))]
  [(tree Pos natural string string_1) 
   ,(format "~aPos" (term  string_1))]
  [(tree (→ S T) 0 string string_1) 
   ,(format "~a(→ ... ...)" (term  string_1))]
  [(tree (→ S T) natural string string_1) 
   ,(format "~a(→ ~a\n~a)"
     (term  string_1)
     (term (tree S natural_new string_new ""))
     (term (tree T natural_new string_new string_new)))
   (where string_new  ,(string-append (term string  ) "   "))
   (where natural_new ,(- (term natural) 1))]
  [(tree (Dl_i ...) 0 string string_1)
   ,(format "~a(...)" (term  string_1))]
  [(tree (Dl_i ...) natural string string_1)
   ,(format "~a(\n~a~a)"
      (term string_1) 
      (apply string-append 
             (term ((Dl-tree Dl_i 
                             ,(- (term natural) 1) 
                             ,(string-append (term string) "   ")
                             ,(string-append (term string) "   ")) ...)))
      (term string))]
  [(tree (μ X T) 0 string string_1)
   ,(format "~a(μ ~a ...)" (term string_1) (term X))]
  ; no decrement/increment here, because (subst X (μ X T) T) is just 
  ; another (printable) way of saying (μ X T)
  [(tree (μ X T) natural string string_1)
   (tree (subst X (μ X T) T) natural string string_1)]
)

(define-metafunction L
  Dl-tree : Dl natural string string -> string
  [(Dl-tree (val l T) natural string string_1)
   ,(format "~a(val ~a ~a)\n" 
            (term string_1)
            (term l)
            (term (tree T natural string "")))]
)
  
(define (print-tree T n) (printf "~a\n\n" (term (tree ,T ,n "" ""))))

(test-equal (term (subtype Pos Int)) #t)
(test-equal (term (subtype Pos Pos)) #t)
(test-equal (term (subtype Int Pos)) #f)

(test-equal (term (subtype (→ Int Pos) (→ Pos Int))) #t)
(test-equal (term (subtype (→ Pos Pos) (→ Int Pos))) #f)
(test-equal (term (subtype (→ Int Int) (→ Int Pos))) #f)

; order of labels does not matter
(test-equal (term (subtype [(val a Int) (val b Int)]
                           [(val b Int) (val a Int)])) #t)
(test-equal (term (subtype [(val a Int) (val b Int)]
                           [(val b Int) (val a Top)])) #t)
(test-equal (term (subtype [(val a Int) (val b Top)]
                           [(val b Int) (val a Int)])) #f)

; missing label
(test-equal (term (subtype [(val a Int) (val c Int)]
                           [(val b Int) (val a Int)])) #f)


(test-equal (term (subtype
  ((val o1 ((val a Int) (val b Int))) (val o2 ((val c Pos) (val d Int))))
  ((val o1 ((val a Top) (val b Int))) (val o2 ((val c Int) (val d Int)))))) #t)

(test-equal (term (subtype
  ((val o1 ((val a Int) (val b Int))) (val o2 ((val c Pos) (val d Int))))
  ((val o1 ((val a Int) (val b Int))) (val o2 ((val c Pos) (val d Pos)))))) #f)

; PosStream and IntStream
(test-equal (term (subtype (μ A ((val head Pos) (val tail A))) 
                           (μ A ((val head Int) (val tail A))))) #t)
(test-equal (term (subtype (μ A ((val head Int) (val tail A))) 
                           (μ A ((val head Pos) (val tail A))))) #f)
(test-equal (term (subtype (μ A ((val head Pos) (val tail A))) 
                           (μ A ((val head Pos) (val tail A))))) #t)

; test unbound type vars
(test-equal (term (subtype (μ A ((val head Pos) (val tail A))) 
                           (μ A ((val head Pos) (val tail Foo))))) #f)
(test-equal (term (subtype (μ A ((val head Pos) (val tail Foo))) 
                           (μ A ((val head Pos) (val tail A))))) #f)
(test-equal (term (subtype (μ A ((val head Pos) (val tail Foo))) 
                           (μ A ((val head Pos) (val tail Foo))))) #t)

; Window and Menu
; Window = (Id and Menu), Menu = (Id and Window)

; Window1 and Window2 are two different ways of defining a window,
; same for Menu1 and Menu2
(define Window1 (term (μ W [(val id Int) 
                            (val menu [(val id Int) (val window W)])])))
(define Menu1 (term [(val id Int) (val window ,Window1)]))
(define Menu2 (term (μ M [(val id Int) 
                          (val window [(val id Int) (val menu M)])])))
(define Window2 (term [(val id Int) (val menu ,Menu2)]))

(test-equal (term (subtype ,Window1 ,Window2)) #t)
(test-equal (term (subtype ,Window2 ,Window1)) #t)
(test-equal (term (subtype ,Menu1 ,Menu2)) #t)
(test-equal (term (subtype ,Menu2 ,Menu1)) #t)

; Window and Menu with positive Id
(define PWindow (term (μ W [(val id Pos) 
                            (val menu [(val id Pos) (val window W)])])))
(define PMenu (term [(val id Pos) (val window ,PWindow)]))

(test-equal (term (subtype ,PWindow ,Window1)) #t)
(test-equal (term (subtype ,PMenu ,Menu1)) #t)
(test-equal (term (subtype ,Window1 ,PWindow)) #f)
(test-equal (term (subtype ,Menu1 ,PMenu)) #f)

; an interesting property
(define T1 (term (μ A (μ B [(val a A) (val b B)]))))
(define T2 (term (μ A [(val a A) (val b A)])))
(test-equal (term (subtype ,T1 ,T2)) #t)
(test-equal (term (subtype ,T2 ,T1)) #t)

(test-results)

(print-tree (term (→ Int (→ (→ Pos Int) Top))) 4)
(print-tree (term (→ Int (→ (→ Pos Int) Top))) 3)
(print-tree (term (→ Int (→ (→ Pos Int) Top))) 2)
(print-tree (term (→ Int (→ (→ Pos Int) Top))) 1)
(print-tree (term (→ Int (→ (→ Pos Int) Top))) 0)

(print-tree (term (μ A ((val head Pos) (val tail A)))) 4)
(print-tree Window1 3)
(print-tree T1 3)
(print-tree T2 3)

(define T3 (term (μ A (μ B [
  (val f1 [
     (val x A)
     (val y B)
  ])
  (val f2 [
     (val a A)
     (val b B)
  ])
]))))
(print-tree T3 4)

(define T4 (term (μ A (μ B [
  (val x [
    (val a A)
    (val b B)
  ])
  (val y [
    (val x A)
    (val y B)
  ])
]))))
(print-tree T4 4)

#| DOT
T5 = Top{ z =>
  A: Top{ u => 
    aVal: Top
    a: z.A
    b: z.B
  }
  B: Top{ z =>
    bVal: Top
    a: z.A
    b: z.B
  }
  myA: z.A
}
"L: T" being a shorthand for "L: T..T"
|#

#| Scala
  //Does not compile in 2.9.1 
  object test1 {
    type A = {
      val aVal: Any
      val a: A
      val b: B
    }
    type B = {
      val bVal: Any
      val a: A
      val b: B
    }
    val myA: A = null
  }
|#

#| simple-vN   (where n > 1)
(
  (type A [
    (val aVal Top)
    (val a A)
    (val b B)
  ])
  (type B [
    (val bVal Top)
    (val a A)
    (val b B)
  ])
  (val myA A 0)
)
|#

#| μ notation |#
(define T5 (term (μ A [
  (val aVal Top)
  (val a A)
  (val b (μ B [
    (val bVal Top)
    (val a A)
    (val b B)
  ]))
])))
(print-tree T5 4)
