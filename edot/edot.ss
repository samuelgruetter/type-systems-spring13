#lang racket

(require redex)
(require "dotf.ss")
(require "trcl.ss")
(provide (all-defined-out))

; This is an attempt to translate DOT types into existential types

(define-extended-language edot dot  
  ; edot types
  
  ((x% y% z%) id)
  (X% (cx id)) ; type variable
  (l% (cv id))
  (m% (cm id))
  (Lt% (ct id))
  ((S% T% U% V% W%) 
    X%                ; type variable
    E%                ; existential type
    (T% ∧ T%)         ; intersection type
    Bot
    Top)
  (E%
    ; existential type where type var X_i has bounds S_i..U_i
    ; the bounds may refer to the X_i
    ; each type var has a label (with the same id as in the dot type),
    ; which indicates the type's "role" and is used in subtype checking
    ; the list of type variables can be empty
    (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl% ... Dm% ...)))
  (Dl% (: l% T%))
  (Dm% (: m% S% U%))
  
  ; edot expressions
  
  ; edot expressions are the same as dot expressions, but all T are replaced by T%
  (v% v)
  (vx% v% x%)
  (e% vx% (val x% = new c% in e%) (sel e% l%) (sel e% m% e%))
  (c% (T% (l% vx%) ... (m% x% e%) ...))

  ; auxiliaries
  
  (sb ((sel p Lt) X%))        ; substitution path type -> type variable
  (sbs (sb ...))              ; a set of substitutions
  (bd (X% S% U%))             ; lower and upper bound of a type variable
  (bds (bd ...))              ; a set of bounds for type variables
  (id variable-not-otherwise-mentioned)
  (cc-or-ca cc ca)
  (conds-or-#f
     ((S% T%) ...)
     #f)
  (bool boolean)    ; workaround, boolean_1 is not accepted, but bool_1 is
)

; If we only quantify one variable per ∃, then we have the following problem:
; The bounds of an existentially quantified type variable might refer
; to a bound that is only quantified later, e.g.
; (∃ X Bot Y (∃ Y Bot X T))

(define-metafunction edot
  T->T% : sbs T -> T%
  [(T->T% (sb ...) (rfn Top z (: (cc-or-ca id_i) S_i U_i) ... 
                              (: l_j T_j) ... 
                              (: m_k V_k W_k) ...))
   (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl% ... Dm% ...))
   ; generate fresh type variables with names similar to those in given type labels
   (where (id_new ...) ,(variables-not-in (term (sb ...)) (term (id_i ...))))
   (where (X%_i ...) ((cx id_new) ...))   
   (where sbs_new (sb ... ((sel z (cc-or-ca id_i)) X%_i) ...))
   (where (Dl% ...) ((: l_j (T->T% sbs_new T_j)) ...))
   (where (Dm% ...) ((: m_k (T->T% sbs_new V_k) (T->T% sbs_new W_k)) ...))
   (where (S%_i ...) ((T->T% sbs_new S_i) ...))
   (where (U%_i ...) ((T->T% sbs_new U_i) ...))
   (where (Lt%_i ...) ((ct id_i) ...))]
  [(T->T% (sb ...) (rfn T z DLt ... Dl ... Dm ...))
   ,(error "refinements of types other than Top not yet supported")]
  [(T->T% (sb_i ... ((sel p Lt) X%) sb_j ...) (sel p Lt)) X%]
  [(T->T% sbs Top) Top]
  [(T->T% sbs Bot) Bot]  
)

(define-metafunction edot
  e->e% : sbs e -> e%
  [(e->e% sbs vx) vx]
  [(e->e% sbs (val x = new (Top) in e))
   (val x = new ((∃ () ())) in (e->e% sbs))]
  [(e->e% (sb ...) (val x = new (Tc (l_i vx_i) ... (m_j x_j e_j) ...) in e))
   (val x = new (T% (l_i vx_i) ... (m_j x_j (e->e% sbs_new e_j)) ...) in (e->e% sbs_new e))
   (where T% (T->T% (sb ...) Tc))
   (where (∃ ((X%_i (ct id_i) S%_i U%_i) ...) (Dl% ... Dm% ...)) T%)
   ; we don't know if the label was a ca or cc, so just add both to substitutions
   (where sbs_new (sb ... ((sel x (cc id_i)) X%_i) ... ((sel x (ca id_i)) X%_i) ... ))]
  [(e->e% (val x = new c in e))
   ,(error "constructors of types which are not a refinement of Top are not yet supported")]
  [(e->e% sbs (sel e l))
   (sel (e->e% sbs e) l)]
  [(e->e% sbs (sel e_1 m e_2))
   (sel (e->e% sbs e_1) m (e->e% sbs e_2))]
)

; subtyping
(define-metafunction edot
  sub : bds T% T% -> bool
  [(sub bds T%  Top) #t]
  [(sub bds Bot T% ) #t]
  [(sub bds T%  T% ) #t]
  
  [(sub (bd_i ...) E%_b E%_a) bool
   ; if subtype-conditions returns #f instead of a list of conditions, we also return #f
   ; if it returns a list of conditions, it's not matched by pattern bool and this case does not apply
   (where bool (subtype-conditions E%_b E%_a))]
  [(sub (bd_i ...) E%_b E%_a)
   (and (sub bds_new S% T%) ...)
   (where E%_b2 (adapt-typevar-names E%_b E%_a))
   (where ((S% T%) ...) (subtype-conditions E%_b2 E%_a))
   (where (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...)) E%_b2)
   ; type variable names might shadow each other
   (where bds_new (update (bd_i ...) ((X%_i S%_i U%_i) ...)))]
    
  ; old style:
  ; [(sub (bd_i ... (X% S% U%) bd_j ...) X% U%) #t]
  ; [(sub (bd_i ... (X% S% U%) bd_j ...) S% X%) #t]
  ; new style 1:
  ;[(sub bds S% T%) #t
  ; (side-condition (term (in-trcl (S% T%) (bds->relation bds))))]
  ; new style 2:
  ; weaken what we extract from transitive closure with something (T%) not in domain of transitive closure
  [(sub bds S% T%) #t
   ; S <: U and U <: T => S <: T (hardcode subsumption)
   (where ((V%_i W%_i) ... (S% U%) (V%_j W%_j) ...) (sub-trcl (bds->relation bds)))
   (side-condition (term (different S% U%))) ; to prevent inf. loops
   (side-condition (term (sub bds U% T%)))]
  [(sub bds S% T%) #t
   ; S <: U and U <: T => S <: T (hardcode subsumption)
   (where ((V%_i W%_i) ... (U% T%) (V%_j W%_j) ...) (sub-trcl (bds->relation bds)))
   (side-condition (term (different U% T%))) ; to prevent inf. loops
   (side-condition (term (sub bds S% U%)))]
  
  [(sub bds T% S%) #f]
)

(define-metafunction edot
  bds->relation : bds -> ((S% T%) ...)
  [(bds->relation ((X%_i S%_i U%_i) ...))
   ((S%_i X%_i) ... (X%_i U%_i) ...)]
)

; decide whether the predicate (S% <: T%) is in the transitive closure of the relation ((S%_i <: T%_i) ...)
(define-metafunction edot
  in-trcl : (S% T%) ((S% T%) ...) -> bool
  [(in-trcl (S% T%) ((S%_i T%_i) ...))
   ; later, this can be replaced by an algo which does not explicitly calculate the transitive closure
   ; but since redex caches metafunction results, performance shouldn't be too bad
   (element-of (S% T%) (sub-trcl ((S%_i T%_i) ...)))]
)

(define-metafunction edot
  sub-trcl : ((S% T%) ...) -> ((S% T%) ...)
  [(sub-trcl ((S% T%) ...))
   ,(trcl (term ((S% T%) ...)))]
)

; (adapt-typevar-names E%_b E%_a) inspects the labels of the type variables
; and renames the type variables of E%_b such that if a type variable of E%_b
; has the same label as a type variable of E%_a, it also has the same name.
; Returns #f if E%_a has type variables with labels not present in E%_b.
(define-metafunction edot
  adapt-typevar-names : E% E% -> E% or #f
  [(adapt-typevar-names E%_b E%_a) #f
   (where (∃ ((X%_b Lt%_b S%_b U%_b) ... ) (Dl%_bj ... Dm%_bk ...)) E%_b)
   (where (∃ ((X%_a Lt%_a S%_a U%_a) ... ) (Dl%_aj ... Dm%_ak ...)) E%_a)
   (side-condition (not (term (subset (Lt%_a ...) (Lt%_b ...)))))]
  [(adapt-typevar-names E%_b E%_a) E%_b
   (where (∃ ((X%_b Lt%_b S%_b U%_b) ... ) (Dl%_bj ... Dm%_bk ...)) E%_b)
   (where (∃ ((X%_a Lt%_a S%_a U%_a) ... ) (Dl%_aj ... Dm%_ak ...)) E%_a)
   (side-condition (term (subset ((X%_a Lt%_a) ...) ((X%_b Lt%_b) ...))))]
  ; TODO Make it work if a type variable named X%_a is in E%_b !
  [(adapt-typevar-names E%_b E%_a)
   (adapt-typevar-names (substitute X%_b X%_a E%_b) E%a)
   (where (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_b Lt% S%_b U%_b) (X%_j Lt%_j S%_j U%_j) ...) ((: l% T%) ... (: m% V% W%) ...)) E%_b)
   (where (∃ ((X%_1 Lt%_1 S%_1 U%_1) ... (X%_a Lt% S%_a U%_a) (X%_2 Lt%_2 S%_2 U%_2) ...) (Dl%_3 ... Dm%_4 ...)) E%_a)
   (side-condition (term (different X%_b X%_a)))]
)

(define-metafunction edot
  subset : (any ...) (any ...) -> bool
  [(subset () (any ...)) #t]
  [(subset (any any_k ...) (any_i ... any any_j ...))
   (subset (any_k ...) (any_i ... any any_j ...))]
  [(subset (any any_k ...) (any_i ...)) #f]
)

(define-metafunction edot
  element-of : any (any ...) -> bool
  [(element-of any (any_i ... any any_j ...)) #t]
  [(element-of any (any_i ...)) #f]
)

(define-metafunction edot
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t]
)

; (substitute X%_1 X%_2 T%) substitutes X%_1 by X%_2 in type expression T%
(define-metafunction edot
  substitute : X% X% T% -> T%
  ; stop recursion because X%_1 is bound by ∃
  [(substitute X%_1 X%_2 (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_1 Lt% S% U%) (X%_j Lt%_j S%_j U%_j) ...) (Dl%_j ... Dm%_k ...)))
                    (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_1 Lt% S% U%) (X%_j Lt%_j S%_j U%_j) ...) (Dl%_j ... Dm%_k ...))]
  ; X%_1 not bound, but X%_2 bound (avoid variable capture)
  [(substitute X%_1 X%_2 E%) 
   (substitute X%_1 X%_2 (substitute X%_2 X%_3 E%))
   (where (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_2 Lt% S% U%) (X%_j Lt%_j S%_j U%_j) ...) (Dl%_j ... Dm%_k ...)) E%)
   (where (cx id) X%_2)
   (where X%_3 (,(variable-not-in (term E%) (term id))))]
  ; X%_1 and X%_2 both unbound
  [(substitute X%_1 X%_2 (∃ ((X%_i Lt%_i S%_i U%_i) ...) ((: l% T%) ... (: m% V% W%) ...)))
   (∃ (((substitute X%_1 X%_2 X%_i) Lt%_i (substitute X%_1 X%_2 S%_i) (substitute X%_1 X%_2 U%_i)) ...) 
      ((: l% (substitute X%_1 X%_2 T%)) ... (: m% (substitute X%_1 X%_2 V%) (substitute X%_1 X%_2 W%)) ...))]
  ; base cases
  [(substitute X%_1 X%_2 Top) Top]
  [(substitute X%_1 X%_2 Bot) Bot]
  [(substitute X%_1 X%_2 X%_1) X%_2]
  [(substitute X%_1 X%_2 X%_3) X%_3]
)
; Given two existential types E%_b and E%_a, collect all subtyping relations 
; ((S% T%) ...) that must hold in order to have E%_b <: E%_a.
; Or if a label present in E%_a is not in E%_b, return #f.
; Works by recursion on the members of E%_a. Trivial but messy code.
(define-metafunction edot
  subtype-conditions : E% E% -> ((S% T%) ...) or #f
  ; remove method decl from rhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_before ... (: m% S% U%) Dm%_after ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ... (: m% V% W%))))
   (extend (extend (subtype-conditions (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_before ... Dm%_after ...))
                                       (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ... )))
                   (V% S%)) (U% W%))]
  ; method decl from rhs type not found in lhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ... (: m% V% W%))))
   #f]
  ; remove label decl from rhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_before ... (: l% S%) Dl%_after ... Dm%_j ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... (: l% T%))))
   (extend (subtype-conditions (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_before ... Dl%_after ...))
                               (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ...)))
           (S% T%))]
  ; label decl from rhs type not found in lhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... (: l% T%))))
   #f]
  ; remove type variable from rhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_1 Lt% S%_1 U%_1) (X%_j Lt%_j S%_j U%_j) ...) (Dl%_j ... Dm%_k ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ... (X%_2 Lt% S%_2 U%_2)) ()))
   (extend (extend (subtype-conditions (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_j Lt%_j S%_j U%_j) ...) ())
                                        (∃ ((X%_a Lt%_a S%_a U%_a) ...) ()))
                   ; old style
                   ; (S%_2 S%_1)) (U%_1 U%_2))
                   ; new style
                   (S%_2 X%_2)) (X%_2 U%_2))
   ]
  ; type variable from rhs type not found in lhs type
  [(subtype-conditions 
     (∃ ((X%_i Lt%_i S%_i U%_i) ... (X%_j Lt%_j S%_j U%_j) ...) (Dl%_j ... Dm%_k ...))
     (∃ ((X%_a Lt%_a S%_a U%_a) ... (X%_2 Lt% S%_2 U%_2)) ()))
   #f]
  ; base case  
  [(subtype-conditions E% (∃ () ())) ()]
)

; logical and
(define-metafunction edot
  and : bool ... -> bool
  [(and #f bool ...) #f]
  [(and #t) #t]
  [(and #t bool_1 bool ...) (and bool_1 bool ...)]
)

(define-metafunction edot
  extend : conds-or-#f (S% T%) -> conds-or-#f
  [(extend #f (S% T%)) #f]
  [(extend ((S%_i T%_i) ... (S%_new T%_new) (S%_j T%_j) ...) (S%_new T%_new))
           ((S%_i T%_i) ... (S%_new T%_new) (S%_j T%_j) ...)]
  [(extend ((S%_i T%_i) ...) (S%_new T%_new))
           ((S%_i T%_i) ...  (S%_new T%_new))]
)

; (update bds_old bds_new) returns the union of bds_old and bds_new, but
; in case of conflicts, bds_new overrides bds_old
(define-metafunction edot
  update : bds bds -> bds
  [(update (bd_i ... (X% S% U%) bd_j ...) ((X% V% W%) bd_k ...))
   (update (bd_i ... (X% V% W%) bd_j ... bd_k ...))]
  [(update (bd_i ...) ((X% V% W%) bd_k ...))
   (update (bd_i ... (X% V% W%)) (bd_k ...))]
  [(update bds ()) bds]
)

(define-metafunction edot
  intersect : bds T% T% -> T%
  ; if one is an intersection, it might help to evaluate it first
  [(intersect bds T% (S% ∧ U%))
   (intersect bds T% (intersect bds S% U%))]
  [(intersect bds (S% ∧ U%) T%)
   (intersect bds (intersect bds S% U%) T%)]
  ; if one is a type variable, we cannot do anything
  [(intersect bds T% X%) (T% ∧ %X)]
  [(intersect bds X% T%) (X% ∧ %T)]
  ; if one is a subtype of the other, it's the subtype
  [(intersect bds S% T%) %S
   (side-condition (term (sub bds S% T%)))]
  [(intersect bds T% S%) %S
   (side-condition (term (sub bds S% T%)))]
  ; if both are existential types: take declarations from rhs and put them into lhs until lhs <: rhs
  [(intersect bds (∃ (               (X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...))
                  (∃ ((X% Lt% S% U%) (X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ...)))
   (intersect bds (∃ ((X% Lt% S% U%) (X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...))
                  (∃ ((X% Lt% S% U%) (X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ...)))
   (side-condition (not (term (in Lt% (Lt%_i ...)))))]
  [(intersect bds (∃ ((X%_1 Lt% S%_1 U%_1) (X%_i Lt%_i S%_i U%_i) ...) (Dl%_j ... Dm%_k ...))
                  (∃ ((X%_2 Lt% S%_2 U%_2) (X%_a Lt%_a S%_a U%_a) ...) (Dl%_b ... Dm%_c ...)))
   TODO
   ; synchronize type var names, when taking union/intersection of bounds, take into account other bounds -> bds_new, ...
   (side-condition (or (term (different S%_1 S%_2)) (term (different U%_1 U%_2))))]
   ; TODO more cases
)

; We don't (yet) have union types, but if one is a subtype of the other, it is
; possible to calculate the union of two types.
(define-metafunction edot
  eval-union : bds T% T% -> T%
  [(eval-union T%_1 T%_2) T%_1
   (side-condition (term (sub T%_2 T%_1)))]
  [(eval-union T%_2 T%_1) T%_1
   (side-condition (term (sub T%_2 T%_1)))]
)
