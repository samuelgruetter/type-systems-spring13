;;;;; DDOT - a different approach to DOT ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; work in progress ... ;-)

#lang racket

(require redex)

(provide (all-defined-out))

; Subtyping does not need expansion
; -> throw away expansion and see how far we get

; In constructors new T{inits}, T must be a refinement of Top. 
; This is not really a restriction, because in inits, we need to initialize 
; all members anyway, so we need to know them, and so we would also be able to 
; write type annotations for each member, now just collect these type
; annotations and put them in a refinement of Top. 
; -> also throw away distinction between abstract and concrete types, because
;    this is only needed to know if type is allowed in constructor

; Why is there a store in arguments to is_subtype of dot, but no store in the 
; rules in the paper?
; -> Try to do subtyping without store.


(define-language ddot
  ((x y z u)                             ; variable
    id)
  (l                                     ; value label
    (cv id))
  (m                                     ; method label
    (cm id))
  (e                                     ; expression
    x
    (val x = new c in e)
    (sel e l) 
    (sel e m e))
  (p                                     ; path
    x
    (sel p l))
  (c                                     ; constructor
    (Toprfn (l x) ... (m x e) ...))
  (d                                     ; initialization
    (l x)
    (m x e))
  (Γ                                     ; environment
    {(x T) ...})
  (store                                 ; store is as in paper
    {(x c) ...})                         ;   (different from dotf.ss)
  (Lt                                    ; type label 
    (ct id))
  ((S T U V W)                           ; type
    (T / (y S))                          ;   paths beginning with y are needed
    (sel p Lt)                           ;     to express type T
    (rfn T z DLt ... Dl ... Dm ...)
    (T ∧ T) 
    (T ∨ T)
    Top 
    Bot)
  (D DLt Dl Dm)                          ; declarations
  (DLt (: Lt S U))
  (Dlm Dl Dm)
  (Dl (: l T))
  (Dm (: m S U))
  
  ; auxiliaries
  (Ltm Lt m)
  (Lany Lt l m)
  (bool #t #f)
  (Toprfn (rfn Top z DLt ... Dl ... Dm ...))
  (D#f D #f)
  (id variable-not-otherwise-mentioned)
  (n natural)
  (Tpath (sel p Lt))
)

; expand T, discarding all pathT, to set of all members that can be obtained without
; using path types of length greater than n
(define-judgment-form ddot
  #:mode (expansion I I I I O)
  #:contract (expansion (pathT ...) n Γ T (DLt ... Dl ... Dm ...))
  
  [ ; needn't reinvent the wheel, better modify dotf.ss
   ---
   (expansion (pathT ...) n Γ T ())]; (DLt ... Dl ... Dm ...))]
)

; type assignment (Γ ⊢ t : T) (type Γ e T)
(define-judgment-form ddot
  #:mode (type I I O)
  #:contract (type Γ e T)
  
  ; note that it's safe to have this rule because always using Γ-update
  ; guarantees that Γ contains at most 1 binding for each variable
  ; (otherwise we would have to make sure that we always take the most
  ; recent binding)
  [----------------------------------------------- ; (VAR)
   (type {(x_i T_i) ... (x T) (x_j T_j) ...} x T)]
  
  [(membership-e Γ e l (: l T))
   -------------------------- ; (SEL)
   (type Γ (sel e l) T)]
  
  [(membership-e Γ e_1 m (: m T U))
   (type Γ e_2 S)
   (subtype Γ S T)
   ------------------------------- ; (MSEL)
   (type Γ (sel e_1 m e_2) U)]
  
   ; TODO is this a valid replacement for y not in fn(T')?
  [(Γ-doesnt-contain Γ y)
   (where (rfn Top y (: Lt S U) ... (: l T) ... (: m V W) ...) T_y)
   (where Γ_new (Γ-update Γ (y T_y)))
   (decl Γ_new (l x) (: l T)) ...
   (decl Γ_new (m x_m e_m) (: m V W)) ...
   (subtype Γ_new S U) ...
   (type Γ_new e T_e)
   ---------------------------------------------------------------- ; (NEW)
   (type Γ (val y = new (T_y (l x) ... (m x_m e_m) ...) in e) T_e)]
  
  ; since the type in the constructor has to be a refinement of Top anyway, we
  ; can also add the restriction that its self reference must be the same as
  ; the val we're defining
)

; declaration assignment (Γ ⊢ d : D) (decl Γ d D)
(define-judgment-form ddot
  #:mode (decl I I I)
  #:contract (decl Γ d D)
  
  [(type Γ x S)
   (subtype Γ S T)
   ----------------------- ; (VDECL)
   (decl Γ (l x) (: l T))]
  
  [(where Γ_new (Γ-update Γ (x S)))
   (type Γ_new e T)
   (subtype Γ_new T U)
   ------------------------------- ; (MDECL)
   (decl Γ (m x e) (: m S U))]
)

; membership-e (Γ ⊢ t ∋ D) (membership-e Γ e Lany D)
; Answers "in Γ, what declaration does e contain for label Lany?".
; TODO this is far from making sense or being complete...
(define-judgment-form ddot
  #:mode (membership-e I I I O)
  ; D contains Lany, but Lany is needed as I argument
  #:contract (membership-e Γ e Lany D#f)
  
  ; for non-paths, delegate to membership-T        (TERM-∋)
  ; but take care of self reference
  
  [(isnt-path e)
   (type Γ e T)
   (where z_fresh ,(variable-not-in (term (Γ e T)) 'z0))
   (membership-T Γ T z_fresh Lany (: Lany U ...))
   --------------------------
   (membership-e Γ e Lany (: Lany (add/ U (z_fresh T)) ...))]
  ; If we have e.g. (membership-e Γ e m (: m (S / (z01 T1)) (U / (z01 T1))))
  ; it does not matter if later we rename one z01 but not the other and thus
  ; forget that they're the same, because e is a non-path, so we can only 
  ; select something from it once.
  ; But not sure if we ever will rename z01.
  ; But what we may have to do is: add it to Γ, and then later we add another
  ; z01 to Γ, which overrides old z01, but shouldn't!
  ; => TODO these z0 names must be distinct from all possible var names!
  ; (for the moment just never use a var name starting with z0)
  
  ; rules for paths  (PATH-∋)
  ; also delegate to membership-T, but substitute self ref by path
  
  [(type Γ p T)
   (where z_fresh ,(variable-not-in (term (p T)) 'z0))
   (membership-T Γ T z_fresh Lany D_0)
   (where D_p (subst D_0 z_fresh p))
   -------------------------------------
   (membership-e Γ p Lany D_p)]
  
)

; if the helper variable z is needed to express type T, add it to T,
; otherwise return T unmodified
(define-metafunction ddot
  add/ : T (z U) -> T
  ; self reference is indeed used
  [(add/ T (z U)) (T / (z U))
   (where #t (variable-in z T))]
  ; self reference is not used
  [(add/ T (z U)) T]
  ; TODO something special if it's already a slash type?
  ; Do we allow ((T / (x U)) / (y S)) ?
)

(define-judgment-form ddot
  #:mode (membership-T I I I I O)
  ; z is name of self reference which might be used in D
  ; D contains Lany, but Lany is needed as I argument
  #:contract (membership-T Γ T z Lany D#f)
  
  [-----------------------------
   (membership-T Γ Top z Lany #f)]
  
  ; this is D_Bot from DOT paper:
  [---------------------------------------
   (membership-T Γ Bot z Lt (: Lt Top Bot))]
  [---------------------------------
   (membership-T Γ Bot z l (: l Bot))]
  [-------------------------------------
   (membership-T Γ Bot z m (: m Top Bot))]

  [(membership-T Γ T_1 z Lany D_1)
   (membership-T Γ T_2 z Lany D_2)
   -----------------------------------------------------------
   (membership-T Γ (T_1 ∧ T_2) z Lany (decl-intersect D_1 D_2))]
  
  [(membership-T Γ T_1 z Lany D_1)
   (membership-T Γ T_2 z Lany D_2)
   -------------------------------------------------------
   (membership-T Γ (T_1 ∨ T_2) z Lany (decl-union D_1 D_2))]
    
  [(where #f (member Lany {Lany_i ...}))
   (membership-T Γ T z Lany D);TODO
   ----------------------------------------------------------
   (membership-T Γ {rfn T y (: Lany_i U_i ...)  ...} z Lany D)]
  
  [(membership-T Γ T z Lany D_1)
   (where (: Lany U ...) D_2)
   (where D (decl-intersect D_1 D_2))
   ------------------------------------------------------
   (membership-T Γ {rfn T z D_i ... D_2 D_j ...} z Lany D)]
  
  ; TODO this is will run into infinite loops
  ; TODO this case is not used by membership-e and type assignment, 
  ; but only by subtyping, so maybe do subtyping differently, then
  ; it's not necessary at all
  ; then restrict membership to Dlm (instead of D)
  ; but we still will have to handle this case if we want to know if l or m is
  ; member of path.L
  [(type Γ p T_p)
   (membership-T Γ T_p z Lt (: Lt S U))
   (membership-T Γ U z Lany D)
   -----------------------------------
   (membership-T Γ (sel p Lt) z Lany D)]
  
)

(define-metafunction ddot
  decl-intersect : D#f D#f -> D#f
  [(decl-intersect (: Lt S_1 U_1) (: Lt S_2 U_2))
   (: Lt (S_1 ∨ S_2) (U_1 ∧ U_2))]
  [(decl-intersect (: l T_1) (: l T_2)) 
   (: l (T_1 ∧ T_2))]
  [(decl-intersect (: m S_1 U_1) (: m S_2 U_2))
   (: m (S_1 ∨ S_2) (U_1 ∧ U_2))]
  [(decl-intersect #f D#f) D#f]
  [(decl-intersect D#f #f) D#f]
  ; if both args are not #f but label does not match: error (don't return #f)
)
(define-metafunction ddot
  decl-union : D#f D#f -> D#f
  [(decl-union (: Lt S_1 U_1) (: Lt S_2 U_2))
   (: Lt (S_1 ∧ S_2) (U_1 ∨ U_2))]
  [(decl-union (: l T_1) (: l T_2)) 
   (: l (T_1 ∨ T_2))]
  [(decl-union (: m S_1 U_1) (: m S_2 U_2))
   (: m (S_1 ∧ S_2) (U_1 ∨ U_2))]
  [(decl-union #f D#f) #f]
  [(decl-union D#f #f) #f]
  ; if both args are not #f but label does not match: error (don't return #f)
)

; Definition:
; A function f : Gammas x Types x Types --> Naturals is called magic if
; for all Γ, S, T, we have
; (Γ ⊢ S <: T) implies (in the proof of (Γ ⊢ S <: T), no path types of
;                      length greater than f(Γ, S, T) appear)
;
; Note that if S is not a subtype of T, f is allowed to return any natural.

; Since we don't know whether there is magic function which is computable,
; just do this: 
; (a slightly more civilized version of dotf's max-iter ;-) )
(define-metafunction ddot
  magic : Γ S T -> natural
  [(magic Γ S T) 100]
)

; subtyping (Γ ⊢ S <: T) (subtype Γ S T)
(define-judgment-form ddot
  #:mode (subtype I I I)
  #:contract (subtype Γ T T)
  
  [---------------- ; (REFL)
   (subtype Γ T T)]
  
  [------------------ ; (BOT-<:)
   (subtype Γ Bot T)]
  
  [------------------ ; (<:-TOP)
   (subtype Γ T Top)]
  
  [(side-condition #f)           ; TODO z.path can refer to something in S!
   (subtype Γ S T)
   (subtype Γ S (rfn Top z DLt ... Dl ... Dm ...))
   ----------------------------------------------- ; (<:-RFN)
   (subtype Γ S (rfn T z DLt ... Dl ... Dm ...))]
  
  ; TODO is it as easy as that?
  ; what if we need some restrictions made by refinement in order to have <: ?
  [(subtype Γ T S)
   ----------------------------------------------- ; (RFN-<:)
   (subtype Γ (rfn T z DLt ... Dl ... Dm ...) S)]
  
  [(membership-e Γ p Lt (: Lt S U))
   (subtype Γ S U)
   (subtype Γ T S)
   ------------------------------ ; (<:-TSEL)
   (subtype Γ T (sel p Lt))]
  
  [(membership-e Γ p Lt (: Lt S U))
   (subtype Γ S U)
   (subtype Γ U T)
   ------------------------------ ; (TSEL-<:)
   (subtype Γ (sel p Lt) T)]
   
  [(subtype Γ T T_1)
   (subtype Γ T T_2)
   -------------------------- ; (<:-∧)
   (subtype Γ T (T_1 ∧ T_2))]
  
  ; TODO there might be cases where none of the two rules below applies but 
  ; still, we  would like to have T_1 ∧ T_2 <: T
  ; e.g. T_1 has a decl that needs to be further restricted by T_2 to have <:,
  ; and T_2 has a decl that needs to be further restricted by T_1 to have <:
  
  [(subtype Γ T_1 T)
   -------------------------- ; (∧1-<:)
   (subtype Γ (T_1 ∧ T_2) T)]
  
  [(subtype Γ T_2 T)
   -------------------------- ; (∧2-<:)
   (subtype Γ (T_1 ∧ T_2) T)]
  
  [(subtype Γ T_1 T)
   (subtype Γ T_2 T)
   -------------------------- ; (∨-<:)
   (subtype Γ (T_1 ∨ T_2) T)]
  
  ; TODO there are cases where none of the two rules below applies but still, 
  ; we would like to have T <: T_1 ∨ T_2 (cf my_dotf_tests.ss)
  
  [(subtype Γ T T_1)
   -------------------------- ; (<:-∨1)
   (subtype Γ T (T_1 ∨ T_2))]
  
  [(subtype Γ T T_2)
   -------------------------- ; (<:-∨2)
   (subtype Γ T (T_1 ∨ T_2))]
)


(define-metafunction ddot
  Γ-update : Γ (x T) -> Γ
  [(Γ-update {(x_i T_i) ... (x T_old) (x_j T_j) ...} (x T_new))
   {(x_i T_i) ... (x T_new) (x_j T_j) ...}]
  [(Γ-update {(x_i T_i) ...} (x T))
   {(x_i T_i) ... (x T)}]
)

(define-metafunction ddot
  variable-in : x any -> bool
  [(variable-in x x) #t]
  [(variable-in x (any ...))
   (or ((variable-in x any) ...))]
)

; logical and
(define-metafunction ddot
  and : bool ... -> bool
  [(and #f bool ...) #f]
  [(and #t) #t]
  [(and #t bool_1 bool ...) (and bool_1 bool ...)]
)
; logical or
(define-metafunction ddot
  or : bool ... -> bool
  [(or #t bool ...) #t]
  [(or #f) #f]
  [(or #f bool_1 bool ...) (or bool_1 bool ...)]
)


(define-judgment-form ddot
  #:mode (Γ-doesnt-contain I I)
  [(Γ-doesnt-contain Γ x)
   (side-condition (not-in-Γ Γ x))]
)
(define-metafunction ddot
  not-in-Γ : Γ x -> bool
  [(not-in-Γ {(x_i T_i) ... (x T) (x_j T_j) ...} (x U)) #f]
  [(not-in-Γ Γ x) #t]
)

(define-judgment-form ddot
  #:mode (isnt-path I)
  [(isnt-path e)
   (side-condition (not-path e))]
)
(define-metafunction ddot
  not-path : e -> bool
  [(not-path p) #f]
  [(not-path e) #t]
)

(require racket/set)
(define-metafunction ddot
  intersect : {any ...} ... -> {any ...}
  [(intersect {any_i ...} ...)
   ,(set->list (apply set-intersect (map (lambda (l) (list->set l)) 
                                         (term ({any_i ...} ...)))))]
)
(define-metafunction ddot
  union : {any ...} ... -> {any ...}
  [(union {any_i ...} ...)
   ,(set->list (apply set-union (map (lambda (l) (list->set l)) 
                                     (term ({any_i ...} ...)))))]
)
(define-metafunction ddot
  member : any {any ...} -> bool
  [(member any_1 {any_i ... any_1 any_j ...}) #t]
  [(member any_1 {any_i ...}) #f]
)
#|(define-judgment-form ddot
  #:mode (not-member I I)
  #:contract (not-member any {any ...})
)|#

; copied from https://github.com/namin/dot/blob/master/src/redex/dotf.ss
(define-metafunction ddot
  subst : any x any -> any
  ;; 1. x_1 bound
  [(subst (m_1 x_1 any_1) x_1 any_2)
   (m_1 x_1 any_1)]
  [(subst (val x_1 = new c_1 in any_1) x_1 any_2)
   (val x_1 = new c_1 in any_1)]
  [(subst (rfn T_1 x_1 D_1 ...) x_1 any_2)
   (rfn (subst T_1 x_1 any_2) x_1 D_1 ...)]
  
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst (m_1 x_1 any_1) x_2 any_2)
   (m_1 x_3
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 any_1 any_2))
                                (term x_1)))]
  [(subst (val x_1 = new c_1 in any_1) x_2 any_2)
   (val x_3 = new (subst (subst-var c_1 x_1 x_3) x_2 any_2) in
        (subst (subst-var any_1 x_1 x_3) x_2 any_2))
   (where x_3 ,(variable-not-in (term (x_2 c_1 any_1 any_2))
                                (term x_1)))]
  [(subst (rfn T_1 x_1 D_1 ...) x_2 any_2)
   (rfn (subst T_1 x_2 any_2) x_3 (subst (subst-var D_1 x_1 x_3) x_2 any_2) ...)
   (where x_3 ,(variable-not-in (term (D_1 ... x_2 any_2))
                                (term x_1)))]

  ;; do not treat labels as variables
  [(subst (cv variable_1) x_1 any_1) (cv variable_1)]
  [(subst (cm variable_1) x_1 any_1) (cm variable_1)]
  ;[(subst (cc variable_1) x_1 any_1) (cc variable_1)]
  ;[(subst (ca variable_1) x_1 any_1) (ca variable_1)]
  [(subst (ct variable_1) x_1 any_1) (ct variable_1)]

  ;; 3. replace x_1 with any_1
  [(subst x_1 x_1 any_1) any_1]
  
  ;; the last two cases just recur on the tree structure of the term
  [(subst (any_2 ...) x_1 any_1)
   ((subst any_2 x_1 any_1) ...)]
  [(subst any_2 x_1 any_1) any_2]
)
(define-metafunction ddot
  subst-var : any x x -> any
  [(subst-var (cv variable_1) x_1 x_2) (cv variable_1)]
  [(subst-var (cm variable_1) x_1 x_2) (cm variable_1)]
  ;[(subst-var (cc variable_1) x_1 x_2) (cc variable_1)]
  ;[(subst-var (ca variable_1) x_1 x_2) (ca variable_1)]
  [(subst-var (ct variable_1) x_1 x_2) (ct variable_1)]
  
  [(subst-var (any_1 ...) x_1 x_2)
   ((subst-var any_1 x_1 x_2) ...)]
  [(subst-var x_1 x_1 x_2) x_2]
  [(subst-var any_1 x_1 x_2) any_1]
)

