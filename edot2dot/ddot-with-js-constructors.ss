#lang racket

; this is a deprecated version of ddot where constructors have special syntax
;   new {...}
; instead of
;   new T {...}

(require redex)
(provide (all-defined-out))

; subtyping does not need expansion
; define constructors such that they do not need expansion either (but still are
; equivalent to DOT constructors, i.e. allow non-collapsed bounds, whatever that is good for)
; -> throw away expansion, but will need something like "simplify intersection" and
;    "simplify refinement", which will be very similar to expansion. So what we really will
;    (hopefully) get rid of is having two kinds of types (types and sets of declarations),
;    because these will become the same
; -> also throw away distinction between abstract and concrete types, because this is only 
;    needed to know if type is allowed in constructor
; Possible problem: Adding abstract types which already initialize some members might be more 
; difficult than in dot.

; Why is there a store in arguments to is_subtype of dot, but no store in the rules in the paper?
; -> Try to do subtyping without store.

; What is a refinement of p.L, i.e. p.L{z=>decls} ? Is it just a refinement of upper bound of p.L?
; No, because p.L{z=>decls} <: p.L,
; but (upper bound of p.L){z=>decls) is not a subtype of p.L

; Can we translate
;    p.L{z=>decls}
; into something like
;    p.L ∧ [z.L_i -> z.L_i ∧ p.L_i]{L_i, decls}
; where L_i are all the type labels of p.L and in decls??
; No. Consider a label z.L_k in decls. Now if p.L also contains L_k, we would need
; to replace the z.L_k in decls by "z.L_k ∧ (unknown path to the object of type p.L).L_k".
; And note that we don't even know if p.L contains L_k

(define-language ddot
  ((x y z u)                             ; variable
    id)
  (l                                     ; value label
    (cv id))
  (m                                     ; method label
    (cm id))
  (v                                     ; value
    x)
  (e                                     ; expression
    v 
    (val x = new c in e)
    (sel e l) 
    (sel e m e))
  (p                                     ; path
    x
    (sel p l))
  (c                                     ; constructor is different from dot
    {DLt ... dl ... dm ... })
  (d                                     ; initialization, must be typed because otherwise we have a
    dm                                   ;    cyclic dependency in (NEW): to infer return type of
    dl)                                  ;    method we would need to know the type being instantiated
  (dl                                    ; initialization of label
    (Dl v))
  (dm                                    ; initialization of method including type of argument
    (Dm x e))
  (Γ                                     ; environment
    {(x T) ...})
  (store                                 ; store is as in paper (different from dotf.ss)
    {(x c) ...})
  (Lt                                    ; type label (no distinction between abstract/concrete)
    (ct id))
  ((S T U V W)                           ; type
    (T / Γ)                              ;   Γ contains auxiliary variables needed to express type T
    (sel p Lt) 
    (rfn T z DLt ... Dl ... Dm ...)
    (T ∧ T) 
    (T ∨ T)
    Top 
    Bot)
  (D DLt Dl Dm)                          ; declarations
  (DLt (: Lt S U))
  (DLtn (: Lt Sn Un))
  (Dl (: l T))
  (Dm (: m S U))
  
  ; auxiliaries
  (Ltm Lt m)
  (Lany Lt l m)
  (bool #t #f)
  (id variable-not-otherwise-mentioned)
)

(define-judgment-form ddot
  #:mode (type I I O)
  #:contract (type Γ e T)
  
  [----------------------------------------------- ; (VAR)
   (type {(x_i T_i) ... (x T) (x_j T_j) ...} x T)]
  
  [(membership Γ e l (: l T))
   -------------------------- ; (SEL)
   (type Γ (sel e l) T)]
  
  [(membership Γ e_1 m (: m T U))
   (type Γ e_2 S)
   (subtype Γ S T)
   ------------------------------- ; (MSEL)
   (type Γ (sel e_1 m e_2) U)]
  
  [(Γ-doesnt-contain Γ y) ; TODO is this a valid replacement for y not in fn(T') ?
   (where T_y (rfn Top y (: Lt S U) ... (: l T) ... (: m V W) ...))
   (where Γ_new (Γ-update Γ (y T_y)))
   (decl Γ_new ((: l T) v)) ...
   (decl Γ_new ((: m V W) x_m e_m)) ...
   (subtype Γ_new S U) ...
   (type Γ_new e T_e)
   ----------------------------------------------------------------------------------------- ; (NEW)
   (type Γ (val y = new {(: Lt S U) ... ((: l T) v) ... ((: m V W) x_m e_m) ...} in e) T_e)]
)

(define-judgment-form ddot
  #:mode (decl I I)
  #:contract (decl Γ d)
  
  [(type Γ v S)
   (subtype Γ S T)
   --------------------- ; (VDECL)
   (decl Γ ((: l T) v))]
  
  [(where Γ_new (Γ-update Γ (x S)))
   (type Γ_new e T)
   (subtype Γ_new T U)
   ------------------------------- ; (MDECL)
   (decl Γ ((: m S U) x e))]
)

; Answers "in Γ, what declaration does e contain for label Lany?".
; TODO this is far from making sense or being complete...
(define-judgment-form ddot
  #:mode (membership I I I O)
  #:contract (membership Γ e Lany D) ; D contains Lany, but Lany is needed as I argument
  
  ; rules for paths
  
  [(type Γ p T)
   (where {rfn Top z D_i ... D D_j ...} T)
   (where (: Lany S ...) D)
   --------------------------------------- ; (PATH-∋)
   (membership Γ p Lany D)]
   
  
  ; rules for non-paths
  
  ; types in declaration use self reference
  [(isnt-path e)
   (type Γ e T)
   (where {rfn Top z D_i ... (: l V) D_j ...} T)
   (side-condition (term (variable-in z V)))
   (where D (: l (V/{(z T)})))
   ------------------------------------------------------ ; (TERM-∋)
   (membership Γ e l D)]
  
  ; types in declaration use self reference
  [(isnt-path e)
   (type Γ e T)
   (where {rfn Top z D_i ... (: Ltm V W) D_j ...} T)
   ;(side-condition (or (variable-in z V) (variable-in z W)))
   (where D (: Ltm (V / {(z T)}) (W / {(z T)})))
   ------------------------------------------------------ ; (TERM-∋)
   (membership Γ e Ltm D)]
  
)


(define-judgment-form ddot
  #:mode (subtype I I I)
  #:contract (subtype Γ T T)
  
  [-------
   (subtype Γ T T)]
   
)

(define-metafunction ddot
  intersect-decl : D D -> D
  [(intersect-decl (: Lt S_1 U_1) (: Lt S_2 U_2)) (: Lt (S_1 ∨ S_2) (U_1 ∧ U_2))]
  [(intersect-decl (: l T_1) (: l T_2)) (: l (T_1 ∧ T_2))]
  [(intersect-decl (: m S_1 U_1) (: m S_2 U_2)) (: m (S_1 ∨ S_2) (U_1 ∧ U_2))]
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
