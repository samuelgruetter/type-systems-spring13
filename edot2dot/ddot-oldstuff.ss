; old deprecated stuff from ddot.ss

#lang racket

(require redex)
(require "trcl.ss")
(require "ddot.ss")

;;;;;;;;;; lm-expand ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; not good because some path types have no expansion!
; expansion for Dl and Dm only (Γ ⊢ T <z D) (lm-expand Γ z T (Dl ... Dm ...))
(define-judgment-form ddot
  #:mode (lm-expand I I I O)
  #:contract (lm-expand Γ z T (Dl ... Dm ...))
  
  [(lm-expand Γ z T (Dlm_1 ...))
   ------------------------------------------------------------- ; (RFN-LME)
   (lm-expand Γ z (rfn T z DLt ... Dlm_2 ...)
              (intersect-lms (Dlm_1 ...) (Dlm_2 ...)))]
  
  ; TODO (TSEL-<) is dangerous for loops, but we still need something like this
  ; what is upper bound of label: something using label itself of not?
  
  [(lm-expand Γ z T_1 (Dlm_1 ...))
   (lm-expand Γ z T_2 (Dlm_2 ...))
   ---------------------------------------------------------------- ; (∧-LME)
   (lm-expand Γ z (T_1 ∧ T_2) (intersect-lms (Dlm_1 ...) (Dlm_2 ...)))]
  
  [(lm-expand Γ z T_1 (Dlm_1 ...))
   (lm-expand Γ z T_2 (Dlm_2 ...))
   ---------------------------------------------------------------- ; (∨-LME)
   (lm-expand Γ z (T_1 ∨ T_2) (union-lms (Dlm_1 ...) (Dlm_2 ...)))]
  
  [----------------------- ; (TOP-LME)
   (lm-expand Γ z Top ())]
   
  [------------------------------------------------------- ; (BOT-LME)
   (lm-expand Γ z Bot ((: (cv l492746274639271637) Top)))] ; <-- hack
)


(define-metafunction ddot
  intersect-lms : (Dl ... Dm ...) (Dl ... Dm ...) -> (Dl ... Dm ...)
  [(intersect-lms () ()) ()]
)

(define-metafunction ddot
  union-lms : (Dl ... Dm ...) (Dl ... Dm ...) -> (Dl ... Dm ...)
  [(union-lms () ()) ()]
)


;;;;;;;;;; xT->rel ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; for each type label x.path.L yield two tuples (S <: p.L) and (p.L <: T)
; might yield more tuples (in case of union types)
; problem: if in x.l.m, l is of type x.L, x.l.m will never appear in result, 
; because if we recursively go into fields with a path type, we can get
; infinitely long path types, so we don't do that
(define-metafunction ddot
  xT->rel : (x T) -> {(S T) ...}
  [(xT->rel (x (rfn T_1 z (: Lt S_z U_z) ...  (: (cv id) T_z) ... Dm ...))) 
   (union {(V_i W_i) ...} {(S (sel x Lt)) ...} {((sel x Lt) U) ...} 
          {(V_k W_k) ... ...})
   ; subst z by x
   (where {S ...} {(subst S_z z x) ...})
   (where {U ...} {(subst U_z z x) ...})
   (where {T ...} {(subst T_z z x) ...})
   ; path types in (V_i W_i) start with x => OK
   (where {(V_i W_i) ...} (xT->rel (x T_1)))
   ; path types in (V_j W_j) start with id => prepend x
   (where {{(V_j W_j) ...} ...} 
          {(xT->rel (id T)) ...})
   (where {{(V_k W_k) ...} ...} 
          {(prepend-var-to-types-in-rel x id {(V_j W_j) ...}) ...})]
  [(xT->rel (x (S ∧ T)))
   (union (xT->rel (x S)) (xT->rel (x T)))] ; here it's enough to take xT->rel
  [(xT->rel (x (S ∨ T)))
   (intersect (xT->trrel (x S)) (xT->trrel (x T)))] ; here we need xT-trrel
  [(xT->rel (x Top)) {}]
  [(xT->rel (x Bot)) {}]
  [(xT->rel (x (sel p Lt))) {}]
  [(xT->rel (x (T / (y S)))) ,(error "not yet implemented")]
)

; for each type label p.L inside the types of Γ, yield two tuples 
; (S <: p.L) and (p.L <: T)
(define-metafunction ddot
  Γ->rel : Γ -> {(S T) ...}
 
)

; from an (x: T), extract a transitive relation 
; {(x.path.L1 <: x.path.L2) ... (x.path.L3 <: T) ... (T <: x.path.L4) ...}
; not necessarily ordered like this
(define-metafunction ddot
  xT->trrel : (x T) -> {(T T) ...}
  [(xT->trrel (x T))
   ,(trcl (term (xT->rel (x T))))]
)

(define-metafunction ddot
  prepend-var-to-types-in-rel : x x {(T T) ...} -> {(T T) ...}
  [(prepend-var-to-types-in-rel x y {(S T) ...})
   {((prepend-var-to-type x y S) (prepend-var-to-type x y T)) ...}]
)

; (prepend-var-to-type x_newroot x_oldroot T) does the following:
; if T is a path type starting with x_oldroot, it prepends x_newroot to the path
; otherwise it recursively applies itself to all types inside T
(define-metafunction ddot
  prepend-var-to-type : x x T -> T
  [(prepend-var-to-type x_newroot x_oldroot (sel p Lt)) 
   (sel (prepend-var-to-path x_newroot p) Lt)
   (where #t (path-starts-with x_oldroot p))]
  [(prepend-var-to-type x_newroot x_oldroot (sel p Lt)) 
   (sel p Lt)
   (where #f (path-starts-with x_oldroot p))]
  [(prepend-var-to-type x_newroot x_oldroot (T / (y S)))
   ,(error "not yet implemented")]
  ; old root is bound inside T: nothing to do
  [(prepend-var-to-type x_newroot z (rfn T z D ...))
   (rfn T z D ...)]
  [(prepend-var-to-type x_newroot x_oldroot (rfn T_z z D_z ...))
   (rfn T_1 z (: Lt (prepend-var-to-type x_newroot x_oldroot S) 
                    (prepend-var-to-type x_newroot x_oldroot U)) ... 
              (: l  (prepend-var-to-type x_newroot x_oldroot T)) ... 
              (: m  (prepend-var-to-type x_newroot x_oldroot V)
                    (prepend-var-to-type x_newroot x_oldroot W)) ...)
   ; avoid variable capture
   (where z_fresh ,(variable-not-in 
                     (term (x_newroot x_oldroot (rfn T_z z D_z ...))) 'zz))
   (where (rfn T_1 z_fresh (: Lt S U) ... (: l T) ... (: m V W) ...)
          (subst (rfn T_z z D_z ...) z z_fresh))]
  [(prepend-var-to-type x_newroot x_oldroot (S ∧ T))
   (   (prepend-var-to-type x_newroot x_oldroot S) 
     ∧ (prepend-var-to-type x_newroot x_oldroot T))]
  [(prepend-var-to-type x_newroot x_oldroot (S ∨ T))
   (   (prepend-var-to-type x_newroot x_oldroot S) 
     ∨ (prepend-var-to-type x_newroot x_oldroot T))]
  [(prepend-var-to-type x_newroot x_oldroot Top) Top]
  [(prepend-var-to-type x_newroot x_oldroot Bot) Bot]
)
  
; (prepend-var x path) = x.path
; a.b.c.d.L = (sel (sel (sel (sel a b) c) d) L)
(define-metafunction ddot
  prepend-var-to-path : x p -> p
  [(prepend-var-to-path x y) 
   (sel x (cv y))]
  [(prepend-var-to-path x (sel p l))
   (sel (prepend-var-to-path x p) l)]
)
   
(define-metafunction ddot
  path-starts-with : x p -> bool
  [(path-starts-with x x) #t]
  [(path-starts-with x y) #f]
  [(path-starts-with x (sel p l)) 
   (path-starts-with x p)]
)

