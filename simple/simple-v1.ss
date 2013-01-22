#lang racket
(require redex)

(provide L-simple-v1)

;;; The Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language L-simple-v1
  (prog                       ; program 
    stat)                     ;    one statement
  (stat                       ; statement
    (ign e)                   ;   `(ign e)` instead of `e;` : ignore void
    { stat stat ... }         ;   block of statements
    d                        ;   type or value declaration
    (println e)               ;   print line
    (if e stat)               ;   if-then with no return value
    (if e stat stat)          ;   if-then-else with no return value
    (while e stat))           ;   while loop
  
  (d                          ; declaration
    vd                        ;   value declaration
    td)                       ;   type declaration
  
  (vd                         ; value declaration
    (val id t e)              ;   typed value declaration 
    (val id e))               ;   untyped value declaration
  
                              ; always keep in mind that an id can refer to a
                              ; value, but also to a type
  
  (td                         ; type declaration
    (type id t))              ;   allowed wherever vd is allowed
  
  (t                          ; type expression
    Void                      ;   the type of `void`
    Null                      ;   the type of `null`
    primt                     ;   primitive type
    intft                     ;   interface type
    funct                     ;   function type
    intst                     ;   intersection type
    patht                     ;   path type
    (var t))                  ;   type of reference cells
  (primt                      ; primitive type
    Int                       ;   integer
    Bool                      ;   boolean
    Str)                      ;   string
  (intft                      ; interface type
    [(val id t) ...])         ;   sequence of vals with id and type
  (funct                      ; function type
    (-> t t))                 ;   t -> t
  (intst                      ; intersection type
    (& t t))                  ;   t & t
  (patht                      ; path type ("indirect type")
    id                        ;   identifier
    ;(sel patht id)           ;   pathh.id is only useful if we can specify in
    )                         ;   an interface that an object must have a given
                              ;   type member -> that would be DOT, and we're
                              ;   not doing DOT here, so it's commented out.

  (e                          ; "normal" expression
    (e e)                     ;   function application
    oc                        ;   object construction
    id                        ;   identifier
    {stat ... e}              ;   block expression (!= block of statements)
    (=> (id t) e)             ;   anonymous function
    (if e e e)                ;   if then else returning a value
    binop                     ;   binary operator expression
    (sel e id)                ;   e.id
    literal)                  ;   literal
  
  (oc                         ; object construction
    (vd ...))                 ;   (possibly empty) list of value declarations
  
  (binop                      ; binary operator expression
    (&& e e)                  ;   logical and
    (|| e e)                  ;   logical or
    (== e e)                  ;   equality (TODO by address or structure?)
    (< e e)                   ;   less than for integers
    (+ e e)                   ;   integer addition or string concatenation
    (- e e)                   ;   integer subtraction
    (* e e)                   ;   integer multiplication
    (/ e e))                  ;   integer division
   
  (literal                    ; literal
    number                    ;   integer (provided by racket)
    true                      ;   boolean
    false                     ;   boolean
    string)                   ;   string (provided by racket)
  
  (id                         ; identifier
    variable-not-otherwise-mentioned)
)


;;; Technical ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; typing environment Γ
; Usually, Γ is only used to store mappings of the form (myValName -> itsType).
; But here, we also use it to store mappings of the form (myTypeAlias -> aType).
; We store it in the same environment, because in a given context, we do not
; allow a value and a type to have the same name.
; To distinguish whether the mapping is (myValName -> itsType) or 
; (myTypeAlias -> aType), we prefix them with `val` or `type`.
(define-extended-language L-simple-v1+Γ L-simple-v1
  [mapping                   ; Γ item
    (val id t)               ;   (myValName -> itsType)
    (type id t)]             ;   (myTypeAlias -> aType)
  [Γ                         ; typing environment
    (mapping ...)]           ;   list of mappings
)
(define-metafunction L-simple-v1+Γ
  Γ-lookup-mapping : Γ id -> mapping or #f
  [(Γ-lookup-mapping (mapping_s ... (val id_req t_req)) id_req) 
    (val id_req t_req)]
  [(Γ-lookup-mapping (mapping_s ... (type id_req t_req)) id_req) 
    (type id_req t_req)]
  [(Γ-lookup-mapping (mapping_s ... mapping_not-matching) id_req)
   (Γ-lookup-mapping (mapping_s ...) id_req)]
  [(Γ-lookup-mapping () id_req) #f]
)
(define-metafunction L-simple-v1+Γ
  Γ-lookup-val : Γ id -> t or #f
  [(Γ-lookup-val (mapping_s ... (val id_req t_req)) id_req) 
    t_req]
  [(Γ-lookup-val (mapping_s ... (val id_last t_last)) id_req)
   (Γ-lookup-val (mapping_s ...) id_req)]
  [(Γ-lookup-val () id_req) #f]
)
(define-metafunction L-simple-v1+Γ
  Γ-lookup-type : Γ id -> t or #f
  [(Γ-lookup-type (mapping_s ... (type id_req t_req)) id_req) 
    t_req]
  [(Γ-lookup-type (mapping_s ... (type id_last t_last)) id_req)
   (Γ-lookup-type (mapping_s ...) id_req)]
  [(Γ-lookup-type () id_req) #f]
)
(define-metafunction L-simple-v1+Γ
  Γ-extend-unsafe : Γ mapping -> Γ
  [(Γ-extend-unsafe (mapping_s ...) mapping_new)
   (mapping_s ... mapping_new)]
)
(define-metafunction L-simple-v1+Γ
  Γ-extend : Γ mapping -> Γ
  [(Γ-extend Γ (val id_new t_new))
   (Γ-extend-unsafe Γ (val id_new t_new))
   (side-condition (not (term (Γ-lookup-mapping Γ id_new))))]
  [(Γ-extend Γ (type id_new t_new))
   (Γ-extend-unsafe Γ (type id_new t_new))
   (side-condition (not (term (Γ-lookup-mapping Γ id_new))))]
  [(Γ-extend Γ mapping)
   (, (error 'Γ-extend "redefining mapping")) ; TODO better error message
   ]
)
; Γ-extend-with-ds extends Γ with mappings obtained from declarations
(define-metafunction L-simple-v1+Γ
  Γ-extend-with-ds : Γ (d ...) -> Γ
  [(Γ-extend-with-ds Γ ()) Γ]
  [(Γ-extend-with-ds Γ ((val id t e) d_s ...))
   (Γ-extend-with-ds (Γ-extend Γ (val id t)) (d_s ...))]
  [(Γ-extend-with-ds Γ ((val id e) d_s ...))
   (Γ-extend-with-ds (Γ-extend Γ id INFER) (d_s ...))];TODO
  [(Γ-extend-with-ds Γ ((type id t) d_s ...))
   (Γ-extend-with-ds (Γ-extend Γ (type id t)) (d_s ...))]
)

; true iff two identifiers are different
(define-metafunction L-simple-v1+Γ
  [(different id_1 id_1) #f]
  [(different id_1 id_2) #t]
)

; filter-for-vds filters a list of statements, keeping only value declarations
(define-metafunction L-simple-v1+Γ
  filter-for-vds : (stat ...) -> (vd ...)
  [(filter-for-vds ()) ()]
  [(filter-for-vds (vd stat_s ...))
   ((filter-for-vds (stat_s)) ... vd)]
  [(filter-for-vds (stat_notvd stat_s ...))
   ((filter-for-vds (stat_s)) ...)]
)

; Note that define-judgment-form expects the same name everywhere,
; so a rule cannot combine different judgments. To work around this,
; we have to define the judgments as metafunctions. 


;;; Typechecking ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (wf-stat Γ stat) means that in Γ, stat is a well-formed statement
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-stat I I)
  #:contract (wf-stat Γ stat)
  [(wf-stat Γ stat)
   (side-condition (is-wf-stat Γ stat))]
)
(define-metafunction L-simple-v1+Γ
  is-wf-stat : Γ stat -> bool
  [(is-wf-stat Γ vd)                     ; view value declaration as statement
   (judgement-holds (wf-vd vd t_unbound))]
  [(is-wf-stat Γ td)                     ; view type declaration as statement
   (judgement-holds (wf-vd td t_unbound))]
  [(is-wf-stat Γ (ign e))                ; ign-statement
   (judgment-holds (types Γ e Void))] 
  [(is-wf-stat Γ {})                     ; empty statement block
   #t]
  [(is-wf-stat Γ {stat_before ... stat}) ; statement block
    (and 
      (is-wf-stat Γ {stat_before ... })
      (judgement-holds (types 
        (Γ-extend-with-vds Γ (filter-for-vds stat_before ...))
        stat)))]
  [(is-wf-stat Γ (println e))            ; println a primitive type
   (judgement-holds (types Γ e primt))]
  [(is-wf-stat Γ (if e stat))            ; if-then with no return value
    (and
      (judgement-holds (types Γ e Bool))
      (is-wf-stat Γ stat))] 
  [(is-wf-stat Γ (if e stat_1 stat_2))   ; if-then-else with no return value
     (and
       (judgement-holds (types Γ e Bool))
       (and
         (is-wf-stat Γ stat_1)
         (is-wf-stat Γ stat_2)))]
  [(is-wf-stat Γ (while e stat))         ; while
    (and
      (judgement-holds (types Γ e Bool))
      (is-wf-stat Γ stat))]
)

; (wf-oc Γ oc intft) means that in Γ, oc is a well-formed object construction
; of interface type intft
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-oc I I O)
  #:contract (wf-oc Γ oc intft)
  [(wf-oc Γ () [])]                                         ; empty/void object
  #|
  [(wf-oc Γ (vd_s ... vd) [(val id_s t_s) ... (val id t)])  ; non-empty object
   (wf-oc Γ (vd_s ...) [(val id_s t_s) ...])
   (side-condition (judgement-holds (wf-vd vd t)))]
  |#
  ; TODO connect id of vd oc with id in interface
  ; TODO distinguish typed and untyped case (fix ambiguity...)
)

; (wf-vd Γ vd t) means that in Γ, vd is a well-formed value declaration of 
; type t
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-vd I I O)
  #:contract (wf-vd Γ vd t)
  [(wf-vd Γ (val id t e) t)                  ; typed vd initialized with e
   ;(side-condition (judgement-holds (types e t)))
   ]
  ; TODO
)

; (calc-type Γ e) returns the type of expression e
(define-metafunction L-simple-v1+Γ
  calc-type : Γ e -> t
  [(calc-type Γ e)
   (head-of-singleton-list (judgment-holds (types Γ e t) t))]
  ; TODO why does everything look like a work-around?
)
(define-metafunction L-simple-v1+Γ
  head-of-singleton-list : (any ...) -> any
  [(head-of-singleton-list (any)) any]
)

; (types Γ e t) means that in Γ, e is of type t
(define-judgment-form
  L-simple-v1+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
 
  [(types Γ e_1 (-> t_2 t_3))
   (types Γ e_2 t_2)
   -------------------------- ; (Function Application)
   (types Γ (e_1 e_2) t_3)]
 
  [(types (id : t_1 Γ) e t_2)
   --------------------------------------- ; (Type of anonymous function)
   (types Γ (=> (id t_1) e) (-> t_1 t_2))]
  
  ; TODO what if Γ-lookup returns #f ??
  [(where t (Γ-lookup Γ id))
   ----------------------------------------- ; (Extract val's type from Γ)
   (types Γ id t)]
  
  [--------------------  ; (integer literals)
   (types Γ number Int)]
  
  [--------------------  ; (string literals)
   (types Γ string Str)]
  
  [--------------------  ; (boolean literal)
   (types Γ true Bool)]
  
  [--------------------  ; (boolean literal)
   (types Γ false Bool)]
  
  [(types Γ e_1 Bool)
   (types Γ e_2 t)
   (types Γ e_3 t)
   ------------------------------ ; (if-then-else expression)
   (types Γ (if e_1 e_2 e_3) t)]
  
  [(types Γ stat Stat) ...
   (types Γ e t)
   --------------------------- ; (expression block)
   (types Γ { stat ... e } t)]
  
  #| TODO fix this
  [(side-condition (judgement-holds (wf-oc Γ oc intft)))
   ----------------------------------------------------- ; (object construction)
   (types Γ oc intft)]
  |#
  
  ; TODO type rule for (sel e id)
  
  

  
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (integer addition)
   (types Γ (+ e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Str)
   -------------------------- ; (concat Int and Str to Str)
   (types Γ (+ e_1 e_2) Str)]
 
  [(types Γ e_1 String)
   (types Γ e_2 Int)
   -------------------------- ; (concat Str and Int to Str)
   (types Γ (+ e_1 e_2) String)]
  
  [(types Γ e_1 String)
   (types Γ e_2 String)
   -------------------------- ; (concat two strings)
   (types Γ (+ e_1 e_2) String)]
  
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   -------------------------- ; (logical and)
   (types Γ (&& e_1 e_2) Bool)]
    
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   -------------------------- ; (logical or)
   (types Γ (|| e_1 e_2) Bool)]
  
  [(types Γ e_1 String)
   (types Γ e_2 String)
   -------------------------- ; (String equality)
   (types Γ (== e_1 e_2) Bool)]
  
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   -------------------------- ; (Bool equality)
   (types Γ (== e_1 e_2) Bool)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (Int equality)
   (types Γ (== e_1 e_2) Bool)]
  
  ; Note: for equality on objects, define an equals method (as in Java)
  ; == object comparision by address is not supported
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (Int <)
   (types Γ (< e_1 e_2) Bool)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (Int subtraction)
   (types Γ (- e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (Int multiplication)
   (types Γ (* e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (Int division)
   (types Γ (/ e_1 e_2) Int)]
  
)

; (wf-t Γ t) means that in Γ, t is a well-formed type expression
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-t I I)
  #:contract (wf-t Γ t)
  [(wf-t Γ Void)]                        ; the type of `void`
  [(wf-t Γ Null)]                        ; the type of `null`
  [(wf-t Γ primt)]                       ; primitive type
  [(wf-t Γ (var t))                      ; reference cell type
   (wf-t Γ t)]
  
  #| TODO all these:

    intft                     ;   interface type
    funct                     ;   function type
    intst                     ;   intersection type
    patht                     ;   path type 
  
  (intft                      ; interface type
    [(val id t) ...])         ;   sequence of vals with id and type
  (funct                      ; function type
    (-> t t))                 ;   t -> t
  (intst                      ; intersection type
    (& t t))                  ;   t & t
  (patht                      ; path type ("indirect type")
    id                        ;   identifier
    (sel patht id))           ;   pathh . id  
     ---> TODO requires compile-time store
  |#

)

;;; Reduction Relation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; state = statements to evaluate + values + values of reference cells + ...?
; TODO :P

(define-extended-language L-simple-v1-Ev L-simple-v1+Γ
  (p (stat ...))                    ; Program to evaluate
  (P (e ... E e ...))
  (E (v E)
     (E e)
     (+ v ... E e ...)
     (if0 E e e)
     (fix E)
     hole)
  (v (λ (x t) e)
     (fix v)
     number))


