#lang racket
(require redex)

(provide (all-defined-out))

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
    ;(sel patht id)           ;   path.id is only useful if we can specify in
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
    (d ...))                  ;   (possibly empty) list of declarations
  
  (binop                      ; binary operator expression
    (&& e e)                  ;   logical and
    (|| e e)                  ;   logical or
    (== e e)                  ;   equality for primitive types and Null
    (< e e)                   ;   less than for integers
    (+ e e)                   ;   integer addition or string concatenation
    (- e e)                   ;   integer subtraction
    (* e e)                   ;   integer multiplication
    (/ e e))                  ;   integer division
   
  (literal                    ; literal
    number                    ;   integer (provided by racket)
    true                      ;   boolean
    false                     ;   boolean
    null                      ;   bottom type
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

; Note that define-judgment-form expects the same name everywhere,
; so a rule cannot combine different judgments. To work around this,
; we have to define the judgments as metafunctions. 


;;; Typechecking ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (wf-prog prog) means that prog is a well-formed program
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-prog I)
  #:contract (wf-prog prog)
  [(wf-prog prog)
   ; just check if prog is a well-formed statement in the empty enviroment
   (side-condition (is-wf-stat () prog))]
)

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
  [(is-wf-stat Γ d)                      ; view declaration as statement
   (is-wf-d Γ d)]
  [(is-wf-stat Γ (ign e))                ; ign-statement
   (judgment-holds (types Γ e Void))] 
  [(is-wf-stat Γ {})                     ; empty statement block
   #t]
  [(is-wf-stat Γ {d stat_after ...})     ; statement block beginning with d
   (and
     (is-wf-d Γ d)
     (is-wf-stat Γ_new {stat_after ...}))
   (where Γ_new (Γ-extend Γ (d-to-mapping d Γ)))]
  [(is-wf-stat Γ {stat stat_after ...})  ; statement block not beginning with d
   (and
     (is-wf-stat Γ stat)
     (is-wf-stat Γ {stat_after ...}))]  
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

; (wf-d Γ d) means that in Γ, d is a well-formed declaration
; Does not check that id is not yet in Γ
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-d I I)
  #:contract (wf-d Γ d)
  [(wf-d Γ d)
   (side-condition (is-wf-d Γ d))]
)
(define-metafunction L-simple-v1+Γ
  is-wf-d : Γ d -> bool
  [(is-wf-d Γ (val id t e))               ; typed val decl
   (judgement-holds (types Γ e t))]
  [(is-wf-d Γ (val id e))                 ; untyped val decl
   (judgement-holds (types Γ e t_unbound))]
  [(is-wf-d Γ (type id t))                ; type decl
   (is-wf-t Γ t)]
)

; (calc-oc-type Γ oc) returns the interface type of object construction oc
; also typechecks rhs of declarations
(define-metafunction L-simple-v1+Γ
  calc-oc-type : Γ oc -> intft or #f
  [(calc-oc-type Γ ()) []]
  [(calc-oc-type Γ (d d_s ...))
   (if (is-wf-d Γ d)
       ; Γs have the same form as intfts :)
       (Γ-extend (calc-oc-type Γ_new (d_s ...)) mp)
       #f)
   (where Γ_new (Γ-extend Γ mp))
   (where mp (d-to-mapping d Γ))]
)

; converts a value or type declaration to a mapping which can be stored in a Γ
; Γ_outer is the context needed to construct the type of untyped vds
(define-metafunction L-simple-v1+Γ
  d-to-mapping : d Γ_outer -> mapping
  [(d-to-mapping (val id t e) Γ_outer)    ; typed val decl
   (val id t)]
  [(d-to-mapping (val id e) Γ_outer)      ; untyped val decl
   (val id t)
   (where t (calc-e-type Γ_outer e))]
  [(d-to-mapping (type id t) Γ_outer)     ; type decl
   (type id t)]
)

; (calc-e-type Γ e) returns the type of expression e
(define-metafunction L-simple-v1+Γ
  calc-e-type : Γ e -> t
  [(calc-e-type Γ e)
   ;t (where t (judgement-holds (types Γ e t)))]
   (head-of-singleton-list (judgment-holds (types Γ e t) t))]
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
  
  ; TODO what if Γ-lookup-val returns #f ??
  [(where t (Γ-lookup-val Γ id))
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
  
  [(types Γ e t)
   ----------------- ; (expression block of one single expression)
   (types Γ {e} t)]
  
  [(types (Γ-extend Γ (d-to-mapping Γ d)) {stat_s ... e} t)
   (side-condition (is-wf-d Γ d))   
   ---------------------------------------- ; (expression block starting with d)
   (types Γ { d stat_s ... e } t)]
  
  [(types Γ {stat_s ... e} t)
   (side-condition (is-wf-stat Γ stat))
   ----------------------------------- ; (expression block not starting with d)
   (types Γ { stat stat_s ... e } t)]
  
  [------------------------------- ; (type of object construction)
   (types Γ oc (calc-oc-type oc))]
  
  ; we consider the intft returned by (calc-type e) as a Γ
  [(where t (Γ-lookup-val (calc-type e) id))
   ------------------------------------------  ; (e.id)
   (types Γ (sel e id) t)]
    
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

; (eval-type Γ t) evaluates a type expression t in environment Γ
(define-metafunction L-simple-v1+Γ
  eval-type : Γ t -> t
  [(eval-type Γ Void) Void ]         ; Void
  [(eval-type Γ Null) Null ]         ; Null
  [(eval-type Γ primt) primt ]       ; primitive types
  [(eval-type Γ intft) intft ]       ; interface types
  [(eval-type Γ (-> t_arg t_ret))    ; function types
   (-> (eval-type Γ t_arg)
       (eval-type Γ t_ret))]
  [(eval-type Γ (& t_1 t_2))         ; intersection types
   (intersect-ts 
     (eval-type Γ t_1) 
     (eval-type Γ t_2))]
  [(eval-type Γ id)                  ; id referring to type decl
   (Γ-lookup-type Γ id)]
  [(eval-type Γ (var t))             ; reference cells
   (var (eval-type Γ t))]
)
; types given as argument must be  shallowly simplified (evaluated) before
; type returned is also simplified
(define-metafunction L-simple-v1
  intersect-ts : t t -> t or #f
  
  [(intersect-ts t t) t]
  
  [(intersect-ts (-> t_arg t_ret1) (-> t_arg t_ret2))
   (-> t_arg (intersect-ts t_ret1 t_ret2))]
  ; once we have untion types, we can take union on argument type
  
  [(intersect-ts intft_1 intft_2)
   (intersect-intfts intft_1 intft_2)]
  
  [(intersect-ts t_1 t_2) #f] ; incompatible (not "empty type")
)
(define-metafunction L-simple-v1
  intersect-intfts : intft intft -> intft
  [(intersect-intfts intft_1 intft_2)
   (intersect-sorted-intfts (sort-intft intft_1) (sort-intft intft_2))]
)
(define-metafunction L-simple-v1+Γ
  intersect-sorted-intfts : ((val id t) ...) ((val id t) ...) -> ((val id t) ...)
  [(intersect-sorted-intfts 
     ((val id_same t_1) mapping_1 ...) 
     ((val id_same t_2) mapping_2 ...))
   ,(cons (term (val id_same (intersect-ts (eval-type t_1) (eval-type t_2))))
          (term (intersect-sorted-intfts (mapping_1 ...) (mapping_2 ...))))]
  [(intersect-sorted-intfts 
     ((val id_same t_1) mapping_1 ...) 
     (mapping_21 ... (val id_same t_2) mapping_22 ...))
   ,(cons (term (val id_same (intersect-ts (eval-type t_1) (eval-type t_2))))
          (term (intersect-sorted-intfts (mapping_1 ...) (mapping_22 ...))))]
  [(intersect-sorted-intfts 
     (mapping_11 ... (val id_same t_1) mapping_12 ...) 
     ((val id_same t_2) mapping_2 ...))
   ,(cons (term (val id_same (intersect-ts (eval-type t_1) (eval-type t_2))))
          (term (intersect-sorted-intfts (mapping_12 ...) (mapping_2 ...))))]
  [(intersect-sorted-intfts 
     ((val id_1 t_1) mapping_1 ...) 
     ((val id_2 t_2) mapping_2 ...))
   ,(cons (term (val id_1 (eval-type t_1)))
          (cons (term (val id_2 (eval-type t_2)))
                (term (intersect-sorted-intfts (mapping_1 ...) (mapping_2 ...)))))]
  [(intersect-sorted-intfts (mapping_1 ...) ())
   (mapping_1 ...)]
  [(intersect-sorted-intfts () (mapping_2 ...))
   (mapping_2 ...)]
)
(define-metafunction L-simple-v1
  sort-intft : ((val id t) ...) -> ((val id t) ...)
  [(sort-intft ((val id t) ...)) 
   ,(raw-sort-intft (term (id ...)))]
)
(define (raw-sort-intft decls) 
  (sort decls #:key (lambda (x) (symbol->string x)) string<?)
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


; UNUSED ;

#|

; convert mappings from Γ to interface type, taking only value declarations
; and ignoring type declarations.
; Γ_outer is the context needed to construct the type of untyped vds
(define-metafunction L-simple-v1+Γ
  Γ-to-intft : Γ Γ -> intft
  [(Γ-to-intft ()) ()]
  [(Γ-to-intft (mapping_s ... (val id t e)) Γ_outer); typed value declarations
   ((Γ-to-intft (mapping_s) ... (val id t)))]
  [(Γ-to-intft (mapping_s ... (val id e)) Γ_outer)  ; untyped value declarations
   ((Γ-to-intft (mapping_s) ... (val id (calc-e-type Γ_outer e))))]
  [(Γ-to-intft (mapping_s ... (type id t)) Γ_outer) ; ignore type declarations
   (Γ-to-intft (mapping_s ...))]
)


#|
; Γ-extend-with-ds extends Γ with mappings obtained from declarations
; Γ_outer is the context needed to construct the type of untyped vds
(define-metafunction L-simple-v1+Γ
  Γ-extend-with-ds : Γ Γ (d ...) -> Γ
  
  [(Γ-extend-with-ds Γ Γ_outer ()) Γ]
  
  [(Γ-extend-with-ds Γ Γ_outer (d d_s ...))
   (Γ-extend-with-ds 
        (Γ-extend Γ d)
        (Γ-extend Γ_outer d) ; current d visible for subsequent d_s
        (d_s ...))]
) TODO unused?|#


; true iff two identifiers are different
#|(define-metafunction L-simple-v1+Γ
  [(different id_1 id_1) #f]
  [(different id_1 id_2) #t]
)|# ; TODO unused?


; filter-for-ds filters a list of statements, keeping only declarations
(define-metafunction L-simple-v1+Γ
  filter-for-ds : (stat ...) -> (d ...)
  [(filter-for-ds ()) ()]
  [(filter-for-ds (d stat_s ...))
   ((filter-for-ds (stat_s)) ... d)]
  [(filter-for-ds (stat_notd stat_s ...))
   ((filter-for-ds (stat_s)) ...)]
)


#|; (wf-oc Γ oc intft) means that in Γ, oc is a well-formed object construction
; of precisely (no subtype) interface type intft
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-oc I I O)
  #:contract (wf-oc Γ oc intft)
  [(wf-oc Γ oc intft)
   (where intft (calc-oc-type Γ oc))]
) TODO unused?|#

|#

#|
(wf-t Γ t) is not used because we always use eval-type instead

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
  [(wf-t Γ ((val id t) ...))             ; interface type
   (wf-t Γ t) ... ]
  [(wf-t Γ (-> t_arg t_ret))             ; function type
   (wf-t Γ t_arg)
   (wf-t Γ t_ret)]
  [(wf-t Γ (& t_1 t_2))                  ; intersection type currently only for
   (wf-t Γ t_1)
   (wf-t Γ t_2)]
  [(wf-t Γ id)                           ; id referring to a type decl
   (where t (Γ-lookup-type Γ id))]
)
|#
