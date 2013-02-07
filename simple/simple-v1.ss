#lang racket
(require redex)

(provide (all-defined-out))

;;; The Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language L-simple-v1
  (stat                       ; statement
    (ign e)                   ;   `(ign e)` instead of `e;` : ignore void
    { stat stat ... }         ;   block of statements
    d                         ;   type or value declaration
    (println e)               ;   print line
    (if e stat)               ;   if-then with no return value
    (if e stat stat))          ;   if-then-else with no return value
  
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
    (→ t t))                  ;   t -> t
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
    (↦ (id t) e)              ;   anonymous function
    (if e e e)                ;   if then else returning a value
    binop                     ;   binary operator expression
    (sel e id)                ;   e.id
    (cell e)                  ;   a cell storing mutable data. (cell e) is of 
                              ;     type (var t) if e is of type t
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
    void                      ;   returned by functions used as statements
    string)                   ;   string (provided by racket)
  
  (id                         ; identifier
    variable-not-otherwise-mentioned)
)


;;; Technical ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note: In English, both "judgment" and "judgement" are correct, but in redex,
; only "judgment" is correct. Avoid being confused by weird error messages due
; to misspelling that word.

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
  [t-or-#f                   ; a type or #f, meaning that no type was found
    t #f]
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
  Γ-lookup-val : Γ id -> t-or-#f
  [(Γ-lookup-val (mapping_s ... (val id_req t_req)) id_req) 
    t_req]
  [(Γ-lookup-val (mapping_s ... (val id_last t_last)) id_req)
   (Γ-lookup-val (mapping_s ...) id_req)]
  [(Γ-lookup-val () id_req) #f]
)
(define-metafunction L-simple-v1+Γ
  Γ-lookup-type : Γ id -> t-or-#f
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

; (wf-stat Γ stat) means that in Γ, stat is a well-formed statement
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-stat I I)
  #:contract (wf-stat Γ stat)
  [(wf-stat Γ stat)
   (side-condition (is-wf-stat Γ stat))]
)
(define-metafunction L-simple-v1+Γ
  is-wf-stat : Γ stat -> boolean
  [(is-wf-stat Γ d)                         ; view declaration as statement
   (is-wf-d Γ d)]
  [(is-wf-stat Γ (ign e)) #t                ; ign-statement
   (judgment-holds (types Γ e Void))] 
  [(is-wf-stat Γ {})                        ; empty statement block
   #t]
  [(is-wf-stat Γ {d stat_after ...})        ; statement block beginning with d
   (and
     (is-wf-d Γ d)
     (is-wf-stat Γ_new {stat_after ...}))
   (where Γ_new (Γ-extend Γ (d-to-mapping Γ d)))]
  [(is-wf-stat Γ {stat stat_after ...})     ; stat block not beginning with d
   (and
     (is-wf-stat Γ stat)
     (is-wf-stat Γ {stat_after ...}))]  
  [(is-wf-stat Γ (println e)) #t            ; println a primitive type
   (judgment-holds (types Γ e Bool))]
  [(is-wf-stat Γ (if e stat))               ; if-then with no return value
   (is-wf-stat Γ stat)
   (judgment-holds (types Γ e Bool))]
   [(is-wf-stat Γ (if e stat_1 stat_2))     ; if-then-else with no return value
    (and
      (is-wf-stat Γ stat_1)
      (is-wf-stat Γ stat_2))
    (judgment-holds (types Γ e Bool))]
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
  is-wf-d : Γ d -> boolean
  [(is-wf-d Γ (val id t e)) #t            ; typed val decl
   (judgment-holds (subtype Γ (calc-e-type Γ e) t))]
  [(is-wf-d Γ (val id e)) #t              ; untyped val decl
   (where t_unused (calc-e-type Γ e))]
  [(is-wf-d Γ (type id t))                ; type decl
   (is-wf-t Γ t)]
)

; (calc-oc-type Γ oc) returns the interface type of object construction oc
; also typechecks rhs of declarations
(define-metafunction L-simple-v1+Γ
  calc-oc-type : Γ oc -> intft
  [(calc-oc-type Γ ()) []]
  [(calc-oc-type Γ (d d_s ...))
   ; Γs have the same form as intfts :)
   (Γ-extend (calc-oc-type Γ_new (d_s ...)) mapping)
   (judgment-holds (wf-d Γ d))
   (where Γ_new (Γ-extend Γ mapping))
   (where mapping (d-to-mapping Γ d))]
)

; converts a value or type declaration to a mapping which can be stored in a Γ
; Γ_outer is the context needed to construct the type of untyped vds
(define-metafunction L-simple-v1+Γ
  d-to-mapping : Γ_outer d -> mapping
  [(d-to-mapping Γ_outer (val id t e))    ; typed val decl
   (val id t)]
  [(d-to-mapping Γ_outer (val id e))      ; untyped val decl
   (val id t)
   (where t (calc-e-type Γ_outer e))]
  [(d-to-mapping Γ_outer (type id t))     ; type decl
   (type id t)]
)

; (calc-e-type Γ e) returns the type of expression e
(define-metafunction L-simple-v1+Γ
  calc-e-type : Γ e -> t
  [(calc-e-type Γ e) t_1
   (where (t_1) ,(judgment-holds (types Γ e t) t))]
  ; sometimes it finds the same type in two different ways:
  ; TODO why, and can it also be >2x?
  [(calc-e-type Γ e) t_1
   (where (t_1 t_1) ,(judgment-holds (types Γ e t) t))]
)

; (types Γ e t) means that in Γ, e is of type t
(define-judgment-form
  L-simple-v1+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
 
  ; We cannot write this rule, because redex cannot guess t_2:
  ;
  ; [(types Γ e t_1)
  ; (side-condition (subtype Γ t_1 t_2))
  ; ---------------------------------- ; (subsumption)
  ; (types Γ e t_2)]
  ;
  ; Instead, we have to make the function application rule more powerful,
  ; but that's sufficient.
  
  [(types Γ e_fun (→ t_arg2 t_ret))
   (types Γ e_arg t_arg1)
   (subtype Γ t_arg1 t_arg2)
   ------------------------------ ; (Function Application)
   (types Γ (e_fun e_arg) t_ret)]
 
  [(types (mapping ... (val id t_1)) e t_2)
   --------------------------------------------------- ; (Type of anon func)
   (types (mapping ...) (↦ (id t_1) e) (→ t_1 t_2))]
  
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
  
  [--------------------  ; (void literal)
   (types Γ void Void)]
  
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
  
  ; we consider the intft returned by (calc-e-type e) as a Γ
  [(where t (Γ-lookup-val (calc-e-type e) id))
   ------------------------------------------  ; (e.id)
   (types Γ (sel e id) t)]
  
  [(types Γ e t)
   --------------------------- ; (new cell)
   (types Γ (cell e) (var t))]
  
  [(types Γ e (var t))
   ---------------------------------- ; (cell.get)
   (types Γ (sel e get) (→ Void t))]
  
  [(types Γ e (var t))
   ---------------------------------- ; (cell.set)
   (types Γ (sel e set) (→ t Void))]
    
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   -------------------------- ; (integer addition)
   (types Γ (+ e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Str)
   -------------------------- ; (concat Int and Str to Str)
   (types Γ (+ e_1 e_2) Str)]
 
  [(types Γ e_1 Str)
   (types Γ e_2 Int)
   -------------------------- ; (concat Str and Int to Str)
   (types Γ (+ e_1 e_2) Str)]
  
  [(types Γ e_1 Str)
   (types Γ e_2 Str)
   -------------------------- ; (concat two strings)
   (types Γ (+ e_1 e_2) Str)]
  
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   -------------------------- ; (logical and)
   (types Γ (&& e_1 e_2) Bool)]
    
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   -------------------------- ; (logical or)
   (types Γ (|| e_1 e_2) Bool)]
  
  [(types Γ e_1 Str)
   (types Γ e_2 Str)
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

; (sub t_1 t_2) means that t_1 <: t_2
; t_1 and t_2 must be evaluated before
(define-judgment-form
  L-simple-v1+Γ
  #:mode (sub I I)
  ; Also accepts #f as arg, because that's what unsuccessful lookup returns,
  ; but if one or both args are #f, the judgment never holds.
  #:contract (sub t-or-#f t-or-#f)
  
  [----------------
   (sub Void Void)]
  
  [----------------
   (sub Null Null)]
  
  [------------------
   (sub primt primt)]
  
  [---------------
   (sub intft [])]
  
  [(sub (Γ-lookup-val intft_1 id_2) t_2) ; val is covariant 
   (sub intft_1 [(val id_2rest t_2rest) ...])
   ----------------------------------------------------------
   (sub intft_1 [(val id_2 t_2) (val id_2rest t_2rest) ...])]
  
  [(sub t_arg2 t_arg1)
   (sub t_ret1 t_ret2)
   --------------------------------------------
   (sub (→ t_arg1 t_ret1) (→ t_arg2 t_ret2))]
  
  [(sub t_1 t_2)
   (sub t_2 t_1)
   -----------------------------
   (sub (var t_1) (var t_2))]
)


; (subtype Γ t_1 t_2) means that in Γ, t_1 <: t_2
; t_1 and t_2 are evaluated in Γ
(define-judgment-form
  L-simple-v1+Γ
  #:mode (subtype I I I)
  #:contract (subtype Γ t t)
  [(subtype Γ t_1 t_2)
   (sub (eval-type Γ t_1) (eval-type Γ t_2))]
)

; two types are equal iff each is a subtype of the other
; types must be simplified before
(define-metafunction L-simple-v1+Γ
  types-equal : t t -> boolean
  [(types-equal t_1 t_2) #t
   (judgment-holds (sub t_1 t_2))
   (judgment-holds (sub t_2 t_1))]
  [(types-equal t_1 t_2) #f]
)

; (is-wf-t Γ t) rejects e.g. bad type intersections
(define-metafunction L-simple-v1+Γ
  is-wf-t : Γ t -> boolean
  [(is-wf-t Γ t) #t
   (where t_2 (eval-type Γ t))]
)

; (eval-type Γ t) evaluates a type expression t in environment Γ
(define-metafunction L-simple-v1+Γ
  eval-type : Γ t -> t
  [(eval-type Γ Void) Void ]         ; Void
  [(eval-type Γ Null) Null ]         ; Null
  [(eval-type Γ primt) primt ]       ; primitive types
  [(eval-type Γ ((val id t) ...))    ; interface types
   ((val id (eval-type Γ t)) ...)]
  [(eval-type Γ (→ t_arg t_ret))    ; function types
   (→ (eval-type Γ t_arg)
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

; We don't (yet) have union types, but in some special cases, it is still 
; possible to calculate the union of two types.
; Types given as argument must be simplified (evaluated) before.
; Type returned is also simplified.
(define-metafunction L-simple-v1+Γ
  union-ts : t t -> t
  [(union-ts t_1 t_2)
   t_1
   (judgment-holds (sub t_2 t_1))]
  [(union-ts t_1 t_2)
   t_2
   (judgment-holds (sub t_1 t_2))]
)

; types given as argument must be simplified (evaluated) before
; type returned is also simplified
(define-metafunction L-simple-v1
  intersect-ts : t t -> t
  [(intersect-ts t_1 t_2)
   t_1
   (judgment-holds (sub t_1 t_2))]
  [(intersect-ts t_1 t_2)
   t_2
   (judgment-holds (sub t_2 t_1))]
  [(intersect-ts (→ t_arg1 t_ret1) (→ t_arg2 t_ret2))
   (→ (union-ts t_arg1 t_arg2) (intersect-ts t_ret1 t_ret2))]  
  [(intersect-ts intft_1 intft_2)
   (intersect-intfts intft_1 intft_2)]  
  ; It can happen that two types are incompatible for intersection,
  ; e.g. Str and Int. In such cases, there is no match, and it crashes.
)

; intersects two interface types which do not need to be sorted
(define-metafunction L-simple-v1
  intersect-intfts : intft intft -> intft
  [(intersect-intfts 
     ((val id_same t_1) (val id_1r t_1r) ...)
     ((val id_2l t_2l) ... (val id_same t_2) (val id_2r t_2r) ...))
   ,(cons (term (val id_same (intersect-ts t_1 t_2)))
          (term (intersect-intfts 
              ((val id_1r t_1r) ...) 
              ((val id_2l t_2l) ... (val id_2r t_2r) ...))))]
  [(intersect-intfts
     ((val id_1 t_1) (val id_1r t_1r) ...)
     ((val id_2r t_2r) ...))
   ,(cons (term (val id_1 t_1))
          (term (intersect-intfts 
              ((val id_1r t_1r) ...)
              ((val id_2r t_2r) ...))))]
  [(intersect-intfts () ((val id_s t_s) ...))
   ((val id_s t_s) ...)]
)


;;; Reduction Relation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO merge all grammars into one language because
; Note that define-extended-language is a nice idea, but would cause much
; code duplication. For instance, (cl myFunc (+ arg 1) ()) is a runtime 
; expression, but not a compile time expression, so it is not allowed in
; L-simple-v1, but only added in L-simple-v1-Ev. But then, e has to be redefined
; in L-simple-v1-Ev, because e now also can be a closure. Finally, 
; L-simple-v1-Ev is has to be a duplicate of L-simple-v1, with some details 
; changed. 
; Conclusion: Don't use define-extended-language and put everything into one
; language. Disadvantage: Source code can contain constructs which should not
; be written at compile time, but only be created at run time.

(define-extended-language L-simple-v1-Ev L-simple-v1+Γ
  (se                         ; simplified (evaluated) expression ("value")
    sre                       ;   simplified reference (= "not primitive") expr
    literal)                  ;   simplified expression of primitive type
  (sre                        ; simplified reference expression
    soc                       ;   simplified object construction
    (cid natural)             ;   reference to a cell, cid = cell id
    (getter natural)          ;   get function of a cell
    (setter natural)          ;   set function of a cell
    (cl id e (vv ...)))       ;   anonymous function (closure) with environment
  (soc                        ; simplified object construction
    ((val id se) ...))        ;   types are erased

  (vv                         ; val value
    (id se))                  ;   maps an id to its value
  (cv                         ; cell value
    (natural se))             ;   maps a natural-id to the current value of cell

  (pstate                      ; state of program execution
    (e (vv ...) (cv ...)))    ;   expr to evaluate, val values, cell values

  (state                      ; state of program execution, with one hole
    (E (vv ...) (cv ...)))    ;   expr to evaluate, val values, cell values
  
  (S                          ; statement with a hole to evaluate
    (ign E)                   ;   `(ign e)` instead of `e;` : ignore void
    { S stat ... }            ;   evaluate one after the other statement
    (val id t E)              ;   typed value declaration
    (val id E)                ;   untyped value declaration
    (println E)               ;   print line
    (if E stat)               ;   if-then with no return value
    (if E stat stat)          ;   if-then-else with no return value
    stat-done)                ;   a "done" (executed) statement
  
  (E                          ; expression with a hole to evaluate
    ((cl id e (vv ...)) E)    ;   1) simplify function 2) simpl. arg 3) apply
    ( (val id_s se_s) ...     ;   object construction with evaluated part,
      (val id t E)            ;     part to evaluate,
      d ...)                  ;     and not yet evaluated part
    ( (val id_s se_s) ...     ;   dito, but
      (val id E)              ;     val decl is untyped
      d ...)                  ;
    {S stat ... e}            ;   block expression
    {E}                       ;
    (if E e e)                ;   if
    (sel E id)                ;   e.id
    (cell E)                  ;   new cell storing mutable value
    (&& E e)                  ;   logical and
    (&& #t E)                 ;     lazy evaluation (only if first is true)
    (|| E e)                  ;   logical or
    (|| #f E)                 ;     lazy
    (== E e)                  ;   equality
    (== se E)                 ;   
    (< E e)                   ;   less than for integers
    (< number E)              ;   
    (+ E e)                   ;   integer addition or string concatenation
    (+ se E)                  ;   
    (- E e)                   ;   integer subtraction
    (- number E)              ;   
    (* E e)                   ;   integer multiplication
    (* number E)              ;   
    (/ E e)                   ;   integer division
    (/ number E)              ;
    hole)                     ;   hole
)

(define red
  (reduction-relation
    L-simple-v1-Ev
    #:domain pstate
    
    (--> (in-hole state {(type id t) stat ...})
         (in-hole state {stat ...})
         "{t}") ; ignore type declaration inside block statement
    (--> (in-hole state {(type id t) stat ... e})
         (in-hole state {stat ... e})
         "{t-e}") ; ignore type declaration inside block expression
         
    (--> (in-hole (E (vv ...)         (cv ...)) {(val id t se) stat ...})
         (in-hole (E (vv ... (id se)) (cv ...)) {stat ...})
         "{tv}") ; typed value inside block statement
    (--> (in-hole (E (vv ...)         (cv ...)) {(val id t se) stat ... e})
         (in-hole (E (vv ... (id se)) (cv ...)) {stat ... e})
         "{tv-e}") ; typed value inside block expression
    (--> (in-hole (E (vv ...)         (cv ...)) {(val id se) stat ...})
         (in-hole (E (vv ... (id se)) (cv ...)) {stat ...})
         "{utv}") ; untyped value inside block statement
    (--> (in-hole (E (vv ...)         (cv ...)) {(val id se) stat ... e})
         (in-hole (E (vv ... (id se)) (cv ...)) {stat ... e})
         "{utv-e}") ; untyped value inside block expression
    
    (--> (in-hole state (println literal))
         ,(begin
            (printf "~a\n" (term literal))
            (term (in-hole state stat-done)))
         "println")
    
    (--> (in-hole state (if true stat))
         (in-hole state stat)
         "if-t-s") ; if true statement
    (--> (in-hole state (if false stat))
         (in-hole state stat-done)
         "if-f-s") ; if false statement
    (--> (in-hole state (if true stat_1 stat_2))
         (in-hole state stat_1)
         "if-t-s1s2") ; if true
    (--> (in-hole state (if false stat_1 stat_2))
         (in-hole state stat_2)
         "if-f-s1s2") ; if false
    
    (--> (in-hole (E (vv_env ... ) (cv ...)) 
                  ((cl id e (vv_cl ...)) se_arg))
         (in-hole (E (vv_cl ... (id se_arg)) (cv ...)) 
                  e)
         "apply")
    
    (--> (in-hole (E (vv_before ... (id se) vv_after ...) (cv ...)) id)
         (in-hole (E (vv_before ... (id se) vv_after ...) (cv ...)) se)
         "lookup") ; lookup value
    
    (--> (in-hole (E (vv ...) (cv ...)) (↦ (id t) e))
         (in-hole (E (vv ...) (cv ...)) (cl id e (vv ...)))
         "new-cl") ; closure creation
    
    (--> (in-hole state ( (val id_s se_s) ...
                          (type id t)
                          d ...))
         (in-hole state ( (val id_s se_s) ...
                          d ...))
         "oc-t") ; object construction ignore type declaration
    
    (--> (in-hole (E (vv ...) (cv ...)) ( (val id_s se_s) ...
                                          (val id se)
                                          d ...))
         (in-hole (E (vv ... (id se)) (cv ...)) ( (val id_s se_s) ... 
                                                  (val id se)
                                                  d ...))
         "oc-utv") ; object construction untyped value
    (--> (in-hole (E (vv ...) (cv ...)) ( (val id_s se_s) ...
                                          (val id t se)
                                          d ...))
         (in-hole (E (vv ... (id se)) (cv ...)) ( (val id_s se_s) ... 
                                                  (val id se)
                                                  d ...))
         "oc-tv") ; object construction typed value
    
    (--> (in-hole state {stat-done})
         (in-hole state stat-done)
         "{}")
    (--> (in-hole state {se})
         (in-hole state se)
         "{se}")
    (--> (in-hole state {stat-done stat ...})
         (in-hole state {stat ...})
         "{sd}") ; stat-done in block statement
    (--> (in-hole state {stat-done stat ... e})
         (in-hole state {stat ... e})
         "{sd-e}") ; stat-done in block expression
    
    (--> (in-hole state (ign void))
         (in-hole state stat-done)
         "ign") ; ignore void return value of statement
    
    (--> (in-hole state (if true e_1 e_2))
         (in-hole state e_1)
         "if-t")
    (--> (in-hole state (if false e_1 e_2))
         (in-hole state e_2)
         "if-f")
    
    (--> (in-hole state (sel ( (val id_before se_before) ... 
                               (val id_req se_req) 
                               (val id_after se_after) ...)
                             id_req))
         (in-hole state se_req)
         "sel")
    
    (--> (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  (sel (cid natural) get))
         (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  (getter natural))
         "cell.get")
    (--> (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  (sel (cid natural) set))
         (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  (setter natural))
         "cell.set")
    (--> (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  ((getter natural) ()))
         (in-hole (E (vv ...) (cv_before ... (natural se) cv_after ...))
                  se)
         "apply-get")
    (--> (in-hole (E (vv ...) (cv_before ... (natural se_old) cv_after ...))
                  ((setter natural) se_new))
         (in-hole (E (vv ...) (cv_before ... (natural se_new) cv_after ...))
                  void)
         "apply-set")
    
    (--> (in-hole (E (vv ...) (cv ...)) (cell se))
         (in-hole (E (vv ...) (cv ... (n se))) (cid n))
         (where n (new-cid (cv ...)))
         "new-cell")
    
    (--> (in-hole state (&& false e    )) (in-hole state false) "&&f"  )
    (--> (in-hole state (&& true  false)) (in-hole state false) "&&tf" )
    (--> (in-hole state (&& true  true )) (in-hole state true ) "&&tt" )
    (--> (in-hole state (|| true  e    )) (in-hole state true ) "||t"  )
    (--> (in-hole state (|| false true )) (in-hole state true ) "||ft" )
    (--> (in-hole state (|| false false)) (in-hole state false) "||ff" )
    (--> (in-hole state (== true  true )) (in-hole state true ) "==tt" )
    (--> (in-hole state (== true  false)) (in-hole state false) "==tf" )
    (--> (in-hole state (== false true )) (in-hole state false) "==ft" )
    (--> (in-hole state (== false false)) (in-hole state true ) "==ff" )
    
    (--> (in-hole state (== string string)) 
         (in-hole state true)
         "==ss")
    (--> (in-hole state (== string_1 string_2)) 
         (in-hole state false)
         (side-condition (not (equal? (term string_1) (term string_2))))
         "==s1s2")
    (--> (in-hole state (== number number)) 
         (in-hole state true)
         "==nn")
    (--> (in-hole state (== number_1 number_2)) 
         (in-hole state false)
         (side-condition (not (equal? (term number_1) (term number_2))))
         "==n1n2")    
    (--> (in-hole state (< number_1 number_2)) 
         (in-hole state true) 
         (side-condition (< (term number_1) (term number_2)))
         "<n1n2")
    (--> (in-hole state (< number_1 number_2)) 
         (in-hole state false) 
         (side-condition (not (< (term number_1) (term number_2))))
         "!<n1n2")
    
    (--> (in-hole state (+ number_1 number_2)) 
         (in-hole state ,(+ (term number_1) (term number_2)))
         "+n1n2")
    (--> (in-hole state (+ number string)) 
         (in-hole state ,(string-append (~a (term number)) (term string)))
         "+ns")
    (--> (in-hole state (+ string number)) 
         (in-hole state ,(string-append (term string) (~a (term number))))
         "+sn")
    (--> (in-hole state (+ string_1 string_2)) 
         (in-hole state ,(string-append (term string_1) (term string_2)))
         "+s1s2")
    
    (--> (in-hole state (- number_1 number_2)) 
         (in-hole state ,(- (term number_1) (term number_2)))
         "-n1n2")
    (--> (in-hole state (* number_1 number_2)) 
         (in-hole state ,(* (term number_1) (term number_2)))
         "*n1n2")
    (--> (in-hole state (/ number_1 number_2)) 
         (in-hole state ,(/ (term number_1) (term number_2)))
         "/n1n2")
))

; returns lowest natural not used as id in list of cell values
; assumes that it is sorted by ascending id
(define-metafunction L-simple-v1-Ev
  new-cid : (cv ...) -> natural
  [(new-cid ()) 0]
  [(new-cid ((natural_before se_before) ... (natural_last se_last)))
   ,(+ (term natural_last) 1)]
)

; UNUSED ;

#|
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
   ,(cons (term (val id_same (intersect-ts t_1 t_2)))
          (term (intersect-sorted-intfts (mapping_1 ...) (mapping_2 ...))))]
  [(intersect-sorted-intfts 
     ((val id_same t_1) mapping_1 ...) 
     (mapping_21 ... (val id_same t_2) mapping_22 ...))
   ,(cons (term (val id_same (intersect-ts t_1 t_2)))
          (term (intersect-sorted-intfts (mapping_1 ...) (mapping_22 ...))))]
  [(intersect-sorted-intfts 
     (mapping_11 ... (val id_same t_1) mapping_12 ...) 
     ((val id_same t_2) mapping_2 ...))
   ,(cons (term (val id_same (intersect-ts t_1 t_2)))
          (term (intersect-sorted-intfts (mapping_12 ...) (mapping_2 ...))))]
  [(intersect-sorted-intfts 
     ((val id_1 t_1) mapping_1 ...) 
     ((val id_2 t_2) mapping_2 ...))
   ,(if (string<? (symbol->string (term id_1))
                  (symbol->string (term id_2)))
       (cons (term (val id_1 t_1))
          (cons (term (val id_2 t_2))
             (term (intersect-sorted-intfts (mapping_1 ...) (mapping_2 ...)))))
       (cons (term (val id_2 t_2))
          (cons (term (val id_1 t_1))
             (term (intersect-sorted-intfts (mapping_1 ...) (mapping_2 ...))))))
   ]
  [(intersect-sorted-intfts (mapping_1 ...) ())
   (mapping_1 ...)]
  [(intersect-sorted-intfts () (mapping_2 ...))
   (mapping_2 ...)]
)
(define-metafunction L-simple-v1
  sort-intft : ((val id t) ...) -> ((val id t) ...)
  [(sort-intft ((val id t) ...)) 
   ,(raw-sort-intft (term ((val id t) ...)))]
)
(define (raw-sort-intft decls) 
  (sort decls #:key (lambda (x) (symbol->string (cadr x))) string<?)
)
|#

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
)|#


; true iff two identifiers are different
#|(define-metafunction L-simple-v1+Γ
  [(different id_1 id_1) #f]
  [(different id_1 id_2) #t]
)|# 


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
)|#

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
  [(wf-t Γ (→ t_arg t_ret))             ; function type
   (wf-t Γ t_arg)
   (wf-t Γ t_ret)]
  [(wf-t Γ (& t_1 t_2))                  ; intersection type currently only for
   (wf-t Γ t_1)
   (wf-t Γ t_2)]
  [(wf-t Γ id)                           ; id referring to a type decl
   (where t (Γ-lookup-type Γ id))]
)
|#

  
#|
; (wf-prog prog) means that prog is a well-formed program
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-prog I)
  #:contract (wf-prog prog)
  [(wf-prog prog)
   ; just check if prog is a well-formed statement in the empty enviroment
   (side-condition (is-wf-stat () prog))]
)
|#
  