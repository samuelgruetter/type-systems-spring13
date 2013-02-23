#lang racket
(require redex)

(provide (all-defined-out))

;;; The Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language L
  (stat                       ; statement
    statnd                    ;   statement which is not a declaration
    d)                        ;   type or value declaration
  
  (statnd                     ; statement which is not a declaration
    (ign e))                  ;   (ign e) instead of e; : ignore void
                              ;   for a block of statements, use
                              ;     (ign { stat_s ... void })
                              ;   println not part of language, but in library
                              ;   for an if-then with no return value, use
                              ;     (ign (if e {stat void} void))
                              ;   for an if-then-else with no return value, use
                              ;     (ign (if e {stat_1 void} {stat_2 void}))
  
  (d                          ; declaration
    vd                        ;   value declaration
    td)                       ;   type declaration
  
  (vd                         ; value declaration
    ;(val id t e)             ;   typed vd omitted for simplicity
    (val id e))               ;   untyped vd
  
                              ; always keep in mind that an id can refer to a
                              ; value, but also to a type
  
  (td                         ; type declaration
    (type id t))              ;   allowed wherever vd is allowed
  
  (t                          ; type expression
    Void                      ;   the type of `void`
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

  (e                          ; any expression (but not a type expression)
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
    literal                   ;   literal
    rtse                      ;   runtime simplified expression
    peoc)                     ;   partially evaluated oc (runtime)
  
  (oc                         ; object construction
    (d ...))                  ;   (possibly empty) list of declarations
  
  (binop                      ; binary operator expression
    (== e e)                  ;   equality for primitive types
    (< e e)                   ;   less than for integers
    (+ e e)                   ;   integer addition or string concatenation
    (- e e)                   ;   integer subtraction
    (* e e)                   ;   integer multiplication
    (/ e e))                  ;   integer division
   
  (literal                    ; literal
    number                    ;   integer (provided by racket)
    true                      ;   boolean
    false                     ;   boolean
    void                      ;   returned by functions used as statements
    string)                   ;   string (provided by racket)
  
  (id                         ; identifier
    variable-not-otherwise-mentioned)
  
  ; typing environment Γ
  ; Usually, Γ is only used to store mappings of the form (valName -> itsType).
  ; But here, we also use it to store mappings of the form (typeAlias -> aType).
  ; We store it in the same environment, because in a given context, we do not
  ; allow a value and a type to have the same name.
  ; To distinguish whether the mapping is (myValName -> itsType) or 
  ; (myTypeAlias -> aType), we prefix them with `val` or `type`.
  (mapping                    ; Γ item
    (val id t)                ;   (myValName -> itsType)
    (type id t))              ;   (myTypeAlias -> aType)
  (Γ                          ; typing environment
    (mapping ...))            ;   list of mappings
  (Γ-or-#f                    ; a Γ or #f, meaning that Γ could not be extended
    Γ #f)
  
  ; definitions needed for the reduction relation
  
  (peoc                       ; partially evaluated object construction
    ((id se) ... d ...))      ;   
  
  (rtse                       ; se which only exists at runtime
    (cid natural)             ;   reference to a cell, cid = cell id
    (getter natural)          ;   get function of a cell
    (setter natural)          ;   set function of a cell
    (cl id e (vv ...)))       ;   anonymous function (closure) with environment
  
  (se                         ; simplified (evaluated) expression ("value")
    sre                       ;   simplified reference (= "not primitive") expr
    literal)                  ;   simplified expression of primitive type
  (sre                        ; simplified reference expression
    soc                       ;   simplified object construction
    rtse)                     ;   runtime simplified expression
  (soc                        ; simplified object construction
    ((id se) ...))            ;   types are erased, val keyword is removed

  (vv                         ; val value
    (id se))                  ;   maps an id to its value
  (cv                         ; cell value
    (natural se))             ;   maps a natural-id to the current value of cell

  (pstate                     ; state of program execution
    (e (vv ...) (cv ...)))    ;   expr to evaluate, val values, cell values

  (state                      ; state of program execution, with one hole
    (E (vv ...) (cv ...)))    ;   expr to evaluate, val values, cell values
  
  (S                          ; statement with a hole to evaluate
    (ign E)                   ;   (ign e) instead of e; : ignore void
    (val id E)                ;   untyped value declaration
    stat-done)                ;   a "done" (executed) statement
  
  (E                          ; expression with a hole to evaluate
    (E e)                     ;   1) simplify function 
    ((cl id e (vv ...)) E)    ;   2) simplify arg 
                              ;   3) apply (cf reduction rule "apply")
    ( (id_s se_s) ...         ;   object construction with evaluated part,
      (val id E)              ;     part to evaluate,
      d ...)                  ;     and not yet evaluated part
    {S stat ... e}            ;   block expression
    {E}                       ;
    (if E e e)                ;   if
    (sel E id)                ;   e.id
    (cell E)                  ;   new cell storing mutable value
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


;;; Technical ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note on define-extended-language:
; The define-extended-language directive is a nice idea, but would cause much
; code duplication. For instance, (cl myFunc (+ arg 1) ()) is a runtime 
; expression, but not a compile time expression, so it is not allowed in
; L, but only added in L-Ev. But then, e has to be redefined in L-Ev as e-Ev, 
; because e now also can be a closure. But now every non-terminal using an e
; also needs to be redefined, replacing e by e-Ev. Finally, L-Ev is has to be a
; duplicate of L, with some details changed. 
; Conclusion: Don't use define-extended-language and put everything into one
; language. Disadvantage: Source code can contain constructs which should not
; be written at compile time, but only be created at run time.

; Note on spelling:
; In English, both "judgment" and "judgement" are correct, but in redex,
; only "judgment" is correct. Avoid being confused by weird error messages due
; to misspelling that word.

#|
(define-metafunction L
  not-in-Γ : Γ id -> boolean
  [(not-in-Γ (mapping_before ... (val  id t) mapping_after ...) id) #f]
  [(not-in-Γ (mapping_before ... (type id t) mapping_after ...) id) #f]
  [(not-in-Γ Γ id) #t]
)|#

(define-metafunction L
  extend : Γ mapping -> Γ or #f
  [(extend (mapping_i ... (val  id t_1) mapping_j ...) (val  id t_2)) #f]
  [(extend (mapping_i ... (type id t_1) mapping_j ...) (val  id t_2)) #f]
  [(extend (mapping_i ... (val  id t_1) mapping_j ...) (type id t_2)) #f]
  [(extend (mapping_i ... (type id t_1) mapping_j ...) (type id t_2)) #f]
  [(extend (mapping_i ...) mapping_new) (mapping_i ... mapping_new)]
)

(define-metafunction L
  not-in-vvs : (vv ...) id -> boolean
  [(not-in-vvs (vv_before ... (id se) vv_after ...) id) #f]
  [(not-in-vvs (vv ...) id) #t]
)

(define-metafunction L
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t]
)

;;; Typechecking ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (types Γ e t) means that in Γ, e is of type t
(define-judgment-form L
  #:mode (types I I O)
  #:contract (types Γ-or-#f e t)
  
  ; We cannot write this rule, because redex runs into an infinite loop:
  ; 
  ; [(types Γ e t)
  ;  (where t_simpl (eval-type Γ t))
  ;  (side-condition (different t t_simpl)) ; <- does not help
  ;  -------------------------------------- ; (simplify type)
  ;  (types Γ e t_simpl)]
  ;
  ; Instead, each rule whose "input" are types from the source code has
  ; to call eval-type.
 
  ; We cannot write this rule, because redex cannot guess t_2:
  ;
  ; [(types Γ e t_1)
  ; (side-condition (subtype Γ t_1 t_2))
  ; ------------------------------------ ; (subsumption)
  ; (types Γ e t_2)]
  ;
  ; Instead, we have to subtyping in function application and in typed val
  ; decls, but that's sufficient.
  
  [(types Γ e_fun (→ t_arg2 t_ret))
   (types Γ e_arg t_arg1)
   (subtype Γ t_arg1 t_arg2)
   --------------------------------                 ; (function application)
   (types Γ (e_fun e_arg) t_ret)]
 
  [(types (extend Γ (val id t_1)) e t_2)
   ----------------------------------------         ; (type of anon func)
   (types Γ (↦ (id t_1) e) (→ t_1 t_2))]
  
  [(where (mapping_i ... (val id t) mapping_j ...) Γ)
   ------------------------------------------------ ; (lookup)
   (types Γ id t)]
  
  [--------------------                             ; (integer literals)
   (types Γ number Int)]
  
  [--------------------                             ; (string literals)
   (types Γ string Str)]
  
  [--------------------                             ; (boolean literal)
   (types Γ true Bool)]
  
  [--------------------                             ; (boolean literal)
   (types Γ false Bool)]
  
  [--------------------                             ; (void literal)
   (types Γ void Void)]
   
  [(types Γ e_1 Bool)
   (types Γ e_2 t_2)
   (types Γ e_3 t_3)
   ---------------------------------------------    ; (if-then-else expression)
   (types Γ (if e_1 e_2 e_3) (union-ts t_2 t_3))]
  
  [(types Γ e t)
   -----------------                                ; (block of one expr)
   (types Γ {e} t)]
    
  [(types Γ e t)
   (where Γ_new (extend Γ (val id t)))
   (types Γ_new {stat_s ... e_last} t_last)         
   ------------------------------------------------ ; (block starting with vd)
   (types Γ {(val id e) stat_s ... e_last} t_last)]
  
  [(where t_simpl (eval-type Γ t))
   (where Γ_new (extend Γ (type id t_simpl)))
   (types Γ_new {stat_s ... e_last} t_last)
   ------------------------------------------------ ; (block starting with td)
   (types Γ {(type id t) stat_s ... e_last} t_last)]
  
  [(types Γ {stat_s ... e} t)
   (types Γ e_void Void)
   ------------------------------------------       ; (block starting with ign)
   (types Γ { (ign e_void) stat_s ... e } t)]
  
  [----------------                                 ; (type of empty oc)
   (types Γ () [])]
    
  [(types Γ e t)
   (where Γ_new (extend Γ (val id t)))
   (types Γ_new (d_s ...) intft)
   (where intft_new (extend intft (val id t)))
   -------------------------------------------      ; (oc starting with vd)
   (types Γ ((val id e) d_s ...) intft_new)]
  
  [(where t_simpl (eval-type Γ t))
   (where Γ_new (extend Γ (type id t_simpl)))
   (types Γ_new (d_s ...) intft)
   ------------------------------------------       ; (oc starting with td)
   (types Γ ((type id t) d_s ...) intft)]
  
  [(types Γ e [mapping_i ... 
               (val id t) 
               mapping_j ...])
   ---------------------------                      ; (e.id)
   (types Γ (sel e id) t)]
  
  [(types Γ e t)
   ---------------------------                      ; (new cell)
   (types Γ (cell e) (var t))]
  
  [(types Γ e (var t))
   ----------------------------------               ; (cell.get)
   (types Γ (sel e get) (→ Void t))]
  
  [(types Γ e (var t))
   ----------------------------------               ; (cell.set)
   (types Γ (sel e set) (→ t Void))]
    
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   --------------------------                       ; (integer addition)
   (types Γ (+ e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Str)
   --------------------------                       ; (concat Int + Str to Str)
   (types Γ (+ e_1 e_2) Str)]
 
  [(types Γ e_1 Str)
   (types Γ e_2 Int)
   --------------------------                       ; (concat Str + Int to Str)
   (types Γ (+ e_1 e_2) Str)]
  
  [(types Γ e_1 Str)
   (types Γ e_2 Str)
   --------------------------                       ; (concat two strings)
   (types Γ (+ e_1 e_2) Str)]
  
  [(types Γ e_1 Str)
   (types Γ e_2 Str)
   ----------------------------                     ; (String equality)
   (types Γ (== e_1 e_2) Bool)]
  
  [(types Γ e_1 Bool)
   (types Γ e_2 Bool)
   ----------------------------                     ; (Bool equality)
   (types Γ (== e_1 e_2) Bool)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   ----------------------------                     ; (Int equality)
   (types Γ (== e_1 e_2) Bool)]
  
  ; Note: for equality on objects, define an equals method (as in Java)
  ; == object comparision by address is not supported
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   ---------------------------                      ; (Int <)
   (types Γ (< e_1 e_2) Bool)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   --------------------------                       ; (Int subtraction)
   (types Γ (- e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   --------------------------                       ; (Int multiplication)
   (types Γ (* e_1 e_2) Int)]
  
  [(types Γ e_1 Int)
   (types Γ e_2 Int)
   --------------------------                       ; (Int division)
   (types Γ (/ e_1 e_2) Int)]
  
)

; convenience method for testing
(define-judgment-form L
  #:mode (types-as I I)
  #:contract (types-as e t)
  [(types {} e t_1)
   (subtype {} t_1 t_2)
   ------------------
   (types-as e t_2)]
)


; (sub t_1 t_2) means that t_1 <: t_2
; t_1 and t_2 must be evaluated before
(define-judgment-form L
  #:mode (sub I I)
  
  ; Also accepts #f as arg, because that's what unsuccessful lookup returns,
  ; but if one or both args are #f, the judgment never holds.
  ; #:contract (sub t-or-#f t-or-#f)
  
  #:contract (sub t t)
  
  [----------------
   (sub Void Void)]
  
  [------------------
   (sub primt primt)]
  
  [---------------
   (sub intft [])]
  
  ; (sub intft_b intft_a) is defined by recursion on length of intft_a.
  [(sub t_b t_a) ; covariance
   (sub [(val id_b1 t_b1) ... (val id t_b) (val id_b2 t_b2) ...]
        [(val id_a1 t_a1) ...])
   -------------------------------------------------------------
   (sub [(val id_b1 t_b1) ... (val id t_b) (val id_b2 t_b2) ...]
        [(val id t_a) (val id_a1 t_a1) ...])]
  
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
(define-judgment-form L
  #:mode (subtype I I I)
  #:contract (subtype Γ t t)
  [(subtype Γ t_1 t_2)
   (sub (eval-type Γ t_1) (eval-type Γ t_2))]
)

; two types are equal iff each is a subtype of the other
; types must be simplified before
(define-metafunction L
  types-equal : t t -> boolean
  [(types-equal t_1 t_2) #t
   (judgment-holds (sub t_1 t_2))
   (judgment-holds (sub t_2 t_1))]
  [(types-equal t_1 t_2) #f]
)

; (eval-type Γ t) evaluates a type expression t in environment Γ
(define-metafunction L
  eval-type : Γ t -> t
  [(eval-type Γ Void) Void ]         ; Void
  [(eval-type Γ primt) primt ]       ; primitive types
  [(eval-type Γ ((val id t) ...))    ; interface types
   ((val id (eval-type Γ t)) ...)]
  [(eval-type Γ (→ t_arg t_ret))     ; function types
   (→ (eval-type Γ t_arg)
       (eval-type Γ t_ret))]
  [(eval-type Γ (& t_1 t_2))         ; intersection types
   (intersect-ts 
     (eval-type Γ t_1) 
     (eval-type Γ t_2))]
  [(eval-type                        ; id referring to type decl
     (mapping_before ... (type id t) mapping_after ...) id)
   t]
  [(eval-type Γ (var t))             ; reference cells
   (var (eval-type Γ t))]
)

; We don't (yet) have union types, but if one is a subtype of the other, it is
; possible to calculate the union of two types.
; Types given as argument must be simplified (evaluated) before.
; Type returned is also simplified.
(define-metafunction L
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
(define-metafunction L
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
(define-metafunction L
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

(define red
  (reduction-relation
    L
    #:domain pstate
    
    (--> (in-hole state {(type id t) stat ... e})
         (in-hole state {stat ... e})
         "{t-e}") ; ignore type declaration inside block expression
         
    (--> (in-hole (E (vv ...)         (cv ...)) {(val id se) stat ... e})
         (in-hole (E (vv ... (id se)) (cv ...)) {stat ... e})
         (side-condition (term (not-in-vvs (vv ...) id)))
         "{utv-e}") ; untyped value inside block expression
    
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
    
    (--> (in-hole state ( (id_s se_s) ...
                          (type id t)
                          d ...))
         (in-hole state ( (id_s se_s) ...
                          d ...))
         "oc-t") ; object construction ignore type declaration
    
    (--> (in-hole (E (vv ...) (cv ...)) ( (id_s se_s) ...
                                          (val id se)
                                          d ...))
         (in-hole (E (vv ... (id se)) (cv ...)) ( (id_s se_s) ... 
                                                  (id se)
                                                  d ...))
         (side-condition (term (not-in-vvs (vv ...) id)))
         "oc-utv") ; object construction untyped value
    
    (--> (in-hole state {stat-done})
         (in-hole state stat-done)
         "{}")
    (--> (in-hole state {se})
         (in-hole state se)
         "{se}")
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
(define-metafunction L
  new-cid : (cv ...) -> natural
  [(new-cid ()) 0]
  [(new-cid ((natural_before se_before) ... (natural_last se_last)))
   ,(+ (term natural_last) 1)]
)

; UNUSED ;

#|
; (calc-oc-type Γ oc) returns the interface type of object construction oc
; also typechecks rhs of declarations
(define-metafunction L
  calc-oc-type : Γ oc -> intft
  [(calc-oc-type Γ ()) []]
  [(calc-oc-type Γ (d d_s ...))
   ; Γs have the same form as intfts :)
   (Γ-extend (calc-oc-type Γ_new (d_s ...)) mapping)
   (judgment-holds (wf-d Γ d))
   (where Γ_new (Γ-extend Γ mapping))
   (where mapping (d-to-mapping Γ d))]
)
|#

#|
(define-metafunction L
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
)|#

#|
(define-metafunction L
  Γ-lookup-mapping : Γ id -> mapping or #f
  [(Γ-lookup-mapping (mapping_s ... (val id_req t_req)) id_req) 
    (val id_req t_req)]
  [(Γ-lookup-mapping (mapping_s ... (type id_req t_req)) id_req) 
    (type id_req t_req)]
  [(Γ-lookup-mapping (mapping_s ... mapping_not-matching) id_req)
   (Γ-lookup-mapping (mapping_s ...) id_req)]
  [(Γ-lookup-mapping () id_req) #f]
)
(define-metafunction L
  Γ-lookup-val : Γ id -> t-or-#f
  [(Γ-lookup-val (mapping_before ... (val id_req t_req) mapping_after ...) 
id_req) 
   t_req]
  [(Γ-lookup-val Γ id_req) #f]
)
(define-metafunction L
  Γ-lookup-type : Γ id -> t-or-#f
  [(Γ-lookup-type (mapping_before ... (type id_req t_req) mapping_after ...) 
id_req) 
   t_req]
  [(Γ-lookup-type Γ id_req) #f]
)
(define-metafunction L
  Γ-extend-unsafe : Γ mapping -> Γ
  [(Γ-extend-unsafe (mapping_s ...) mapping_new)
   (mapping_s ... mapping_new)]
)

(define-judgment-form L
  #:mode (not-in-Γ I I)
  #:contract (not-in-Γ Γ id)
  [(not-in-Γ Γ id)
   (side-condition (not (term (Γ-lookup-mapping Γ id))))]
)|#

#|

; (wf-stat Γ stat) means that in Γ, stat is a well-formed statement
(define-judgment-form
  L
  #:mode (wf-stat I I)
  #:contract (wf-stat Γ stat)
  [(wf-stat Γ stat)
   (side-condition (is-wf-stat Γ stat))]
)
(define-metafunction L
  is-wf-stat : Γ stat -> boolean
  [(is-wf-stat Γ d)                         ; view declaration as statement
   (is-wf-d Γ d)]
  [(is-wf-stat Γ (ign e)) #t                ; ign-statement
   (judgment-holds (types Γ e Void))] 
)

; (wf-d Γ d) means that in Γ, d is a well-formed declaration
; Does not check that id is not yet in Γ
(define-judgment-form
  L
  #:mode (wf-d I I)
  #:contract (wf-d Γ d)
  [(wf-d Γ d)
   (side-condition (is-wf-d Γ d))]
)
|#

#|

; converts a value or type declaration to a mapping which can be stored in a Γ
; Γ_outer is the context needed to construct the type of untyped vds
(define-metafunction L
  d-to-mapping : Γ_outer d -> mapping
  [(d-to-mapping Γ_outer vd)              ; val decl
   (vd-to-mapping Γ_outer vd)]
  [(d-to-mapping Γ_outer (type id t))     ; type decl
   (type id t)]
)

; (calc-e-type Γ e) returns the type of expression e
(define-metafunction L
  calc-e-type : Γ e -> t
  [(calc-e-type Γ e) t_1
   (where (t_1) ,(judgment-holds (types Γ e t) t))]
  ; sometimes it finds the same type in two different ways:
  ; TODO why, and can it also be >2x?
  [(calc-e-type Γ e) t_1
   (where (t_1 t_1) ,(judgment-holds (types Γ e t) t))]
)
|#