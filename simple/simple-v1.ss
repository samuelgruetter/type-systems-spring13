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
    vd                        ;   value declaration
    (println e)               ;   print line
    (if e stat)               ;   if-then with no return value
    (if e stat stat)          ;   if-then-else with no return value
    (while e stat))           ;   while loop
  
  (vd                         ; value declaration TODO this is ambiguous
    (val id t e)              ;   typed value declaration 
    (val id g))               ;   untyped value declaration
  (g                          ; general expression
    e                         ;   "normal" expression 
    t)                        ;   type expression
  
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
    (sel patht id))           ;   pathh . id

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
(define-extended-language L-simple-v1+Γ L-simple-v1
  [Γ ([id T] ...)]
)
(define-metafunction L-simple-v1+Γ
  Γ-extend : Γ id T -> Γ
  [(Γ-extend ((id_before t_before) ...) id_new t_new)
   ((id_before t_before) ... (id_new t_new))]
)
(define-metafunction L-simple-v1+Γ
  Γ-lookup : Γ id -> t or #f
  [(Γ-lookup ((id_before t_before) ... (id_req t_req)) id_req) 
    t_req]
  [(Γ-lookup ((id_before t_before) ... (id_last t_last)) id_req)
   (Γ-lookup ((id_before t_before) ...) id_req)]
  [(Γ-lookup () id_req) #f]
)

; true iff two identifiers are different
(define-metafunction L-simple-v1+Γ
  [(different id_1 id_1) #f]
  [(different id_1 id_2) #t])


; TODO Γ-extend-with-vds
 
 ; TODO filter-for-vds (list of statements)

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
  
  #| TODO fix this
  [(side-condition (same (Γ-lookup Γ id) t))
   ----------------------------------------- ; (Extract val's type from Γ)
   (types Γ id t)]
  |#

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
  
  
  
  #| TODO rules for  
    (&& e e)                  ;   logical and
    (|| e e)                  ;   logical or
    (== e e)                  ;   equality (TODO by address or structure?)
    (< e e)                   ;   less than for integers
    (+ e e)                   ;   integer addition or string concatenation
    (- e e)                   ;   integer subtraction
    (* e e)                   ;   integer multiplication
    (/ e e))                  ;   integer division
  |#
  
)

; (wf-t Γ t) means that in Γ, t is a well-formed type expression
(define-judgment-form
  L-simple-v1+Γ
  #:mode (wf-t I I)
  #:contract (wf-t Γ t)

  [(wf-t Γ t) ; TODO :P
   ]
  
  #| TODO all these:
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
    (sel patht id))           ;   pathh . id  
  |#

)