#lang racket
(require redex)

(provide L-simple-v1)

(define-language L-simple-v1
  (prog                       ; program 
    stat)                     ;    one statement
  (stat                       ; statement
    (ign e)                   ;   `(ign e)` instead of `e;` ("ignore value of expression")
    { stat stat ... }         ;   block of statements
    vd                        ;   value declaration
    (println e)               ;   print line
    (if e stat)               ;   if-then with no return value
    (if e stat stat)          ;   if-then-else with no return value
    (while e stat))           ;   while loop
  
  (vd                         ; value declaration
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
    (vd ...)                  ;   object construction
    id                        ;   identifier
    {stat ... e}              ;   block expression (not the same as a block of statements)
    (=> (id t) e)             ;   anonymous function
    (if e e e)                ;   if then else returning a value
    binop                     ;   binary operator expression
    (sel e id)                ;   e.id
    literal)                  ;   literal
  
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

