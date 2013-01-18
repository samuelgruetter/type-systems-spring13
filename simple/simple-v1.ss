#lang racket
(require redex)

(define-language frog
  (prog                       ; program 
    stat)                     ;    one statement
  (stat                       ; statement
    (ign e)                   ;   `(ign e)` instead of `e;` ("ignore value of expression")
    { stat stat ... }         ;   block of statements
    vd)                       ;   value declaration
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
    (arrow t t))              ;   t -> t
  (intst                      ; intersection type
    (intersect t t)           ;   t & t
  (patht                      ; path type ("indirect type")
    id                        ;   identifier
    (sel patht id))           ;   pathh . id

  (e                          ; "normal" expression
    )
  
  (oc                         ; object construction
    (vd ...))                 ;   sequence of value declarations
  (f                          ; anonymous function
    (arrow (id t) e))         ;   id : t => e
)

#|

If ::= `if` Expr `then` Expr (`else` Expr)?
While ::= `while` Expr `do` Expr
Println ::= `println` Expr
BinOpExpr ::= 
    Expr ( `&&` | `||` | `==` | `<` | `+` | `-` | `*` | `/` ) Expr
GetField ::= Expr `.` Identifier
Literal ::= <int literal> | `true` | `false` | `"`<string literal>`"`

ExprWithParenNoFuncAppl ::= '(' Expr ')' | ObjConstr 
ExprNoParenNoFuncAppl ::= Identifier | Block | AnonFunc | If | While 
                          | Println | BinOpExpr | GetField | Literal

FuncApplWithParen ::= Expr ExprWithParenNoFuncAppl
FuncApplNoParen ::= Expr ExprNoParenNoFuncAppl

Expr ::= ExprWithParenNoFuncAppl | ExprNoParenNoFuncAppl 
         | FuncApplWithParen | FuncApplNoParen

Identifier	::=	<java identifier>
|#



(define-language frog0 
  (p bc)                      ; Program ::= BlockContent
  (bc (bcls ...))             ; BlockContent ::= BlockContentLineSeparated *
  (bcls (bcl lll))              ; BlockContentLineSeparated ::= BlockContentLine `,`
  (bcl vd e)                  ; BlockContentLine ::= ValDecl | Expr
  (vd (id : t = e)            ; ValDecl ::= Identifier `:` TypeExpr `=` Expr
      (id = g))               ; ValDecl ::= Identifier `=` GeneralExpr
  (g e t)                     ; GeneralExpr ::= (Expr | TypeExpr)
)
