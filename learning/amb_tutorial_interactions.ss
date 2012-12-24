Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
> (redex-match
   L
   e
   (term (λ (x) x)))
#f
> (redex-match
   L
   (e_1 ... e_2 e_3 ...)
   (term ((+ 1 2)
          (+ 3 4)
          (+ 5 6))))

(list
 (match
  (list (bind 'e_1 '()) (bind 'e_2 '(+ 1 2)) (bind 'e_3 '((+ 3 4) (+ 5 6)))))
 (match
  (list (bind 'e_1 '((+ 1 2))) (bind 'e_2 '(+ 3 4)) (bind 'e_3 '((+ 5 6)))))
 (match
  (list (bind 'e_1 '((+ 1 2) (+ 3 4))) (bind 'e_2 '(+ 5 6)) (bind 'e_3 '()))))
> (redex-match
   L
   (e_1 e_2 e_3)
   (term ((+ 1 2)
          (+ 3 4)
          (+ 5 6))))

(list (match (list (bind 'e_1 '(+ 1 2)) (bind 'e_2 '(+ 3 4)) (bind 'e_3 '(+ 5 6)))))
> (redex-match
   L
   (foo)
   (term ((+ 1 2)
          (+ 3 4)
          (+ 5 6))))

#f
> (redex-match
   L
   (e)
   (term ((+ 1 2)
          (+ 3 4)
          (+ 5 6))))

#f
> (redex-match
   L
   (e e e)
   (term ((+ 1 2)
          (+ 3 4)
          (+ 5 6))))

#f
> (redex-match
   L
   (x)
   (foo)
   )
. . foo: undefined;
 cannot reference an identifier before its definition
> (redex-match
   L
   (x)
   (term (foo))
  )

(list (match (list (bind 'x 'foo))))
> (redex-match
   L
   (x_1 x_2 x_3)
   (term foo foo bar)
  )

. term: expected a keyword in: foo
>  (redex-match
   L
   (x_1 x_2 x_3)
   (term (foo) (foo) (bar))
  )
. term: expected a keyword in: (foo)
> (redex-match
   L
   (x_1 x_2 x_3)
   (term (foo) (bar))
  )
. term: expected a keyword in: (bar)
> (redex-match
   L
   (x_1 x_2 x_3)
   (term (foo foo bar))
  )
(list (match (list (bind 'x_1 'foo) (bind 'x_2 'foo) (bind 'x_3 'bar))))
> (redex-match
   L
   (e)
   (term (((λ (x) (+ x 1)) 17)))
  )
#f
> (redex-match
   L
   (e)
   (term (((λ (x num) (+ x 1)) 17)))
  )
(list (match (list (bind 'e '((λ (x num) (+ x 1)) 17)))))
> (redex-match
   L
   ((λ (x t) e_1) e_2)
   (term (((λ (x num) (+ x 1)) 17)))
  )
#f
> (redex-match
   L
   (e_1 e_2)
   (term (((λ (x num) (+ x 1)) 17)))
  )
#f
> (redex-match
   L
   (e_1)
   (term (((λ (x num) (+ x 1)) 17)))
  )
(list (match (list (bind 'e_1 '((λ (x num) (+ x 1)) 17)))))
> (redex-match
   L
   ((λ (x t) e_1) e_2)
   (term ((λ (x num) (+ x 1)) 17))
  )
(list (match (list (bind 'e_1 '(+ x 1)) (bind 'e_2 17) (bind 't 'num) (bind 'x 'x))))
> (redex-match
   L
   (→ t_1 t_2)
   (term (→ num (→ num num)))
  )
(list (match (list (bind 't_1 'num) (bind 't_2 '(→ num num)))))
> (redex-match
   L
   (→ t1 t2)
   (term (→ num (→ num num)))
  )
#f
> (redex-match
   L
   (e_1 e_2)
   (term (1 2 3 4))
  )
#f
> (redex-match
   L
   (e_1 e_2 ...)
   (term (1 2 3 4))
  )
(list (match (list (bind 'e_1 1) (bind 'e_2 '(2 3 4)))))
> (redex-match
   L
   (e_100 ... e_1 e_2 e_101 ...)
   (term (1 2 3 4))
  )
(list
 (match (list (bind 'e_1 1) (bind 'e_100 '()) (bind 'e_101 '(3 4)) (bind 'e_2 2)))
 (match (list (bind 'e_1 2) (bind 'e_100 '(1)) (bind 'e_101 '(4)) (bind 'e_2 3)))
 (match (list (bind 'e_1 3) (bind 'e_100 '(1 2)) (bind 'e_101 '()) (bind 'e_2 4))))
> (redex-match
   L
   (e_foo1 ..._1 e_left e_middle ... e_foo2 ..._1)
   (term (1 2 3 4 5))
  )
(list
 (match (list (bind 'e_foo1 '()) (bind 'e_foo2 '()) (bind 'e_left 1) (bind 'e_middle '(2 3 4 5))))
 (match (list (bind 'e_foo1 '(1)) (bind 'e_foo2 '(5)) (bind 'e_left 2) (bind 'e_middle '(3 4))))
 (match (list (bind 'e_foo1 '(1 2)) (bind 'e_foo2 '(4 5)) (bind 'e_left 3) (bind 'e_middle '()))))
> (redex-match
   L
   (e_foo1 ..._1 e_left e_middle ... e_right e_foo2 ..._1)
   (term (1 2 3 4 5))
  )
(list
 (match (list (bind 'e_foo1 '()) (bind 'e_foo2 '()) (bind 'e_left 1) (bind 'e_middle '(2 3 4)) (bind 'e_right 5)))
 (match (list (bind 'e_foo1 '(1)) (bind 'e_foo2 '(5)) (bind 'e_left 2) (bind 'e_middle '(3)) (bind 'e_right 4))))
> (redex-match
   L
   (e_foo1 ..._1 e_left e_middle ... e_right e_foo2 ..._1)
   (term (1 2 3 4 5 6))
  )
(list
 (match (list (bind 'e_foo1 '()) (bind 'e_foo2 '()) (bind 'e_left 1) (bind 'e_middle '(2 3 4 5)) (bind 'e_right 6)))
 (match (list (bind 'e_foo1 '(1)) (bind 'e_foo2 '(6)) (bind 'e_left 2) (bind 'e_middle '(3 4)) (bind 'e_right 5)))
 (match (list (bind 'e_foo1 '(1 2)) (bind 'e_foo2 '(5 6)) (bind 'e_left 3) (bind 'e_middle '()) (bind 'e_right 4))))
> (redex-match
   L
   (e_foo1 ..._1 e_left e_foo3 e_middle ... e_right e_foo2 ..._1)
   (term (1 2 3 4 5 6))
  )
(list
 (match (list (bind 'e_foo1 '()) (bind 'e_foo2 '()) (bind 'e_foo3 2) (bind 'e_left 1) (bind 'e_middle '(3 4 5)) (bind 'e_right 6)))
 (match (list (bind 'e_foo1 '(1)) (bind 'e_foo2 '(6)) (bind 'e_foo3 3) (bind 'e_left 2) (bind 'e_middle '(4)) (bind 'e_right 5))))
> (redex-match
   L
   (e_foo1 ..._1 e_left e_foo3 e_middle1 ..._2 e_middle2 ..._2 e_right e_foo2 ..._1)
   (term (1 2 3 4 5 6))
  )
#f
> (redex-match
   L
   (e_foo1 ..._1 e_left e_foo3 e_middle1 ..._2 e_middle2 ..._2 e_right e_foo2 ..._1)
   (term (1 2 3 4 5))
  )
(list
 (match
  (list
   (bind 'e_foo1 '())
   (bind 'e_foo2 '())
   (bind 'e_foo3 2)
   (bind 'e_left 1)
   (bind 'e_middle1 '(3))
   (bind 'e_middle2 '(4))
   (bind 'e_right 5)))
 (match
  (list
   (bind 'e_foo1 '(1))
   (bind 'e_foo2 '(5))
   (bind 'e_foo3 3)
   (bind 'e_left 2)
   (bind 'e_middle1 '())
   (bind 'e_middle2 '())
   (bind 'e_right 4))))
> (redex-match
   L
   (e_1 e_2 e_3 e_2 e_1)
   (term (1 2 3 2 1))
  )
(list (match (list (bind 'e_1 1) (bind 'e_2 2) (bind 'e_3 3))))
> (redex-match
   L
   (e_1 e_2 e_3 e_2 e_2)
   (term (1 2 3 2 1))
  )
#f
> 


Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
>  (judgment-holds
   (types ·
          ((λ (x num) (amb x 1))
           (+ 1 2))
          t)
   t)
'(num)
>  (judgment-holds
     (types · 3 t)
   t)
'(num)
> (judgment-holds
   (types ·
          (λ (f (→ num (→ num num))) (f (amb 1 2)))
          (→ t_1 t_2))
   t_2)
'((→ num num))
> (test-equal
   (judgment-holds
    (types · (λ (x num) x) t)
    t)
   (list (term (→ num num))))
> (test-equal
   (judgment-holds
    (types · (λ (x num) (λ (z num) x)) t)
    t)
   (list (term (→ num num))))
FAILED :25.2
  actual: '((→ num (→ num num)))
expected: '((→ num num))
> test-results
#<procedure:test-results>
> (test-results)
1 test failed (out of 2 total).
> 

;; ex5

; different side-condition commented out, in last example, z has two different types

Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
> (judgment-holds
   (types · (λ (x num) (λ (z num) x)) t)
  t)
   
'((→ num (→ num num)))
> (judgment-holds
   (types · (λ (x num) (λ (z num) (+ x z))) t)
  t)   
'((→ num (→ num num)))
> (judgment-holds
   (types · (λ (f (→ num num)) (λ (z num) (f z))) t)
  t)
'((→ (→ num num) (→ num num)))
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) (+ z z))) t)
  t)
'((→ (→ num num) (→ num num)))
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) t)
  t)
'((→ (→ num num) (→ num (→ num num))) (→ (→ num num) (→ num num)))
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t)))
  t)
'((→ num num) num)
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t_z)))
  t)
'(t t)
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t_z)))
  t_z)
'((→ num num) num)
> 


; different side-condition uncommented, in last example, z STILL has two different types

Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t_z)))
  t)
'(t t)
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t_z)))
  t_z)
'((→ num num) num)
> 

; after adding this

(define-metafunction L+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

; to the declarations, z only has one type, as expected:

Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
> (judgment-holds
   (types · (λ (z (→ num num)) (λ (z num) z)) (→ (→ num num) (→ num t_z)))
  t_z)
'(num)
> 

; but it is weird that I don't get a warning like "undefined metafunction 'different'"

; if I include 

 (side-condition (differentgwrenjkvaub x_1 x_2))

; in the declarations, I don't get any warning either...


;; ex6

Welcome to DrRacket, version 5.3.1--2012-05-05(-/f) [3m].
Language: racket; memory limit: 128 MB.
> (judgment-holds
    (types · (amb 1 2) t)
    t)
. . types: input (amb 1 2) at position 2 does not match its contract
> (judgment-holds
    (types · (amb num 1 2) t)
    t)
'(num)
> (judgment-holds
    (types · (amb num 1 2 3) t)
    t)
. . types: input (amb num 1 2 3) at position 2 does not match its contract
> (test-equal
   (judgment-holds
    (types · (amb num 4 5) t)
    t)
   (list (term num)))
> (test-equal
   (judgment-holds
    (types · (amb (→ num num) (λ (x num) 4) (λ (x num) x) ) t)
    t)
   (list (term (→ num num))))
> (test-results)
Both tests passed.
> 



