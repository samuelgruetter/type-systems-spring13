#lang racket

; calculate transitive closure of a relation

(require (planet wmfarr/simple-matrix:1:1/matrix-base))
;(require math/matrix) ; not compatible
(require racket/set)
(provide trcl)

(define (bool-mul a b) (* a b))
(define (bool-add a b) (if (= a b 0) 0 1))

(define (bool-matrix-mul m1 m2)
  (let ((m (matrix-rows m1))
        (n (matrix-cols m2)))
    (for*/matrix m n
      ((i (in-range m))
       (j (in-range n)))
      (for/fold ((sum 0))
        ((k (in-range (matrix-cols m1))))
        (bool-add sum (bool-mul (matrix-ref m1 i k) (matrix-ref m2 k j)))))))

(define (bool-matrix-add m1 m2)
  (for/matrix (matrix-rows m1) (matrix-cols m1)
    ((x (in-matrix m1))
     (y (in-matrix m2)))
       (bool-add x y)))

(define (trcl-matrix/acc m acc)
  (let ((acc2 (bool-matrix-add acc (bool-matrix-mul m acc))))
       (if (equal? acc acc2)
           acc
           (trcl-matrix/acc m acc2))))

(define (trcl-matrix m) (trcl-matrix/acc m m))

#| tests
> (trcl-matrix (matrix* 3 3 0 1 0 0 0 1 0 0 0))
(matrix 3 3 '#(0 1 1 0 0 1 0 0 0))
> (trcl-matrix (matrix* 4 4 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0))
(matrix 4 4 '#(0 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0))
> (trcl-matrix (matrix* 4 4 0 1 0 0 0 0 1 0 1 0 0 0 1 0 0 0))
(matrix 4 4 '#(1 1 1 0 1 1 1 0 1 1 1 0 1 1 1 0))
|#

(define (domain-of-relation r) 
  (set->list
     (set-union (list->set (map (lambda (p) (car p)) r))
                (list->set (map (lambda (p) (cadr p)) r)))))

(define (relation->matrix rel dom) 
  (let ([relset (list->set rel)]
       [n (length dom)])
    (for*/matrix n n 
      ((e1 (in-list dom))
        (e2 (in-list dom)))
          (if (set-member? relset (list e1 e2)) 1 0))))

(define (matrix->relation mat dom)
  (let ([n (length dom)])
       (for*/list ([i (in-range n)]
              [j (in-range n)]
                #:when (equal? 1 (matrix-ref mat i j)))
                (list (list-ref dom i) (list-ref dom j))
            )))

#|;test 
(define testrel '((1 1) (1 10) (2 20) (30 30)))
(define testdom (domain-of-relation testrel))
(define testmat (relation->matrix testrel testdom))
(matrix->relation testmat testdom)
|#

; calculate transitive closure of relation r
; a relation is given as a list of lists of length 2 (= a list of tuples)
(define (trcl r)
  (let ([domain (domain-of-relation r)])
     (let ([m (relation->matrix r domain)])
       (matrix->relation (trcl-matrix m) domain))))

; test
#| (define testrel '((a b) (b c) (c a) (d a) (d e)))
(trcl testrel) |#


