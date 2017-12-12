#lang eopl

(provide empty-env empty-env? extend-env apply-env extend-env*)

; Exercise 2.11
(define (empty-env) '())

(define (empty-env? e) (eqv? e '()))

(define (extend-env k v e) (cons (list (list k) (list v)) e))

(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

(define (apply-env k e)
  (define (aux k ks vs)
    (cond
      [(null? ks) #f]
      [(null? vs) #f]
      [else (if (eqv? k (car ks)) (car vs) (aux k (cdr ks) (cdr vs)))]))
  (cond
    [(null? e) (report-no-binding-found k)]
    [else (let ([v (aux k (caar e) (cadar e))])
            (if v v (apply-env k (cdr e))))]))

(define (extend-env* ks vs e) (cons (list ks vs) e))