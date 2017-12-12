#lang eopl

(provide empty-env extend-env apply-env)

(define (empty-env)
  (lambda (var)
    (eopl:error 'empty-env "No binding found for ~s" var)))

(define (apply-env env var) (env var))

(define (extend-env var val env)
  (lambda (var1)
    (if (eqv? var var1) val (apply-env env var1))))

(define (extend-env-rec f x body env)
  (lambda (var)
    (if (eqv? x var)
        (proc-val (procedure x body env))
        (apply-env env var))))