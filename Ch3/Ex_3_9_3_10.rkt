#lang eopl

; Environments.
(require "ListEnv.rkt")

; Lexical specification and grammar.
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    (expression (identifier) var-exp)
    
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("emptylist")
     emptylist-exp)
    
    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("null?" expression)
     null?-exp)

    (expression
     ("car" expression)
     car-exp)

    (expression
     ("cdr" expression)
     cdr-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)

    (binding
     (identifier "=" expression)
     binding-exp)
    
    (expression
     ("let*" (arbno binding) "in" expression)
     let*-exp)))

; SLLGEN boilerplate.

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

; Expressed (expressible?) values for the LET language.
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (list-val
   (list list?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else 'WUT)))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else 'WUT2)))

(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else 'WUT3)))

#|(define (any->expval val)
  (cond
    [(integer? val) (num-val val)]
    [(boolean? val) (bool-val val)]
    [(list? val) (list-val val)]))
|#

(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (list-val (l) l)))

; The initial environment.
; init-env : () -> Env
(define (init-env)
  (extend-env
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))

; Interpreter for the LET language.
; run : String -> ExpVal
(define (run string)
  (value-of-program (scan&parse string)))

(define (run2 string) (expval->any (run string)))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1) (value-of exp1 (init-env)))))

; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    (const-exp (num)
               (num-val num))
    (var-exp (var)
             (apply-env var env))
    (diff-exp (exp1 exp2)
              (num-val (-
                        (expval->num (value-of exp1 env))
                        (expval->num (value-of exp2 env)))))
    (zero?-exp (exp)
               (if (= 0 (expval->num (value-of exp env)))
                   (bool-val #t)
                   (bool-val #f)))
    (if-exp (exp1 exp2 exp3)
            (if (eqv? #t (expval->bool (value-of exp1 env)))
                (value-of exp2 env)
                (value-of exp3 env)))
    (let-exp (var exp body)
             (value-of body (extend-env var (value-of exp env) env)))
    (emptylist-exp ()
                   (list-val '()))
    (cons-exp (e1 e2)
              (list-val (cons
                         (value-of e1 env) ; beware
                         (expval->list (value-of e2 env)))))
    (null?-exp (e)
               (bool-val (null? (expval->list (value-of e env)))))
    (car-exp (e)
             (car (expval->list (value-of e env))))
    (cdr-exp (e)
             (cdr (expval->list (value-of e env))))
    (list-exp (e)
              (cond
                [(null? e) (list-val '())]
                [else (list-val (cons
                  (value-of (car e) env) ; beware
                  (expval->list (value-of (list-exp (cdr e)) env))))]))
    (let*-exp
     (bindings body)
     (cond
       [(null? bindings) (value-of body env)]
       [else
        (cases binding (car bindings)
          (binding-exp (var exp)
                       (value-of (let*-exp (cdr bindings) body)
                                 (extend-env var (value-of exp env) env))))]))))
