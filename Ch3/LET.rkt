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
     let-exp)))

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
   (bool boolean?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else 'WUT)))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else 'WUT2)))

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

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1) (value-of exp1 (init-env)))))

; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (var-exp (var) (apply-env env var))
    (diff-exp (exp1 exp2)
              (num-val (-
                        (expval->num (value-of exp1 env))
                        (expval->num (value-of exp2 env)))))
    (zero?-exp (exp) (if
                      (= 0 (expval->num (value-of exp env)))
                      (bool-val #t)
                      (bool-val #f)))
    (if-exp (exp1 exp2 exp3)
            (if (eqv? #t (expval->bool (value-of exp1 env)))
                (value-of exp2 env)
                (value-of exp3 env)))
    (let-exp (var exp body)
             (value-of body (extend-env var (value-of exp env) env)))))