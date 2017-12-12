#lang eopl

(require racket/vector)

; A helper.
(define (range a b)
  (if (>= a b) '() (cons a (range (+ a 1) b))))

; Environments.
(define identifier? symbol?)

(define-datatype env env?
  (empty-env)
  (extend-env (k identifier?) (body vector?) (e env?))
  (extend-env-rec* (fs vector?) (bodies vector?) (e env?)))

(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

(define (extend-env-rec f x body env)
  (let ((vec (make-vector 1)))
    (let ((new-env (extend-env f vec env)))
      (vector-set! vec 0
                   (proc-val (procedure x body new-env)))
      new-env)))

(define (extend-env-rec2 fs xs bodies env)
  (let ((len (vector-length fs)))
    (let ((vec (make-vector len)))
      (let ((new-env (extend-env-rec* fs vec env)))
        (for-each
         (lambda (pos x body)
           (vector-set! vec pos
                        (proc-val (procedure x body new-env))))
         (range 0 len) (vector->list xs) (vector->list bodies))
        new-env))))

(define (apply-env k e)
  (cases env e
    (empty-env () (report-no-binding-found k))
    (extend-env (k1 vec e1)
                (if (eqv? k k1)
                    (vector-ref vec 0)
                    (apply-env k e1)))
    (extend-env-rec* (fs bodies e1)
                     (let ((n (vector-member k fs)))
                       (if n
                           (vector-ref bodies n)
                           (apply-env k e1))))))

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
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("letrec" identifier "(" identifier ")"
               "=" expression "in" expression)
     letrec-exp)

    (expression
     ("letrec*"
      (arbno identifier "(" identifier ")" "=" expression)
      "in" expression)
     letrec*-exp)))

; SLLGEN boilerplate.

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

; Expressed (expressible?) values for the PROC language.
(define (procedure var body env)
  (lambda (val) (value-of body (extend-env var (vector val) env))))

(define (apply-procedure f x) (f x))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc procedure?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else 'WUT)))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else 'WUT2)))

(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else 'WUT3)))

(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)))

; The initial environment.
; init-env : () -> Env
(define (init-env)
  (extend-env
   'i (vector (num-val 1))
   (extend-env
    'v (vector (num-val 5))
    (extend-env
     'x (vector (num-val 10))
     (empty-env)))))

; Interpreter for the LET language.
; run : String -> ExpVal
(define (run string)
  (value-of-program (scan&parse string)))

(define (run2 string) (expval->any (run string)))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (e) (value-of e (init-env)))))

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
             (value-of body
              (extend-env var (vector (value-of exp env)) env)))
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    (call-exp (e1 e2)
              (apply-procedure
               (expval->proc (value-of e1 env))
               (value-of e2 env)))
    (letrec-exp (f x body letrec-body)
                (value-of letrec-body
                          (extend-env-rec f x body env)))
    (letrec*-exp (fs xs bodies letrec*-body)
                 (value-of letrec*-body
                           (extend-env-rec2
                            (list->vector fs)
                            (list->vector xs)
                            (list->vector bodies)
                            env)))))