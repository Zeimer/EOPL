#lang eopl

; Ex. 4.4
;
; (value-of e0 ρ σ) = (val, σ')
; ---------------------------------------------
; (value-of (begin-exp e0 '()) ρ σ) = (val, σ')
;
; (value-of e0 ρ σ) = (val, σ')
; (value-of (begin-exp e es) ρ σ') = (val', σ'')
; ------------------------------------------------------
; (value-of (begin-exp e0 (cons e es) ρ σ) = (val', σ'')

; Environments.
(define identifier? symbol?)

(define-datatype env env?
  (empty-env)
  (extend-env (k identifier?) (v expval?) (e env?))
  (extend-env-rec (bindings list?) (e env?)))

(define (empty-env? e)
  (cases env e
    (empty-env () #t)
    (else #f)))

(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

(define (apply-list k bindings e e1)
  (cond
    [(null? bindings) (apply-env k e1)]
    [else
     (cases letrec-binding (car bindings)
       (binding-exp (f x body)
                    (if (eqv? f k)
                        (proc-val (procedure x body e))
                        (apply-list k (cdr bindings) e e1))))]))

(define (apply-env k e)
  (cases env e
    (empty-env () (report-no-binding-found k))
    (extend-env (k2 v e1) (if (eqv? k k2) v (apply-env k e1)))
    (extend-env-rec (bindings e1) (apply-list k bindings e e1))))

; The store.
(define (empty-store) '())

(define the-store 'uninitialized)

(define (get-store) the-store)

(define (initialize-store!)
  (set! the-store (empty-store)))

(define reference? integer?)

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (report-invalid-reference ref store)
  (eopl:error 'setref! "Invalid reference ~s in the store ~s"
              ref store))

(define (setref! ref val)
  (set! the-store
        (letrec
            ((setref-inner
              (lambda (store1 ref1)
                (cond
                  [(null? store1)
                   report-invalid-reference ref the-store]
                  [(zero? ref1)
                   (cons val (cdr store1))]
                  [else
                   (cons
                    (car store1)
                    (setref-inner
                     (cdr store1)
                     (- ref1 1)))]))))
          (setref-inner the-store ref))))

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
    
    (letrec-binding
     (identifier "(" identifier ")" "=" expression)
     binding-exp)

    (expression
     ("letrec" (arbno letrec-binding) "in" expression)
     letrec-exp)

    (expression
     ("newref" "(" expression ")")
     newref-exp)

    (expression
     ("deref" "(" expression ")")
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)

    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)))

; SLLGEN boilerplate.
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

; Expressed (expressible?) values for the EXPLICIT-REFS language.
(define (procedure var body env)
  (lambda (val) (value-of body (extend-env var val env))))

(define (apply-procedure f x) (f x))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc procedure?))
  (ref-val
   (ref reference?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (eopl:error 'expval->num "~s is not a number" val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (eopl:error 'expval->bool "~s is not a boolean" val))))

(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (eopl:error 'expval->proc "~s is not a procedure" val))))

(define (expval->ref val)
  (cases expval val
    (ref-val (ref) ref)
    (else (eopl:error 'expval->ref "~s is not a reference" val))))

(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (ref-val (r) r)))

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
  (initialize-store!)
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
             (value-of body (extend-env var (value-of exp env) env)))
    (proc-exp (var body)
              (proc-val (procedure var body env)))
    (call-exp (e1 e2)
              (apply-procedure
               (expval->proc (value-of e1 env))
               (value-of e2 env)))
    (letrec-exp (bindings body)
                 (value-of body (extend-env-rec bindings env)))
    (newref-exp (e)
                (let ((v1 (value-of e env)))
                  (ref-val (newref v1))))
    (deref-exp (e)
               (let ((v1 (value-of e env)))
                 (let ((ref1 (expval->ref v1)))
                   (deref ref1))))
    (setref-exp (e1 e2)
                (let ((ref (expval->ref (value-of e1 env))))
                  (let ((val2 (value-of e2 env)))
                    (begin (setref! ref val2)
                           (num-val 23)))))
    (begin-exp (e es) (value-of-begin (cons e es) env))))

(define (value-of-begin es env)
  (cond
    [(null? (cdr es)) (value-of (car es) env)]
    [else
     (value-of (car es) env)
     (value-of-begin (cdr es) env)]))