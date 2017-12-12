#lang eopl

(require racket/vector)

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
(define store? vector?)

(define (empty-store) (make-vector 0))

(define reference? integer?)

(define (newref val store)
  (let ((next-ref (vector-length store)))
    (an-answer
     (ref-val next-ref)
     (vector-append store (make-vector 1 val)))))

(define (deref ref store)
  (vector-ref store ref))

(define (report-invalid-reference ref store)
  (eopl:error 'setref! "Invalid reference ~s in the store ~s"
              ref store))

(define (setref! ref val store)
  (vector-set! store ref val)
  (an-answer (num-val 42) store))

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
  (lambda (val store) (value-of body (extend-env var val env) store)))

(define (apply-procedure f x store) (f x store))

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

; Interpreter for the EXPLICIT-REFS language.
; run : String -> ExpVal
(define (run string)
  (cases answer (value-of-program (scan&parse string))
    (an-answer (val new-store) (expval->any val))))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (e) (value-of e (init-env) (empty-store)))))

(define-datatype answer answer?
  (an-answer (val expval?) (store store?)))

(define (ans->expval a)
  (cases answer a
    (an-answer (val store) val)))

; value-of : Exp * Env -> Answer
(define (value-of exp env store)
  (cases expression exp
    (const-exp (num)
      (an-answer (num-val num) store))
    
    (var-exp (var)
      (an-answer (apply-env var env) store))
    
    (diff-exp (exp1 exp2)
      (cases answer (value-of exp1 env store)
        (an-answer (val1 new-store1)
          (cases answer (value-of exp2 env new-store1)
            (an-answer (val2 new-store2)
              (an-answer
               (num-val (- (expval->num val1) (expval->num val2)))
               new-store2))))))
    
    (zero?-exp (exp)
      (cases answer (value-of exp env store)
        (an-answer (val new-store)
          (an-answer
           (if (= 0 (expval->num val)) (bool-val #t) (bool-val #f))
           new-store))))
    
    (if-exp (exp1 exp2 exp3)
      (cases answer (value-of exp1 env store)
        (an-answer (val new-store)
          (if (expval->bool val)
              (value-of exp2 env new-store)
              (value-of exp3 env new-store)))))
    
    (let-exp (var exp body)
      (cases answer (value-of exp env store)
        (an-answer (val new-store)
          (value-of body (extend-env var val env) new-store))))
    
    (proc-exp (var body)
      (an-answer
        (proc-val (procedure var body env))
        store))
    
    (call-exp (e1 e2)
      (cases answer (value-of e1 env store)
        (an-answer (val1 new-store1)
          (cases answer (value-of e2 env new-store1)
            (an-answer (val2 new-store2)
              (apply-procedure (expval->proc val1) val2 store))))))
    
    (letrec-exp (bindings body)
      (value-of body (extend-env-rec bindings env) store))
    
    (newref-exp (e)
      (cases answer (value-of e env store)
        (an-answer (val new-store)
          (newref val new-store))))
    
    (deref-exp (e)
      (cases answer (value-of e env store)
        (an-answer (val new-store)
          (an-answer
           (deref (expval->ref val) new-store)
           new-store))))
    
    (setref-exp (e1 e2)
      (cases answer (value-of e1 env store)
        (an-answer (val1 new-store1)
          (cases answer (value-of e2 env new-store1)
            (an-answer (val2 new-store2)
              (setref! (expval->ref val1) val2 new-store2))))))
    
    (begin-exp (e es) (value-of-begin (cons e es) env store))))

(define (value-of-begin es env store)
  (cond
    [(null? (cdr es)) (value-of (car es) env store)]
    [else
     (cases answer (value-of (car es) env store)
       (an-answer (val new-store)
         (value-of-begin (cdr es) env new-store)))]))