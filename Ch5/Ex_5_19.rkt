#lang eopl

;;;;;;;;;;;;;;;;;;;;;;; Lexical specification ;;;;;;;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; Grammar ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     letrec-exp)))

;;;;;;;;;;;;;;;;;;;; SLLGEN boilerplate ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;; Expressible values ;;;;;;;;;;;;;;;;;;;;;;;;;

; procedure : Var * ExpVal * Env * Cont -> Proc
(define (procedure var body env)
  (lambda (val cont)
    (value-of/k body (extend-env var val env) cont)))

; apply-procedure : Proc * ExpVal * Cont -> ExpVal
(define (apply-procedure f x cont) (f x cont))

; ExpVal = Int + Bool + Proc
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc procedure?)))

; expval->num : ExpVal -> Int
(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (eopl:error 'expval->num "~s is not a number" val))))

; expval->bool : ExpVal -> Bool
(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (eopl:error 'expval->bool "~s is not a boolean" val))))

; expval->proc : ExpVal -> Proc
(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (eopl:error 'expval->proc "~s is not a procedure" val))))

; expval->any : ExpVal -> SchemeVal
(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Environments ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Var = Symbol
; Ident = Symbol
; identifier? : SchemeVal -> Bool
(define identifier? symbol?)

; Env = empty-env
;     | extend-env Ident ExpVal Env
;     | extend-env-rc Ident Ident Exp Env
(define-datatype env env?
  (empty-env)
  (extend-env (k identifier?) (v expval?) (e env?))
  (extend-env-rec (f identifier?) (x identifier?)
                  (body expression?) (e env?)))

; report-no-binding-found : Ident -> Error
(define (report-no-binding-found k)
  (eopl:error 'apply-env "No binding for ~s" k))

; apply-env : Var -> 
(define (apply-env e k)
  (cases env e
    (empty-env () (report-no-binding-found k))
    (extend-env (k2 v e1) (if (eqv? k k2) v (apply-env e1 k)))
    (extend-env-rec (f x body e1)
                    (if (eqv? f k)
                        (proc-val (procedure x body e))
                        (apply-env e1 k)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;; Continuations ;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FinalAnswer = ExpVal
; Cont = ExpVal -> ExpVal
; Bounce = ExpVal + (() -> Bounce)

; apply-cont : Cont * ExpVal -> Bounce
(define (apply-cont cont val)
  (lambda () (cont val)))

; end-cont : () -> Cont
(define (end-cont)
  (lambda (val)
    (begin
      (eopl:printf "End of computation.~%")
      val)))

; zero1 : Cont * ExpVal -> ExpVal
(define (zero1-cont cont)
  (lambda (val)
    (apply-cont cont (bool-val (zero? (expval->num val))))))

; let-exp-cont : Var * Exp * Env * Cont -> Cont
(define (let-exp-cont var body env cont)
  (lambda (val)
    (value-of/k body (extend-env var val env) cont)))

; if-test-cont : Exp * Exp * Env * Cont * Cont
(define (if-test-cont expt expf env cont)
  (lambda (val)
    (if (expval->bool val)
        (value-of/k expt env cont)
        (value-of/k expf env cont))))

; diff1-cont : Exp * Env * Cont -> Cont
(define (diff1-cont exp env cont)
  (lambda (val)
    (value-of/k exp env (diff2-cont val cont))))

; diff2-cont : ExpVal * Cont -> Cont
(define (diff2-cont v1 cont)
  (lambda (v2)
    (apply-cont cont
                (num-val (- (expval->num v1) (expval->num v2))))))

; rator-cont : Exp * Env * Cont -> Cont
(define (rator-cont exp env cont)
  (lambda (f)
    (value-of/k exp env (rand-cont f cont))))

; rand-cont : Proc * Cont -> Cont
(define (rand-cont f cont)
  (lambda (x)
    (apply-procedure (expval->proc f) x cont)))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Interpreter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : String -> SchemeVal
(define (run string)
  (expval->any (value-of-program (scan&parse string))))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp)
      (trampoline (value-of/k exp (init-env) (end-cont))))))

; trampoline : Bounce -> ExpVal
(define (trampoline bounce)
  (if (expval? bounce)
      bounce
      (trampoline (bounce))))

; value-of/k : Exp * Env * Cont -> Bounce
(define (value-of/k exp env cont)
  (cases expression exp
    
    (const-exp (num)
      (apply-cont cont (num-val num)))
    
    (var-exp (var)
      (apply-cont cont (apply-env env var)))
    
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont)))

    (zero?-exp (exp)
      (value-of/k exp env (zero1-cont cont)))

    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-test-cont exp2 exp2 env cont)))

    (let-exp (var exp body)
      (value-of/k exp env (let-exp-cont var body env cont)))
    
    (proc-exp (var body)
      (apply-cont cont (proc-val (procedure var body env))))

    (call-exp (e1 e2)
      (value-of/k e1 env (rator-cont e2 env cont)))

    (letrec-exp (f x body letrec-body)
      (value-of/k letrec-body
                  (extend-env-rec f x body env)
                  cont))))