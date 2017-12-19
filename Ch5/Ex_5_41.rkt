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
     letrec-exp)
    
    (expression
     ("try" expression "catch" "(" identifier ")" expression)
     try-exp)
    
    (expression
     ("raise" expression)
     raise-exp)

    (expression
     ("emptylist")
     emptylist-exp)
    
    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)

    (expression
     ("null?" "(" expression ")")
     null?-exp)

    (expression
     ("car" "(" expression ")")
     car-exp)

    (expression
     ("cdr" "(" expression ")")
     cdr-exp)

    (expression
     ("list" "(" (separated-list expression ",") ")")
     list-exp)))

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

; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure f x cont) (f x cont))

; ExpVal = Int + Bool + Proc + List
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc procedure?))
  (list-val
   (list list?)))

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

; expval->list : ExpVal -> List
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (eopl:error 'expval->list "~s is not a list" val))))

; expval->any : ExpVal -> SchemeVal
(define (expval->any val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (list-val (l) l)))

; any->expval : Any -> ExpVal
(define (any->expval v)
  (cond
    [(integer? v) (num-val v)]
    [(boolean? v) (bool-val v)]
    [(procedure? v) (proc-val v)]
    [(list? v) (list-val v)]
    [else
     eopl:error 'any->expval "~s can't be made into an ExpVal." v]))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Environments ;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;; Continuations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FinalAnswer = ExpVal
; Any = any scheme value
(define (any? x) #t)

; Cont = (ExpVal -> ExpVal) * (ExpVal -> ExpVal)

; apply-cont : Cont * ExpVal -> ExpVal
(define (apply-cont cont val)
  ((car cont) val))

; apply-handler : Cont * ExpVal -> ExpVal
(define (apply-handler val cont)
  ((cadr cont) val))

; end-cont : () -> Cont
(define (end-cont)
  (list
   (lambda (val)
     (begin
       (eopl:printf "End of computation.~%")
       val))
   (lambda () (report-uncaught-exception))))

; zero?-cont : Cont * ExpVal -> ExpVal
(define (zero?-cont cont)
  (list
   (lambda (val)
     (apply-cont cont (bool-val (zero? (expval->num val)))))
   (lambda (val)
     (apply-handler val cont))))

; let-exp-cont : Var * Exp * Env * Cont -> Cont
(define (let-exp-cont var body env cont)
  (list
   (lambda (val)
     (value-of/k body (extend-env var val env) cont))
   (lambda (val)
     (apply-handler val cont))))
     
; if-cont : Exp * Exp * Env * Cont * Cont
(define (if-cont expt expf env cont)
  (list
   (lambda (val)
     (if (expval->bool val)
         (value-of/k expt env cont)
         (value-of/k expf env cont)))
   (lambda (val)
     (apply-handler val cont))))
  
; diff1-cont : Exp * Env * Cont -> Cont
(define (diff1-cont exp env cont)
  (list
   (lambda (val)
     (value-of/k exp env (diff2-cont val cont)))
   (lambda (val)
     (apply-handler val cont))))

; diff2-cont : ExpVal * Cont -> Cont
(define (diff2-cont v1 cont)
  (list
   (lambda (v2)
     (apply-cont cont
                 (num-val (- (expval->num v1) (expval->num v2)))))
   (lambda (val)
     (apply-handler val cont))))

; rator-cont : Exp * Env * Cont -> Cont
(define (rator-cont exp env cont)
  (list
   (lambda (f)
     (value-of/k exp env (rand-cont f cont)))
   (lambda (val)
     (apply-handler val cont))))

; rand-cont : Proc * Cont -> Cont
(define (rand-cont f cont)
  (list
   (lambda (x)
     (apply-procedure (expval->proc f) x cont))
   (lambda (val)
     (apply-handler val cont))))

; try-cont : Var * Exp * Env * Cont -> Cont
(define (try-cont var handler env cont)
  (list
   (lambda (val)
     (apply-cont cont val))
   (lambda (val)
     (value-of/k handler (extend-env var val env) cont))))

; raise-cont : Cont -> Cont
(define (raise-cont cont)
  (list
   (lambda (val)
     (apply-handler val cont))
   (lambda (val)
     (apply-handler val cont))))
     
; unop-cont : Any * Cont -> Cont
(define (unop-cont op cont)
  (list
   (lambda (val)
     (apply-cont cont (any->expval (op (expval->any val)))))
   (lambda (val)
     (apply-handler val cont))))

; head-cont : Exp * Env * Cont -> Cont
(define (head-cont tail-exp env cont)
  (list
   (lambda (val)
     (value-of/k tail-exp env (tail-cont (expval->any val) cont)))
   (lambda (val)
     (apply-handler val cont))))

; tail-cont : Any * Cont -> Cont
(define (tail-cont head cont)
  (list
   (lambda (val)
     (apply-cont cont (list-val (cons head (expval->list val)))))
   (lambda (val)
     (apply-handler val cont))))

; report-uncaught-exception : Error
(define (report-uncaught-exception)
  (eopl:error "Uncaught exception!"))

;;;;;;;;;;;;;;;;;;;;;;;;;;; Interpreter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : String -> SchemeVal
(define (run string)
  (expval->any (value-of-program (scan&parse string))))

; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp) (value-of/k exp (init-env) (end-cont)))))

; value-of/k : Exp * Env * Cont -> FinalAnswer
(define (value-of/k exp env cont)
  (cases expression exp
    
    (const-exp (num)
      (apply-cont cont (num-val num)))
    
    (var-exp (var)
      (apply-cont cont (apply-env env var)))
    
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont)))

    (zero?-exp (e)
      (value-of/k e env (unop-cont zero? cont)))
    
    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-cont exp2 exp3 env cont)))

    (let-exp (var exp body)
      (value-of/k exp env (let-exp-cont var body env cont)))
    
    (proc-exp (var body)
      (apply-cont cont (proc-val (procedure var body env))))

    (call-exp (e1 e2)
      (value-of/k e1 env (rator-cont e2 env cont)))

    (letrec-exp (f x body letrec-body)
      (value-of/k letrec-body
                  (extend-env-rec f x body env)
                  cont))

    (try-exp (e v h)
      (value-of/k e env (try-cont v h env cont)))

    (raise-exp (e)
      (value-of/k e env (raise-cont cont)))
    
    (emptylist-exp ()
      (apply-cont cont (list-val '())))
    
    (cons-exp (e1 e2)
      (value-of/k e1 env (head-cont e2 env cont)))
    
    (null?-exp (e)
      (value-of/k e env (unop-cont null? cont)))

    (car-exp (e)
      (value-of/k e env (unop-cont car cont)))

    (cdr-exp (e)
      (value-of/k e env (unop-cont cdr cont)))

    (list-exp (e)
      (cond
        [(null? e) (apply-cont cont (list-val '()))]
        [else
         (value-of/k (car e) env
           (head-cont (list-exp (cdr e)) env cont))]))))