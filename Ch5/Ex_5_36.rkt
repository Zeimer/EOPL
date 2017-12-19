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
  (lambda (val cont ex)
    (value-of/k body (extend-env var val env) cont ex)))

; apply-procedure : Proc * ExpVal -> ExpVal
(define (apply-procedure f x cont ex) (f x cont ex))

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

; Cont = end-cont
;      | zero?-cont Cont
;      | let-exp-cont Var Exp Env Cont
;      | if-cont Exp Exp Env Cont
;      | diff1-cont Exp Env Cont
;      | diff2-cont ExpVal Cont
;      | rator-cont Exp Env Cont
;      | rand-cont Proc Cont
;      | try-cont Var Exp Env Cont
;      | raise1-cont Cont
(define-datatype cont cont?
  (end-cont)
  (zero?-cont (c cont?))
  (let-exp-cont
    (var identifier?) (body expression?) (env env?) (cont cont?))
  (if-cont
    (expt expression?) (expf expression?) (env env?) (cont cont?))
  (diff1-cont (exp expression?) (env env?) (cont cont?))
  (diff2-cont (v1 expval?) (cont cont?))
  (rator-cont (exp expression?) (env env?) (cont cont?))
  (rand-cont (f expval?) (cont cont?))
  (try-cont
    (var identifier?) (handle expression?) (env env?) (cont cont?)
    (ex cont?))
  (raise1-cont (cont cont?))
  (unop-cont (op any?) (cont cont?))
  (head-cont (tail-exp expression?) (env env?) (cont cont?))
  (tail-cont (head any?) (cont cont?)))

; apply-cont : Cont * ExpVal -> ExpVal
(define (apply-cont c ex val)
  (cases cont c
    (end-cont ()
      (begin
        (eopl:printf "End of computation.~%")
        val))
    (zero?-cont (cont)
      (apply-cont cont ex (bool-val (zero? (expval->num val)))))
    (let-exp-cont (var body env cont)
      (value-of/k body (extend-env var val env) cont ex))
    (if-cont (expt expf env cont)
      (if (expval->bool val)
          (value-of/k expt env cont ex)
          (value-of/k expf env cont ex)))
    (diff1-cont (exp env cont)
      (value-of/k exp env (diff2-cont val cont) ex))
    (diff2-cont (v1 cont)
      (apply-cont
        cont ex (num-val (- (expval->num v1) (expval->num val)))))
    (rator-cont (exp env cont)
      (value-of/k exp env (rand-cont val cont) ex))
    (rand-cont (f cont)
      (apply-procedure (expval->proc f) val cont ex))
    (try-cont (var handler env cont e)
      (apply-cont cont e val))
    (raise1-cont (cont)
      (apply-handler val ex))
    (unop-cont (op cont)
      (apply-cont cont ex (any->expval (op (expval->any val)))))
    (head-cont (tail-exp env cont)
      (value-of/k tail-exp env (tail-cont (expval->any val) cont) ex))
    (tail-cont (head cont)
      (apply-cont cont ex (list-val (cons head (expval->list val)))))))

; apply-handler : ExpVal * Cont -> ExpVal
(define (apply-handler val e)
  (cases cont e
    (try-cont (var handler env cont ex)
      (value-of/k handler (extend-env var val env) cont ex))
    (end-cont () (report-uncaught-exception))
    (zero?-cont (ex)
      (apply-handler val ex))
    (let-exp-cont (var body env ex)
      (apply-handler val ex))
    (if-cont (expt expf env ex)
      (apply-handler val ex))
    (diff1-cont (exp env ex)
      (apply-handler val ex))
    (diff2-cont (v1 ex)
      (apply-handler val ex))
    (rator-cont (exp env ex)
      (apply-handler val ex))
    (rand-cont (f ex)
      (apply-handler val ex))
    (raise1-cont (ex)
      (apply-handler val ex))
    (unop-cont (op ex)
      (apply-handler val ex))
    (head-cont (tail-exp env ex)
      (apply-handler val ex))
    (tail-cont (head ex)
      (apply-handler val ex))))


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
    (a-program (exp)
      (value-of/k exp (init-env) (end-cont) (end-cont)))))

; value-of/k : Exp * Env * Cont -> FinalAnswer
(define (value-of/k exp env cont ex)
  (cases expression exp
    
    (const-exp (num)
      (apply-cont cont ex (num-val num)))
    
    (var-exp (var)
      (apply-cont cont ex (apply-env env var)))
    
    (diff-exp (exp1 exp2)
      (value-of/k exp1 env (diff1-cont exp2 env cont) ex))

    (zero?-exp (e)
      (value-of/k e env (unop-cont zero? cont) ex))
    
    (if-exp (exp1 exp2 exp3)
      (value-of/k exp1 env (if-cont exp2 exp3 env cont) ex))

    (let-exp (var exp body)
      (value-of/k exp env (let-exp-cont var body env cont) ex))
    
    (proc-exp (var body)
      (apply-cont cont ex (proc-val (procedure var body env))))

    (call-exp (e1 e2)
      (value-of/k e1 env (rator-cont e2 env cont) ex))

    (letrec-exp (f x body letrec-body)
      (value-of/k letrec-body
                  (extend-env-rec f x body env)
                  cont ex))

    (try-exp (e v h)
      (value-of/k e env cont (try-cont v h env cont ex)))

    (raise-exp (e)
      (value-of/k e env (raise1-cont cont) ex))
    
    (emptylist-exp ()
      (apply-cont cont (list-val '())))
    
    (cons-exp (e1 e2)
      (value-of/k e1 env (head-cont e2 env cont) ex))
    
    (null?-exp (e)
      (value-of/k e env (unop-cont null? cont) ex))

    (car-exp (e)
      (value-of/k e env (unop-cont car cont) ex))

    (cdr-exp (e)
      (value-of/k e env (unop-cont cdr cont) ex))

    (list-exp (e)
      (cond
        [(null? e) (apply-cont cont ex (list-val '()))]
        [else
         (value-of/k (car e) env
           (head-cont (list-exp (cdr e)) env cont) ex)]))))